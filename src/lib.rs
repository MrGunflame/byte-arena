//! A statically sized arena for byte buffers.
//!
//! This crate provides an [`Arena`] for allocation of dynmically sized byte buffers (`[u8]`)
//! without dependency on `std` or `alloc`.
//!
//! # Usage
//!
//! ```
//! use byte_arena::Arena;
//!
//! // Create a new arena with 8KiB backing storage.
//! let mut arena = Arena::new([0; 8192]);
//!
//! // Allocate a 1KiB buffer.
//! let mut buf = arena.alloc(1024).unwrap();
//! buf.fill(42);
//! // The index allows access to the allocation after the
//! // buffer has been dropped.
//! let mut buf_index = buf.index();
//!
//! // Allocate a 1KiB zeroed buffer.
//! let mut zeroed_buffer = arena.alloc(1024).unwrap();
//! let mut zeroed_buffer_index = buf.index();
//!
//! let buf = arena.get(buf_index).unwrap();
//!
//! arena.dealloc(buf_index);
//! arena.dealloc(zeroed_buffer_index);
//! ```
//!
//! Note that the use of [`Index`] values between different [`Arena`] instances is not specified
//! and may cause panics, corrupt the internal representations but will not cause undefined
//! behavoir.

#![no_std]

#[cfg(test)]
extern crate std;

use core::fmt::{self, Display, Formatter};
use core::ops::{Deref, DerefMut};

/// A statically-sized arena for allocation of byte buffers.
#[derive(Clone, Debug)]
pub struct Arena<const N: usize> {
    storage: [u8; N],
    head: Option<NonMaxUsize>,
}

impl<const N: usize> Arena<N> {
    /// Creates a new `Arena`.
    #[inline]
    pub const fn new(storage: [u8; N]) -> Self {
        Self {
            storage,
            head: None,
        }
    }

    /// Allocates a new chunk from this `Arena`.
    ///
    /// Returns an [`AllocError`] if the given `size` exceeeds to amount of bytes this `Arena` can
    /// still allocate.
    ///
    /// Note that a zero-sized allocation will always suceed and a allocation greater than `N` will
    /// always fail.
    pub fn alloc(&mut self, size: usize) -> Result<BufMut<'_>, AllocError> {
        if size == 0 {
            return Ok(BufMut {
                index: Index(usize::MAX),
                slice: &mut [],
            });
        }

        // We can never allocate more than our buffer size is.
        if size > self.storage.len() - Header::SIZE {
            return Err(AllocError(size));
        }

        // Arena is completely empty, allocate the new chnuk at
        // the start.
        if self.head.is_none() {
            if size > self.storage.len() - Header::SIZE {
                return Err(AllocError(size));
            }

            let header = Header {
                next: None,
                prev: None,
                size,
            };

            self.head = NonMaxUsize::new(0);
            header.write_to_slice(&mut self.storage[..Header::SIZE]);
            return Ok(BufMut {
                index: Index(0),
                slice: &mut self.storage[Header::SIZE..Header::SIZE + size],
            });
        }

        let mut next = self.head.map(|v| v.get());

        while let Some(next_chunk) = next {
            let mut header = Header::from_slice(&self.storage[next_chunk..next_chunk + 24]);

            let chunk_start = next_chunk + Header::SIZE;
            let chunk_end = header.next.unwrap_or(NonMaxUsize::new(N).unwrap()).get();
            let chunk_len = chunk_end - chunk_start;
            let free_len = chunk_len - header.size;

            if free_len >= size + Header::SIZE {
                let new_chunk_start = chunk_start + header.size;
                let new_header = Header {
                    next: header.next,
                    prev: NonMaxUsize::new(next_chunk),
                    size,
                };

                if let Some(next) = &mut header.next {
                    let mut next_header = self.read_header(next.get());
                    next_header.prev = Some(NonMaxUsize::new(new_chunk_start).unwrap());
                    self.write_header(next.get(), next_header);
                }

                header.next = Some(NonMaxUsize::new(new_chunk_start).unwrap());

                header.write_to_slice(&mut self.storage[next_chunk..next_chunk + Header::SIZE]);

                new_header.write_to_slice(
                    &mut self.storage[new_chunk_start..new_chunk_start + Header::SIZE],
                );

                let index = Index(new_chunk_start);
                let slice = &mut self.storage
                    [new_chunk_start + Header::SIZE..new_chunk_start + Header::SIZE + size];

                return Ok(BufMut { index, slice });
            }

            next = header.next.map(|v| v.get());
        }

        Err(AllocError(size))
    }

    /// Allocates a new zeroed chunk from this `Arena`.
    ///
    /// This method is equivalent to `alloc`, except that the returned buffer is zeroed.
    pub fn alloc_zeroed(&mut self, size: usize) -> Result<BufMut<'_>, AllocError> {
        let mut buf = self.alloc(size)?;
        buf.fill(0);
        Ok(buf)
    }

    /// Deallocates a previously allocated chunk.
    pub fn dealloc(&mut self, index: Index) {
        let index = index.0;

        // Index points to outside our storage buffer and is invalid.
        if index.saturating_add(Header::SIZE) >= self.storage.len() {
            return;
        }

        let header = self.read_header(index);

        if cfg!(feature = "zero_headers") {
            self.storage[index..index + Header::SIZE].fill(0);
        }

        if let Some(next) = header.next {
            let mut next_header = self.read_header(next.get());
            next_header.prev = header.prev;
            self.write_header(next.get(), next_header);
        }

        if let Some(prev) = header.prev {
            let mut prev_header = self.read_header(prev.get());
            prev_header.next = header.next;
            self.write_header(prev.get(), prev_header);
        } else {
            self.head = header.next;
        }
    }

    /// Returns the chunk with the given [`Index`].
    pub fn get(&self, index: Index) -> Option<Buf<'_>> {
        let index = index.0;
        if index == usize::MAX {
            return Some(Buf {
                index: Index(index),
                slice: &[],
            });
        }

        if index.saturating_add(Header::SIZE) >= self.storage.len() {
            return None;
        }

        let header = Header::from_slice(self.storage.get(index..index + Header::SIZE)?);
        self.storage
            .get(index + Header::SIZE..index + Header::SIZE + header.size)
            .map(|slice| Buf {
                index: Index(index),
                slice,
            })
    }

    /// Returns the chunk with the given [`Index`] without checking if the [`Index`] is valid.
    ///
    /// # Safety
    ///
    /// The caller must guarantee:
    /// - The index has been returned from a [`Buf`] or [`BufMut`] value that has been allocated
    /// with this [`Arena`].
    /// - The buffer with the `index` has not been deallocated.
    /// - No [`Index`] values from a different [`Arena`] were ever given to [`get`], [`get_mut`],
    /// [`get_unchecked`], [`get_unchecked_mut`] or [`dealloc`] on this [`Arena`] instance.
    ///
    /// [`get`]: Self::get
    /// [`get_mut`]: Self::get_mut
    /// [`get_unchecked`]: Self::get_unchecked
    /// [`get_unchecked_mut`]: Self::get_unchecked_mut
    /// [`dealloc`]: Self::dealloc
    pub unsafe fn get_unchecked(&self, index: Index) -> Buf<'_> {
        let index = index.0;

        // SAFETY: The caller guarantees that the indices are in bounds and the
        // header instance is valid.
        unsafe {
            let header =
                Header::from_slice(self.storage.get_unchecked(index..index + Header::SIZE));
            let slice = self
                .storage
                .get_unchecked(index + Header::SIZE..index + Header::SIZE + header.size);
            Buf {
                index: Index(index),
                slice,
            }
        }
    }

    /// Returns the chunk with the given [`Index`].
    pub fn get_mut(&mut self, index: Index) -> Option<BufMut<'_>> {
        let index = index.0;

        if index == usize::MAX {
            return Some(BufMut {
                index: Index(index),
                slice: &mut [],
            });
        }

        if index.saturating_add(Header::SIZE) >= self.storage.len() {
            return None;
        }

        let header = Header::from_slice(self.storage.get(index..index + Header::SIZE)?);
        self.storage
            .get_mut(index + Header::SIZE..index + Header::SIZE + header.size)
            .map(|slice| BufMut {
                index: Index(index),
                slice,
            })
    }

    /// Returns the chunk with the given [`Index`] without checking if the [`Index`] is valid.
    ///
    /// # Safety
    ///
    /// The caller must guarantee:
    /// - The index has been returned from a [`Buf`] or [`BufMut`] value that has been allocated
    /// with this [`Arena`].
    /// - The buffer with the `index` has not been deallocated.
    /// - No [`Index`] values from a different [`Arena`] were ever given to [`get`], [`get_mut`],
    /// [`get_unchecked`], [`get_unchecked_mut`] or [`dealloc`] on this [`Arena`] instance.
    ///
    /// [`get`]: Self::get
    /// [`get_mut`]: Self::get_mut
    /// [`get_unchecked`]: Self::get_unchecked
    /// [`get_unchecked_mut`]: Self::get_unchecked_mut
    /// [`dealloc`]: Self::dealloc
    pub unsafe fn get_unchecked_mut(&mut self, index: Index) -> BufMut<'_> {
        let index = index.0;

        // SAFETY: The caller guarantees that the indices are in bounds and the
        // header instance is valid.
        unsafe {
            let header =
                Header::from_slice(self.storage.get_unchecked(index..index + Header::SIZE));
            let slice = self
                .storage
                .get_unchecked_mut(index + Header::SIZE..index + Header::SIZE + header.size);
            BufMut {
                index: Index(index),
                slice,
            }
        }
    }

    pub fn clear(&mut self) {
        self.head = None;

        if cfg!(feature = "zero_headers") {
            self.storage.fill(0);
        }
    }

    fn read_header(&mut self, index: usize) -> Header {
        Header::from_slice(&self.storage[index..index + Header::SIZE])
    }

    fn write_header(&mut self, index: usize, header: Header) {
        header.write_to_slice(&mut self.storage[index..index + Header::SIZE]);
    }
}

impl<const N: usize> Default for Arena<N> {
    #[inline]
    fn default() -> Self {
        Self::new([0; N])
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct AllocError(usize);

impl Display for AllocError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "allocation of {} bytes failed", self.0)
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Index(usize);

#[derive(Copy, Clone, Debug)]
struct Header {
    next: Option<NonMaxUsize>,
    prev: Option<NonMaxUsize>,
    size: usize,
}

#[derive(Copy, Clone, Debug)]
pub struct Buf<'a> {
    index: Index,
    slice: &'a [u8],
}

impl<'a> Buf<'a> {
    #[inline]
    pub fn index(&self) -> Index {
        self.index
    }
}

impl<'a> Deref for Buf<'a> {
    type Target = [u8];

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.slice
    }
}

#[derive(Debug)]
pub struct BufMut<'a> {
    index: Index,
    slice: &'a mut [u8],
}

impl<'a> BufMut<'a> {
    #[inline]
    pub fn as_slice(&self) -> &[u8] {
        &self.slice
    }

    #[inline]
    pub fn index(&self) -> Index {
        self.index
    }
}

impl<'a> Deref for BufMut<'a> {
    type Target = [u8];

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.slice
    }
}

impl<'a> DerefMut for BufMut<'a> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.slice
    }
}

impl Header {
    const SIZE: usize = 24;

    fn from_slice(slice: &[u8]) -> Self {
        let next: usize = usize::from_ne_bytes(slice[0..8].try_into().unwrap());
        let prev: usize = usize::from_ne_bytes(slice[8..16].try_into().unwrap());
        let size: usize = usize::from_ne_bytes(slice[16..24].try_into().unwrap());

        Self {
            next: NonMaxUsize::new(next),
            prev: NonMaxUsize::new(prev),
            size,
        }
    }

    fn write_to_slice(&self, buf: &mut [u8]) {
        buf[0..8].copy_from_slice(
            &self
                .next
                .map(|v| v.get())
                .unwrap_or(usize::MAX)
                .to_ne_bytes(),
        );
        buf[8..16].copy_from_slice(
            &self
                .prev
                .map(|v| v.get())
                .unwrap_or(usize::MAX)
                .to_ne_bytes(),
        );
        buf[16..24].copy_from_slice(&self.size.to_ne_bytes());
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
struct NonMaxUsize(usize);

impl NonMaxUsize {
    pub fn new(value: usize) -> Option<Self> {
        if value == usize::MAX {
            None
        } else {
            Some(Self(value))
        }
    }

    pub fn get(self) -> usize {
        self.0
    }
}

#[cfg(test)]
mod tests {
    use std::vec::Vec;

    use super::{Arena, Header, NonMaxUsize};

    #[test]
    fn arena_alloc() {
        let mut arena = Arena::new([0; 8192]);

        {
            arena.alloc(1024).unwrap();
            assert_eq!(arena.head, Some(NonMaxUsize::new(0).unwrap()));
            let header = arena.read_header(arena.head.unwrap().get());
            assert_eq!(header.next, None);
            assert_eq!(header.prev, None);
            assert_eq!(header.size, 1024);
        }

        {
            arena.alloc(1024).unwrap();
            assert_eq!(arena.head, Some(NonMaxUsize::new(0).unwrap()));
            let header0 = arena.read_header(arena.head.unwrap().get());
            assert_eq!(
                header0.next,
                Some(NonMaxUsize::new(1024 + Header::SIZE).unwrap())
            );
            assert_eq!(header0.prev, None);
            assert_eq!(header0.size, 1024);

            let header1 = arena.read_header(1024 + Header::SIZE);
            assert_eq!(header1.next, None);
            assert_eq!(header1.prev, Some(NonMaxUsize::new(0).unwrap()));
            assert_eq!(header1.size, 1024);
        }

        {
            arena.alloc(1024).unwrap();
            assert_eq!(arena.head, Some(NonMaxUsize::new(0).unwrap()));
            let header0 = arena.read_header(arena.head.unwrap().get());
            assert_eq!(
                header0.next,
                Some(NonMaxUsize::new(1024 + Header::SIZE).unwrap())
            );
            assert_eq!(header0.prev, None);
            assert_eq!(header0.size, 1024);

            let header1 = arena.read_header(1024 + Header::SIZE);
            assert_eq!(
                header1.next,
                Some(NonMaxUsize::new((1024 + Header::SIZE) * 2).unwrap())
            );
            assert_eq!(header1.prev, Some(NonMaxUsize::new(0).unwrap()));
            assert_eq!(header1.size, 1024);

            let header2 = arena.read_header((1024 + Header::SIZE) * 2);
            assert_eq!(header2.next, None);
            assert_eq!(
                header2.prev,
                Some(NonMaxUsize::new(1024 + Header::SIZE)).unwrap()
            );
            assert_eq!(header2.size, 1024);
        }
    }

    #[test]
    fn arena_alloc_free() {
        let mut arena = Arena::new([0; 8192]);

        for _ in 0..1024 {
            let index = arena.alloc(8000).unwrap().index();
            arena.dealloc(index);
        }
    }

    #[test]
    fn arena_alloc_free_with_growth() {
        let mut arena = Arena::new([0; 8192]);

        let keys: Vec<_> = (0..128).map(|_| arena.alloc(8).unwrap().index()).collect();

        for key in keys {
            arena.dealloc(key);
        }
    }

    #[test]
    fn fuzz1() {
        let mut arena = Arena::new([0; 8192]);
        let mut keys = Vec::new();

        keys.push(arena.alloc(16).unwrap().index());
        keys.push(arena.alloc(16).unwrap().index());
        arena.dealloc(keys.remove(1));
        arena.dealloc(keys.remove(0));
        assert_eq!(arena.head, None);
        keys.push(arena.alloc(64).unwrap().index())
    }
}
