use core::borrow::Borrow;
use core::fmt::{self, Display, Formatter};
use core::ops::{Deref, DerefMut};

#[derive(Clone, Debug)]
pub struct Arena<const N: usize> {
    storage: [u8; N],
    head: Option<NonMaxUsize>,
}

impl<const N: usize> Arena<N> {
    pub const fn new(storage: [u8; N]) -> Self {
        Self {
            storage,
            head: None,
        }
    }

    pub fn alloc(&mut self, size: usize) -> Result<BufMut<'_>, AllocError> {
        if size == 0 {
            return Ok(BufMut {
                index: Index(usize::MAX),
                slice: &mut [],
            });
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

    pub fn alloc_zeroed(&mut self, size: usize) -> Result<BufMut<'_>, AllocError> {
        let mut buf = self.alloc(size)?;
        buf.fill(0);
        Ok(buf)
    }

    pub fn dealloc(&mut self, index: Index) {
        let index = index.0;

        let header = self.read_header(index);

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

    pub fn get(&mut self) {}

    pub fn get_mut(&mut self, index: Index) -> Option<BufMut<'_>> {
        let header = Header::from_slice(self.storage.get(index.0..index.0 + Header::SIZE)?);
        self.storage
            .get_mut(index.0 + Header::SIZE..index.0 + Header::SIZE + header.size)
            .map(|slice| BufMut { index, slice })
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

impl<'a> Borrow<Index> for Buf<'a> {
    #[inline]
    fn borrow(&self) -> &Index {
        &self.index
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

impl<'a> Borrow<Index> for BufMut<'a> {
    #[inline]
    fn borrow(&self) -> &Index {
        &self.index
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
}
