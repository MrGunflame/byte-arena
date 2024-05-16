#![no_main]

use arbitrary::Arbitrary;
use byte_arena::Arena;
use libfuzzer_sys::fuzz_target;

fuzz_target!(|ops: Vec<FuzzOp>| {
    let mut arena = Arena::new([0; 8192]);
    let mut keys = Vec::new();

    for op in ops {
        match op {
            FuzzOp::Alloc { size } => {
                let Ok(mut buf) = arena.alloc(size) else {
                    continue;
                };

                for b in buf.as_slice() {
                    if *b == 255 {
                        panic!("buffer already allocated");
                    }
                }

                buf.fill(255);
                keys.push(buf.index());
            }
            FuzzOp::Dealloc { index } => {
                if keys.len() == 0 {
                    continue;
                }

                let mut key = keys.remove(index % keys.len());

                let mut buf = arena.get_mut(key).unwrap();
                buf.fill(0);
                arena.dealloc(key);
            }
        }
    }
});

#[derive(Copy, Clone, Debug, Arbitrary)]
pub enum FuzzOp {
    Alloc { size: usize },
    Dealloc { index: usize },
}
