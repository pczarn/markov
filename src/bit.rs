/// A trait which allows numbers to act as fixed-size bit arrays
pub trait BitArray {
  /// Is this bit set?
  fn bit(&self, idx: uint) -> bool;

  /// Returns an array which is just the bits from start to end
  fn bit_slice(&self, start: uint, end: uint) -> uint;

  /// 
  fn len_bits(&self) -> uint;
}

impl BitArray for uint {
    /// Is bit set?
    fn bit(&self, idx: uint) -> bool {
        (*self >> (idx % uint::BITS)) & 1 == 1
    }

    /// Returns an array which is just the bits from start to end
    fn bit_slice(&self, start: uint, end: uint) -> uint {
        (*self & (1 << end) - 1) >> start
    }

    fn len_bits(&self) -> uint {
        uint::BITS
    }
}

pub fn u64_from_le_bytes(data: &[u8], start: uint, size: uint) -> u64 {
    use std::ptr::{copy_nonoverlapping_memory};
    use std::num::Int;

    assert!(size <= 8u);

    if data.len() - start < size {
        panic!("index out of bounds");
    }

    let mut buf = [0u8, ..8];
    unsafe {
        let ptr = data.as_ptr().offset(start as int);
        let out = buf.as_mut_ptr();
        copy_nonoverlapping_memory(out.offset((8 - size) as int), ptr, size);
        Int::from_le(*(out as *const u64))
    }
}

impl<'a> BitArray for &'a [u8] {
    /// Is bit set?
    fn bit(&self, idx: uint) -> bool {
        (self[idx / u8::BITS] >> (idx % u8::BITS)) & 1 == 1
    }

    /// Returns an array which is just the bits from start to end
    fn bit_slice(&self, start: uint, end: uint) -> uint {
        // FIXME check for start oob?
        if start == end { return 0 }
        // if end - start == uint::BITS { return self[] }
        // if (end + u8::BITS - 1) / u8::BITS - start / u8::BITS > 8 {
        //     println!("{} {} {}", start, end, (end + u8::BITS - 1 - start) / u8::BITS)
        // }
        println!("{}-{}: {}-{} {}-{}", start, end, start / u8::BITS, (end + u8::BITS - 1 - start) / u8::BITS, start % u8::BITS, end - start + (start % u8::BITS));
        let r = u64_from_le_bytes(*self, start / u8::BITS, (end + u8::BITS - 1 - start) / u8::BITS) as uint;
        if end - start == 64 {
            r
        } else {
            // let start = ;
            r.bit_slice(start % u8::BITS, end - start + (start % u8::BITS))
        }

        // if (start / uint::BITS) == (end / uint::BITS) {
        //     self[start / uint::BITS].bit_slice(start % uint::BITS, end % uint::BITS)
        // } else if end % uint::BITS == 0 && end - start <= 64 {
        //     self[start / uint::BITS] >> (start % uint::BITS)
        // } else if end - start <= 64 {
        //     ((self[start / uint::BITS] >> (start % uint::BITS))
        //      | (
        //         (self[end / uint::BITS] & (end % uint::BITS))
        //             <<
        //         (uint::BITS - (start % uint::BITS))))
        // } else {
        //     fail!("invalid range from {} to {}", start, end);
        // }
    }

    fn len_bits(&self) -> uint {
        self.len() * u8::BITS
    }
}

impl<'a> BitArray for &'a [uint] {
    /// Is bit set?
    fn bit(&self, idx: uint) -> bool {
        (self[idx / uint::BITS] >> (idx % uint::BITS)) & 1 == 1
    }

    /// Returns an array which is just the bits from start to end
    fn bit_slice(&self, start: uint, end: uint) -> uint {
        // FIXME check for start oob?
        if start == end { return 0 }

        if (start / uint::BITS) == (end / uint::BITS) {
            self[start / uint::BITS].bit_slice(start % uint::BITS, end % uint::BITS)
        } else if end % uint::BITS == 0 && end - start <= 64 {
            self[start / uint::BITS] >> (start % uint::BITS)
        } else if end - start <= 64 {
            ((self[start / uint::BITS] >> (start % uint::BITS))
             | (
                (self[end / uint::BITS] & (end % uint::BITS))
                    <<
                (uint::BITS - (start % uint::BITS))))
        } else {
            panic!("invalid range from {} to {}", start, end);
        }
    }

    fn len_bits(&self) -> uint {
        self.len() * uint::BITS
    }
}

#[test]
fn test_bit() {
    // assert!(3u);
    assert!(3u.bit(0));
}

// impl uint {
//     /// Bitwise and with `n` ones
//     fn mask(self, n: uint) -> uint {
//         self & ((1 << n) - 1)
//     }

//     // /// Returns an array which is just the bits from start to end
//     // fn bit_slice_from(&self, start: uint, end: uint) -> &[uint] {
//     //     (*self & (1 << end) - 1) >> start
//     // }
// }
