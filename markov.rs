#![feature(phase)]

extern crate debug;
#[phase(plugin)]
extern crate regex_macros;
extern crate regex;

use std::io::{BufferedReader, File};
use std::rand;
use std::rand::Rng;
use std::collections::hashmap::{HashMap, HashSet};
use std::collections::TrieMap;
use std::cmp;
use std::mem::size_of;
use std::uint;
use std::fmt::Show;

struct WeightedTrie<T> {
_d:()
}

// struct FenwickTree

// struct SegmentTree {
//     root: Option<Box<TreeNode<K, V>>>,
//     length: uint
// }

// struct TreeNode<K, V> {
//     key: K,
//     value: V,
//     left: Option<Box<TreeNode<K, V>>>,
//     right: Option<Box<TreeNode<K, V>>>,
//     level: uint
// }

/// A trait which allows numbers to act as fixed-size bit arrays
pub trait BitArray {
  /// Is bit set?
  fn bit(&self, idx: uint) -> bool;

  /// Returns an array which is just the bits from start to end
  fn bit_slice(&self, start: uint, end: uint) -> uint;
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
            fail!("invalid range from {} to {}", start, end);
        }
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

struct PatriciaTrie<V> {
    data: Option<V>,
    child_l: Option<Box<PatriciaTrie<V>>>,
    child_r: Option<Box<PatriciaTrie<V>>>,
    prefix: uint,
    skip_len: u8
}

impl<V> PatriciaTrie<V> {
  pub fn new() -> PatriciaTrie<V> {
    PatriciaTrie {
      data: None,
      child_l: None,
      child_r: None,
      prefix: 0,
      skip_len: 0
    }
  }

  fn insert(&mut self, key: &[uint], value: V) -> bool {
    let mut node = self;
    let mut idx = 0;
    let key_len = key.len() * uint::BITS;

    // println!("insert({})", key);
    loop {
        // Mask in case search key is shorter than node key
        let slice_len = cmp::min(node.skip_len as uint,
                        cmp::min(key_len - idx,
                                 uint::BITS));
        let mut masked_prefix = node.prefix;
        if slice_len < 64 {
            masked_prefix &= ((1 << slice_len) - 1);
        }
        // println!("{} len::{} slice_len:{}", idx, key.len(), slice_len);
        let key_slice = if slice_len == 0 {
            0
        } else {
            key.bit_slice(idx, idx + slice_len)
        };

        // println!("{masked_prefix} == {key_slice}", masked_prefix = masked_prefix, key_slice = key_slice);
        if masked_prefix == key_slice {
            // Prefixes match
            let slice_len = key_len - idx;
            // Search key is shorter than skip prefix: truncate the prefix and attach
            // the old data as a child
            if node.skip_len as uint > slice_len {
                // Remove the old node's children
                let child_l = node.child_l.take();
                let child_r = node.child_r.take();
                let value_neighbor = node.data.take();
                // Put the old data in a new child, with the remainder of the prefix
                let new_child = if node.prefix.bit(slice_len)
                                  { &mut node.child_r } else { &mut node.child_l };
                *new_child = Some(box PatriciaTrie {
                  data: value_neighbor,
                  child_l: child_l,
                  child_r: child_r,
                  prefix: node.prefix >> (slice_len + 1),
                  skip_len: node.skip_len - slice_len as u8 - 1
                });
                // Chop the prefix down and put the new data in place
                node.skip_len = slice_len as u8;
                node.prefix = key_slice;
                node.data = Some(value);
                return true;
            }
            else if node.skip_len as uint == slice_len {
                // If we have an exact match, great, insert it
                // println!("exact");
                if node.data.is_none() {
                  node.data = Some(value);
                  return true;
                }
                // if overwrite {
                //   node.data = Some(value);
                // }
                return false;
            }
            else {
                // Search key longer than node key, recurse
                // println!("equal recurse {} + {} + 1", idx, node.skip_len);
                idx += node.skip_len as uint + 1;
                let tmp = node;  // hack to appease borrowck
                let subtree = if key.bit(idx - 1)
                                { &mut tmp.child_r } else { &mut tmp.child_l };
                let slice_len = cmp::min(key_len, idx + uint::BITS);
                // Recurse, adding a new node if necessary
                if subtree.is_none() {
                  // println!("skip_len: {slice_len} as u8 - {idx} as u8, prefix = {:x}", key.bit_slice(idx, slice_len), slice_len = slice_len, idx = idx)
                  *subtree = Some(box PatriciaTrie {
                    data: None,
                    child_l: None,
                    child_r: None,
                    prefix: key.bit_slice(idx, slice_len),
                    skip_len: slice_len as u8 - idx as u8
                  });
                }
                // subtree.get_mut_ref is a &mut Box<U> here, so &mut ** gets a &mut U
                node = &mut **subtree.get_mut_ref();
            } // end search_len vs prefix len
        }
        else {
            // Prefixes do not match: split key
            let diff = (masked_prefix ^ key_slice).trailing_zeros();
            // println!("{:x} ^ {:x}  diff={}", masked_prefix, key_slice, diff);

            // Remove the old node's children
            let child_l = node.child_l.take();
            let child_r = node.child_r.take();
            let value_neighbor = node.data.take();
            let tmp = node;  // borrowck hack
            let (mut insert, neighbor) = if key_slice.bit(diff)
                                          { (&mut tmp.child_r, &mut tmp.child_l) }
                                     else { (&mut tmp.child_l, &mut tmp.child_r) };

            // let mut sidx = idx + diff + 1;
            // // let mut eidx = key_len - sidx;
            // while key_len - sidx > uint::BITS {
            //     let mut tmp2 = box PatriciaTrie {
            //       data: None,
            //       child_l: None,
            //       child_r: None,
            //       prefix: key.bit_slice(sidx, sidx + uint::BITS),
            //       skip_len: uint::BITS as u8
            //     };
            //     let insert2 = if key.bit(sidx + uint::BITS) { &mut tmp2.child_r } else { &mut tmp2.child_l };
            //     *insert = Some(tmp2);
            //     sidx += uint::BITS + 1;
            // }
            let mut sidx = idx + diff + 1;
            let mut eidx = key_len;
            let mut obj = (None, None);
            // let mut eidx = key_len - sidx;
            while eidx - sidx > uint::BITS {
                let (l, r) = obj;
                // println!("{}  len:{}", eidx - uint::BITS, key.len());
                let mut tmp2 = box PatriciaTrie {
                  data: None,
                  child_l: l,
                  child_r: r,
                  prefix: key.bit_slice(eidx - uint::BITS, eidx),
                  skip_len: uint::BITS as u8
                };
                eidx -= uint::BITS + 1;
                obj = if key.bit(eidx) { (None, Some(tmp2)) } else { (Some(tmp2), None) };
                // let insert2 = if key.bit(sidx + uint::BITS) { &mut tmp2.child_r } else { &mut tmp2.child_l };
                // *insert = Some(tmp2);
                // sidx += uint::BITS + 1;
            }
            // if (key_len - idx - diff - 1) <= 64 {
                let (l, r) = obj;
                // println!("{}  len:{}", sidx, key.len());
                *insert = Some(box PatriciaTrie {
                    data: None,
                    child_l: l,
                    child_r: r,
                    prefix: key.bit_slice(sidx, eidx),
                    skip_len: (eidx - sidx) as u8
                });
            // } else {
            //     let mut oidx = idx + diff + 1;
            //     let mut nidx = cmp::min(oidx + uint::BITS, key_len);
            //     loop {
            //         *insert = Some(box PatriciaTrie {
            //           data: None,
            //           child_l: None,
            //           child_r: None,
            //           prefix: key.bit_slice(oidx, nidx),
            //           skip_len: (nidx - oidx) as u8
            //         });
            //         if nidx == key_len { break; }
            //         oidx = nidx;
            //         nidx = cmp::min
            //         insert = &mut insert.child_
            //     }
            // }
            *neighbor = Some(box PatriciaTrie {
              data: value_neighbor,
              child_l: child_l,
              child_r: child_r,
              prefix: tmp.prefix >> (diff + 1),
              skip_len: tmp.skip_len - diff as u8 - 1
            });
            // Chop the prefix down
            tmp.skip_len = diff as u8;
            tmp.prefix = tmp.prefix & ((1 << diff) - 1);
            // Recurse
            // println!("recurse");
            idx += 1 + diff;
            node = &mut **insert.get_mut_ref();
        } // end if prefixes match
    } // end loop
  }

  pub fn lookup<'a>(&'a self, key: &[uint]) -> Option<&'a V> {
    let mut node = self;
    let mut key_idx = 0;
    let key_len = key.len() * uint::BITS;

    // println!("lookup({})", key);
    loop {
        // If the search key is shorter than the node prefix, there is no
        // way we can match, so fail.
        if key_len - key_idx < node.skip_len as uint {
          return None;
        }



        // Key fails to match prefix --- no match
        if node.prefix != key.bit_slice(key_idx, key_idx + node.skip_len as uint) {
          return None;
        }

        // Key matches prefix: if they are an exact match, return the data
        if node.skip_len as uint == key_len - key_idx {
          return node.data.as_ref();
        } else {
          // Key matches prefix: search key longer than node key, recurse
          key_idx += 1 + node.skip_len as uint;
          let subtree = if key.bit(key_idx - 1) { &node.child_r } else { &node.child_l };
          // println!("bit {} => {}", key_idx - 1, key.bit(key_idx - 1));
          match subtree {
            &Some(ref bx) => {
              node = &**bx;  // bx is a &Box<U> here, so &**bx gets &U
            }
            &None => { return None; }
          }
        }
    } // end loop
  }

  /// Lookup a value by exactly matching `key` and return a referenc
  pub fn lookup_mut<'a>(&'a mut self, key: &[uint]) -> Option<&'a mut V> {
    // Caution: `lookup_mut` never modifies its self parameter (in fact its
    // internal recursion uses a non-mutable self, so we are OK to just
    // transmute our self pointer into a mutable self before passing it in.
    use std::mem::transmute;
    unsafe { transmute(self.lookup(key)) }
  }
}

impl<V:Show> PatriciaTrie<V> {
  /// Print the entire tree
  pub fn print<'a>(&'a self) {
    fn recurse<'a, V:Show>(tree: &'a PatriciaTrie<V>, depth: uint) {
      for i in range(0, tree.skip_len as uint) {
        print!("{:}", if tree.prefix.bit(i) { 1u } else { 0 });
      }
      println!(": {:}", tree.data);
      // left gets no indentation
      match tree.child_l {
        Some(ref t) => {
          for _ in range(0, depth + tree.skip_len as uint) {
            print!("-");
          }
          print!("0");
          recurse(&**t, depth + tree.skip_len as uint + 1);
        }
        None => { }
      }
      // right one gets indentation
      match tree.child_r {
        Some(ref t) => {
          for _ in range(0, depth + tree.skip_len as uint) {
            print!("_");
          }
          print!("1");
          recurse(&**t, depth + tree.skip_len as uint + 1);
        }
        None => { }
      }
    }
    recurse(self, 0);
  }
}

fn append(trie: &mut PatriciaTrie<Vec<uint>>, slice: &[uint], elem: uint) {
    let found = match trie.lookup_mut(slice) {
        Some(set_ref) => {
            // set_ref.find_with_or_insert_with(interned_syl, (), |_k, v_ref, _u| *v_ref += 1, |_k, _u| 1);
            set_ref.push(elem);
            true
        }
        None => false
    };

    if !found {
        let mut syllable_multiset: Vec<uint> = Vec::new();

        syllable_multiset.push(elem);

        trie.insert(slice, syllable_multiset);
    }
}

fn main() {
    let mut intern_syl: HashMap<String, uint> = HashMap::new();
    let mut intern_syl_vec: Vec<String> = Vec::new();
    // let mut syllable_multiset: Vec<uint> = Vec::new();
    let mut syl_trie: PatriciaTrie<Vec<uint>> = PatriciaTrie::new();
    // let mut syl_trie = TrieMap::new();

    // let s = "Ala ma ko ta lu bi mle ko ten ko tek ży";
    // Ala ma ko ta lu bi mle ten

    intern_syl.insert(" ".to_string(), 0);
    intern_syl_vec.push(" ".to_string());
    let mut syls = vec![0, 0, 0];//Vec::new();

    let file = File::open(&Path::new("data/ASOIAF.txt"));
    let mut reader = BufferedReader::new(file);

    for line in reader.lines() {
        let line = line.unwrap();
        let tokens = regex!(r"([:\d\.]+|[\p{Alphabetic}'-]+|\p{P}\s?|\s)");
        let whitespace = regex!(r"\s+");

        let line = whitespace.replace_all(line.as_slice(), " ");

        for (start, end) in tokens.find_iter(line.as_slice()) {
            let syl = line.as_slice().slice(start, end);
            let i = intern_syl.len();
            let interned_syl = *intern_syl.find_with_or_insert_with(syl.to_string(),
                                                                    i,
                                                                    |_k, _v, _a| (),
                                                                    |_k, a| {
                                                                        intern_syl_vec.push(syl.to_string());
                                                                        a
                                                                    });

            // syllable_multiset.find_with_or_insert_with(interned_syl, (), |_k, v_ref, _u| *v_ref += 1, |_k, _u| 1);
            // syllable_multiset.push(interned_syl);

            match syls.slice_from(syls.len() - 3) {
                [a, b, c] => {
                    append(&mut syl_trie, &[c, b, a], interned_syl);
                    append(&mut syl_trie, &[c, b], interned_syl);
                    append(&mut syl_trie, &[c], interned_syl);
                }
                _ => unreachable!()
            }

            syls.push(interned_syl);
        }
    }

    // for i in range(0u, intern_syl_vec.len()) {
    //     match syl_trie.lookup(&[i]) {
    //         Some(set_ref) => {
    //             println!("{} => {}!!", i, set_ref);
    //         }
    //         None => {
    //             println!("None: {}", i);
    //         }
    //     }
    // }

    // intern_syl.insert("Ala".to_string(), 0);
    // intern_syl.insert(" ".to_string(), 1);
    // intern_syl.insert("ma".to_string(), 2);
    // intern_syl.insert("ko".to_string(), 3);
    // intern_syl.insert("ta".to_string(), 4);

    // syllable_multiset.insert(4, 1);

    // let path = [3u, 2];

    // println!("{:?}", syl_trie);
    // syl_trie.print();
    // println!("{}", syllable_multiset);

    // // syl_trie.insert(path.as_slice(), 12345);
    // // syl_trie.insert(path.as_slice().slice_to(1), 6789u);

    // // println!("{:?}", syl_trie);
    // // println!("{:?}", path.as_slice().bit_slice(1, 65));

    // println!("{:?}", syl_trie.lookup(path.as_slice()));

    let mut rng = rand::task_rng();

    // let i: uint = rng.gen_range();
    let last_i = rng.gen_range(0, syls.len());
    let mut last = *rng.choose(syls.as_slice()).unwrap();//intern_syl_vec.get(last_i);
    // println!("{}", last);

    for _ in range(0u, 10000) {
        match syl_trie.lookup(&[last]) {
            Some(set_ref) => {
                let len = set_ref.len();
                let i = rng.gen_range(0, len);
                last = set_ref[i];
                // let (&i, _) = set_ref.iter().skip(i).next().unwrap();
                // println!("{} => {}!", last_i, i);
                // last_i = i;
                // println!("{}!", intern_syl_vec.get(last_i));
            }
            None => {
                last = syls[rng.gen_range(0, syls.len())];
                // println!("{}", intern_syl_vec.get(last_i));
            }
        }
        print!("{}", intern_syl_vec.get(last));
    }
    println!("\n{}", intern_syl_vec.len());
}
