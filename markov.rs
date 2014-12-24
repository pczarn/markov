#![feature(phase, default_type_params, while_let)]

#[phase(plugin)]
extern crate regex_macros;
extern crate regex;

use std::io::{BufferedReader, File};
use std::rand;
use std::rand::Rng;
use std::rand::distributions::{IndependentSample, Sample, Range};
use std::collections::{HashMap, HashSet};
use std::collections::hash_map::Entry;
use std::collections::TrieMap;
use std::collections::RingBuf;
use std::cmp;
use std::cmp::{Ord, Equal, Greater, Less};
use std::mem::size_of;
use std::uint;
use std::u8;
use std::u64;
use std::fmt::Show;
use std::hash::Hash;
use std::default::Default;
use std::clone::Clone;
use std::mem;
use std::rc::Rc;
use std::iter::Iterator;
use std::str;
use std::slice::SlicePrelude;

use std::io::extensions::u64_from_be_bytes;

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
        println!("{}-{}: {}-{} {}-{}", start, end, start / u8::BITS, (end + u8::BITS - 1 - start) / u8::BITS, start % u8::BITS, end - start + (start % u8::BITS))
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

// struct WeightedPatriciaTrie<V> {
//     data: Option<V>,

//     child_l: Option<Box<PatriciaTrie<V>>>,
//     child_r: Option<Box<PatriciaTrie<V>>>,
//     weight_l: uint,
//     prefix: uint,
//     skip_len: u8
// }

#[deriving(Clone, Default)]
struct NoData<V>;

trait TreeData<V> {
    fn update(&mut self, value: &V);
    fn add(&mut self, other: &Self);
}

impl<V> TreeData<V> for NoData<V> {
    #[inline]
    fn update(&mut self, _v: &V) {}
    fn add(&mut self, _o: &NoData<V>) {}
}

// enum Child<V> {
//     Internal(PatriciaTrie<V>),
//     External()
// }

struct PatriciaTrie<V, D = NoData<V>> {
    data: Option<V>,
    data_l: D,
    child_l: Option<Box<PatriciaTrie<V, D>>>,
    child_r: Option<Box<PatriciaTrie<V, D>>>,
    prefix: uint,
    // skip_prefix: uint,
    skip_len: u8
}

impl<V, D: Clone + Default + TreeData<V>> PatriciaTrie<V, D> {
  pub fn new() -> PatriciaTrie<V, D> {
    PatriciaTrie {
      data: None,
      data_l: Default::default(),
      child_l: None,
      child_r: None,
      prefix: 0,
      skip_len: 0
      // skip_prefix: 0,
    }
  }

  fn insert<K: BitArray>(&mut self, key: K, value: V) -> bool {
    let mut node = self;
    let mut idx = 0;
    let key_len = key.len_bits();

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
            match (node.skip_len as uint).cmp(&slice_len) {
                Greater => {
                    // Remove the old node's children
                    let child_l = node.child_l.take();
                    let child_r = node.child_r.take();
                    let value_neighbor = node.data.take();
                    // Put the old data in a new child, with the remainder of the prefix
                    let (new_child, data_l) = if node.prefix.bit(slice_len) {
                        (&mut node.child_r, Default::default())
                    } else {
                        (&mut node.child_l, node.data_l.clone())
                    };
                    *new_child = Some(box PatriciaTrie {
                        data: value_neighbor,
                        data_l: mem::replace(&mut node.data_l, data_l),
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
                Equal => {
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
                Less => {
                    // Search key longer than node key, recurse
                    idx += node.skip_len as uint + 1;
                    let tmp = node;  // hack to appease borrowck
                    let subtree = if key.bit(idx - 1)
                                    { &mut tmp.child_r } else {
                        // The value is going to be inserted in the left branch.
                        tmp.data_l.update(&value);
                        &mut tmp.child_l
                    };
                    let slice_len = cmp::min(key_len, idx + uint::BITS);
                    // Recurse, adding a new node if necessary
                    if subtree.is_none() {
                      // println!("skip_len: {slice_len} as u8 - {idx} as u8, prefix = {:x}", key.bit_slice(idx, slice_len), slice_len = slice_len, idx = idx)
                      *subtree = Some(box PatriciaTrie {
                        data: None,
                        data_l: Default::default(),
                        child_l: None,
                        child_r: None,
                        prefix: key.bit_slice(idx, slice_len),
                        skip_len: slice_len as u8 - idx as u8
                      });

                    }
                    // subtree.as_mut().unwrap() is a &mut Box<U> here, so &mut ** gets a &mut U
                    node = &mut **subtree.as_mut().unwrap();
                }
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

            let mut sidx = idx + diff + 1;
            let mut eidx = key_len;
            let mut obj = (None, None);
            while eidx - sidx > uint::BITS {
                let (l, r) = obj;
                let mut tmp2 = box PatriciaTrie {
                    data: None,
                    data_l: Default::default(),
                    child_l: l,
                    child_r: r,
                    prefix: key.bit_slice(eidx - uint::BITS, eidx),
                    skip_len: uint::BITS as u8
                };
                eidx -= uint::BITS + 1;
                obj = if key.bit(eidx) { (None, Some(tmp2)) } else { (Some(tmp2), None) };
            }
            let (l, r) = obj;
            *insert = Some(box PatriciaTrie {
                data: None,
                data_l: Default::default(),
                child_l: l,
                child_r: r,
                prefix: key.bit_slice(sidx, eidx),
                skip_len: (eidx - sidx) as u8
            });
            *neighbor = Some(box PatriciaTrie {
                data: value_neighbor,
                data_l: Default::default(),
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
            node = &mut **insert.as_mut().unwrap();
        } // end if prefixes match
    } // end loop
  }
}

impl<V, D: Default + TreeData<V>> PatriciaTrie<V, D> {
  pub fn lookup<'a, K: BitArray>(&'a self, key: K) -> Option<&'a V> {
    let mut node = self;
    let mut key_idx = 0;
    // let key_len = key.len() * uint::BITS;
    let key_len = key.len_bits();

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

  /// Lookup a value by exactly matching `key` and return a ref
  pub fn lookup_mut<'a>(&'a mut self, key: &[uint]) -> Option<&'a mut V> {
    use std::mem::transmute;
    let res: Option<&'a V> = self.lookup(key);
    let res: Option<&'a mut V> = unsafe { transmute(res) };
    res
  }
}

impl<V, D: Default + TreeData<V>> PatriciaTrie<V, D> {
  pub fn subtree<'a>(&'a self, key: &[uint], f: |&PatriciaTrie<V, D>, bool|) -> (&'a PatriciaTrie<V, D>, uint) {
    let mut node = self;
    let mut key_idx = 0;
    let key_len = key.len() * uint::BITS;

    // if key_len == 0 { return (node, 0) }

    loop {
        // // If the search key is shorter than the node prefix, there is no
        // // way we can match, so fail.
        if key_len - key_idx < node.skip_len as uint {
            return (node, key_idx);
        }

        // Key fails to match prefix --- no match
        if node.prefix != key.bit_slice(key_idx, key_idx + node.skip_len as uint) {
            return (node, key_idx);
        }

        // Key matches prefix: if they are an exact match, return the data
        if node.skip_len as uint == key_len - key_idx {
            return (node, key_len);
        } else {
            // f(node);
            // Key matches prefix: search key longer than node key, recurse
            key_idx += 1 + node.skip_len as uint;
            let subtree = if key.bit(key_idx - 1) {
                // if node.child_r.is_some() { f(node) } // NOPE
                &node.child_r
            } else { &node.child_l };
            // println!("bit {} => {}", key_idx - 1, key.bit(key_idx - 1));
            match subtree {
                &Some(ref bx) => {
                    f(node, key.bit(key_idx - 1));
                    node = &**bx;  // bx is a &Box<U> here, so &**bx gets &U
                }
                &None => { return (node, key_idx - 1); }
            }
        }
    } // end loop
  }

  pub fn walk<'a>(&'a self, f: |&PatriciaTrie<V, D>| -> bool) -> Option<&'a V> {
    let mut node = self;

    loop {
        // Key matches prefix: if they are an exact match, return the data
        if node.child_l.is_none() && node.child_r.is_none() {
            return node.data.as_ref();
        } else {
            let subtree = if f(node) { &node.child_r } else { &node.child_l };
            match subtree {
                &Some(ref bx) => {
                  node = &**bx;  // bx is a &Box<U> here, so &**bx gets &U
                }
                &None => { return None; }
            }
        }
    } // end loop
  }

  // /// Returns an iterator over all elements in the tree
  // pub fn iter<'a>(&'a self) -> Items<'a, V> {
  //   Items {
  //     node: Some(self),
  //     parents: vec![],
  //     started: false
  //   }
  // }

  #[inline]
  pub fn map<Q, U: Default + TreeData<Q>>(self,
                mut f: |V| -> Q)
                -> (PatriciaTrie<Q, U>, U) {
    fn recurse<V, D: TreeData<V>, Q, U: Default + TreeData<Q>>(subtree: PatriciaTrie<V, D>,
                                                               outer_data: &mut U,
                                                               f: &mut |V| -> Q)
                                                               -> PatriciaTrie<Q, U> {
        let PatriciaTrie {
            data,
            child_l,
            child_r,
            prefix,
            skip_len,
            ..
        } = subtree;

        let mut data_l: U = Default::default();

        let data = data.map(|d| {
            let v = (*f)(d);
            outer_data.update(&v);
            v
        });

        let child_l = child_l.map(|child| box recurse(*child, &mut data_l, f));
        let child_r = child_r.map(|child| box recurse(*child, outer_data, f));

        outer_data.add(&data_l);

        PatriciaTrie {
            data: data,
            data_l: data_l,
            child_l: child_l,
            child_r: child_r,
            prefix: prefix,
            skip_len: skip_len
        }
    }

    let mut data_l = Default::default();
    let trie = recurse(self, &mut data_l, &mut f);
    (trie, data_l)
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

struct MarkovModel {
    model: WeightedPatriciaTrie<WeightedVec<uint>>,
    total_weight: uint,
}

impl MarkovModel {
    fn new(trie: PatriciaTrie<Vec<uint>>) -> MarkovModel {
        let (weighted_trie, bound) = trie.map(|v| WeightedVec::from_vec(v));
        MarkovModel {
            model: weighted_trie,
            total_weight: bound.weight,
        }
    }

    fn sample(&self, rng: &mut rand::TaskRng, buf_slice: &[uint], at_least: uint) -> Option<uint> {
        let mut high = self.total_weight;//self.between.sample(rng);

        // let (node, depth) = self.model.subtree(buf_slice, |subtree| {
        //     // println!("rand={}", rand);
        //     if rand >= subtree.data_l.weight {
        //         rand -= subtree.data_l.weight;
        //     }
        // });
        // print!("@");
        let (node, depth) = self.model.subtree(buf_slice, |subtree, dir| {
            high = if dir {
                high - subtree.data_l.weight
            } else {
                subtree.data_l.weight
            }
        });

        // print!("[{}<{}]", depth, at_least);
        if depth < at_least {
            return None;
        }

        let mut rand = rng.gen_range(0, high);

        // print!("$");
        node.walk(|subtree| {
            if rand < subtree.data_l.weight {
                false
            } else {
                rand -= subtree.data_l.weight;
                true
            }
        }).and_then(|weighted_vec| {
            // print!("%")
            // assert!(rand < weighted_vec.len());
            // assert_eq!(rand, weighted_vec.len()); // NOPE
            // weighted_vec.bsearch(rand)
            // if weighted_vec.len() <= 2 { println!("{}; {}", weighted_vec.len(), weighted_vec.inner) };
            weighted_vec.bsearch(rand)
        }).map(|n| *n)
    }
}

struct MarkovChain {
    state: Vec<uint>,
    last_meaningful: uint,
    order: uint,
    model: MarkovModel,
    rng: rand::TaskRng,
}

impl MarkovChain {
    fn new(model: MarkovModel, order: uint) -> MarkovChain {
        MarkovChain {
            state: Vec::with_capacity(order),
            last_meaningful: 0,
            order: order,
            model: model,
            rng: rand::task_rng(),
        }
    }
}

impl Iterator<uint> for MarkovChain {
    fn next(&mut self) -> Option<uint> {
        loop {
            // println!(";\n:: {} #{}:{}", self.last_meaningful, self.state.len(), self.state)
            let sample = self.model.sample(&mut self.rng, self.state.as_slice(), self.last_meaningful * uint::BITS);

            match sample {
                Some(elem) => {
                    if self.rng.gen_range(0, self.order * 8 - self.state.len() * 2) < self.order {
                        self.state.pop();
                        self.state.pop();
                        // self.last_meaningful = cmp::max(self.last_meaningful, 1) - 1;
                        self.last_meaningful = 0;
                        // println!("#");
                    } else if self.state.len() == self.order {
                        self.state.pop();
                    }
                    else {
                        self.last_meaningful += 1;
                    }
                    self.state.insert(0, elem);
                    return Some(elem);
                }
                None => {
                    self.state.pop();
                    self.last_meaningful -= 1;
                }
            }
        }
    }
}

#[deriving(Show)]
struct TrieInfo {
    elems: uint,
    nodes: uint,
    meaningful: uint,
    skipped: uint,
}

impl<V> PatriciaTrie<V> {
  /// Print the entire tree
  pub fn print_stat<'a>(&'a self) {
    fn recurse<'a, V>(tree: &'a PatriciaTrie<V>, depth: uint, info: &mut TrieInfo) {
      // for i in range(0, tree.skip_len as uint) {
      //   print!("{:}", if tree.prefix.bit(i) { 1u } else { 0 });
      // }
      // println!(": {:}", tree.data);
      info.skipped += tree.skip_len as uint;
      if tree.data.is_some() { info.elems += 1; }
      if tree.child_l.is_some() && tree.child_r.is_some() { info.meaningful += 1; }
      info.nodes += 1;
      // left gets no indentation
      match tree.child_l {
        Some(ref t) => {
          // for _ in range(0, depth + tree.skip_len as uint) {
          //   print!("-");
          // }
          // print!("0");
          recurse(&**t, depth + tree.skip_len as uint + 1, info);
        }
        None => { }
      }
      // right one gets indentation
      match tree.child_r {
        Some(ref t) => {
          // for _ in range(0, depth + tree.skip_len as uint) {
          //   print!("_");
          // }
          // print!("1");
          recurse(&**t, depth + tree.skip_len as uint + 1, info);
        }
        None => { }
      }
    }
    let mut info = TrieInfo { elems: 0, nodes: 0, meaningful: 0, skipped: 0 };
    recurse(self, 0, &mut info);
    println!("{}", info);
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

// TODO: std​::rand​::distributions​::WeightedChoice​
#[deriving(Default, Show)]
struct IndexedItem<T> {
    end_idx: uint,
    item: T
}

// ?
#[deriving(Default)]
struct WeightedVec<T> {
    inner: Vec<IndexedItem<T>>,
    len: uint
}

#[deriving(Clone, Default)]
struct Weight<V> {
    weight: uint
}

impl<V: Collection> TreeData<V> for Weight<V> {
    #[inline]
    fn update(&mut self, value: &V) {
        self.weight += value.len();
    }

    #[inline]
    fn add(&mut self, other: &Weight<V>) {
        self.weight += other.weight;
    }
}

type WeightedPatriciaTrie<V> = PatriciaTrie<V, Weight<V>>;

impl<T: Copy + Eq + Hash> WeightedVec<T> {
    pub fn from_multiset(multiset: &HashMap<T, uint>) -> WeightedVec<T> {
        let mut cumul = 0u;
        let inner = multiset.iter().map(|(&elem, &count)| {
            cumul += count;
            // println!("{}", cumul);
            IndexedItem {
                end_idx: cumul,
                item: elem
            }
        }).collect();
        WeightedVec {
            inner: inner,
            len: cumul
        }
    }
}

impl<T: Eq + Ord> WeightedVec<T> {
    pub fn from_vec(mut vec: Vec<T>) -> WeightedVec<T> {
        vec.sort();
        let mut iter = vec.into_iter();
        match iter.next() {
            Some(mut first) => {
                let mut cumul_sum = 0;
                let mut weighted_vec = vec![];

                for v in iter {
                    cumul_sum += 1;
                    if v != first {
                        weighted_vec.push(IndexedItem {
                            end_idx: cumul_sum,
                            item: mem::replace(&mut first, v)
                        });
                    }
                }
                cumul_sum += 1;
                weighted_vec.push(IndexedItem {
                    end_idx: cumul_sum,
                    item: first
                });

                WeightedVec {
                    inner: weighted_vec,
                    len: cumul_sum
                }
            }
            None => WeightedVec {
                inner: vec![],
                len: 0
            }
        }
    }
}

impl<T> WeightedVec<T> {
    fn bsearch<'a>(&'a self, idx: uint) -> Option<&'a T> {
        // println!("idx={} {:?}", idx, self);
        let mut base: uint = 0;
        let mut lim: uint = self.inner.len();

        while lim != 0 {
            let ix = base + (lim >> 1);
            // println!("ix={}", ix);
            if idx > self.inner[ix].end_idx {
                base = ix + 1;
                lim -= 1;
                // println!("less than self.inner[{}].end_idx={} base={} lim={}", ix, self.inner[ix].end_idx, base, lim);
            } else if ix == 0 || idx >= self.inner[ix - 1].end_idx {
                return Some(&self.inner[ix].item);
            }
            lim >>= 1;
        }
        // return None;
        Some(&self.inner[0].item)
    }
}

trait Collection {
    fn len(&self) -> uint;
}

impl<T> Collection for WeightedVec<T> {
    fn len(&self) -> uint {
        self.len
    }
}

static ORDER: uint = 6;

fn main() {
    // DST ?
    let mut dict_trie: PatriciaTrie<Vec<u16>> = PatriciaTrie::new();
    let file = File::open(&Path::new("/usr/share/myspell/dicts/hyph_en_US.dic"));
    let mut reader = BufferedReader::new(file);

    for line in reader.lines().skip(3) {
        let line = line.unwrap();
        let mut buf = [0u16, ..32];
        let mut i = 0u;
        // let mut s = String::with_capacity(line.len() / 2);
        let mut s = Vec::with_capacity(line.len() / 2);
        for ch in line.as_slice().trim().chars() {
            if ch.is_digit() {
                let n = ch.to_digit(10).unwrap();
                let mut x = (1 << ((n + 1) >> 1)) - 1;
                if n & 1 == 0 {
                    x |= x << 8;
                }
                buf[i] = x;
                println!("{} {}", x, buf.slice_to(i));
            } else {
                s.push(ch as uint);
                if i > 32 { println!("{}", i); }
                i += 1;
            }
        }

        if buf[i] != 0 {
            i += 1;
        }

        // impl BitStream for &[T]
        let b=dict_trie.insert(s.as_slice(), buf.slice_to(i).to_vec());
        println!("{} => {} {}", s, buf.slice_to(i), b);
        assert_eq!(Some(buf.slice_to(i)), dict_trie.lookup(s.as_slice()).map(|x|x.as_slice()));
        println!("");
    }
    // println!("{}", dict_trie.lookup("ttes".as_bytes()));

    let mut intern_syl: HashMap<Rc<String>, uint> = HashMap::new();
    let mut intern_syl_vec: Vec<Rc<String>> = Vec::new();
    // let mut syllable_multiset: Vec<uint> = Vec::new();
    // let mut syl_trie: HashMap<&[uint], Vec<uint>> = PatriciaTrie::new();
    let mut syl_trie: PatriciaTrie<Vec<uint>> = PatriciaTrie::new();
    // let mut syl_trie: PatriciaTrie<HashSet<uint, uint>> = PatriciaTrie::new();
    // let mut syl_trie = TrieMap::new();

    // let s = "Ala ma ko ta lu bi mle ko ten ko tek ży";
    // Ala ma ko ta lu bi mle ten

    let space = Rc::new(" ".to_string());
    intern_syl.insert(space.clone(), 0);
    intern_syl_vec.push(space);
    let mut buf_syls = Vec::from_elem(ORDER, 0);

    let file = File::open(&Path::new("data/ASOIAF.txt"));
    let mut reader = BufferedReader::new(file);

    let tokens = regex!(r"[:\d\.]+|[\p{Alphabetic}'-]+|\p{P}\s*|\s+|$");

    let mut wraparound_buf = String::new();

    while let Ok(buf) = reader.fill_buf() {
        let buf = str::from_utf8(buf).unwrap();
        let buf = if wraparound_buf.is_empty() {
            buf
        } else {
            let end = match tokens.find(buf) {
                Some((start, end)) => {
                    // let (beginning, rest) = buf.split_at(end);
                    wraparound_buf.push_str(buf.slice_to(end));
                    end
                }
                None => continue
            };
            buf.slice_from(end)
        };

        // for (start, end) in tokens.find_iter(wraparound_buf.as_slice()).chain(tokens.find_iter(buf)) {
        for (start, end) in tokens.find_iter(buf) {
            if end == buf.len() && start != end {
                wraparound_buf.push_str(buf.slice_from(start));
            }

            let syl_untrim = buf.slice(start, end);
            let mut syl = syl_untrim.trim_right().into_string();
            if syl.len() != syl_untrim.len() || syl_untrim.is_empty() {
                syl.push(' ');
            }

            let idx = intern_syl.len();
            let rcstr = Rc::new(syl);
            let interned_syl =
            match intern_syl.entry(rcstr.clone()) {
                Entry::Vacant(elem) => {
                    elem.set(idx);
                    intern_syl_vec.push(rcstr);
                    idx
                }
                Entry::Occupied(elem) =>
                    *elem.get(),
            };

            append(&mut syl_trie, buf_syls.as_slice(), interned_syl);
            buf_syls.pop();
            buf_syls.insert(0, interned_syl);
        }
    }

    // for line in reader.lines() {
    //     let line = line.unwrap();
    //     // let whitespace = regex!(r"\s+");

    //     // let line = whitespace.replace_all(line.as_slice(), " ");

    //     for (start, end) in tokens.find_iter(line.as_slice()) {
    //         let syl_untrim = line.as_slice().slice(start, end);
    //         let mut syl = syl_untrim.trim_right().to_string();
    //         if syl.len() != syl_untrim.len() || syl_untrim.is_empty() {
    //             syl.push(' ');
    //         }

    //         let i = intern_syl.len();
    //         let interned_syl = *intern_syl.find_with_or_insert_with(Rc::new(syl),
    //                                                                 i,
    //                                                                 |_k, _v, _a| (),
    //                                                                 |k, a| {
    //                                                                     intern_syl_vec.push(k.clone());
    //                                                                     a
    //                                                                 });

    //         // syllable_multiset.find_with_or_insert_with(interned_syl, (), |_k, v_ref, _u| *v_ref += 1, |_k, _u| 1);
    //         // syllable_multiset.push(interned_syl);

    //         append(&mut syl_trie, buf_syls.as_slice(), interned_syl);

    //         buf_syls.pop();
    //         buf_syls.unshift(interned_syl);
    //     }
    // }

    // TODO: deserialize

    let model = MarkovModel::new(syl_trie);
    let mut chain = MarkovChain::new(model, ORDER);

    for elem in chain.take(2_000_000) {
        print!("{}", intern_syl_vec.get(elem));
    }
}
