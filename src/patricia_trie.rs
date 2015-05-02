use bit::BitArray;

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

#[test]
fn test_insert() {
    let mut trie: PatriciaTrie<uint, NoData<uint>> = PatriciaTrie::new();
    for i in range(0, 100) {
        if !trie.insert(i, i) {
            trie.print();
            panic!("{}", i);
        }
    }
}
