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

use patricia_trie::PatriciaTrie;

mod patricia_trie;
mod bit;
// mod bit;

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

// struct WeightedPatriciaTrie<V> {
//     data: Option<V>,

//     child_l: Option<Box<PatriciaTrie<V>>>,
//     child_r: Option<Box<PatriciaTrie<V>>>,
//     weight_l: uint,
//     prefix: uint,
//     skip_len: u8
// }

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
