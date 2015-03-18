// Copyright 2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.


//! A HashMap wrapper that holds key-value pairs in insertion order.
//!
//! # Examples
//!
//! ```
//! # extern crate "linked-hash-map" as linked_hash_map;
//! # fn main() {
//! use linked_hash_map::LinkedHashMap;
//!
//! let mut map = LinkedHashMap::new();
//! map.insert(2, 20);
//! map.insert(1, 10);
//! map.insert(3, 30);
//! assert_eq!(map[1], 10);
//! assert_eq!(map[2], 20);
//! assert_eq!(map[3], 30);
//!
//! let items: Vec<(i32, i32)> = map.iter().map(|t| (*t.0, *t.1)).collect();
//! assert_eq!(vec![(2, 20), (1, 10), (3, 30)], items);
//! # }
//! ```

#![feature(box_patterns)]
#![feature(box_syntax)]
#![feature(unsafe_destructor)]
#![feature(std_misc)]
#![feature(alloc)]
#![feature(core)]

use std::borrow::Borrow;
use std::boxed;
use std::cmp::{PartialEq, Eq, Ordering};
use std::collections::hash_map::{self, HashMap};
use std::collections::hash_state::HashState;
use std::default::Default;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::iter::IntoIterator;
use std::iter;
use std::marker;
use std::mem;
use std::ops::{Index, IndexMut};
use std::ptr;

struct KeyRef<K> { k: *const K }

struct LinkedHashMapEntry<K, V> {
    next: *mut LinkedHashMapEntry<K, V>,
    prev: *mut LinkedHashMapEntry<K, V>,
    key: K,
    value: V,
}

/// A linked hash map.
pub struct LinkedHashMap<K, V, S = hash_map::RandomState> {
    map: HashMap<KeyRef<K>, Box<LinkedHashMapEntry<K, V>>, S>,
    head: *mut LinkedHashMapEntry<K, V>,
}

impl<K: Hash> Hash for KeyRef<K> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        unsafe { (*self.k).hash(state) }
    }
}

impl<K: PartialEq> PartialEq for KeyRef<K> {
    fn eq(&self, other: &KeyRef<K>) -> bool {
        unsafe{ (*self.k).eq(&*other.k) }
    }
}

impl<K: Eq> Eq for KeyRef<K> {}

// This type exists only to support borrowing `KeyRef`s, which cannot be borrowed to `Q` directly
// due to conflicting implementations of `Borrow`. The layout of `&Qey<Q>` must be identical to
// `&Q` in order to support transmuting in the `Qey::from_ref` method.
#[derive(Hash, PartialEq, Eq)]
struct Qey<Q: ?Sized>(Q);

impl<Q: ?Sized> Qey<Q> {
    fn from_ref(q: &Q) -> &Qey<Q> { unsafe { mem::transmute(q) } }
}

impl<K, Q: ?Sized> Borrow<Qey<Q>> for KeyRef<K> where K: Borrow<Q> {
    fn borrow(&self) -> &Qey<Q> {
        Qey::from_ref(unsafe { (*self.k).borrow() })
    }
}

impl<K, V> LinkedHashMapEntry<K, V> {
    fn new(k: K, v: V) -> LinkedHashMapEntry<K, V> {
        LinkedHashMapEntry {
            key: k,
            value: v,
            next: ptr::null_mut(),
            prev: ptr::null_mut(),
        }
    }
}

impl<K: Hash + Eq, V> LinkedHashMap<K, V> {
    /// Creates a linked hash map.
    pub fn new() -> LinkedHashMap<K, V> { LinkedHashMap::with_map(HashMap::new()) }

    /// Creates an empty linked hash map with the given initial capacity.
    pub fn with_capacity(capacity: usize) -> LinkedHashMap<K, V> {
        LinkedHashMap::with_map(HashMap::with_capacity(capacity))
    }
}

impl<K: Hash + Eq, V, S: HashState> LinkedHashMap<K, V, S> {
    fn with_map(map: HashMap<KeyRef<K>, Box<LinkedHashMapEntry<K, V>>, S>) -> LinkedHashMap<K, V, S> {
        let map = LinkedHashMap {
            map: map,
            head: unsafe{ boxed::into_raw(box mem::uninitialized::<LinkedHashMapEntry<K, V>>()) },
        };
        unsafe {
            (*map.head).next = map.head;
            (*map.head).prev = map.head;
        }
        return map;
    }

    /// Creates an empty linked hash map with the given initial hash state.
    pub fn with_hash_state(hash_state: S) -> LinkedHashMap<K, V, S> {
        LinkedHashMap::with_map(HashMap::with_hash_state(hash_state))
    }

    /// Creates an empty linked hash map with the given initial capacity and hash state.
    pub fn with_capacity_and_hash_state(capacity: usize, hash_state: S) -> LinkedHashMap<K, V, S> {
        LinkedHashMap::with_map(HashMap::with_capacity_and_hash_state(capacity, hash_state))
    }

    /// Reserves capacity for at least `additional` more elements to be inserted into the map. The
    /// map may reserve more space to avoid frequent allocations.
    ///
    /// # Panics
    ///
    /// Panics if the new allocation size overflows `usize.`
    pub fn reserve(&mut self, additional: usize) { self.map.reserve(additional); }

    /// Shrinks the capacity of the map as much as possible. It will drop down as much as possible
    /// while maintaining the internal rules and possibly leaving some space in accordance with the
    /// resize policy.
    pub fn shrink_to_fit(&mut self) { self.map.shrink_to_fit(); }

    /// Inserts a key-value pair into the map. If the key already existed, the old value is
    /// returned.
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate "linked-hash-map" as linked_hash_map;
    /// # fn main() {
    /// use linked_hash_map::LinkedHashMap;
    /// let mut map = LinkedHashMap::new();
    ///
    /// map.insert(1, "a");
    /// map.insert(2, "b");
    /// assert_eq!(map[1], "a");
    /// assert_eq!(map[2], "b");
    /// # }
    /// ```
    pub fn insert(&mut self, k: K, v: V) -> Option<V> {
        let (node_ptr, node_opt, old_val) = match self.map.get_mut(&KeyRef{k: &k}) {
            Some(node) => {
                let old_val = mem::replace(&mut node.value, v);
                let node_ptr: *mut LinkedHashMapEntry<K, V> = &mut **node;
                (node_ptr, None, Some(old_val))
            }
            None => {
                let mut node = box LinkedHashMapEntry::new(k, v);
                let node_ptr: *mut LinkedHashMapEntry<K, V> = &mut *node;
                (node_ptr, Some(node), None)
            }
        };
        match node_opt {
            None => {
                // Existing node, just update LRU position
                self.detach(node_ptr);
                self.attach(node_ptr);
            }
            Some(node) => {
                let keyref = unsafe { &(*node_ptr).key };
                self.map.insert(KeyRef{k: keyref}, node);
                self.attach(node_ptr);
            }
        }
        old_val
    }

    /// Checks if the map contains the given key.
    pub fn contains_key<Q: ?Sized>(&self, k: &Q) -> bool where K: Borrow<Q>, Q: Eq + Hash {
        self.map.contains_key(Qey::from_ref(k))
    }

    /// Returns the value corresponding to the key in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate "linked-hash-map" as linked_hash_map;
    /// # fn main() {
    /// use linked_hash_map::LinkedHashMap;
    /// let mut map = LinkedHashMap::new();
    ///
    /// map.insert(1, "a");
    /// map.insert(2, "b");
    /// map.insert(2, "c");
    /// map.insert(3, "d");
    ///
    /// assert_eq!(map.get(&1), Some(&"a"));
    /// assert_eq!(map.get(&2), Some(&"c"));
    /// # }
    /// ```
    pub fn get<Q: ?Sized>(&self, k: &Q) -> Option<&V> where K: Borrow<Q>, Q: Eq + Hash {
        self.map.get(Qey::from_ref(k)).map(|e| &e.value)
    }

    /// Returns the mutable reference corresponding to the key in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate "linked-hash-map" as linked_hash_map;
    /// # fn main() {
    /// use linked_hash_map::LinkedHashMap;
    /// let mut map = LinkedHashMap::new();
    ///
    /// map.insert(1, "a");
    /// map.insert(2, "b");
    ///
    /// *map.get_mut(&1).unwrap() = "c";
    /// assert_eq!(map.get(&1), Some(&"c"));
    /// # }
    /// ```
    pub fn get_mut<Q: ?Sized>(&mut self, k: &Q) -> Option<&mut V> where K: Borrow<Q>, Q: Eq + Hash {
        self.map.get_mut(Qey::from_ref(k)).map(|e| &mut e.value)
    }

    /// Returns the value corresponding to the key in the map.
    ///
    /// If value is found, it is moved to the end of the list.
    /// This operation can be used in implemenation of LRU cache.
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate "linked-hash-map" as linked_hash_map;
    /// # fn main() {
    /// use linked_hash_map::LinkedHashMap;
    /// let mut map = LinkedHashMap::new();
    ///
    /// map.insert(1, "a");
    /// map.insert(2, "b");
    /// map.insert(3, "d");
    ///
    /// assert_eq!(map.get_refresh(&2), Some(&"b"));
    ///
    /// assert_eq!((&2, &"b"), map.iter().rev().next().unwrap());
    /// # }
    /// ```
    pub fn get_refresh<Q: ?Sized>(&mut self, k: &Q) -> Option<&V> where K: Borrow<Q>, Q: Eq + Hash {
        let (value, node_ptr_opt) = match self.map.get_mut(Qey::from_ref(k)) {
            None => (None, None),
            Some(node) => {
                let node_ptr: *mut LinkedHashMapEntry<K, V> = &mut **node;
                (Some(unsafe { &(*node_ptr).value }), Some(node_ptr))
            }
        };
        match node_ptr_opt {
            None => (),
            Some(node_ptr) => {
                self.detach(node_ptr);
                self.attach(node_ptr);
            }
        }
        return value;
    }

    /// Removes and returns the value corresponding to the key from the map.
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate "linked-hash-map" as linked_hash_map;
    /// # fn main() {
    /// use linked_hash_map::LinkedHashMap;
    /// let mut map = LinkedHashMap::new();
    ///
    /// map.insert(2, "a");
    ///
    /// assert_eq!(map.remove(&1), None);
    /// assert_eq!(map.remove(&2), Some("a"));
    /// assert_eq!(map.remove(&2), None);
    /// assert_eq!(map.len(), 0);
    /// # }
    /// ```
    pub fn remove<Q: ?Sized>(&mut self, k: &Q) -> Option<V> where K: Borrow<Q>, Q: Eq + Hash {
        let removed = self.map.remove(Qey::from_ref(k));
        removed.map(|mut node| {
            let node_ptr: *mut LinkedHashMapEntry<K,V> = &mut *node;
            self.detach(node_ptr);
            node.value
        })
    }

    /// Returns the maximum number of key-value pairs the map can hold without reallocating.
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate "linked-hash-map" as linked_hash_map;
    /// # fn main() {
    /// use linked_hash_map::LinkedHashMap;
    /// let mut map: LinkedHashMap<i32, &str> = LinkedHashMap::new();
    /// let capacity = map.capacity();
    /// # }
    /// ```
    pub fn capacity(&self) -> usize {
        self.map.capacity()
    }

    /// Removes the first entry.
    ///
    /// Can be used in implementation of LRU cache.
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate "linked-hash-map" as linked_hash_map;
    /// # fn main() {
    /// use linked_hash_map::LinkedHashMap;
    /// let mut map = LinkedHashMap::new();
    /// map.insert(1, 10);
    /// map.insert(2, 20);
    /// map.pop_front();
    /// assert_eq!(map.get(&1), None);
    /// assert_eq!(map.get(&2), Some(&20));
    /// # }
    /// ```
    #[inline]
    pub fn pop_front(&mut self) {
        if self.len() > 0 {
            let lru = unsafe { (*self.head).prev };
            self.detach(lru);
            self.map.remove(&KeyRef{k: unsafe { &(*lru).key }});
        }
    }

    /// Returns the number of key-value pairs in the map.
    pub fn len(&self) -> usize { self.map.len() }

    /// Returns whether the map is currently empty.
    pub fn is_empty(&self) -> bool { self.len() == 0 }

    /// Clear the map of all key-value pairs.
    pub fn clear(&mut self) {
        self.map.clear();
        unsafe {
            (*self.head).prev = self.head;
            (*self.head).next = self.head;
        }
    }

    /// A double-ended iterator visiting all key-value pairs in order of insertion.
    /// Iterator element type is `(&'a K, &'a V)`
    ///
    /// # Examples
    /// ```
    /// # extern crate "linked-hash-map" as linked_hash_map;
    /// # fn main() {
    /// use linked_hash_map::LinkedHashMap;
    ///
    /// let mut map = LinkedHashMap::new();
    /// map.insert("a", 10);
    /// map.insert("c", 30);
    /// map.insert("b", 20);
    ///
    /// let mut iter = map.iter();
    /// assert_eq!((&"a", &10), iter.next().unwrap());
    /// assert_eq!((&"c", &30), iter.next().unwrap());
    /// assert_eq!((&"b", &20), iter.next().unwrap());
    /// assert_eq!(None, iter.next());
    /// # }
    /// ```
    pub fn iter(&self) -> Iter<K, V> {
        Iter {
            head: unsafe { (*self.head).prev },
            tail: self.head,
            remaining: self.len(),
            marker: marker::PhantomData,
        }
    }

    /// A double-ended iterator visiting all key-value pairs in order of insertion.
    /// Iterator element type is `(&'a K, &'a mut V)`
    /// # Examples
    /// ```
    /// # extern crate "linked-hash-map" as linked_hash_map;
    /// # fn main() {
    /// use linked_hash_map::LinkedHashMap;
    ///
    /// let mut map = LinkedHashMap::new();
    /// map.insert("a", 10);
    /// map.insert("c", 30);
    /// map.insert("b", 20);
    ///
    /// {
    ///     let mut iter = map.iter_mut();
    ///     let mut entry = iter.next().unwrap();
    ///     assert_eq!(&"a", entry.0);
    ///     *entry.1 = 17;
    /// }
    ///
    /// assert_eq!(&17, map.get(&"a").unwrap());
    /// # }
    /// ```
    pub fn iter_mut(&mut self) -> IterMut<K, V> {
        IterMut {
            head: unsafe { (*self.head).prev },
            tail: self.head,
            remaining: self.len(),
            marker: marker::PhantomData
        }
    }

    /// A double-ended iterator visiting all key in order of insertion.
    ///
    /// # Examples
    /// ```
    /// # extern crate "linked-hash-map" as linked_hash_map;
    /// # fn main() {
    /// use linked_hash_map::LinkedHashMap;
    ///
    /// let mut map = LinkedHashMap::new();
    /// map.insert('a', 10);
    /// map.insert('c', 30);
    /// map.insert('b', 20);
    ///
    /// let mut keys = map.keys();
    /// assert_eq!(&'a', keys.next().unwrap());
    /// assert_eq!(&'c', keys.next().unwrap());
    /// assert_eq!(&'b', keys.next().unwrap());
    /// assert_eq!(None, keys.next());
    /// # }
    /// ```
    pub fn keys<'a>(&'a self) -> Keys<'a, K, V> {
        fn first<A, B>((a, _): (A, B)) -> A { a }
        let first: fn((&'a K, &'a V)) -> &'a K = first; // coerce to fn ptr

        Keys { inner: self.iter().map(first) }
    }

    /// A double-ended iterator visiting all values in order of insertion.
    ///
    /// # Examples
    /// ```
    /// # extern crate "linked-hash-map" as linked_hash_map;
    /// # fn main() {
    /// use linked_hash_map::LinkedHashMap;
    ///
    /// let mut map = LinkedHashMap::new();
    /// map.insert('a', 10);
    /// map.insert('c', 30);
    /// map.insert('b', 20);
    ///
    /// let mut values = map.values();
    /// assert_eq!(&10, values.next().unwrap());
    /// assert_eq!(&30, values.next().unwrap());
    /// assert_eq!(&20, values.next().unwrap());
    /// assert_eq!(None, values.next());
    /// # }
    /// ```
    pub fn values<'a>(&'a self) -> Values<'a, K, V> {
        fn second<A, B>((_, b): (A, B)) -> B { b }
        let second: fn((&'a K, &'a V)) -> &'a V = second; // coerce to fn ptr

        Values { inner: self.iter().map(second) }
    }
}

impl<K, V, S, Q: ?Sized> Index<Q> for LinkedHashMap<K, V, S>
    where K: Hash + Eq + Borrow<Q>, S: HashState, Q: Eq + Hash
{
    type Output = V;

    fn index(&self, index: &Q) -> &V {
        self.get(index).expect("no entry found for key")
    }
}

impl<K, V, S, Q: ?Sized> IndexMut<Q> for LinkedHashMap<K, V, S>
    where K: Hash + Eq + Borrow<Q>, S: HashState, Q: Eq + Hash
{
    fn index_mut(&mut self, index: &Q) -> &mut V {
        self.get_mut(index).expect("no entry found for key")
    }
}

impl<K: Hash + Eq, V, S: HashState> LinkedHashMap<K, V, S> {
    #[inline]
    fn detach(&mut self, node: *mut LinkedHashMapEntry<K, V>) {
        unsafe {
            (*(*node).prev).next = (*node).next;
            (*(*node).next).prev = (*node).prev;
        }
    }

    #[inline]
    fn attach(&mut self, node: *mut LinkedHashMapEntry<K, V>) {
        unsafe {
            (*node).next = (*self.head).next;
            (*node).prev = self.head;
            (*self.head).next = node;
            (*(*node).next).prev = node;
        }
    }
}

// FIXME: `HashMap` doesn't expose its hash state, so we cannot clone fully parameterized
// `LinkedHashMap`s without cloning the original map and clearing it. For now, only
// `LinkedHashMap<K, V>`s implement `Clone`.
impl<K: Hash + Eq + Clone, V: Clone> Clone for LinkedHashMap<K, V> {
    fn clone(&self) -> LinkedHashMap<K, V> {
        self.iter().map(|(k, v)| (k.clone(), v.clone())).collect()
    }
}

impl<K: Hash + Eq, V, S: HashState + Default> Default for LinkedHashMap<K, V, S> {
    fn default() -> LinkedHashMap<K, V, S> { LinkedHashMap::with_hash_state(Default::default()) }
}

impl<K: Hash + Eq, V, S: HashState> Extend<(K, V)> for LinkedHashMap<K, V, S> {
    fn extend<T: IntoIterator<Item=(K, V)>>(&mut self, iter: T) {
        for (k, v) in iter {
            self.insert(k, v);
        }
    }
}

impl<K: Hash + Eq, V, S: HashState + Default> iter::FromIterator<(K, V)> for LinkedHashMap<K, V, S> {
    fn from_iter<I: IntoIterator<Item=(K, V)>>(iter: I) -> LinkedHashMap<K, V, S> {
        let iter = iter.into_iter();
        let mut map = LinkedHashMap::with_capacity_and_hash_state(iter.size_hint().0, Default::default());
        map.extend(iter);
        map
    }
}

impl<A: fmt::Debug + Hash + Eq, B: fmt::Debug, S: HashState> fmt::Debug for LinkedHashMap<A, B, S> {
    /// Returns a string that lists the key-value pairs in insertion order.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        try!(write!(f, "{{"));

        for (i, (k, v)) in self.iter().enumerate() {
            if i != 0 { try!(write!(f, ", ")); }
            try!(write!(f, "{:?}: {:?}", *k, *v));
        }

        write!(f, "}}")
    }
}

impl<K: Hash + Eq, V: PartialEq, S: HashState> PartialEq for LinkedHashMap<K, V, S> {
    fn eq(&self, other: &LinkedHashMap<K, V, S>) -> bool {
        self.len() == other.len() && self.iter().zip(other.iter()).all(|(l, r)| l == r)
    }
}

impl<K: Hash + Eq, V: Eq, S: HashState> Eq for LinkedHashMap<K, V, S> {}

impl<K: Hash + Eq + PartialOrd, V: PartialOrd, S: HashState> PartialOrd for LinkedHashMap<K, V, S> {
    fn partial_cmp(&self, other: &LinkedHashMap<K, V, S>) -> Option<Ordering> {
        iter::order::partial_cmp(self.iter(), other.iter())
    }
}

impl<K: Hash + Eq + Ord, V: Ord, S: HashState> Ord for LinkedHashMap<K, V, S> {
    fn cmp(&self, other: &LinkedHashMap<K, V, S>) -> Ordering {
        iter::order::cmp(self.iter(), other.iter())
    }
}

impl<K: Hash + Eq, V: Hash, S: HashState> Hash for LinkedHashMap<K, V, S> {
    fn hash<H: Hasher>(&self, h: &mut H) { for e in self.iter() { e.hash(h); } }
}

unsafe impl<K: Send, V: Send, S: Send> Send for LinkedHashMap<K, V, S> {}

unsafe impl<K: Sync, V: Sync, S: Sync> Sync for LinkedHashMap<K, V, S> {}

#[unsafe_destructor]
impl<K, V, S> Drop for LinkedHashMap<K, V, S> {
    fn drop(&mut self) {
        unsafe {
            let node = Box::from_raw(self.head);
            // Prevent compiler from trying to drop the un-initialized field in the sigil node.
            let box internal_node = node;
            let LinkedHashMapEntry { next: _, prev: _, key: k, value: v } = internal_node;
            mem::forget(k);
            mem::forget(v);
        }
    }
}

pub struct Iter<'a, K: 'a, V: 'a> {
    head: *const LinkedHashMapEntry<K, V>,
    tail: *const LinkedHashMapEntry<K, V>,
    remaining: usize,
    marker: marker::PhantomData<(&'a K, &'a V)>,
}

pub struct IterMut<'a, K: 'a, V: 'a> {
    head: *mut LinkedHashMapEntry<K, V>,
    tail: *mut LinkedHashMapEntry<K, V>,
    remaining: usize,
    marker: marker::PhantomData<(&'a K, &'a mut V)>,
}

impl<'a, K, V> Clone for Iter<'a, K, V> {
    fn clone(&self) -> Iter<'a, K, V> { Iter { ..*self } }
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<(&'a K, &'a V)> {
        if self.head == self.tail {
            None
        } else {
            self.remaining -= 1;
            unsafe {
                let r = Some((&(*self.head).key, &(*self.head).value));
                self.head = (*self.head).prev;
                r
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining, Some(self.remaining))
    }
}

impl<'a, K, V> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    fn next(&mut self) -> Option<(&'a K, &'a mut V)> {
        if self.head == self.tail {
            None
        } else {
            self.remaining -= 1;
            unsafe {
                let r = Some((&(*self.head).key, &mut (*self.head).value));
                self.head = (*self.head).prev;
                r
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining, Some(self.remaining))
    }
}

impl<'a, K, V> DoubleEndedIterator for Iter<'a, K, V> {
    fn next_back(&mut self) -> Option<(&'a K, &'a V)> {
        if self.head == self.tail {
            None
        } else {
            self.remaining -= 1;
            unsafe {
                self.tail = (*self.tail).next;
                let r = Some((&(*self.tail).key, &(*self.tail).value));
                r
            }
        }
    }
}

impl<'a, K, V> DoubleEndedIterator for IterMut<'a, K, V> {
    fn next_back(&mut self) -> Option<(&'a K, &'a mut V)> {
        if self.head == self.tail {
            None
        } else {
            self.remaining -= 1;
            unsafe {
                self.tail = (*self.tail).next;
                let r = Some((&(*self.tail).key, &mut (*self.tail).value));
                r
            }
        }
    }
}

impl<'a, K, V> ExactSizeIterator for Iter<'a, K, V> {}

impl<'a, K, V> ExactSizeIterator for IterMut<'a, K, V> {}


pub struct Keys<'a, K: 'a, V: 'a> {
    inner: iter::Map<Iter<'a, K, V>, fn((&'a K, &'a V)) -> &'a K>
}

impl<'a, K, V> Clone for Keys<'a, K, V> {
    fn clone(&self) -> Keys<'a, K, V> { Keys { inner: self.inner.clone() } }
}

impl<'a, K, V> Iterator for Keys<'a, K, V> {
    type Item = &'a K;

    #[inline] fn next(&mut self) -> Option<(&'a K)> { self.inner.next() }
    #[inline] fn size_hint(&self) -> (usize, Option<usize>) { self.inner.size_hint() }
}

impl<'a, K, V> DoubleEndedIterator for Keys<'a, K, V> {
    #[inline] fn next_back(&mut self) -> Option<(&'a K)> { self.inner.next_back() }
}

impl<'a, K, V> ExactSizeIterator for Keys<'a, K, V> {}


pub struct Values<'a, K: 'a, V: 'a> {
    inner: iter::Map<Iter<'a, K, V>, fn((&'a K, &'a V)) -> &'a V>
}

impl<'a, K, V> Clone for Values<'a, K, V> {
    fn clone(&self) -> Values<'a, K, V> { Values { inner: self.inner.clone() } }
}

impl<'a, K, V> Iterator for Values<'a, K, V> {
    type Item = &'a V;

    #[inline] fn next(&mut self) -> Option<(&'a V)> { self.inner.next() }
    #[inline] fn size_hint(&self) -> (usize, Option<usize>) { self.inner.size_hint() }
}

impl<'a, K, V> DoubleEndedIterator for Values<'a, K, V> {
    #[inline] fn next_back(&mut self) -> Option<(&'a V)> { self.inner.next_back() }
}

impl<'a, K, V> ExactSizeIterator for Values<'a, K, V> {}

impl<'a, K: Hash + Eq, V, S: HashState> IntoIterator for &'a LinkedHashMap<K, V, S> {
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V>;
    fn into_iter(self) -> Iter<'a, K, V> { self.iter() }
}

impl<'a, K: Hash + Eq, V, S: HashState> IntoIterator for &'a mut LinkedHashMap<K, V, S> {
    type Item = (&'a K, &'a mut V);
    type IntoIter = IterMut<'a, K, V>;
    fn into_iter(self) -> IterMut<'a, K, V> { self.iter_mut() }
}

#[cfg(test)]
mod tests {
    use super::LinkedHashMap;

    fn assert_opt_eq<V: PartialEq>(opt: Option<&V>, v: V) {
        assert!(opt.is_some());
        assert!(opt.unwrap() == &v);
    }

    #[test]
    fn test_insert_and_get() {
        let mut map = LinkedHashMap::new();
        map.insert(1, 10);
        map.insert(2, 20);
        assert_opt_eq(map.get(&1), 10);
        assert_opt_eq(map.get(&2), 20);
        assert_eq!(map.len(), 2);
    }

    #[test]
    fn test_index() {
        let mut map = LinkedHashMap::new();
        map.insert(1, 10);
        map.insert(2, 20);
        assert_eq!(10, map[1]);
        map[2] = 22;
        assert_eq!(22, map[2]);
    }

    #[test]
    fn test_insert_update() {
        let mut map = LinkedHashMap::new();
        map.insert("1".to_string(), vec![10, 10]);
        map.insert("1".to_string(), vec![10, 19]);
        assert_opt_eq(map.get(&"1".to_string()), vec![10, 19]);
        assert_eq!(map.len(), 1);
    }

    #[test]
    fn test_debug() {
        let mut map = LinkedHashMap::new();
        assert_eq!(format!("{:?}", map), "{}");
        map.insert(1, 10);
        map.insert(2, 20);
        map.insert(3, 30);
        assert_eq!(format!("{:?}", map), "{1: 10, 2: 20, 3: 30}");
        map.insert(2, 22);
        assert_eq!(format!("{:?}", map), "{1: 10, 3: 30, 2: 22}");
        map.get(&3);
        assert_eq!(format!("{:?}", map), "{1: 10, 3: 30, 2: 22}");
        map.get_refresh(&3);
        assert_eq!(format!("{:?}", map), "{1: 10, 2: 22, 3: 30}");
        map.clear();
        assert_eq!(format!("{:?}", map), "{}");
    }

    #[test]
    fn test_remove() {
        let mut map = LinkedHashMap::new();
        map.insert(1, 10);
        map.insert(2, 20);
        map.insert(3, 30);
        map.insert(4, 40);
        map.insert(5, 50);
        map.remove(&3);
        map.remove(&4);
        assert!(map.get(&3).is_none());
        assert!(map.get(&4).is_none());
        map.insert(6, 60);
        map.insert(7, 70);
        map.insert(8, 80);
        assert_opt_eq(map.get(&6), 60);
        assert_opt_eq(map.get(&7), 70);
        assert_opt_eq(map.get(&8), 80);
    }

    #[test]
    fn test_clear() {
        let mut map = LinkedHashMap::new();
        map.insert(1, 10);
        map.insert(2, 20);
        map.clear();
        assert!(map.get(&1).is_none());
        assert!(map.get(&2).is_none());
        assert_eq!(format!("{:?}", map), "{}");
    }

    #[test]
    fn test_iter() {
        let mut map = LinkedHashMap::new();

        // empty iter
        assert_eq!(None, map.iter().next());

        map.insert("a", 10);
        map.insert("b", 20);
        map.insert("c", 30);

        // regular iter
        let mut iter = map.iter();
        assert_eq!((&"a", &10), iter.next().unwrap());
        assert_eq!((&"b", &20), iter.next().unwrap());
        assert_eq!((&"c", &30), iter.next().unwrap());
        assert_eq!(None, iter.next());
        assert_eq!(None, iter.next());

        // reversed iter
        let mut rev_iter = map.iter().rev();
        assert_eq!((&"c", &30), rev_iter.next().unwrap());
        assert_eq!((&"b", &20), rev_iter.next().unwrap());
        assert_eq!((&"a", &10), rev_iter.next().unwrap());
        assert_eq!(None, rev_iter.next());
        assert_eq!(None, rev_iter.next());

        // mixed
        let mut mixed_iter = map.iter();
        assert_eq!((&"a", &10), mixed_iter.next().unwrap());
        assert_eq!((&"c", &30), mixed_iter.next_back().unwrap());
        assert_eq!((&"b", &20), mixed_iter.next().unwrap());
        assert_eq!(None, mixed_iter.next());
        assert_eq!(None, mixed_iter.next_back());
    }

    #[test]
    fn test_iter_mut() {
        let mut map = LinkedHashMap::new();
        map.insert("a", 10);
        map.insert("c", 30);
        map.insert("b", 20);

        {
            let mut iter = map.iter_mut();
            let entry = iter.next().unwrap();
            assert_eq!(&"a", entry.0);
            *entry.1 = 17;

            // reverse iterator
            let mut iter = iter.rev();
            let entry = iter.next().unwrap();
            assert_eq!(&"b", entry.0);
            *entry.1 = 23;

            let entry = iter.next().unwrap();
            assert_eq!(&"c", entry.0);
            assert_eq!(None, iter.next());
            assert_eq!(None, iter.next());
        }

        assert_eq!(17, map["a"]);
        assert_eq!(23, map["b"]);
    }

    #[test]
    fn test_borrow() {
        #[derive(PartialEq, Eq, Hash)] struct Foo(Bar);
        #[derive(PartialEq, Eq, Hash)] struct Bar(i32);

        impl ::std::borrow::Borrow<Bar> for Foo {
            fn borrow(&self) -> &Bar { &self.0 }
        }

        let mut map = LinkedHashMap::new();
        map.insert(Foo(Bar(1)), "a");
        map.insert(Foo(Bar(2)), "b");

        assert!(map.contains_key(&Bar(1)));
        assert!(map.contains_key(&Bar(2)));
        assert!(map.contains_key(&Foo(Bar(1))));
        assert!(map.contains_key(&Foo(Bar(2))));

        assert_eq!(map.get(&Bar(1)), Some(&"a"));
        assert_eq!(map.get(&Bar(2)), Some(&"b"));
        assert_eq!(map.get(&Foo(Bar(1))), Some(&"a"));
        assert_eq!(map.get(&Foo(Bar(2))), Some(&"b"));

        assert_eq!(map.get_refresh(&Bar(1)), Some(&"a"));
        assert_eq!(map.get_refresh(&Bar(2)), Some(&"b"));
        assert_eq!(map.get_refresh(&Foo(Bar(1))), Some(&"a"));
        assert_eq!(map.get_refresh(&Foo(Bar(2))), Some(&"b"));

        assert_eq!(map.get_mut(&Bar(1)), Some(&mut "a"));
        assert_eq!(map.get_mut(&Bar(2)), Some(&mut "b"));
        assert_eq!(map.get_mut(&Foo(Bar(1))), Some(&mut "a"));
        assert_eq!(map.get_mut(&Foo(Bar(2))), Some(&mut "b"));

        assert_eq!(map[Bar(1)], "a");
        assert_eq!(map[Bar(2)], "b");
        assert_eq!(map[Foo(Bar(1))], "a");
        assert_eq!(map[Foo(Bar(2))], "b");

        assert_eq!(map.remove(&Bar(1)), Some("a"));
        assert_eq!(map.remove(&Bar(2)), Some("b"));
        assert_eq!(map.remove(&Foo(Bar(1))), None);
        assert_eq!(map.remove(&Foo(Bar(2))), None);
    }
}
