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
//! use linked_hash_map::LinkedHashMap;
//!
//! let mut map = LinkedHashMap::new();
//! map.insert(2, 20);
//! map.insert(1, 10);
//! map.insert(3, 30);
//! assert_eq!(map[&1], 10);
//! assert_eq!(map[&2], 20);
//! assert_eq!(map[&3], 30);
//!
//! let items: Vec<(i32, i32)> = map.iter().map(|t| (*t.0, *t.1)).collect();
//! assert_eq!(items, [(2, 20), (1, 10), (3, 30)]);
//! ```

#![forbid(missing_docs)]
#![cfg_attr(feature = "nightly", feature(hashmap_public_hasher))]
#![cfg_attr(all(feature = "nightly", test), feature(test))]

use std::borrow::Borrow;
use std::cmp::Ordering;
use std::collections::hash_map::{self, HashMap};
use std::fmt;
use std::hash::{BuildHasher, Hash, Hasher};
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
    free: *mut LinkedHashMapEntry<K, V>,
}

impl<K: Hash> Hash for KeyRef<K> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        unsafe { (*self.k).hash(state) }
    }
}

impl<K: PartialEq> PartialEq for KeyRef<K> {
    fn eq(&self, other: &Self) -> bool {
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
    fn from_ref(q: &Q) -> &Self { unsafe { mem::transmute(q) } }
}

impl<K, Q: ?Sized> Borrow<Qey<Q>> for KeyRef<K> where K: Borrow<Q> {
    fn borrow(&self) -> &Qey<Q> {
        Qey::from_ref(unsafe { (*self.k).borrow() })
    }
}

impl<K, V> LinkedHashMapEntry<K, V> {
    fn new(k: K, v: V) -> Self {
        LinkedHashMapEntry {
            key: k,
            value: v,
            next: ptr::null_mut(),
            prev: ptr::null_mut(),
        }
    }
}

unsafe fn drop_empty_entry_box<K, V>(the_box: *mut LinkedHashMapEntry<K, V>) {
    // Prevent compiler from trying to drop the un-initialized key and values in the node.
    let LinkedHashMapEntry { key, value, .. } = *Box::from_raw(the_box);
    mem::forget(key);
    mem::forget(value);
}

impl<K: Hash + Eq, V> LinkedHashMap<K, V> {
    /// Creates a linked hash map.
    pub fn new() -> Self { Self::with_map(HashMap::new()) }

    /// Creates an empty linked hash map with the given initial capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        Self::with_map(HashMap::with_capacity(capacity))
    }
}

impl<K, V, S> LinkedHashMap<K, V, S> {
    fn clear_free_list(&mut self) {
        unsafe {
            let mut free = self.free;
            while ! free.is_null() {
                let next_free = (*free).next;
                drop_empty_entry_box(free);
                free = next_free;
            }
            self.free = ptr::null_mut();
        }
    }
}

impl<K: Hash + Eq, V, S: BuildHasher> LinkedHashMap<K, V, S> {
    fn with_map(map: HashMap<KeyRef<K>, Box<LinkedHashMapEntry<K, V>>, S>) -> Self {
        LinkedHashMap {
            map: map,
            head: ptr::null_mut(),
            free: ptr::null_mut(),
        }
    }

    /// Creates an empty linked hash map with the given initial hash state.
    pub fn with_hash_state(hash_state: S) -> Self {
        Self::with_map(HashMap::with_hasher(hash_state))
    }

    /// Creates an empty linked hash map with the given initial capacity and hash state.
    pub fn with_capacity_and_hash_state(capacity: usize, hash_state: S) -> Self {
        Self::with_map(HashMap::with_capacity_and_hasher(capacity, hash_state))
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
    pub fn shrink_to_fit(&mut self) {
        self.map.shrink_to_fit();
        self.clear_free_list();
    }

    /// Inserts a key-value pair into the map. If the key already existed, the old value is
    /// returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use linked_hash_map::LinkedHashMap;
    /// let mut map = LinkedHashMap::new();
    ///
    /// map.insert(1, "a");
    /// map.insert(2, "b");
    /// assert_eq!(map[&1], "a");
    /// assert_eq!(map[&2], "b");
    /// ```
    pub fn insert(&mut self, k: K, v: V) -> Option<V> {
        if self.head.is_null() {
            // allocate the guard node if not present
            unsafe {
                self.head = Box::into_raw(Box::new(mem::uninitialized()));
                (*self.head).next = self.head;
                (*self.head).prev = self.head;
            }
        }
        let (node_ptr, node_opt, old_val) = match self.map.get_mut(&KeyRef{k: &k}) {
            Some(node) => {
                let old_val = mem::replace(&mut node.value, v);
                let node_ptr: *mut LinkedHashMapEntry<K, V> = &mut **node;
                (node_ptr, None, Some(old_val))
            }
            None => {
                let mut node = if self.free.is_null() {
                    Box::new(LinkedHashMapEntry::new(k, v))
                } else {
                    // use a recycled box
                    unsafe {
                        let free = self.free;
                        self.free = (*free).next;
                        ptr::write(free, LinkedHashMapEntry::new(k, v));
                        Box::from_raw(free)
                    }
                };
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
    /// ```
    pub fn get<Q: ?Sized>(&self, k: &Q) -> Option<&V> where K: Borrow<Q>, Q: Eq + Hash {
        self.map.get(Qey::from_ref(k)).map(|e| &e.value)
    }

    /// Returns the mutable reference corresponding to the key in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use linked_hash_map::LinkedHashMap;
    /// let mut map = LinkedHashMap::new();
    ///
    /// map.insert(1, "a");
    /// map.insert(2, "b");
    ///
    /// *map.get_mut(&1).unwrap() = "c";
    /// assert_eq!(map.get(&1), Some(&"c"));
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
    /// use linked_hash_map::LinkedHashMap;
    /// let mut map = LinkedHashMap::new();
    ///
    /// map.insert(1, "a");
    /// map.insert(2, "b");
    /// map.insert(3, "d");
    ///
    /// assert_eq!(map.get_refresh(&2), Some(&mut "b"));
    ///
    /// assert_eq!((&2, &"b"), map.iter().rev().next().unwrap());
    /// ```
    pub fn get_refresh<Q: ?Sized>(&mut self, k: &Q) -> Option<&mut V> where K: Borrow<Q>, Q: Eq + Hash {
        let (value, node_ptr_opt) = match self.map.get_mut(Qey::from_ref(k)) {
            None => (None, None),
            Some(node) => {
                let node_ptr: *mut LinkedHashMapEntry<K, V> = &mut **node;
                (Some(unsafe { &mut(*node_ptr).value }), Some(node_ptr))
            }
        };
        if let Some(node_ptr) = node_ptr_opt {
            self.detach(node_ptr);
            self.attach(node_ptr);
        }
        return value;
    }

    /// Removes and returns the value corresponding to the key from the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use linked_hash_map::LinkedHashMap;
    /// let mut map = LinkedHashMap::new();
    ///
    /// map.insert(2, "a");
    ///
    /// assert_eq!(map.remove(&1), None);
    /// assert_eq!(map.remove(&2), Some("a"));
    /// assert_eq!(map.remove(&2), None);
    /// assert_eq!(map.len(), 0);
    /// ```
    pub fn remove<Q: ?Sized>(&mut self, k: &Q) -> Option<V> where K: Borrow<Q>, Q: Eq + Hash {
        let removed = self.map.remove(Qey::from_ref(k));
        removed.map(|mut node| {
            let node_ptr: *mut LinkedHashMapEntry<K,V> = &mut *node;
            self.detach(node_ptr);
            unsafe {
                // add to free list
                (*node_ptr).next = self.free;
                self.free = node_ptr;
                // forget the box but drop the key and return the value
                mem::forget(node);
                drop(ptr::read(&(*node_ptr).key));
                ptr::read(&(*node_ptr).value)
            }
        })
    }

    /// Returns the maximum number of key-value pairs the map can hold without reallocating.
    ///
    /// # Examples
    ///
    /// ```
    /// use linked_hash_map::LinkedHashMap;
    /// let mut map: LinkedHashMap<i32, &str> = LinkedHashMap::new();
    /// let capacity = map.capacity();
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
    /// use linked_hash_map::LinkedHashMap;
    /// let mut map = LinkedHashMap::new();
    /// map.insert(1, 10);
    /// map.insert(2, 20);
    /// map.pop_front();
    /// assert_eq!(map.get(&1), None);
    /// assert_eq!(map.get(&2), Some(&20));
    /// ```
    #[inline]
    pub fn pop_front(&mut self) -> Option<(K, V)> {
        if self.len() > 0 {
            let lru = unsafe { (*self.head).prev };
            self.detach(lru);
            return self.map
                .remove(&KeyRef{k: unsafe { &(*lru).key }})
                .map(|e| { let e = *e; (e.key, e.value) })
        }
        None
    }

    /// Gets the first entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use linked_hash_map::LinkedHashMap;
    /// let mut map = LinkedHashMap::new();
    /// map.insert(1, 10);
    /// map.insert(2, 20);
    /// assert_eq!(map.front(), Some((&1, &10)));
    /// ```
    #[inline]
    pub fn front(&self) -> Option<(&K, &V)> {
        if self.len() > 0 {
            let lru = unsafe { (*self.head).prev };
            return self.map.get(&KeyRef{k: unsafe { &(*lru).key }})
                .map(|e| (&e.key, &e.value))
        }
        None
    }

    /// Removes the last entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use linked_hash_map::LinkedHashMap;
    /// let mut map = LinkedHashMap::new();
    /// map.insert(1, 10);
    /// map.insert(2, 20);
    /// map.pop_back();
    /// assert_eq!(map.get(&1), Some(&10));
    /// assert_eq!(map.get(&2), None);
    /// ```
    #[inline]
    pub fn pop_back(&mut self) -> Option<(K, V)> {
        if self.len() > 0 {
            let mru = unsafe { (*self.head).next };
            self.detach(mru);
            return self.map
                .remove(&KeyRef{k: unsafe { &(*mru).key }})
                .map(|e| { let e = *e; (e.key, e.value) })
        }
        None
    }

    /// Gets the last entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use linked_hash_map::LinkedHashMap;
    /// let mut map = LinkedHashMap::new();
    /// map.insert(1, 10);
    /// map.insert(2, 20);
    /// assert_eq!(map.back(), Some((&2, &20)));
    /// ```
    #[inline]
    pub fn back(&mut self) -> Option<(&K, &V)> {
        if self.len() > 0 {
            let mru = unsafe { (*self.head).next };
            return self.map.get(&KeyRef{k: unsafe { &(*mru).key }})
                .map(|e| (&e.key, &e.value))
        }
        None
    }

    /// Returns the number of key-value pairs in the map.
    pub fn len(&self) -> usize { self.map.len() }

    /// Returns whether the map is currently empty.
    pub fn is_empty(&self) -> bool { self.len() == 0 }

    /// Clears the map of all key-value pairs.
    pub fn clear(&mut self) {
        self.map.clear();
        // update the guard node if present
        if ! self.head.is_null() {
            unsafe {
                (*self.head).prev = self.head;
                (*self.head).next = self.head;
            }
        }
    }

    /// Returns a double-ended iterator visiting all key-value pairs in order of insertion.
    /// Iterator element type is `(&'a K, &'a V)`
    ///
    /// # Examples
    /// ```
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
    /// ```
    pub fn iter(&self) -> Iter<K, V> {
        let head = if ! self.head.is_null() {
            unsafe { (*self.head).prev }
        } else {
            ptr::null_mut()
        };
        Iter {
            head: head,
            tail: self.head,
            remaining: self.len(),
            marker: marker::PhantomData,
        }
    }

    /// Returns a double-ended iterator visiting all key-value pairs in order of insertion.
    /// Iterator element type is `(&'a K, &'a mut V)`
    /// # Examples
    /// ```
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
    /// ```
    pub fn iter_mut(&mut self) -> IterMut<K, V> {
        let head = if ! self.head.is_null() {
            unsafe { (*self.head).prev }
        } else {
            ptr::null_mut()
        };
        IterMut {
            head: head,
            tail: self.head,
            remaining: self.len(),
            marker: marker::PhantomData,
        }
    }

    /// Returns a double-ended iterator visiting all key in order of insertion.
    ///
    /// # Examples
    /// ```
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
    /// ```
    pub fn keys<'a>(&'a self) -> Keys<'a, K, V> {
        fn first<A, B>((a, _): (A, B)) -> A { a }
        let first: fn((&'a K, &'a V)) -> &'a K = first; // coerce to fn ptr

        Keys { inner: self.iter().map(first) }
    }

    /// Returns a double-ended iterator visiting all values in order of insertion.
    ///
    /// # Examples
    /// ```
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
    /// ```
    pub fn values<'a>(&'a self) -> Values<'a, K, V> {
        fn second<A, B>((_, b): (A, B)) -> B { b }
        let second: fn((&'a K, &'a V)) -> &'a V = second; // coerce to fn ptr

        Values { inner: self.iter().map(second) }
    }
}

impl<'a, K, V, S, Q: ?Sized> Index<&'a Q> for LinkedHashMap<K, V, S>
    where K: Hash + Eq + Borrow<Q>, S: BuildHasher, Q: Eq + Hash
{
    type Output = V;

    fn index(&self, index: &'a Q) -> &V {
        self.get(index).expect("no entry found for key")
    }
}

impl<'a, K, V, S, Q: ?Sized> IndexMut<&'a Q> for LinkedHashMap<K, V, S>
    where K: Hash + Eq + Borrow<Q>, S: BuildHasher, Q: Eq + Hash
{
    fn index_mut(&mut self, index: &'a Q) -> &mut V {
        self.get_mut(index).expect("no entry found for key")
    }
}

impl<K: Hash + Eq, V, S: BuildHasher> LinkedHashMap<K, V, S> {
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

#[cfg(not(feature = "nightly"))]
impl<K: Hash + Eq + Clone, V: Clone> Clone for LinkedHashMap<K, V> {
    fn clone(&self) -> Self {
        self.iter().map(|(k, v)| (k.clone(), v.clone())).collect()
    }
}

#[cfg(feature = "nightly")]
impl<K: Hash + Eq + Clone, V: Clone, S: BuildHasher + Clone> Clone for LinkedHashMap<K, V, S> {
    fn clone(&self) -> Self {
        let mut map = Self::with_hash_state(self.map.hasher().clone());
        map.extend(self.iter().map(|(k, v)| (k.clone(), v.clone())));
        map
    }
}

impl<K: Hash + Eq, V, S: BuildHasher + Default> Default for LinkedHashMap<K, V, S> {
    fn default() -> Self { LinkedHashMap::with_hash_state(Default::default()) }
}

impl<K: Hash + Eq, V, S: BuildHasher> Extend<(K, V)> for LinkedHashMap<K, V, S> {
    fn extend<T: IntoIterator<Item=(K, V)>>(&mut self, iter: T) {
        for (k, v) in iter {
            self.insert(k, v);
        }
    }
}

impl<'a, K, V, S> Extend<(&'a K, &'a V)> for LinkedHashMap<K, V, S>
    where K: 'a + Hash + Eq + Copy, V: 'a + Copy, S: BuildHasher,
{
    fn extend<I: IntoIterator<Item = (&'a K, &'a V)>>(&mut self, iter: I) {
        for (&k, &v) in iter {
            self.insert(k, v);
        }
    }
}

impl<K: Hash + Eq, V, S: BuildHasher + Default> iter::FromIterator<(K, V)> for LinkedHashMap<K, V, S> {
    fn from_iter<I: IntoIterator<Item=(K, V)>>(iter: I) -> Self {
        let iter = iter.into_iter();
        let mut map = Self::with_capacity_and_hash_state(iter.size_hint().0, Default::default());
        map.extend(iter);
        map
    }
}

impl<A: fmt::Debug + Hash + Eq, B: fmt::Debug, S: BuildHasher> fmt::Debug for LinkedHashMap<A, B, S> {
    /// Returns a string that lists the key-value pairs in insertion order.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_map().entries(self).finish()
    }
}

impl<K: Hash + Eq, V: PartialEq, S: BuildHasher> PartialEq for LinkedHashMap<K, V, S> {
    fn eq(&self, other: &Self) -> bool {
        self.len() == other.len() && self.iter().eq(other)
    }

    fn ne(&self, other: &Self) -> bool {
        self.len() != other.len() || self.iter().ne(other)
    }
}

impl<K: Hash + Eq, V: Eq, S: BuildHasher> Eq for LinkedHashMap<K, V, S> {}

impl<K: Hash + Eq + PartialOrd, V: PartialOrd, S: BuildHasher> PartialOrd for LinkedHashMap<K, V, S> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.iter().partial_cmp(other)
    }

    fn lt(&self, other: &Self) -> bool {
        self.iter().lt(other)
    }

    fn le(&self, other: &Self) -> bool {
        self.iter().le(other)
    }

    fn ge(&self, other: &Self) -> bool {
        self.iter().ge(other)
    }

    fn gt(&self, other: &Self) -> bool {
        self.iter().gt(other)
    }
}

impl<K: Hash + Eq + Ord, V: Ord, S: BuildHasher> Ord for LinkedHashMap<K, V, S> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.iter().cmp(other)
    }
}

impl<K: Hash + Eq, V: Hash, S: BuildHasher> Hash for LinkedHashMap<K, V, S> {
    fn hash<H: Hasher>(&self, h: &mut H) { for e in self.iter() { e.hash(h); } }
}

unsafe impl<K: Send, V: Send, S: Send> Send for LinkedHashMap<K, V, S> {}

unsafe impl<K: Sync, V: Sync, S: Sync> Sync for LinkedHashMap<K, V, S> {}

impl<K, V, S> Drop for LinkedHashMap<K, V, S> {
    fn drop(&mut self) {
        unsafe {
            if ! self.head.is_null() {
                drop_empty_entry_box(self.head);
            }
            self.clear_free_list();
        }
    }
}

/// An insertion-order iterator over a `LinkedHashMap`'s entries, with immutable references to the
/// values.
pub struct Iter<'a, K: 'a, V: 'a> {
    head: *const LinkedHashMapEntry<K, V>,
    tail: *const LinkedHashMapEntry<K, V>,
    remaining: usize,
    marker: marker::PhantomData<(&'a K, &'a V)>,
}

/// An insertion-order iterator over a `LinkedHashMap`'s entries, with mutable references to the
/// values.
pub struct IterMut<'a, K: 'a, V: 'a> {
    head: *mut LinkedHashMapEntry<K, V>,
    tail: *mut LinkedHashMapEntry<K, V>,
    remaining: usize,
    marker: marker::PhantomData<(&'a K, &'a mut V)>,
}

unsafe impl<'a, K, V> Send for Iter<'a, K, V> where K: Send, V: Send {}

unsafe impl<'a, K, V> Send for IterMut<'a, K, V> where K: Send, V: Send {}

unsafe impl<'a, K, V> Sync for Iter<'a, K, V> where K: Sync, V: Sync {}

unsafe impl<'a, K, V> Sync for IterMut<'a, K, V> where K: Sync, V: Sync {}

impl<'a, K, V> Clone for Iter<'a, K, V> {
    fn clone(&self) -> Self { Iter { ..*self } }
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

impl<'a, K, V> ExactSizeIterator for Iter<'a, K, V> {
    fn len(&self) -> usize { self.remaining }
}

impl<'a, K, V> ExactSizeIterator for IterMut<'a, K, V> {
    fn len(&self) -> usize { self.remaining }
}

/// An insertion-order iterator over a `LinkedHashMap`'s keys.
pub struct Keys<'a, K: 'a, V: 'a> {
    inner: iter::Map<Iter<'a, K, V>, fn((&'a K, &'a V)) -> &'a K>
}

impl<'a, K, V> Clone for Keys<'a, K, V> {
    fn clone(&self) -> Self { Keys { inner: self.inner.clone() } }
}

impl<'a, K, V> Iterator for Keys<'a, K, V> {
    type Item = &'a K;

    #[inline] fn next(&mut self) -> Option<(&'a K)> { self.inner.next() }
    #[inline] fn size_hint(&self) -> (usize, Option<usize>) { self.inner.size_hint() }
}

impl<'a, K, V> DoubleEndedIterator for Keys<'a, K, V> {
    #[inline] fn next_back(&mut self) -> Option<(&'a K)> { self.inner.next_back() }
}

impl<'a, K, V> ExactSizeIterator for Keys<'a, K, V> {
    fn len(&self) -> usize { self.inner.len() }
}

/// An insertion-order iterator over a `LinkedHashMap`'s values.
pub struct Values<'a, K: 'a, V: 'a> {
    inner: iter::Map<Iter<'a, K, V>, fn((&'a K, &'a V)) -> &'a V>
}

impl<'a, K, V> Clone for Values<'a, K, V> {
    fn clone(&self) -> Self { Values { inner: self.inner.clone() } }
}

impl<'a, K, V> Iterator for Values<'a, K, V> {
    type Item = &'a V;

    #[inline] fn next(&mut self) -> Option<(&'a V)> { self.inner.next() }
    #[inline] fn size_hint(&self) -> (usize, Option<usize>) { self.inner.size_hint() }
}

impl<'a, K, V> DoubleEndedIterator for Values<'a, K, V> {
    #[inline] fn next_back(&mut self) -> Option<(&'a V)> { self.inner.next_back() }
}

impl<'a, K, V> ExactSizeIterator for Values<'a, K, V> {
    fn len(&self) -> usize { self.inner.len() }
}

impl<'a, K: Hash + Eq, V, S: BuildHasher> IntoIterator for &'a LinkedHashMap<K, V, S> {
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V>;
    fn into_iter(self) -> Iter<'a, K, V> { self.iter() }
}

impl<'a, K: Hash + Eq, V, S: BuildHasher> IntoIterator for &'a mut LinkedHashMap<K, V, S> {
    type Item = (&'a K, &'a mut V);
    type IntoIter = IterMut<'a, K, V>;
    fn into_iter(self) -> IterMut<'a, K, V> { self.iter_mut() }
}

#[cfg(all(feature = "nightly", test))]
mod bench {
    extern crate test;

    use super::LinkedHashMap;

    #[bench]
    fn not_recycled_cycling(b: &mut test::Bencher) {
        let mut hash_map = LinkedHashMap::with_capacity(1000);
        for i in 0usize..1000 {
            hash_map.insert(i, i);
        }
        b.iter(|| {
            for i in 0usize..1000 {
                hash_map.remove(&i);
            }
            hash_map.clear_free_list();
            for i in 0usize..1000 {
                hash_map.insert(i, i);
            }
        })
    }

    #[bench]
    fn recycled_cycling(b: &mut test::Bencher) {
        let mut hash_map = LinkedHashMap::with_capacity(1000);
        for i in 0usize..1000 {
            hash_map.insert(i, i);
        }
        b.iter(|| {
            for i in 0usize..1000 {
                hash_map.remove(&i);
            }
            for i in 0usize..1000 {
                hash_map.insert(i, i);
            }
        })
    }
}
