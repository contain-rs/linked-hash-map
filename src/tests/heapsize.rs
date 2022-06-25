#![cfg(all(feature = "heapsize_impl", not(miri)))]

extern crate heapsize;
extern crate linked_hash_map;

use heapsize::HeapSizeOf;
use linked_hash_map::LinkedHashMap;

#[test]
fn empty() {
    assert_eq!(
        LinkedHashMap::<String, String>::new().heap_size_of_children(),
        0
    );
}

#[test]
fn nonempty() {
    let mut map = LinkedHashMap::new();
    map.insert("hello".to_string(), "world".to_string());
    map.insert("hola".to_string(), "mundo".to_string());
    map.insert("bonjour".to_string(), "monde".to_string());
    map.remove("hello");

    assert!(map.heap_size_of_children() != 0);
}
