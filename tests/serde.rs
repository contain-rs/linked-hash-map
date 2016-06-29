#![cfg(feature = "serde_impl")]

extern crate linked_hash_map;
use linked_hash_map::LinkedHashMap;

extern crate serde_test;
use serde_test::{Token, assert_tokens};

#[test]
fn test_ser_de_empty() {
    let map = LinkedHashMap::<String, u32>::new();

    assert_tokens(&map, &[
        Token::MapStart(Some(0)),
        Token::MapEnd,
    ]);
}

#[test]
fn test_ser_de() {
    let mut map = LinkedHashMap::new();
    map.insert("b".to_string(), 20);
    map.insert("a".to_string(), 10);
    map.insert("c".to_string(), 30);

    assert_tokens(&map, &[
        Token::MapStart(Some(3)),
            Token::MapSep,
            Token::Str("b"),
            Token::I32(20),

            Token::MapSep,
            Token::Str("a"),
            Token::I32(10),

            Token::MapSep,
            Token::Str("c"),
            Token::I32(30),
        Token::MapEnd,
    ]);
}
