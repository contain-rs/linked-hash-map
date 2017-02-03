//! An optional implementation of serialization/deserialization. Reference
//! implementations used:
//!
//! - [Serialize][1].
//! - [Deserialize][2].
//!
//! [1]: https://github.com/serde-rs/serde/blob/97856462467db2e90cf368e407c7ebcc726a01a9/serde/src/ser/impls.rs#L601-L611
//! [2]: https://github.com/serde-rs/serde/blob/97856462467db2e90cf368e407c7ebcc726a01a9/serde/src/de/impls.rs#L694-L746

extern crate serde;

use std::fmt::{Formatter, Result as FmtResult};
use std::marker::PhantomData;
use std::hash::{BuildHasher, Hash};

use super::LinkedHashMap;

use self::serde::{Serialize, Serializer, Deserialize, Deserializer};
use self::serde::ser::SerializeMap;
use self::serde::de::{Visitor, MapVisitor, Error};

impl<K, V, S> Serialize for LinkedHashMap<K, V, S>
    where K: Serialize + Eq + Hash,
          V: Serialize,
          S: BuildHasher
{
    #[inline]
    fn serialize<T>(&self, serializer:T) -> Result<T::Ok, T::Error>
        where T: Serializer,
    {
        let mut map_serializer = try!(serializer.serialize_map(Some(self.len())));
        for (k, v) in self {
            try!(map_serializer.serialize_key(k));
            try!(map_serializer.serialize_value(v));
        }
        map_serializer.end()
    }
}

/// `serde::de::Visitor` for a linked hash map.
pub struct LinkedHashMapVisitor<K, V> {
    marker: PhantomData<LinkedHashMap<K, V>>,
}

impl<K, V> LinkedHashMapVisitor<K, V> {
    /// Creates a new visitor for a linked hash map.
    pub fn new() -> Self {
        LinkedHashMapVisitor {
            marker: PhantomData,
        }
    }
}

impl<K, V> Visitor for LinkedHashMapVisitor<K, V>
    where K: Deserialize + Eq + Hash,
          V: Deserialize,
{
    type Value = LinkedHashMap<K, V>;

    fn expecting(&self, formatter: &mut Formatter) -> FmtResult {
        write!(formatter, "a map")
    }

    #[inline]
    fn visit_unit<E>(self) -> Result<Self::Value, E>
        where E: Error,
    {
        Ok(LinkedHashMap::new())
    }

    #[inline]
    fn visit_map<Visitor>(self, mut visitor: Visitor) -> Result<Self::Value, Visitor::Error>
        where Visitor: MapVisitor,
    {
        let mut values = LinkedHashMap::with_capacity(visitor.size_hint().0);

        while let Some((key, value)) = try!(visitor.visit()) {
            values.insert(key, value);
        }

        Ok(values)
    }
}

impl<K, V> Deserialize for LinkedHashMap<K, V>
    where K: Deserialize + Eq + Hash,
          V: Deserialize,
{
    fn deserialize<D>(deserializer: D) -> Result<LinkedHashMap<K, V>, D::Error>
        where D: Deserializer,
    {
        deserializer.deserialize_map(LinkedHashMapVisitor::new())
    }
}
