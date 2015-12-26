//! Collection traits for generic programming.

#![deny(missing_docs)]
#![feature(set_recovery)]

mod std_impls;

/// A collection.
pub trait Collection {
    /// The type of the collection's items.
    type Item;

    /// Checks if the collection contains zero items.
    ///
    /// This is equivalent to `self.len() == 0`, but may be optimized.
    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the number of items in the collection.
    fn len(&self) -> usize;
}

/// A collection that supports insertion.
pub trait Insert: Collection {
    /// Moves all items from the given collection into the collection.
    fn append(&mut self, other: &mut Self) where Self: Sized;
}

/// A collection that supports removal.
pub trait Remove: Collection {
    /// Removes all items from the collection.
    fn clear(&mut self);
}

pub mod map {
    //! Maps.

    /// A map.
    ///
    /// A map is a collection that associates keys with values, where the keys are distinguished
    /// according to some uniqueness criteria.
    pub trait Map: super::Collection<Item = (<Self as Map>::Key, <Self as Map>::Value)> {
        /// The type of the map's keys.
        type Key;

        /// The type of the map's values.
        type Value;
    }

    /// A map that supports lookups using keys of type `&Q`.
    pub trait Get<Q: ?Sized = <Self as Map>::Key>: Map {
        /// Checks if the map contains a key that is equivalent to the given key.
        ///
        /// This is equivalent to `self.get(key).is_some()`, but may be optimized.
        fn contains_key(&self, key: &Q) -> bool {
            self.get(key).is_some()
        }

        /// Returns a reference to the value in the map whose key is equivalent to the given key.
        ///
        /// Returns `None` if the map contains no such key.
        fn get(&self, key: &Q) -> Option<&Self::Value>;

        /// Returns a mutable reference to the value in the map whose key is equivalent to the
        /// given key.
        ///
        /// Returns `None` if the map contains no such key.
        fn get_mut(&mut self, key: &Q) -> Option<&mut Self::Value>;
    }

    /// A map that supports removals using keys of type `&Q`.
    pub trait Remove<Q: ?Sized = <Self as Map>::Key>: Get<Q> + super::Remove {
        /// Removes the key in the map that is equivalent to the given key and returns its value.
        ///
        /// Returns `None` if the map contains no such key.
        fn remove(&mut self, key: &Q) -> Option<Self::Value>;
    }

    /// A map that supports insertion.
    pub trait Insert: Map + super::Insert {
        /// Inserts the given key and value into the map and returns the previous value
        /// corresponding to the given key, if any.
        fn insert(&mut self, key: Self::Key, value: Self::Value) -> Option<Self::Value>;
    }

    /// A map that supports efficient in-place modification.
    ///
    /// `'a` is the lifetime of the map.
    pub trait EntryMap<'a>: Insert + Remove {
        /// The type of the map's occupied entries.
        type OccupiedEntry: OccupiedEntry<'a, Map = Self>;

        /// The type of the map's vacant entries.
        type VacantEntry: VacantEntry<'a, Map = Self>;

        /// Returns the entry in the map corresponding to the given key.
        fn entry(&'a mut self, key: Self::Key) -> Entry<Self>;
    }

    /// An occupied map entry.
    ///
    /// `'a` is the lifetime of the map.
    pub trait OccupiedEntry<'a>: Sized {
        /// The entry's map type.
        type Map: ?Sized + EntryMap<'a, OccupiedEntry = Self>;

        /// Returns a reference to the entry's value.
        fn get(&self) -> &<Self::Map as Map>::Value;

        /// Returns a mutable reference to the entry's value.
        fn get_mut(&mut self) -> &mut <Self::Map as Map>::Value;

        /// Returns a mutable reference to the entry's value with the same lifetime as the map.
        fn into_mut(self) -> &'a mut <Self::Map as Map>::Value;

        /// Replaces the entry's value with the given one and returns the old value.
        fn insert(&mut self, value: <Self::Map as Map>::Value) -> <Self::Map as Map>::Value {
            ::std::mem::replace(self.get_mut(), value)
        }

        /// Removes the entry from the map and returns its value.
        fn remove(self) -> <Self::Map as Map>::Value;
    }

    /// A vacant map entry.
    ///
    /// `'a` is the lifetime of the map.
    pub trait VacantEntry<'a>: Sized {
        /// The entry's map type.
        type Map: ?Sized + EntryMap<'a, VacantEntry = Self>;

        /// Inserts the entry into the map with the given value and returns a mutable reference to
        /// it with the same lifetime as the map.
        fn insert(self, value: <Self::Map as Map>::Value) -> &'a mut <Self::Map as Map>::Value;
    }

    /// A map entry.
    #[derive(Debug)]
    pub enum Entry<'a, M: ?Sized + EntryMap<'a>> {
        /// An occupied map entry.
        Occupied(M::OccupiedEntry),
        /// A vacant map entry.
        Vacant(M::VacantEntry),
    }

    impl<'a, M: ?Sized + EntryMap<'a>> Entry<'a, M> {
        /// Ensures the entry is occupied by inserting it with the given default value if it is
        /// vacant.
        pub fn or_insert(self, default: M::Value) -> &'a mut M::Value {
            match self {
                Entry::Occupied(e) => e.into_mut(),
                Entry::Vacant(e) => e.insert(default),
            }
        }

        /// Ensures the entry is occupied by inserting it with the result of the given function if
        /// it is vacant.
        pub fn or_insert_with<F: FnOnce() -> M::Value>(self, f: F) -> &'a mut M::Value {
            match self {
                Entry::Occupied(e) => e.into_mut(),
                Entry::Vacant(e) => e.insert(f()),
            }
        }
    }

    #[cfg(test)]
    pub fn count<M, I>(items: I) -> M
    where
        M: Default + for<'a> EntryMap<'a, Value = usize>,
        I: IntoIterator<Item = M::Key>,
    {
        let mut map = M::default();
        for item in items { *map.entry(item).or_insert(0) += 1; }
        map
    }
}

pub mod set {
    //! Sets.

    use super::Collection;

    /// A set.
    ///
    /// A set is a collection whose items are distinguished according to some uniqueness criteria.
    pub trait Set: Collection {
        /// Checks if the set is disjoint from the given set.
        fn is_disjoint(&self, other: &Self) -> bool where Self: Sized;

        /// Checks if the set is a subset of the given set.
        fn is_subset(&self, other: &Self) -> bool where Self: Sized;

        /// Checks if the set is a superset of the given set.
        fn is_superset(&self, other: &Self) -> bool where Self: Sized {
            other.is_subset(self)
        }
    }

    /// A set that supports retrievals using items of type `&Q`.
    pub trait Get<Q: ?Sized = <Self as Collection>::Item>: Set {
        /// Checks if the set contains an item that is equivalent to the given item.
        ///
        /// This is equivalent to `self.get(item).is_some()`, but may be optimized.
        fn contains(&self, item: &Q) -> bool {
            self.get(item).is_some()
        }

        /// Returns the item in the set that is equivalent to the given item.
        ///
        /// Returns `None` if the set contains no such item.
        fn get(&self, item: &Q) -> Option<&Self::Item>;
    }

    /// A set that supports removal using items of type `&Q`.
    pub trait Remove<Q: ?Sized = <Self as Collection>::Item>: Get<Q> + super::Remove {
        /// Removes the item in the set that is equivalent to the given item.
        ///
        /// Returns `true` if the set contained such an item, `false` otherwise.
        ///
        /// This is equivalent to `self.take(item).is_some()`, but may be optimized.
        fn remove(&mut self, item: &Q) -> bool {
            self.take(item).is_some()
        }

        /// Removes and returns the item in the set that is equivalent to the given item.
        ///
        /// Returns `None` if the set contained no such item.
        fn take(&mut self, item: &Q) -> Option<Self::Item>;
    }

    /// A set that supports insertion.
    pub trait Insert: Set + super::Insert {
        /// Inserts the given item into the set without replacement.
        ///
        /// Returns `true` if the set contained an equivalent item, `false` otherwise.
        fn insert(&mut self, item: Self::Item) -> bool;

        /// Inserts the given item into the set with replacement.
        ///
        /// Returns the equivalent item if the set contained one, `None` otherwise.
        fn replace(&mut self, item: Self::Item) -> Option<Self::Item>;
    }
}
