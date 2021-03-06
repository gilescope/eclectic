use std::borrow::Borrow;
use std::collections::*;
use std::hash::{BuildHasher, Hash};
use std::mem;
use std::ops::Range;
use super::*;
use trait_tests::test_impl;
use super::tests::*;

impl<T> Mutate for [T] {}

//TODO #[test_impl]
impl<T> Collection for [T] {
    type Item = T;

    fn len(&self) -> usize {
        self.len()
    }

    fn capacity(&self) -> usize {
        self.len()
    }

    fn extend_object(&mut self, _items: &mut Iterator<Item = T>) where Self: AddRemove {
        unimplemented!()
    }

    fn drain<'a>(&'a mut self) -> Box<Iterator<Item = T> + 'a> where Self: AddRemove {
        unimplemented!()
    }

    fn reserve(&mut self, _additional: usize) where Self: AddRemove {
        unimplemented!()
    }

    fn shrink_to_fit(&mut self) where Self: AddRemove {
        unimplemented!()
    }
}

impl<T> Iter for [T] {
    fn iter<'a>(&'a self) -> Box<Iterator<Item = &'a T> + 'a> {
        Box::new(self.iter())
    }

    fn iter_mut<'a>(&'a mut self) -> Box<Iterator<Item = &'a mut T> + 'a> {
        Box::new(self.iter_mut())
    }
}

impl<T> DrainRange<Range<usize>> for [T] {
    fn drain_range<'a>(&'a mut self, _range: Range<usize>)
        -> Box<Iterator<Item = T> + 'a> where Self: AddRemove
    {
        unimplemented!()
    }
}

//TODO edgecase!
impl<T> List for [T] {
    fn get(&self, index: usize) -> Option<&T> {
        self.get(index)
    }

    fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        self.get_mut(index)
    }

    fn swap(&mut self, i: usize, j: usize) {
        self.swap(i, j);
    }

    fn reverse(&mut self) {
        self.reverse();
    }

    fn insert(&mut self, _index: usize, _item: T) where Self: AddRemove {
        unimplemented!()
    }

    fn remove(&mut self, _index: usize) -> Option<T> where Self: AddRemove {
        unimplemented!()
    }

    fn swap_remove(&mut self, _index: usize) -> Option<T> where Self: AddRemove {
        unimplemented!()
    }
}

impl<K: Ord, V> Mutate for BTreeMap<K, V> {}

impl<K: Ord, V> AddRemove for BTreeMap<K, V> {}

//TODO CollectionTests is over isize, but this is (K,V) tuple. Doesn't match.
impl<K: Ord, V> Collection for BTreeMap<K, V> {
    type Item = (K, V);

    fn len(&self) -> usize {
        self.len()
    }

    fn capacity(&self) -> usize {
        self.len()
    }

    fn append(&mut self, other: &mut Self) {
        self.extend(mem::replace(other, Self::new()));
    }

    fn extend_object(&mut self, items: &mut Iterator<Item = (K, V)>) {
        self.extend(items);
    }

    fn clear(&mut self) {
        self.clear();
    }

    fn drain<'a>(&'a mut self) -> Box<Iterator<Item = (K, V)> + 'a> {
        Box::new(mem::replace(self, Self::new()).into_iter())
    }

    fn reserve(&mut self, _additional: usize) {}

    fn shrink_to_fit(&mut self) {}

    fn with_capacity(_capacity: usize) -> Self {
        Self::new()
    }

    fn into_vec(self) -> Vec<(K, V)> {
        self.into_iter().collect()
    }
}

impl<K: Ord, V> map::Base for BTreeMap<K, V> {
    type Key = K;
    type Value = V;

    fn iter<'a>(&'a self) -> Box<Iterator<Item = (&'a K, &'a V)> + 'a> {
        Box::new(self.iter())
    }

    fn iter_mut<'a>(&'a mut self) -> Box<Iterator<Item = (&'a K, &'a mut V)> + 'a> {
        Box::new(self.iter_mut())
    }

    fn insert(&mut self, key: K, value: V) -> Option<V> {
        self.insert(key, value)
    }

    fn entry<'a>(&'a mut self, key: K) -> map::Entry<'a, K, V> {
        match self.entry(key) {
            btree_map::Entry::Occupied(e) => map::Entry::Occupied(Box::new(e)),
            btree_map::Entry::Vacant(e) => map::Entry::Vacant(Box::new(e)),
        }
    }
}

impl<K: Ord + Borrow<Q>, V, Q: ?Sized + Ord> Map<Q> for BTreeMap<K, V> {
    fn get(&self, key: &Q) -> Option<&V> {
        self.get(key)
    }
    
    fn get_mut(&mut self, key: &Q) -> Option<&mut V> {
        self.get_mut(key)
    }
    
    fn remove(&mut self, key: &Q) -> Option<V> {
        self.remove(key)
    }
}

impl<'a, K: 'a + Ord, V: 'a> map::OccupiedEntry for btree_map::OccupiedEntry<'a, K, V> {
    type Key = K;
    type Value = V;
    type MutValue = &'a mut V;

    fn get(&self) -> &V {
        self.get()
    }

    fn get_mut(&mut self) -> &mut V {
        self.get_mut()
    }

    fn into_mut(self: Box<Self>) -> &'a mut V {
        (*self).into_mut()
    }

    fn remove(self: Box<Self>) -> V {
        (*self).remove()
    }
}

impl<'a, K: 'a + Ord, V: 'a> map::VacantEntry for btree_map::VacantEntry<'a, K, V> {
    type Key = K;
    type Value = V;
    type MutValue = &'a mut V;

    fn insert(self: Box<Self>, value: V) -> &'a mut V {
        (*self).insert(value)
    }
}

impl<T: Ord> AddRemove for BTreeSet<T> {}

#[test_impl]
impl<T: Ord> Collection for BTreeSet<T> {
    type Item = T;

    fn len(&self) -> usize {
        self.len()
    }

    fn capacity(&self) -> usize {
        self.len()
    }

    fn append(&mut self, other: &mut Self) {
        self.extend(mem::replace(other, Self::new()));
    }

    fn extend_object(&mut self, items: &mut Iterator<Item = T>) {
        self.extend(items);
    }

    fn clear(&mut self) {
        self.clear();
    }

    fn drain<'a>(&'a mut self) -> Box<Iterator<Item = T> + 'a> {
        Box::new(mem::replace(self, Self::new()).into_iter())
    }

    fn reserve(&mut self, _additional: usize) {}

    fn shrink_to_fit(&mut self) {}

    fn with_capacity(_capacity: usize) -> Self {
        Self::new()
    }

    fn into_vec(self) -> Vec<T> {
        self.into_iter().collect()
    }
}

#[test_impl]
impl<T: Ord> Iter for BTreeSet<T> {
    fn iter<'a>(&'a self) -> Box<Iterator<Item = &'a T> + 'a> {
        Box::new(self.iter())
    }

    fn iter_mut<'a>(&'a mut self) -> Box<Iterator<Item = &'a mut T> + 'a> where Self: Mutate {
        unimplemented!()
    }
}

impl<T: Ord> set::Base for BTreeSet<T> {
    fn is_disjoint(&self, other: &Self) -> bool {
        self.is_disjoint(other)
    }

    fn is_subset(&self, other: &Self) -> bool {
        self.is_subset(other)
    }

    fn insert(&mut self, item: T) -> bool {
        self.insert(item)
    }

    fn replace(&mut self, item: T) -> Option<T> {
        self.replace(item)
    }
}

#[test_impl]
impl<T: Ord + Borrow<Q>, Q: ?Sized + Ord> Set<Q> for BTreeSet<T> {
    fn contains(&self, item: &Q) -> bool {
        self.contains(item)
    }

    fn get(&self, item: &Q) -> Option<&T> {
        self.get(item)
    }

    fn remove(&mut self, item: &Q) -> bool {
        self.remove(item)
    }

    fn take(&mut self, item: &Q) -> Option<T> {
        self.take(item)
    }
}

impl<T: Ord> AddRemove for BinaryHeap<T> {}

#[test_impl]
impl<T: Ord> Collection for BinaryHeap<T> {
    type Item = T;

    fn len(&self) -> usize {
        self.len()
    }

    fn capacity(&self) -> usize {
        self.capacity()
    }

    fn append(&mut self, other: &mut Self) {
        self.extend(other.drain());
    }

    fn extend_object(&mut self, items: &mut Iterator<Item = T>) {
        self.extend(items);
    }

    fn clear(&mut self) {
        self.clear();
    }

    fn drain<'a>(&'a mut self) -> Box<Iterator<Item = T> + 'a> {
        Box::new(self.drain())
    }

    fn reserve(&mut self, additional: usize) {
        self.reserve(additional);
    }

    fn shrink_to_fit(&mut self) {
        self.shrink_to_fit();
    }

    fn with_capacity(capacity: usize) -> Self {
        Self::with_capacity(capacity)
    }

    fn into_vec(self) -> Vec<T> {
        self.into_vec()
    }
}

impl<T: Ord> Iter for BinaryHeap<T> {
    fn iter<'a>(&'a self) -> Box<Iterator<Item = &'a T> + 'a> {
        Box::new(self.iter())
    }

    fn iter_mut<'a>(&'a mut self) -> Box<Iterator<Item = &'a mut T> + 'a> where Self: Mutate {
        unimplemented!()
    }
}

#[test_impl]
impl<T: Ord> Queue for BinaryHeap<T> {
    fn push(&mut self, item: T) {
        self.push(item);
    }

    fn front(&self) -> Option<&T> {
        self.peek()
    }

    fn pop_front(&mut self) -> Option<T> {
        self.pop()
    }
}

#[test_impl]
impl<T: Ord> PrioQueue for BinaryHeap<T> {
    fn push_pop_front(&mut self, item: T) -> T {
        match self.peek_mut() {
            Some(ref mut old) if item < **old => mem::replace(&mut *old, item),
            _ => item,
        }
    }

    fn replace_front(&mut self, item: T) -> Option<T> {
        if let Some(mut old) = self.peek_mut() {
            return Some(mem::replace(&mut *old, item));
        };

        self.push(item);
        None
    }
}

impl<K: Eq + Hash, V, S: BuildHasher> Mutate for HashMap<K, V, S> {}

impl<K: Eq + Hash, V, S: BuildHasher> AddRemove for HashMap<K, V, S> {}

//TODO #[test_impl]
impl<K: Eq + Hash, V, S: BuildHasher + Default> Collection for HashMap<K, V, S> {
    type Item = (K, V);

    fn len(&self) -> usize {
        self.len()
    }

    fn capacity(&self) -> usize {
        self.capacity()
    }

    fn append(&mut self, other: &mut Self) {
        self.extend(other.drain());
    }

    fn extend_object(&mut self, items: &mut Iterator<Item = (K, V)>) {
        self.extend(items);
    }

    fn clear(&mut self) {
        self.clear();
    }

    fn drain<'a>(&'a mut self) -> Box<Iterator<Item = (K, V)> + 'a> {
        Box::new(self.drain())
    }

    fn reserve(&mut self, additional: usize) {
        self.reserve(additional);
    }

    fn shrink_to_fit(&mut self) {
        self.shrink_to_fit();
    }

    fn with_capacity(capacity: usize) -> Self {
        Self::with_capacity(capacity)
    }

    fn into_vec(self) -> Vec<(K, V)> {
        self.into_iter().collect()
    }
}

impl<K: Eq + Hash, V, S: BuildHasher + Default> map::Base for HashMap<K, V, S> {
    type Key = K;
    type Value = V;

    fn iter<'a>(&'a self) -> Box<Iterator<Item = (&'a K, &'a V)> + 'a> {
        Box::new(self.iter())
    }

    fn iter_mut<'a>(&'a mut self) -> Box<Iterator<Item = (&'a K, &'a mut V)> + 'a> {
        Box::new(self.iter_mut())
    }

    fn insert(&mut self, key: K, value: V) -> Option<V> {
        self.insert(key, value)
    }

    fn entry<'a>(&'a mut self, key: K) -> map::Entry<'a, K, V> {
        match self.entry(key) {
            hash_map::Entry::Occupied(e) => map::Entry::Occupied(Box::new(e)),
            hash_map::Entry::Vacant(e) => map::Entry::Vacant(Box::new(e)),
        }
    }
}

impl<K: Eq + Hash + Borrow<Q>, V, S: BuildHasher + Default, Q: ?Sized + Eq + Hash> Map<Q> for HashMap<K, V, S> {
    fn get(&self, key: &Q) -> Option<&V> {
        self.get(key)
    }
    
    fn get_mut(&mut self, key: &Q) -> Option<&mut V> {
        self.get_mut(key)
    }
    
    fn remove(&mut self, key: &Q) -> Option<V> {
        self.remove(key)
    }
}

impl<'a, K: 'a + Eq + Hash, V: 'a> map::OccupiedEntry for hash_map::OccupiedEntry<'a, K, V> {
    type Key = K;
    type Value = V;
    type MutValue = &'a mut V;

    fn get(&self) -> &V {
        self.get()
    }

    fn get_mut(&mut self) -> &mut V {
        self.get_mut()
    }

    fn into_mut(self: Box<Self>) -> &'a mut V {
        (*self).into_mut()
    }

    fn remove(self: Box<Self>) -> V {
        (*self).remove()
    }
}

impl<'a, K: 'a + Eq + Hash, V: 'a> map::VacantEntry for hash_map::VacantEntry<'a, K, V> {
    type Key = K;
    type Value = V;
    type MutValue = &'a mut V;

    fn insert(self: Box<Self>, value: V) -> &'a mut V {
        (*self).insert(value)
    }
}

impl<T: Eq + Hash, S: BuildHasher> AddRemove for HashSet<T, S> {}

//TODO #[test_impl]
impl<T: Eq + Hash, S: BuildHasher + Default> Collection for HashSet<T, S> {
    type Item = T;

    fn len(&self) -> usize {
        self.len()
    }

    fn capacity(&self) -> usize {
        self.capacity()
    }

    fn append(&mut self, other: &mut Self) {
        self.extend(other.drain());
    }

    fn extend_object(&mut self, items: &mut Iterator<Item = T>) {
        self.extend(items);
    }

    fn clear(&mut self) {
        self.clear();
    }

    fn drain<'a>(&'a mut self) -> Box<Iterator<Item = T> + 'a> {
        Box::new(self.drain())
    }

    fn reserve(&mut self, additional: usize) {
        self.reserve(additional);
    }

    fn shrink_to_fit(&mut self) {
        self.shrink_to_fit();
    }

    fn with_capacity(capacity: usize) -> Self {
        Self::with_capacity(capacity)
    }

    fn into_vec(self) -> Vec<T> {
        self.into_iter().collect()
    }
}

impl<T: Eq + Hash, S: BuildHasher + Default> Iter for HashSet<T, S> {
    fn iter<'a>(&'a self) -> Box<Iterator<Item = &'a T> + 'a> {
        Box::new(self.iter())
    }

    fn iter_mut<'a>(&'a mut self) -> Box<Iterator<Item = &'a mut T> + 'a> where Self: Mutate {
        unimplemented!()
    }
}

impl<T: Eq + Hash, S: BuildHasher + Default> set::Base for HashSet<T, S> {
    fn is_disjoint(&self, other: &Self) -> bool {
        self.is_disjoint(other)
    }

    fn is_subset(&self, other: &Self) -> bool {
        self.is_subset(other)
    }

    fn insert(&mut self, item: T) -> bool {
        self.insert(item)
    }

    fn replace(&mut self, item: T) -> Option<T> {
        self.replace(item)
    }
}

//TODO: #[test_impl]
impl<T: Eq + Hash + Borrow<Q>, Q: ?Sized + Eq + Hash, S: BuildHasher + Default> Set<Q> for HashSet<T, S> {
    fn contains(&self, item: &Q) -> bool {
        self.contains(item)
    }

    fn get(&self, item: &Q) -> Option<&T> {
        self.get(item)
    }

    fn remove(&mut self, item: &Q) -> bool {
        self.remove(item)
    }

    fn take(&mut self, item: &Q) -> Option<T> {
        self.take(item)
    }
}

impl<T> Mutate for LinkedList<T> {}

impl<T> AddRemove for LinkedList<T> {}

#[test_impl]
impl<T> Collection for LinkedList<T> {
    type Item = T;

    fn len(&self) -> usize {
        self.len()
    }

    fn capacity(&self) -> usize {
        self.len()
    }

    fn append(&mut self, other: &mut Self) {
        self.append(other);
    }

    fn extend_object(&mut self, items: &mut Iterator<Item = T>) {
        self.extend(items);
    }

    fn clear(&mut self) {
        self.clear();
    }

    fn drain<'a>(&'a mut self) -> Box<Iterator<Item = T> + 'a> {
        Box::new(mem::replace(self, Self::new()).into_iter())
    }

    fn reserve(&mut self, _additional: usize) {}

    fn shrink_to_fit(&mut self) {}

    fn with_capacity(_capacity: usize) -> Self {
        Self::new()
    }

    fn into_vec(self) -> Vec<T> {
        self.into_iter().collect()
    }
}

#[test_impl]
impl<T> Iter for LinkedList<T> {
    fn iter<'a>(&'a self) -> Box<Iterator<Item = &'a T> + 'a> {
        Box::new(self.iter())
    }

    fn iter_mut<'a>(&'a mut self) -> Box<Iterator<Item = &'a mut T> + 'a> {
        Box::new(self.iter_mut())
    }
}

impl<T> Queue for LinkedList<T> {
    fn push(&mut self, item: T) {
        self.push_back(item);
    }

    fn front(&self) -> Option<&T> {
        self.front()
    }

    fn pop_front(&mut self) -> Option<T> {
        self.pop_front()
    }
}

impl<T> Deque for LinkedList<T> {
    fn back(&self) -> Option<&T> {
        self.back()
    }

    fn pop_back(&mut self) -> Option<T> {
        self.pop_back()
    }
}

impl<T> FifoQueue for LinkedList<T> {
    fn front_mut(&mut self) -> Option<&mut T> {
        self.front_mut()
    }
}

impl<T> FifoDeque for LinkedList<T> {
    fn push_front(&mut self, item: T) {
        self.push_front(item);
    }

    fn back_mut(&mut self) -> Option<&mut T> {
        self.back_mut()
    }
}

impl<T> Mutate for Vec<T> {}

impl<T> AddRemove for Vec<T> {}

#[test_impl]
impl<T> Collection for Vec<T> {
    type Item = T;

    fn len(&self) -> usize {
        self.len()
    }

    fn capacity(&self) -> usize {
        self.capacity()
    }

    fn append(&mut self, other: &mut Self) {
        self.append(other);
    }

    fn extend_object(&mut self, items: &mut Iterator<Item = T>) {
        self.extend(items);
    }

    fn clear(&mut self) {
        self.clear();
    }

    fn drain<'a>(&'a mut self) -> Box<Iterator<Item = T> + 'a> {
        Box::new(self.drain(..))
    }

    fn reserve(&mut self, additional: usize) {
        self.reserve(additional);
    }

    fn shrink_to_fit(&mut self) {
        self.shrink_to_fit();
    }

    fn with_capacity(capacity: usize) -> Self {
        Self::with_capacity(capacity)
    }

    fn into_vec(self) -> Vec<T> {
        self
    }
}

impl<T> Iter for Vec<T> {
    fn iter<'a>(&'a self) -> Box<Iterator<Item = &'a T> + 'a> {
        Box::new((**self).iter())
    }

    fn iter_mut<'a>(&'a mut self) -> Box<Iterator<Item = &'a mut T> + 'a> {
        Box::new((**self).iter_mut())
    }
}

#[test_impl]
impl<T> DrainRange<Range<usize>> for Vec<T> {
    fn drain_range<'a>(&'a mut self, range: Range<usize>) -> Box<Iterator<Item = T> + 'a> {
        Box::new(self.drain(range))
    }
}

#[test_impl]
impl<T> List for Vec<T> {
    fn get(&self, index: usize) -> Option<&T> {
        (**self).get(index)
    }

    fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        (**self).get_mut(index)
    }

    fn swap(&mut self, i: usize, j: usize) {
        (**self).swap(i, j);
    }

    fn reverse(&mut self) {
        (**self).reverse();
    }

    fn push(&mut self, item: T) {
        self.push(item);
    }

    fn insert(&mut self, index: usize, item: T) {
        self.insert(index, item);
    }

    fn pop(&mut self) -> Option<T> {
        self.pop()
    }

    fn remove(&mut self, index: usize) -> Option<T> {
        if index < self.len() {
            Some(self.remove(index))
        } else {
            None
        }
    }

    fn swap_remove(&mut self, index: usize) -> Option<T> {
        if index < self.len() {
            Some(self.swap_remove(index))
        } else {
            None
        }
    }

    #[cfg(feature = "nightly")]
    fn truncate(&mut self, len: usize) {
        self.truncate(len);
    }

    fn split_off(&mut self, index: usize) -> Self {
        self.split_off(index)
    }
}

impl<T> Mutate for VecDeque<T> {}

impl<T> AddRemove for VecDeque<T> {}

#[test_impl]
impl<T> Collection for VecDeque<T> {
    type Item = T;

    fn len(&self) -> usize {
        self.len()
    }

    fn capacity(&self) -> usize {
        self.capacity()
    }

    fn clear(&mut self) {
        self.clear();
    }

    fn append(&mut self, other: &mut Self) {
        self.append(other);
    }

    fn extend_object(&mut self, items: &mut Iterator<Item = T>) {
        self.extend(items);
    }

    fn drain<'a>(&'a mut self) -> Box<Iterator<Item = T> + 'a> {
        Box::new(self.drain(..))
    }

    fn reserve(&mut self, additional: usize) {
        self.reserve(additional);
    }

    fn shrink_to_fit(&mut self) {
        self.shrink_to_fit();
    }

    fn with_capacity(capacity: usize) -> Self {
        Self::with_capacity(capacity)
    }

    fn into_vec(self) -> Vec<T> {
        self.into_iter().collect()
    }
}

impl<T> Iter for VecDeque<T> {
    fn iter<'a>(&'a self) -> Box<Iterator<Item = &'a T> + 'a> {
        Box::new(self.iter())
    }

    fn iter_mut<'a>(&'a mut self) -> Box<Iterator<Item = &'a mut T> + 'a> {
        Box::new(self.iter_mut())
    }
}

impl<T> DrainRange<Range<usize>> for VecDeque<T> {
    fn drain_range<'a>(&'a mut self, range: Range<usize>) -> Box<Iterator<Item = T> + 'a> {
        Box::new(self.drain(range))
    }
}

#[test_impl]
impl<T> List for VecDeque<T> {
    fn get(&self, index: usize) -> Option<&T> {
        self.get(index)
    }

    fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        self.get_mut(index)
    }

    fn swap(&mut self, i: usize, j: usize) {
        self.swap(i, j);
    }

    fn reverse(&mut self) {
        let mut it = self.iter_mut();
        while let (Some(a), Some(b)) = (it.next(), it.next_back()) { mem::swap(a, b); }
    }

    fn push(&mut self, item: T) {
        self.push_back(item);
    }

    fn insert(&mut self, index: usize, item: T) {
        self.insert(index, item);
    }

    fn pop(&mut self) -> Option<T> {
        self.pop_back()
    }

    fn remove(&mut self, index: usize) -> Option<T> {
        self.remove(index)
    }

    fn swap_remove(&mut self, index: usize) -> Option<T> {
        self.swap_remove_back(index)
    }

    #[cfg(feature = "nightly")]
    fn truncate(&mut self, len: usize) {
        self.truncate(len);
    }

    fn split_off(&mut self, index: usize) -> Self {
        self.split_off(index)
    }
}

impl<T> Queue for VecDeque<T> {
    fn push(&mut self, item: T) {
        self.push_back(item);
    }

    fn front(&self) -> Option<&T> {
        self.front()
    }

    fn pop_front(&mut self) -> Option<T> {
        self.pop_front()
    }
}

impl<T> Deque for VecDeque<T> {
    fn back(&self) -> Option<&T> {
        self.back()
    }

    fn pop_back(&mut self) -> Option<T> {
        self.pop_back()
    }
}

#[test_impl]
impl<T> FifoQueue for VecDeque<T> {
    fn front_mut(&mut self) -> Option<&mut T> {
        self.front_mut()
    }
}

impl<T> FifoDeque for VecDeque<T> {
    fn push_front(&mut self, item: T) {
        self.push_front(item);
    }

    fn back_mut(&mut self) -> Option<&mut T> {
        self.back_mut()
    }
}

#[test]
fn test_binary_heap_push_pop_front() {
    let mut h = BinaryHeap::new();
    assert_eq!(h.push_pop_front(5), 5);
    assert!(h.is_empty());
    h.push(4);
    assert_eq!(h.push_pop_front(5), 5);
    assert!(h.iter().eq(&[4]));
    assert_eq!(h.push_pop_front(3), 4);
    assert!(h.iter().eq(&[3]));
}

#[test]
fn test_binary_heap_replace_front() {
    let mut h = BinaryHeap::new();
    assert_eq!(h.replace_front(5), None);
    assert!(h.iter().eq(&[5]));
    assert_eq!(h.replace_front(4), Some(5));
    assert!(h.iter().eq(&[4]));
    assert_eq!(h.replace_front(6), Some(4));
    assert!(h.iter().eq(&[6]));
}
