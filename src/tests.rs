use trait_tests::trait_tests;
use super::{AddRemove, PrioQueue, Collection};


#[trait_tests]
pub trait CollectionTests : Collection<Item=isize> + Sized + Default {
    fn test_new_length() {
        let me = Self::default();
        assert_eq!(me.len(), 0);
        assert!(me.capacity() >= me.len());
    }
}

//use std::cmp;
//use std::collections::binary_heap::{Drain, PeekMut};


//#[derive(Eq, PartialEq, Ord, Clone, Debug)]
//pub struct PanicOrd<T>(T, bool);

//use rand::{thread_rng, Rng};
//use std::panic::{self, AssertUnwindSafe};
//use std::sync::atomic::{AtomicUsize, ATOMIC_USIZE_INIT, Ordering};
//#[allow(dead_code)]
//#[trait_tests]
//trait PriorityQueuePanicTests :
//    PrioQueue<Item=PanicOrd<usize>> +
//    AddRemove + Sized + Clone +
//    ::std::iter::FromIterator<PanicOrd<usize>>
//{
//    fn panic_safe() {
//        static DROP_COUNTER: AtomicUsize = ATOMIC_USIZE_INIT;
//
//        impl<T> Drop for PanicOrd<T> {
//            fn drop(&mut self) {
//                // update global drop count
//                DROP_COUNTER.fetch_add(1, Ordering::SeqCst);
//            }
//        }
//
//        impl<T: PartialOrd> PartialOrd for PanicOrd<T> {
//            fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
//                if self.1 || other.1 {
//                    panic!("Panicking comparison");
//                }
//                self.0.partial_cmp(&other.0)
//            }
//        }
//        let mut rng = thread_rng();
//        const DATASZ: usize = 32;
//        const NTEST: usize = 10;
//
//        // don't use 0 in the data -- we want to catch the zeroed-out case.
//        let data = (1..DATASZ + 1).collect::<Vec<_>>();
//
//        // since it's a fuzzy test, run several tries.
//        for _ in 0..NTEST {
//            for i in 1..DATASZ + 1 {
//                DROP_COUNTER.store(0, Ordering::SeqCst);
//
//                let mut panic_ords: Vec<_> = data.iter()
//                    .filter(|&&x| x != i)
//                    .map(|&x| PanicOrd(x, false))
//                    .collect();
//                let panic_item = PanicOrd(i, true);
//
//                // heapify the sane items
//                rng.shuffle(&mut panic_ords);
//                let mut heap = Self::from(panic_ords);
//                let inner_data;
//
//                {
//                    // push the panicking item to the heap and catch the panic
//                    let thread_result = {
//                        let mut heap_ref = AssertUnwindSafe(&mut heap);
//                        panic::catch_unwind(move || {
//                            heap_ref.push(panic_item);
//                        })
//                    };
//                    assert!(thread_result.is_err());
//
//                    // Assert no elements were dropped
//                    let drops = DROP_COUNTER.load(Ordering::SeqCst);
//                    assert!(drops == 0, "Must not drop items. drops={}", drops);
//                    inner_data = heap.clone().into_vec();
//                    drop(heap);
//                }
//                let drops = DROP_COUNTER.load(Ordering::SeqCst);
//                assert_eq!(drops, DATASZ);
//
//                let mut data_sorted = inner_data.into_iter().map(|p| p.0).collect::<Vec<_>>();
//                data_sorted.sort();
//                assert_eq!(data_sorted, data);
//            }
//        }
//    }
//
//    fn from(vec: Vec<PanicOrd<usize>>) -> Self {
//        let pq: Self = vec.iter().cloned().collect();
//        pq
//    }
//}
use super::Queue;

#[trait_tests]
pub trait QueueTests : Queue<Item=isize>
    + AddRemove + Sized + Clone + Default
    + ::std::iter::FromIterator<isize>
{
    //helper
    fn from(vec: Vec<isize>) -> Self {
        let pq  : Self = vec.iter().cloned().collect();
        pq
    }

    fn pop(&mut self) -> Option<isize> {
        self.pop_front()
    }

    fn peek(&self) -> Option<&isize> {
        self.front()
    }

    fn into_sorted_vec(mut self) -> Vec<isize> {
        let mut results = vec![];
        while let Some(next) = self.pop_front() {
            results.push(next);
        }
        results.reverse();
        return results;
    }
    //helper


    fn test_iterator() {
        let data = vec![5, 9, 3];
        let iterout = [9, 5, 3];
        let heap = Self::from(data);
        let mut i = 0;
        for el in heap.iter() {
            assert_eq!(*el, iterout[i]);
            i += 1;
        }
    }

}


#[trait_tests]
pub trait PrioQueueTests : PrioQueue<Item=isize>
    + AddRemove + Sized + Clone + Default
    + ::std::iter::FromIterator<isize>
{
    fn from(vec: Vec<isize>) -> Self {
        let pq  : Self = vec.iter().cloned().collect();
        pq
    }

    fn pop(&mut self) -> Option<isize> {
        self.pop_front()
    }

    fn peek(&self) -> Option<&isize> {
        self.front()
    }

    fn into_sorted_vec(mut self) -> Vec<isize> {
        let mut results = vec![];
        while let Some(next) = self.pop_front() {
            results.push(next);
        }
        results.reverse();
        return results;
    }


    fn test_peek_and_pop() {
        let data = vec![2, 4, 6, 2, 1, 8, 10, 3, 5, 7, 0, 9, 1];
        let mut sorted = data.clone();
        sorted.sort();
        let mut heap = Self::from(data);
        while !heap.is_empty() {
            assert_eq!(heap.peek().unwrap(), sorted.last().unwrap());
            assert_eq!(heap.pop().unwrap(), sorted.pop().unwrap());
        }
    }

//    fn test_iterator_reverse() {
//        let data = vec![5, 9, 3];
//        let iterout = vec![3, 5, 9];
//        let pq = Self::from(data);
//
//        let v: Vec<_> = pq.iter().rev().cloned().collect();
//        assert_eq!(v, iterout);
//    }

//
//    fn test_move_iter() {
//        let data = vec![5, 9, 3];
//        let iterout = vec![9, 5, 3];
//        let pq = Self::from(data);
//
//        let v: Vec<_> = pq.into_iter().collect();
//        assert_eq!(v, iterout);
//    }

//
//    fn test_move_iter_size_hint() {
//        let data = vec![5, 9];
//        let pq = Self::from(data);
//
//        let mut it = pq.into_iter();
//
//        assert_eq!(it.size_hint(), (2, Some(2)));
//        assert_eq!(it.next(), Some(9));
//
//        assert_eq!(it.size_hint(), (1, Some(1)));
//        assert_eq!(it.next(), Some(5));
//
//        assert_eq!(it.size_hint(), (0, Some(0)));
//        assert_eq!(it.next(), None);
//    }


//    fn test_move_iter_reverse() {
//        let data = vec![5, 9, 3];
//        let iterout = vec![3, 5, 9];
//        let pq = Self::from(data);
//
//        let v: Vec<_> = pq.into_iter().rev().collect();
//        assert_eq!(v, iterout);
//    }



//    fn test_peek_mut() {
//        let data = vec![2, 4, 6, 2, 1, 8, 10, 3, 5, 7, 0, 9, 1];
//        let mut heap = Self::from(data);
//        assert_eq!(heap.peek(), Some(&10));
//        {
//            let mut top = heap.peek_mut().unwrap();
//            *top -= 2;
//        }
//        assert_eq!(heap.peek(), Some(&9));
//    }
//
//
//    fn test_peek_mut_pop() {
//        let data = vec![2, 4, 6, 2, 1, 8, 10, 3, 5, 7, 0, 9, 1];
//        let mut heap = Self::from(data);
//        assert_eq!(heap.peek(), Some(&10));
//        {
//            let mut top = heap.peek_mut().unwrap();
//            *top -= 2;
//            assert_eq!(PeekMut::pop(top), 8);
//        }
//        assert_eq!(heap.peek(), Some(&9));
//    }


    fn test_push() {
        let mut heap = Self::from(vec![2, 4, 9]);
        assert_eq!(heap.len(), 3);
        assert!(*heap.peek().unwrap() == 9);
        heap.push(11);
        assert_eq!(heap.len(), 4);
        assert!(*heap.peek().unwrap() == 11);
        heap.push(5);
        assert_eq!(heap.len(), 5);
        assert!(*heap.peek().unwrap() == 11);
        heap.push(27);
        assert_eq!(heap.len(), 6);
        assert!(*heap.peek().unwrap() == 27);
        heap.push(3);
        assert_eq!(heap.len(), 7);
        assert!(*heap.peek().unwrap() == 27);
        heap.push(103);
        assert_eq!(heap.len(), 8);
        assert!(*heap.peek().unwrap() == 103);
    }

//
//    fn test_push_unique() {
//        let mut heap = Self::<Box<_>>::from(vec![box 2, box 4, box 9]);
//        assert_eq!(heap.len(), 3);
//        assert!(**heap.peek().unwrap() == 9);
//        heap.push(box 11);
//        assert_eq!(heap.len(), 4);
//        assert!(**heap.peek().unwrap() == 11);
//        heap.push(box 5);
//        assert_eq!(heap.len(), 5);
//        assert!(**heap.peek().unwrap() == 11);
//        heap.push(box 27);
//        assert_eq!(heap.len(), 6);
//        assert!(**heap.peek().unwrap() == 27);
//        heap.push(box 3);
//        assert_eq!(heap.len(), 7);
//        assert!(**heap.peek().unwrap() == 27);
//        heap.push(box 103);
//        assert_eq!(heap.len(), 8);
//        assert!(**heap.peek().unwrap() == 103);
//    }

    fn check_to_vec(mut data: Vec<isize>) {
        let heap = Self::from(data.clone());
        let mut v = heap.clone().into_vec();
        v.sort();
        data.sort();

        assert_eq!(v, data);
        assert_eq!(heap.into_sorted_vec(), data);
    }


    fn test_to_vec() {
        Self::check_to_vec(vec![]);
        Self::check_to_vec(vec![5]);
        Self::check_to_vec(vec![3, 2]);
        Self::check_to_vec(vec![2, 3]);
        Self::check_to_vec(vec![5, 1, 2]);
        Self::check_to_vec(vec![1, 100, 2, 3]);
        Self::check_to_vec(vec![1, 3, 5, 7, 9, 2, 4, 6, 8, 0]);
        Self::check_to_vec(vec![2, 4, 6, 2, 1, 8, 10, 3, 5, 7, 0, 9, 1]);
        Self::check_to_vec(vec![9, 11, 9, 9, 9, 9, 11, 2, 3, 4, 11, 9, 0, 0, 0, 0]);
        Self::check_to_vec(vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
        Self::check_to_vec(vec![10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]);
        Self::check_to_vec(vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 0, 0, 1, 2]);
        Self::check_to_vec(vec![5, 4, 3, 2, 1, 5, 4, 3, 2, 1, 5, 4, 3, 2, 1]);
    }


    fn test_empty_pop() {
        let mut heap = Self::default();
        assert!(heap.pop().is_none());
    }


    fn test_empty_peek() {
        let empty = Self::default();
        assert!(empty.peek().is_none());
    }


//    fn test_empty_peek_mut() {
//        let mut empty = Self::new();
//        assert!(empty.peek_mut().is_none());
//    }


    fn test_from_iter() {
        let xs = vec![9, 8, 7, 6, 5, 4, 3, 2, 1];

        let mut q: Self = xs.iter().rev().cloned().collect();

        for &x in &xs {
            assert_eq!(q.pop().unwrap(), x);
        }
    }


    fn test_drain() {
        let mut q: Self = [9, 8, 7, 6, 5, 4, 3, 2, 1].iter().cloned().collect();

        assert_eq!(q.drain().take(5).count(), 5);

        assert!(q.is_empty());
    }


//    fn test_extend_ref() {
//        let mut a = Self::new();
//        a.push(1);
//        a.push(2);
//
//        a.extend(&[3, 4, 5]);
//
//        assert_eq!(a.len(), 5);
//        assert_eq!(a.into_sorted_vec(), [1, 2, 3, 4, 5]);
//
//        let mut a = Self::new();
//        a.push(1);
//        a.push(2);
//        let mut b = Self::new();
//        b.push(3);
//        b.push(4);
//        b.push(5);
//
//        a.extend(&b);
//
//        assert_eq!(a.len(), 5);
//        assert_eq!(a.into_sorted_vec(), [1, 2, 3, 4, 5]);
//    }


    fn test_append() {
        let mut a = Self::from(vec![-10, 1, 2, 3, 3]);
        let mut b = Self::from(vec![-20, 5, 43]);

        a.append(&mut b);

        assert_eq!(a.into_sorted_vec(), [-20, -10, 1, 2, 3, 3, 5, 43]);
        assert!(b.is_empty());
    }


    fn test_append_to_empty() {
        let mut a = Self::default();
        let mut b = Self::from(vec![-20, 5, 43]);

        a.append(&mut b);

        assert_eq!(a.into_sorted_vec(), [-20, 5, 43]);
        assert!(b.is_empty());
    }


//    fn test_extend_specialization() {
//        let mut a = Self::from(vec![-10, 1, 2, 3, 3]);
//        let b = Self::from(vec![-20, 5, 43]);
//
//        a.extend(b);
//
//        assert_eq!(a.into_sorted_vec(), [-20, -10, 1, 2, 3, 3, 5, 43]);
//    }


//    fn test_placement() {
//        let mut a = Self::new();
//        &mut a <- 2;
//        &mut a <- 4;
//        &mut a <- 3;
//        assert_eq!(a.peek(), Some(&4));
//        assert_eq!(a.len(), 3);
//        &mut a <- 1;
//        assert_eq!(a.into_sorted_vec(), vec![1, 2, 3, 4]);
//    }
//
//
//    fn test_placement_panic() {
//        let mut heap = Self::from(vec![1, 2, 3]);
//        fn mkpanic() -> usize { panic!() }
//        let _ = panic::catch_unwind(panic::AssertUnwindSafe(|| { &mut heap <- mkpanic(); }));
//        assert_eq!(heap.len(), 3);
//    }

//    #[allow(dead_code)]
//    fn assert_covariance() {
//        fn drain<'new>(d: Drain<'static, &'static str>) -> Drain<'new, &'new str> {
//            d
//        }
//    }

// old Self failed this test
//
// Integrity means that all elements are present after a comparison panics,
// even if the order may not be correct.
//
// Destructors must be called exactly once per element.



}

//Can't use #[trait_tests] here as we don't define BinaryHeap struct in this crate.
//impl PriorityQueueTests for BinaryHeap<isize> {}
//#[test] fn test_binary_heap_isize() { <BinaryHeap<isize> as PriorityQueueTests>::test_all() }

//TODO: panic tests seem to panic...
//#[trait_tests]
//impl PriorityQueuePanicTests for BinaryHeap<::stdx::collections::tests::queue_tests::PanicOrd<usize>> { }









//
// Set tests:
//

use std::fmt::Debug;
use std::hash as hash;
//use stdx::collections::tests::CollectionTests;

use super::{Set};

#[derive(Debug)]
pub struct Foo(&'static str, i32);

impl PartialEq for Foo {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl PartialOrd for Foo {
    fn partial_cmp(&self, other: &Foo) -> Option<::std::cmp::Ordering> {
        self.0.partial_cmp(other.0)
    }
}

impl Ord for Foo {
    fn cmp(&self, other: &Self) -> ::std::cmp::Ordering {
        self.0.cmp(other.0)
    }
}

impl Eq for Foo {}

impl hash::Hash for Foo {
    fn hash<H: hash::Hasher>(&self, h: &mut H) {
        self.0.hash(h);
    }
}

//TODO no drain or retain on BTreeSet. Leave out those tests for now.

#[trait_tests]
pub trait SetTests: Set<isize, Item=isize>
//+ FromIterator<isize>
+ IntoIterator<Item=isize>
+ Debug
+ Eq
+ Sized
+ AddRemove
+ Default
{
    fn test_disjoint()
    {
        let mut xs = Self::default();
        let mut ys = Self::default();

        assert!(xs.is_disjoint(&ys));
        assert!(ys.is_disjoint(&xs));
        assert!(xs.insert(5isize));
        assert!(ys.insert(11));
        assert!(xs.is_disjoint(&ys));
        assert!(ys.is_disjoint(&xs));
        assert!(xs.insert(7));
        assert!(xs.insert(19));
        assert!(xs.insert(4));
        assert!(ys.insert(2));
        assert!(ys.insert(-11));
        assert!(xs.is_disjoint(&ys));
        assert!(ys.is_disjoint(&xs));
        assert!(ys.insert(7));
        assert!(!xs.is_disjoint(&ys));
        assert!(!ys.is_disjoint(&xs));
    }

    fn test_subset_and_superset()
    {
        let mut a = Self::default();
        assert!(a.insert(0));
        assert!(a.insert(5));
        assert!(a.insert(11));
        assert!(a.insert(7));

        let mut b = Self::default();
        assert!(b.insert(0));
        assert!(b.insert(7));
        assert!(b.insert(19));
        assert!(b.insert(250));
        assert!(b.insert(11));
        assert!(b.insert(200));

        assert!(!a.is_subset(&b));
        assert!(!a.is_superset(&b));
        assert!(!b.is_subset(&a));
        assert!(!b.is_superset(&a));

        assert!(b.insert(5));

        assert!(a.is_subset(&b));
        assert!(!a.is_superset(&b));
        assert!(!b.is_subset(&a));
        assert!(b.is_superset(&a));
    }

    fn test_iterate()
    {
        let mut a = Self::default();
        for i in 0..32 {
            assert!(a.insert(i));
        }
        let mut observed: u32 = 0;
        for k in a.iter() {
            observed |= 1 << *k as u32;
        }
        assert_eq!(observed, 0xFFFF_FFFF);
    }

//    fn test_intersection()
//    {
//        let mut a = Self::default();
//        let mut b = Self::default();
//
//        assert!(a.insert(11));
//        assert!(a.insert(1));
//        assert!(a.insert(3));
//        assert!(a.insert(77));
//        assert!(a.insert(103));
//        assert!(a.insert(5));
//        assert!(a.insert(-5));
//
//        assert!(b.insert(2));
//        assert!(b.insert(11));
//        assert!(b.insert(77));
//        assert!(b.insert(-9));
//        assert!(b.insert(-42));
//        assert!(b.insert(5));
//        assert!(b.insert(3));
//
//        let mut i = 0;
//        let expected = [3, 5, 11, 77];
//        for x in a.intersection(&b) {
//            assert!(expected.contains(&x));
//            i += 1
//        }
//        assert_eq!(i, expected.len());
//    }

//    fn test_difference()
//    {
//        let mut a = Self::new();
//        let mut b = Self::new();
//
//        assert!(a.insert(1));
//        assert!(a.insert(3));
//        assert!(a.insert(5));
//        assert!(a.insert(9));
//        assert!(a.insert(11));
//
//        assert!(b.insert(3));
//        assert!(b.insert(9));
//
//        let mut i = 0;
//        let expected = [1, 5, 11];
//        for x in a.difference(&b) {
//            assert!(expected.contains(x));
//            i += 1
//        }
//        assert_eq!(i, expected.len());
//    }

//    fn test_symmetric_difference()
//    {
//        let mut a = Self::new();
//        let mut b = Self::new();
//
//        assert!(a.insert(1));
//        assert!(a.insert(3));
//        assert!(a.insert(5));
//        assert!(a.insert(9));
//        assert!(a.insert(11));
//
//        assert!(b.insert(-2));
//        assert!(b.insert(3));
//        assert!(b.insert(9));
//        assert!(b.insert(14));
//        assert!(b.insert(22));
//
//        let mut i = 0;
//        let expected = [-2, 1, 5, 11, 14, 22];
//        for x in a.symmetric_difference(&b) {
//            assert!(expected.contains(x));
//            i += 1
//        }
//        assert_eq!(i, expected.len());
//    }
//
//    fn test_union()
//    {
//        let mut a = Self::new();
//        let mut b = Self::new();
//
//        assert!(a.insert(1));
//        assert!(a.insert(3));
//        assert!(a.insert(5));
//        assert!(a.insert(9));
//        assert!(a.insert(11));
//        assert!(a.insert(16));
//        assert!(a.insert(19));
//        assert!(a.insert(24));
//
//        assert!(b.insert(-2));
//        assert!(b.insert(1));
//        assert!(b.insert(5));
//        assert!(b.insert(9));
//        assert!(b.insert(13));
//        assert!(b.insert(19));
//
//        let mut i = 0;
//        let expected = [-2, 1, 3, 5, 9, 11, 13, 16, 19, 24];
//        for x in a.union(&b) {
//            assert!(expected.contains(x));
//            i += 1
//        }
//        assert_eq!(i, expected.len());
//    }

//    fn test_from_iter()
//    {
//        let xs = [1, 2, 3, 4, 5, 6, 7, 8, 9];
//
//        let set: Self = xs.iter().cloned().collect();
//
//        for x in &xs {
//            assert!(set.contains(x));
//        }
//    }

    fn test_eq()
    {
        // These constants once happened to expose a bug in insert().
        // I'm keeping them around to prevent a regression.
        let mut s1 = Self::default();

        s1.insert(1);
        s1.insert(2);
        s1.insert(3);

        let mut s2 = Self::default();

        s2.insert(1);
        s2.insert(2);

        assert!(s1 != s2);

        s2.insert(3);

        assert_eq!(s1, s2);
    }

    fn test_show()
    {
        let mut set = Self::default();
        let empty = Self::default();

        set.insert(1);
        set.insert(2);

        let set_str = format!("{:?}", set);

        assert!(set_str == "{1, 2}" || set_str == "{2, 1}");
        assert_eq!(format!("{:?}", empty), "{}");
    }

//    fn test_extend_ref()
//    {
//        let mut a = Self::new();
//        a.insert(1);
//
//        a.extend(vec![2isize, 3, 4]); //TODO should be &[2,3,4]
//
//        assert_eq!(a.len(), 4);
//        assert!(a.contains(&1));
//        assert!(a.contains(&2));
//        assert!(a.contains(&3));
//        assert!(a.contains(&4));
//
//        let mut b = Self::new();
//        b.insert(5);
//        b.insert(6);
//
//        a.extend(b);
//
//        assert_eq!(a.len(), 6);
//        assert!(a.contains(&1));
//        assert!(a.contains(&2));
//        assert!(a.contains(&3));
//        assert!(a.contains(&4));
//        assert!(a.contains(&5));
//        assert!(a.contains(&6));
//    }

    fn test_move_iter()
    {
        let hs = {
            let mut hs = Self::default();

            hs.insert(1);
            hs.insert(2);

            hs
        };

        let v = hs.into_iter().collect::<Vec<isize>>();
        assert!(v == [1, 2] || v == [2, 1]);
    }
}

//type SetTests2Type1=Foo;

//#[trait_tests]
//pub trait SetTests2: Set<Item=Foo> + Sized + IntoIterator<Item=Foo> + AddRemove + Default
//{
//    fn test_replace()
//    {
//        let mut s = Self::default();
//        assert_eq!(s.replace(Foo("a", 1)), None);
//        assert_eq!(s.len(), 1);
//        assert_eq!(s.replace(Foo("a", 2)), Some(Foo("a", 1)));
//        assert_eq!(s.len(), 1);
//
//        let mut it = s.iter();
//        assert_eq!(it.next(), Some(&Foo("a", 2)));
//        assert_eq!(it.next(), None);
//    }
//}

//#[trait_tests]
//pub trait SetTestschar: Set<Item=char> + Sized + IntoIterator<Item=char> + AddRemove + Default
//{
//    //#[test]
//    fn test_move_iter()
//    {
//        let hs = {
//            let mut hs = Self::default();
//
//            hs.insert('a');
//            hs.insert('b');
//
//            hs
//        };
//
//        let v = hs.into_iter().collect::<Vec<char>>();
//        assert!(v == ['a', 'b'] || v == ['b', 'a']);
//    }
//}



//
// List tests
//
use super::{List, Mutate};

use proptest::prelude::*;
use proptest::test_runner::{TestRunner, FailurePersistence, Config};

//pub struct DropCounter<'a> {
//    count: &'a mut u32,
//}
//
//impl<'a> Drop for DropCounter<'a> {
//    fn drop(&mut self) {
//        *self.count += 1;
//    }
//}
//
////TODO TwoVec<'b, T> unused type parameter.
//#[trait_tests]
//pub trait ListTests<'a>: List<DropCounter<'a>> + Sized {
//    fn test_double_drop() {
//        struct TwoVec<'b, T>
//            where T: ListTests<'b>
//        {
//            x: T,
//            y: T,
//           // z: ::std::marker::PhantomData<T>
//        }
//
//        let (mut count_x, mut count_y) = (0, 0);
//        {
//            let mut tv = TwoVec {
//                x: Self::new(),
//                y: Self::new(),
//            };
//            tv.x.push(DropCounter { count: &mut count_x });
//            tv.y.push(DropCounter { count: &mut count_y });
//
//            // If Vec had a drop flag, here is where it would be zeroed.
//            // Instead, it should rely on its internal state to prevent
//            // doing anything significant when dropped multiple times.
//            drop(tv.x);
//
//            // Here tv goes out of scope, tv.y should be dropped, but not tv.x.
//        }
//
//        assert_eq!(count_x, 1);
//        assert_eq!(count_y, 1);
//    }

//#[trait_tests]
//pub trait ListTestsBoxed: List<Item=Box<isize>>
//    + PartialEq
//    + AddRemove + Mutate
//    + Debug + Sized + Default
//{
//    //TODO test_all could return a vec of test functions...
//    //fn test_all() { Self::test_basic() }
//
//    fn pop_back(&mut self) -> Option<Box<isize>> {
//        self.pop()
//    }
//
//    fn pop_front(&mut self) -> Option<Box<isize>> {
//        self.remove(0)
//    }
//    fn push_back(&mut self, item: Box<isize>) {
//        self.push(item);
//    }
//
//    fn push_front(&mut self, item: Box<isize>) {
//        self.insert(0, item)
//    }
//
//    fn test_basic() {
//        //Other half of test_basic isize test.
//        let mut m = Self::default();
//        assert_eq!(m.pop_front(), None);
//        assert_eq!(m.pop_back(), None);
//        assert_eq!(m.pop_front(), None);
//        m.push_front(box 1);
//        assert_eq!(m.pop_front(), Some(box 1));
//        m.push_back(box 2);
//        m.push_back(box 3);
//        assert_eq!(m.len(), 2);
//        assert_eq!(m.pop_front(), Some(box 2));
//        assert_eq!(m.pop_front(), Some(box 3));
//        assert_eq!(m.len(), 0);
//        assert_eq!(m.pop_front(), None);
//        m.push_back(box 1);
//        m.push_back(box 3);
//        m.push_back(box 5);
//        m.push_back(box 7);
//        assert_eq!(m.pop_front(), Some(box 1));
//    }
//}

#[trait_tests]
pub trait ListTests: List<Item=isize>
    + PartialEq
    + Debug
    + Sized
    + AddRemove
    + Mutate
    + Default
    + ::std::iter::FromIterator<isize>
  //  + Index<usize, Output=isize> - not supported by linked list.
{
    fn pop_back(&mut self) -> Option<isize> {
        self.pop()
    }

    fn pop_front(&mut self) -> Option<isize> {
        self.remove(0)
    }

    fn push_back(&mut self, item: isize) {
        self.push(item);
    }

    fn push_front(&mut self, item: isize) {
        self.insert(0, item);
    }

    fn front(&self) -> Option<&isize> {
        self.first()
    }
    fn back(&self) -> Option<&isize> {
        self.last()
    }
    fn front_mut(&mut self) -> Option<&mut isize> {
        self.first_mut()
    }
    fn back_mut(&mut self) -> Option<&mut isize> {
        self.last_mut()
    }
//    fn test_retain() {
//        //TODO WAS let mut vec = vec![1, 2, 3, 4];
//        let vec = &mut Self::new();
//        vec.push(1);
//        vec.push(2);
//        vec.push(3);
//        vec.push(4);
//
//        vec.retain(|&x| x % 2 == 0);
//
//        //TODO assert_eq!(vec, [2, 4]);
//
//        let res = vec.into_iter();
//        assert_eq!(res.next(), Some(2));
//        assert_eq!(res.next(), Some(4));
//        assert_eq!(res.next(), None);
//    }

    fn zero_sized_values() {
        let mut v = Self::default();
        assert_eq!(v.len(), 0);
        v.push(1);
        assert_eq!(v.len(), 1);
        v.push(1);
        assert_eq!(v.len(), 2);
        assert_eq!(v.pop(), Some(1));
        assert_eq!(v.pop(), Some(1));
        assert_eq!(v.pop(), None);

        assert_eq!(v.iter().count(), 0);
        v.push(1);
        assert_eq!(v.iter().count(), 1);
        v.push(1);
        assert_eq!(v.iter().count(), 2);

        for &_ in v.iter() {}

        assert_eq!(v.iter_mut().count(), 2);
        v.push(1);
        assert_eq!(v.iter_mut().count(), 3);
        v.push(1);
        assert_eq!(v.iter_mut().count(), 4);

        for &mut _ in &mut v.iter_mut() {}
        v.truncate(0);
        assert_eq!(v.iter_mut().count(), 0);
    }

    fn test_basic() {
        let mut n = Self::default();
        n.push_front(2);
        n.push_front(3);
        {
            assert_eq!(n.front().unwrap(), &3);
            let x = n.front_mut().unwrap();
            assert_eq!(*x, 3);
            *x = 0;
        }
        {
            assert_eq!(n.back().unwrap(), &2);
            let y = n.back_mut().unwrap();
            assert_eq!(*y, 2);
            *y = 1;
        }
        assert_eq!(n.pop_front(), Some(0));
        assert_eq!(n.pop_front(), Some(1));
    }


    //From liballoc/tests/linked_list.rs:
    fn list_from(v: &[isize]) -> Self {
        v.iter().cloned().collect()
    }

    fn generate_test() -> Self {
        Self::list_from(&[0, 1, 2, 3, 4, 5, 6])
    }

    fn test_split_off() {
        // singleton
        {
            let mut m = Self::default();
            m.push_back(1);

            let p = m.split_off(0);
            assert_eq!(m.len(), 0);
            assert_eq!(p.len(), 1);
            assert_eq!(p.back(), Some(&1));
            assert_eq!(p.front(), Some(&1));
        }

        // not singleton, forwards
        {
            let u = vec![1, 2, 3, 4, 5];
            let mut m = Self::list_from(&u);
            let mut n = m.split_off(2);
            assert_eq!(m.len(), 2);
            assert_eq!(n.len(), 3);
            for elt in 1..3 {
                assert_eq!(m.pop_front(), Some(elt));
            }
            for elt in 3..6 {
                assert_eq!(n.pop_front(), Some(elt));
            }
        }
        // not singleton, backwards
        {
            let u = vec![1, 2, 3, 4, 5];
            let mut m = Self::list_from(&u);
            let mut n = m.split_off(4);
            assert_eq!(m.len(), 4);
            assert_eq!(n.len(), 1);
            for elt in 1..5 {
                assert_eq!(m.pop_front(), Some(elt));
            }
            for elt in 5..6 {
                assert_eq!(n.pop_front(), Some(elt));
            }
        }

        // no-op on the last index
        {
            let mut m = Self::default();
            m.push_back(1);

            let p = m.split_off(1);
            assert_eq!(m.len(), 1);
            assert_eq!(p.len(), 0);
            assert_eq!(m.back(), Some(&1));
            assert_eq!(m.front(), Some(&1));
        }

    }

    fn test_iterator() {
        let m = Self::generate_test();
        for (i, elt) in m.iter().enumerate() {
            assert_eq!(i as isize, *elt);
        }
        let mut n = Self::default();
        assert_eq!(n.iter().next(), None);
        n.push_front(4);
        let mut it = n.iter();
        assert_eq!(it.size_hint(), (1, Some(1)));
        assert_eq!(it.next().unwrap(), &4);
        assert_eq!(it.size_hint(), (0, Some(0)));
        assert_eq!(it.next(), None);
    }

//    fn test_iterator_clone() {
//        let mut n = Self::new();
//        n.push_back(2);
//        n.push_back(3);
//        n.push_back(4);
//        let mut it = n.iter();
//        it.next();
//        let mut jt = it.clone();
//        assert_eq!(it.next(), jt.next());
//        assert_eq!(it.next_back(), jt.next_back());
//        assert_eq!(it.next(), jt.next());
//    }
//
//    fn test_iterator_double_end() {
//        let mut n = Self::new();
//        assert_eq!(n.iter().next(), None);
//        n.push_front(4);
//        n.push_front(5);
//        n.push_front(6);
//        let mut it = n.iter();
//        assert_eq!(it.size_hint(), (3, Some(3)));
//        assert_eq!(it.next().unwrap(), &6);
//        assert_eq!(it.size_hint(), (2, Some(2)));
//        assert_eq!(it.next_back().unwrap(), &4);
//        assert_eq!(it.size_hint(), (1, Some(1)));
//        assert_eq!(it.next_back().unwrap(), &5);
//        assert_eq!(it.next_back(), None);
//        assert_eq!(it.next(), None);
//    }
//
//    fn test_rev_iter() {
//        let m = Self::generate_test();
//        for (i, elt) in m.iter().rev().enumerate() {
//            assert_eq!((6 - i) as isize, *elt);
//        }
//        let mut n = Self::new();
//        assert_eq!(n.iter().rev().next(), None);
//        n.push_front(4);
//        let mut it = n.iter().rev();
//        assert_eq!(it.size_hint(), (1, Some(1)));
//        assert_eq!(it.next().unwrap(), &4);
//        assert_eq!(it.size_hint(), (0, Some(0)));
//        assert_eq!(it.next(), None);
//    }
//
    fn test_mut_iter() {
        let mut m = Self::generate_test();
        let mut len = m.len();
        for (i, elt) in m.iter_mut().enumerate() {
            assert_eq!(i as isize, *elt);
            len -= 1;
        }
        assert_eq!(len, 0);
        let mut n = Self::default();
        assert!(n.iter_mut().next().is_none());
        n.push_front(4);
        n.push_back(5);
        let mut it = n.iter_mut();
        assert_eq!(it.size_hint(), (2, Some(2)));
        assert!(it.next().is_some());
        assert!(it.next().is_some());
        assert_eq!(it.size_hint(), (0, Some(0)));
        assert!(it.next().is_none());
    }
//
//    fn test_iterator_mut_double_end() {
//        let mut n = Self::new();
//        assert!(n.iter_mut().next_back().is_none());
//        n.push_front(4);
//        n.push_front(5);
//        n.push_front(6);
//        let mut it = n.iter_mut();
//        assert_eq!(it.size_hint(), (3, Some(3)));
//        assert_eq!(*it.next().unwrap(), 6);
//        assert_eq!(it.size_hint(), (2, Some(2)));
//        assert_eq!(*it.next_back().unwrap(), 4);
//        assert_eq!(it.size_hint(), (1, Some(1)));
//        assert_eq!(*it.next_back().unwrap(), 5);
//        assert!(it.next_back().is_none());
//        assert!(it.next().is_none());
//    }
//
//    fn test_mut_rev_iter() {
//        let mut m = Self::generate_test();
//        for (i, elt) in m.iter_mut().rev().enumerate() {
//            assert_eq!((6 - i) as isize, *elt);
//        }
//        let mut n = Self::new();
//        assert!(n.iter_mut().rev().next().is_none());
//        n.push_front(4);
//        let mut it = n.iter_mut().rev();
//        assert!(it.next().is_some());
//        assert!(it.next().is_none());
//    }
//
    fn test_eq() {
        let mut n = Self::list_from(&[]);
        let mut m = Self::list_from(&[]);
        assert!(n == m);
        n.push_front(1);
        assert!(n != m);
        m.push_back(1);
        assert!(n == m);

        let n = Self::list_from(&[3, 2, 1]);
        let m = Self::list_from(&[1, 2, 3]);
        assert_ne!(n, m);
    }
//
//    //TODO maybe move to one with hash constraint
////    fn test_hash() {
////        let mut x = Self::new();
////        let mut y = Self::new();
////
////        assert!(::hash(&x) == ::hash(&y));
////
////        x.push_back(1);
////        x.push_back(2);
////        x.push_back(3);
////
////        y.push_front(3);
////        y.push_front(2);
////        y.push_front(1);
////
////        assert!(::hash(&x) == ::hash(&y));
////    }
//
//    fn test_ord() {
//        let n = Self::list_from(&[]);
//        let m = Self::list_from(&[1, 2, 3]);
//        assert!(n < m);
//        assert!(m > n);
//        assert!(n <= n);
//        assert!(n >= n);
//    }
//
//    fn test_ord_nan() {
//        let nan = 0.0f64 / 0.0;
//        let n = Self::list_from(&[nan]);
//        let m = Self::list_from(&[nan]);
//        assert!(!(n < m));
//        assert!(!(n > m));
//        assert!(!(n <= m));
//        assert!(!(n >= m));
//
//        let n = Self::list_from(&[nan]);
//        let one = Self::list_from(&[1.0f64]);
//        assert!(!(n < one));
//        assert!(!(n > one));
//        assert!(!(n <= one));
//        assert!(!(n >= one));
//
//        let u = Self::list_from(&[1.0f64, 2.0, nan]);
//        let v = Self::list_from(&[1.0f64, 2.0, 3.0]);
//        assert!(!(u < v));
//        assert!(!(u > v));
//        assert!(!(u <= v));
//        assert!(!(u >= v));
//
//        let s = Self::list_from(&[1.0f64, 2.0, 4.0, 2.0]);
//        let t = Self::list_from(&[1.0f64, 2.0, 3.0, 2.0]);
//        assert!(!(s < t));
//        assert!(s > one);
//        assert!(!(s <= one));
//        assert!(s >= one);
//    }
//
//    fn test_show() {
//        let list: Self = (0..10).collect();
//        assert_eq!(format!("{:?}", list), "[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]");
//
//        let list: Self = vec!["just", "one", "test", "more"].iter().cloned().collect();
//        assert_eq!(format!("{:?}", list),
//                   "[\"just\", \"one\", \"test\", \"more\"]");
//    }
//
//    fn test_extend_ref() {
//        let mut a = Self::new();
//        a.push_back(1);
//
//        a.extend_objects(&[2, 3, 4]);
//
//        assert_eq!(a.len(), 4);
//        assert_eq!(a, Self::list_from(&[1, 2, 3, 4]));
//
//        let mut b = Self::new();
//        b.push_back(5);
//        b.push_back(6);
//        a.extend_objects(&b);
//
//        assert_eq!(a.len(), 6);
//        assert_eq!(a, Self::list_from(&[1, 2, 3, 4, 5, 6]));
//    }

//    fn test_extend() {
//        let mut a = Self::new();
//        a.push_back(1);
//        a.extend_object(vec![2, 3, 4]); // uses iterator
//
//        assert_eq!(a.len(), 4);
//        assert!(a.iter().eq(&[1, 2, 3, 4]));
//
//        let b: Self = vec![5, 6, 7].into_iter().collect();
//        a.extend_object(b); // specializes to `append`
//
//        assert_eq!(a.len(), 7);
//        assert!(a.iter().eq(&[1, 2, 3, 4, 5, 6, 7]));
//    }

//    fn test_contains() {
//        let mut l = Self::new();
//        l.extend_object(&[2usize, 3, 4]);
//
//        assert!(l.contains(&3));
//        assert!(!l.contains(&1));
//
//        l.clear();
//
//        assert!(!l.contains(&3));
//    }
//
//    fn drain_filter_empty() {
//        let mut list: Self = Self::new();
//
//        {
//            let mut iter = list.drain_filter(|_| true);
//            assert_eq!(iter.size_hint(), (0, Some(0)));
//            assert_eq!(iter.next(), None);
//            assert_eq!(iter.size_hint(), (0, Some(0)));
//            assert_eq!(iter.next(), None);
//            assert_eq!(iter.size_hint(), (0, Some(0)));
//        }
//
//        assert_eq!(list.len(), 0);
//        assert_eq!(list.into_iter().collect::<Vec<_>>(), vec![]);
//    }
//
//    fn drain_filter_zst() {
//        let mut list: Self = vec![(), (), (), (), ()].into_iter().collect();
//        let initial_len = list.len();
//        let mut count = 0;
//
//        {
//            let mut iter = list.drain_filter(|_| true);
//            assert_eq!(iter.size_hint(), (0, Some(initial_len)));
//            while let Some(_) = iter.next() {
//                count += 1;
//                assert_eq!(iter.size_hint(), (0, Some(initial_len - count)));
//            }
//            assert_eq!(iter.size_hint(), (0, Some(0)));
//            assert_eq!(iter.next(), None);
//            assert_eq!(iter.size_hint(), (0, Some(0)));
//        }
//
//        assert_eq!(count, initial_len);
//        assert_eq!(list.len(), 0);
//        assert_eq!(list.into_iter().collect::<Vec<_>>(), vec![]);
//    }
//
//    fn drain_filter_false() {
//        let mut list: Self = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10].into_iter().collect();
//
//        let initial_len = list.len();
//        let mut count = 0;
//
//        {
//            let mut iter = list.drain_filter(|_| false);
//            assert_eq!(iter.size_hint(), (0, Some(initial_len)));
//            for _ in iter.by_ref() {
//                count += 1;
//            }
//            assert_eq!(iter.size_hint(), (0, Some(0)));
//            assert_eq!(iter.next(), None);
//            assert_eq!(iter.size_hint(), (0, Some(0)));
//        }
//
//        assert_eq!(count, 0);
//        assert_eq!(list.len(), initial_len);
//        assert_eq!(list.into_iter().collect::<Vec<_>>(), vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
//    }
//
//    fn drain_filter_true() {
//        let mut list: Self = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10].into_iter().collect();
//
//        let initial_len = list.len();
//        let mut count = 0;
//
//        {
//            let mut iter = list.drain_filter(|_| true);
//            assert_eq!(iter.size_hint(), (0, Some(initial_len)));
//            while let Some(_) = iter.next() {
//                count += 1;
//                assert_eq!(iter.size_hint(), (0, Some(initial_len - count)));
//            }
//            assert_eq!(iter.size_hint(), (0, Some(0)));
//            assert_eq!(iter.next(), None);
//            assert_eq!(iter.size_hint(), (0, Some(0)));
//        }
//
//        assert_eq!(count, initial_len);
//        assert_eq!(list.len(), 0);
//        assert_eq!(list.into_iter().collect::<Vec<_>>(), vec![]);
//    }
//
//    fn drain_filter_complex() {
//
//        {   //                [+xxx++++++xxxxx++++x+x++]
//            let mut list = vec![
//                1,
//                2, 4, 6,
//                7, 9, 11, 13, 15, 17,
//                18, 20, 22, 24, 26,
//                27, 29, 31, 33,
//                34,
//                35,
//                36,
//                37, 39
//            ].into_iter().collect::<Self>();
//
//            let removed = list.drain_filter(|x| *x % 2 == 0).collect::<Vec<_>>();
//            assert_eq!(removed.len(), 10);
//            assert_eq!(removed, vec![2, 4, 6, 18, 20, 22, 24, 26, 34, 36]);
//
//            assert_eq!(list.len(), 14);
//            assert_eq!(
//                list.into_iter().collect::<Vec<_>>(),
//                vec![1, 7, 9, 11, 13, 15, 17, 27, 29, 31, 33, 35, 37, 39]
//            );
//        }
//
//        {   // [xxx++++++xxxxx++++x+x++]
//            let mut list = vec![
//                2, 4, 6,
//                7, 9, 11, 13, 15, 17,
//                18, 20, 22, 24, 26,
//                27, 29, 31, 33,
//                34,
//                35,
//                36,
//                37, 39
//            ].into_iter().collect::<Self>();
//
//            let removed = list.drain_filter(|x| *x % 2 == 0).collect::<Vec<_>>();
//            assert_eq!(removed.len(), 10);
//            assert_eq!(removed, vec![2, 4, 6, 18, 20, 22, 24, 26, 34, 36]);
//
//            assert_eq!(list.len(), 13);
//            assert_eq!(
//                list.into_iter().collect::<Vec<_>>(),
//                vec![7, 9, 11, 13, 15, 17, 27, 29, 31, 33, 35, 37, 39]
//            );
//        }
//
//        {   // [xxx++++++xxxxx++++x+x]
//            let mut list = vec![
//                2, 4, 6,
//                7, 9, 11, 13, 15, 17,
//                18, 20, 22, 24, 26,
//                27, 29, 31, 33,
//                34,
//                35,
//                36
//            ].into_iter().collect::<Self>();
//
//            let removed = list.drain_filter(|x| *x % 2 == 0).collect::<Vec<_>>();
//            assert_eq!(removed.len(), 10);
//            assert_eq!(removed, vec![2, 4, 6, 18, 20, 22, 24, 26, 34, 36]);
//
//            assert_eq!(list.len(), 11);
//            assert_eq!(
//                list.into_iter().collect::<Vec<_>>(),
//                vec![7, 9, 11, 13, 15, 17, 27, 29, 31, 33, 35]
//            );
//        }
//
//        {   // [xxxxxxxxxx+++++++++++]
//            let mut list = vec![
//                2, 4, 6, 8, 10, 12, 14, 16, 18, 20,
//                1, 3, 5, 7, 9, 11, 13, 15, 17, 19
//            ].into_iter().collect::<Self>();
//
//            let removed = list.drain_filter(|x| *x % 2 == 0).collect::<Vec<_>>();
//            assert_eq!(removed.len(), 10);
//            assert_eq!(removed, vec![2, 4, 6, 8, 10, 12, 14, 16, 18, 20]);
//
//            assert_eq!(list.len(), 10);
//            assert_eq!(list.into_iter().collect::<Vec<_>>(), vec![1, 3, 5, 7, 9, 11, 13, 15, 17, 19]);
//        }
//
//        {   // [+++++++++++xxxxxxxxxx]
//            let mut list = vec![
//                1, 3, 5, 7, 9, 11, 13, 15, 17, 19,
//                2, 4, 6, 8, 10, 12, 14, 16, 18, 20
//            ].into_iter().collect::<Self>();
//
//            let removed = list.drain_filter(|x| *x % 2 == 0).collect::<Vec<_>>();
//            assert_eq!(removed.len(), 10);
//            assert_eq!(removed, vec![2, 4, 6, 8, 10, 12, 14, 16, 18, 20]);
//
//            assert_eq!(list.len(), 10);
//            assert_eq!(list.into_iter().collect::<Vec<_>>(), vec![1, 3, 5, 7, 9, 11, 13, 15, 17, 19]);
//        }
//    }

    //Example trait prop_test test:
    fn test_length() {
        let mut runner = TestRunner::new(Config {
            // Turn failure persistence off for demonstration
            failure_persistence: FailurePersistence::Off,
            .. Config::default()
        });

        runner.run(&prop::collection::vec(1..1000isize, 1..10000), | inputs | {
            let mut me = Self::default();
            let input_len = inputs.len();
            for i in inputs.clone() {
                me.push(i);
            }
            assert_eq!(input_len, me.len());
            Ok(())
        }).unwrap();
    }
}

////Can't use custom derive as Vec not defined in this crate.
//impl ListTests for Vec<isize>{}
//#[test] fn test_vec() { <Vec<isize> as ListTests>::test_all() }
//
////#[trait_tests]
//impl ListTestsBoxed for Vec<Box<isize>>{}
//#[test] fn test_vec_boxed() { <Vec<Box<isize>> as ListTestsBoxed>::test_all() }

//#[trait_tests]
//impl ListTests for String{ fn new() -> Self { String::new() } }


//TODO: Compiler error:
//#[trait_tests]
//impl ListTests for &[isize] { fn new() -> Self { Vec::new() } }

//TODO LinkedList doesn't implement List!
//impl ListTests for LinkedList<isize>{ fn new() -> Self { LinkedList::new() } }