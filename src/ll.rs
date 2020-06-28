use std::{
  mem::{replace, MaybeUninit},
  ptr::{drop_in_place, NonNull},
};

/// How many items are stored per node
pub const NODE_SIZE: usize = 64;

struct Node<T> {
  items: [MaybeUninit<T>; NODE_SIZE],
  // only need u8 rn to store NODE_SIZE
  num_items: u8,

  // Pointer to next node in linked list
  next: Option<NonNull<Node<T>>>,
}

impl<T> Node<T> {
  const fn is_full(&self) -> bool { self.num_items == NODE_SIZE as u8 }
  const fn len(&self) -> u8 { self.num_items }
  const fn is_empty(&self) -> bool { self.len() == 0 }

  fn empty(next: Option<NonNull<Self>>) -> Self {
    let items: [MaybeUninit<T>; NODE_SIZE] = unsafe { MaybeUninit::uninit().assume_init() };
    Self {
      items,
      num_items: 0,
      next,
    }
  }
  fn alloc_next(&mut self) -> &mut Self {
    let new = Box::new(Self::empty(self.next.take()));
    assert!(self.next.replace(Box::leak(new).into()).is_none());
    unsafe { &mut *self.next.unwrap().as_ptr() }
  }
  fn next_mut(&mut self) -> Option<&mut Self> { self.next.map(|n| unsafe { &mut *n.as_ptr() }) }
  fn next(&self) -> Option<&Self> { self.next.map(|n| unsafe { &*n.as_ptr() }) }

  // just prints the number of nodes for debugging
  #[allow(dead_code)]
  fn node_count(&mut self) -> usize { self.next_mut().map(|n| n.node_count() + 1).unwrap_or(1) }

  /// Splits this node in half and gives the next node half of it's own
  fn split(&mut self) -> &mut Self {
    assert!(self.is_full());
    self.alloc_next();
    unsafe {
      self.next.unwrap().as_mut().items[..NODE_SIZE / 2]
        .swap_with_slice(&mut self.items[NODE_SIZE / 2..]);
    }
    self.num_items = NODE_SIZE as u8 / 2;
    unsafe {
      self.next.unwrap().as_mut().num_items = NODE_SIZE as u8 / 2;
    }
    self.next_mut().unwrap()
  }
  /// Steals elements from the next node, and deallocates it if it's found that it no longer
  /// contains more than half. If this is the last node does nothing.
  fn steal(&mut self) {
    debug_assert!((self.num_items as usize) < NODE_SIZE / 4);
    let next = if let Some(n) = self.next {
      unsafe { &mut *n.as_ptr() }
    } else {
      return;
    };
    let next_size = next.num_items;
    if next_size as usize > NODE_SIZE / 4 {
      // steal NODE_SIZE/4 items
      self.items[self.num_items as usize..self.num_items as usize + NODE_SIZE / 4]
        .swap_with_slice(&mut next.items[..NODE_SIZE / 4]);
      next.items[..next.num_items as usize].rotate_left(NODE_SIZE / 4);
      next.num_items -= (NODE_SIZE / 4) as u8;
      self.num_items += (NODE_SIZE / 4) as u8;
    } else {
      // Steal all items and deallocate node
      self.items[self.num_items as usize..(self.num_items + next_size) as usize]
        .swap_with_slice(&mut next.items[..next_size as usize]);
      next.num_items = 0;
      self.num_items += next_size;

      // bypass this now empty node (TODO could this be moved to some unused pool?)
      let next_next = next.next.take();
      unsafe { drop_in_place(next) }
      self.next = next_next;
    }
  }

  /// Inserts t at the end of this node, assuming that the node is not full
  fn insert_end(&mut self, t: T) {
    self.items[self.num_items as usize] = MaybeUninit::new(t);
    self.num_items += 1;
  }
  /// Inserts t at position i in this node, or if i > t goes onto the next node
  fn insert(&mut self, i: usize, t: T) {
    // this loop is only here to check when we split
    loop {
      let out = if i < self.num_items as usize {
        if self.is_full() {
          self.split();
          continue;
        }
        self.insert_at(i as u8, t);
      } else {
        let next_idx = i - self.num_items as usize;
        self
          .next_mut()
          .expect("Expected insert to only be called when there are enough nodes")
          .insert(next_idx, t);
      };
      // break OUT, free yo self
      break out;
    }
  }
  fn insert_at(&mut self, i: u8, t: T) {
    debug_assert!(!self.is_full());
    debug_assert!(i < self.num_items);
    self.items[self.num_items as usize] = MaybeUninit::new(t);
    self.num_items += 1;
    self.items[i as usize..self.num_items as usize].rotate_right(1);
  }

  fn remove(&mut self, i: usize) -> T {
    if i < self.num_items as usize {
      self.remove_at(i as u8)
    } else {
      let next_idx = i - self.num_items as usize;
      self
        .next_mut()
        .expect("Expected insert to only be called when there are enough nodes")
        .remove(next_idx)
    }
  }

  fn remove_at(&mut self, i: u8) -> T {
    assert!(self.num_items > i);
    let out = replace(&mut self.items[i as usize], MaybeUninit::uninit());
    let out = unsafe { out.assume_init() };
    self.items[i as usize..self.num_items as usize].rotate_left(1);
    self.num_items -= 1;
    if (self.num_items as usize) < NODE_SIZE / 4 {
      self.steal()
    }
    out
  }

  fn push_back(&mut self, t: T) {
    if let Some(next) = self.next_mut() {
      next.push_back(t);
    } else if self.is_full() {
      self.split().push_back(t);
    } else {
      self.insert_end(t);
    }
  }

  fn pop_back(&mut self) -> T {
    if let Some(next) = self.next_mut() {
      let out = next.pop_back();
      if next.is_empty() {
        assert!(next.next.is_none());
        unsafe { drop_in_place(next) }
        self.next = None;
      }
      out
    } else {
      debug_assert_ne!(self.num_items, 0);
      self.num_items -= 1;
      let out = replace(
        &mut self.items[self.num_items as usize],
        MaybeUninit::uninit(),
      );
      unsafe { out.assume_init() }
    }
  }

  fn push_front(&mut self, t: T) {
    if self.is_full() {
      self.split();
    }
    self.insert_at(0, t);
  }
  fn pop_front(&mut self) -> T { self.remove_at(0) }
}

impl<T> Drop for Node<T> {
  fn drop(&mut self) {
    // Do we manually need to recursively drop the next node?
    if let Some(n) = self.next {
      unsafe { drop_in_place(n.as_ptr()) }
    }
  }
}

#[derive(Debug)]
pub struct LinkedList<T> {
  head: Option<NonNull<Node<T>>>,
  len: usize,
}

macro_rules! get_or_alloc_head {
  ($v: expr) => {
    if let Some(head) = $v.head_mut() {
      head
    } else {
      $v.alloc_head()
    }
  };
}

impl<T> LinkedList<T> {
  /// Returns a new linked list. Does not allocate until items are added
  pub const fn new() -> Self { Self { head: None, len: 0 } }
  pub const fn len(&self) -> usize { self.len }
  pub const fn is_empty(&self) -> bool { self.len == 0 }

  fn alloc_head(&mut self) -> &mut Node<T> {
    let new = Box::new(Node::empty(None));
    assert!(self.head.replace(Box::leak(new).into()).is_none());
    unsafe { &mut *self.head.unwrap().as_ptr() }
  }
  fn head_mut(&mut self) -> Option<&mut Node<T>> { Some(unsafe { &mut *self.head?.as_ptr() }) }
  fn head(&self) -> Option<&Node<T>> { Some(unsafe { &*self.head?.as_ptr() }) }
  pub fn push_back(&mut self, t: T) {
    self.len += 1;
    get_or_alloc_head!(self).push_back(t);
  }
  pub fn push_front(&mut self, t: T) {
    self.len += 1;
    get_or_alloc_head!(self).push_front(t);
  }
  pub fn insert(&mut self, t: T, idx: usize) {
    assert!(idx < self.len);
    self.len += 1;
    get_or_alloc_head!(self).insert(idx, t);
  }
  pub fn pop_front(&mut self) -> Option<T> {
    if self.is_empty() {
      return None;
    }
    self.len -= 1;
    Some(self.head_mut().unwrap().pop_front())
  }
  pub fn pop_back(&mut self) -> Option<T> {
    if self.is_empty() {
      return None;
    }
    self.len -= 1;
    Some(self.head_mut().unwrap().pop_back())
  }
  pub fn remove(&mut self, idx: usize) -> Option<T> {
    if self.is_empty() || idx > self.len {
      return None;
    }
    self.len -= 1;
    Some(self.head_mut().unwrap().remove(idx))
  }

  /// Creates an iterator over this linked list
  pub fn iter(&self) -> impl Iterator<Item = &'_ T> + '_ {
    self
      .head
      .iter()
      .flat_map(|h| Iter::new(unsafe { h.as_ref() }))
  }
  pub fn peek_front(&self) -> Option<&T> {
    if self.is_empty() {
      return None;
    }
    let head = self.head().unwrap();
    Some(unsafe { &*head.items[0].as_ptr() })
  }
}

impl<T> Drop for LinkedList<T> {
  fn drop(&mut self) {
    if let Some(n) = self.head {
      unsafe { std::ptr::drop_in_place(n.as_ptr()) }
    }
  }
}

pub struct Iter<'a, T> {
  curr: &'a Node<T>,
  n: u8,
}

impl<'a, T> Iter<'a, T> {
  fn new(curr: &'a Node<T>) -> Self { Self { curr, n: 0 } }
}

impl<'a, T> Iterator for Iter<'a, T> {
  type Item = &'a T;
  fn next(&mut self) -> Option<Self::Item> {
    loop {
      let out = if self.n < self.curr.num_items {
        let next = unsafe { &*self.curr.items[self.n as usize].as_ptr() };
        self.n += 1;
        next
      } else {
        let next = self.curr.next()?;
        self.curr = next;
        self.n = 0;
        continue;
      };
      // Like a fool, I'm trapped inside a cage
      // trapped Colonel Abrams
      break Some(out);
    }
  }
}

#[test]
fn basic() {
  let mut ll = LinkedList::new();
  let n = 64 * 4;
  for _ in 0..n {
    ll.push_back('b');
  }
  for _ in 0..n {
    ll.push_front('f');
  }
  for _ in 0..n {
    ll.insert('m', n);
  }
  assert_eq!(ll.len, n * 3);
  for _ in 0..n {
    assert_eq!(ll.remove(n), Some('m'));
  }
  for _ in 0..n {
    assert_eq!(ll.pop_front(), Some('f'));
  }
  for _ in 0..n {
    assert_eq!(ll.pop_back(), Some('b'));
  }
  assert!(ll.is_empty());
}
