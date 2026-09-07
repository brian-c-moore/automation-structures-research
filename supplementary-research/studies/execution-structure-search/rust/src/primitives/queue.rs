//! Bounded queue with backpressure.
//!
//! Maps to TLA+ `Queues.tla`. The queue enforces a capacity bound;
//! attempts to enqueue beyond capacity return [`QueueError::Full`],
//! which the caller (e.g. an upstream operator) interprets as
//! backpressure.

use std::collections::VecDeque;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum QueueError {
    Full,
    Empty,
}

#[derive(Debug, Clone)]
pub struct BoundedQueue<T> {
    inner: VecDeque<T>,
    capacity: usize,
}

impl<T> BoundedQueue<T> {
    pub fn new(capacity: usize) -> Self {
        assert!(capacity > 0, "capacity must be positive");
        Self {
            inner: VecDeque::with_capacity(capacity),
            capacity,
        }
    }

    pub fn capacity(&self) -> usize {
        self.capacity
    }

    pub fn len(&self) -> usize {
        self.inner.len()
    }

    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    pub fn is_full(&self) -> bool {
        self.inner.len() >= self.capacity
    }

    /// Backpressure signal: the queue is currently rejecting writes.
    pub fn backpressure(&self) -> bool {
        self.is_full()
    }

    pub fn enqueue(&mut self, item: T) -> Result<(), QueueError> {
        if self.is_full() {
            return Err(QueueError::Full);
        }
        self.inner.push_back(item);
        Ok(())
    }

    pub fn dequeue(&mut self) -> Result<T, QueueError> {
        self.inner.pop_front().ok_or(QueueError::Empty)
    }

    pub fn peek(&self) -> Option<&T> {
        self.inner.front()
    }

    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.inner.iter()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn enqueue_then_dequeue_is_fifo() {
        let mut q = BoundedQueue::new(3);
        q.enqueue(1).unwrap();
        q.enqueue(2).unwrap();
        q.enqueue(3).unwrap();
        assert_eq!(q.dequeue(), Ok(1));
        assert_eq!(q.dequeue(), Ok(2));
        assert_eq!(q.dequeue(), Ok(3));
        assert_eq!(q.dequeue(), Err(QueueError::Empty));
    }

    #[test]
    fn backpressure_kicks_in_at_capacity() {
        let mut q = BoundedQueue::new(2);
        q.enqueue(1).unwrap();
        q.enqueue(2).unwrap();
        assert!(q.backpressure());
        assert_eq!(q.enqueue(3), Err(QueueError::Full));
    }
}
