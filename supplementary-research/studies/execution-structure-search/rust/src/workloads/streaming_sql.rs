//! Streaming SQL workload (bounded study configuration).
//!
//! "A windowed aggregation over an unbounded input. Flink, Kafka
//! Streams, Materialize reproductions run this. Verifies windowing,
//! watermarks, and incremental computation under streaming
//! semantics."

#[derive(Debug, Clone, Copy)]
pub struct Event {
    pub timestamp: u64,
    pub value: i64,
}

#[derive(Debug, Clone, Copy)]
pub struct WindowAggregate {
    pub start: u64,
    pub end: u64,
    pub sum: i64,
    pub count: u32,
}

pub struct StreamingSql {
    pub events: Vec<Event>,
    pub window_size: u64,
}

impl StreamingSql {
    pub fn small_example() -> Self {
        Self {
            window_size: 5,
            events: vec![
                Event {
                    timestamp: 1,
                    value: 10,
                },
                Event {
                    timestamp: 2,
                    value: 20,
                },
                Event {
                    timestamp: 4,
                    value: 5,
                },
                Event {
                    timestamp: 6,
                    value: 7,
                },
                Event {
                    timestamp: 7,
                    value: 3,
                },
                Event {
                    timestamp: 11,
                    value: 100,
                },
            ],
        }
    }

    /// Tumbling-window sum: window [k*W, (k+1)*W) gets the sum and
    /// count of events whose timestamp falls in that range. Returns
    /// windows in start-time order.
    pub fn run(&self) -> Vec<WindowAggregate> {
        if self.events.is_empty() {
            return vec![];
        }
        let mut windows: std::collections::BTreeMap<u64, WindowAggregate> =
            std::collections::BTreeMap::new();
        for ev in &self.events {
            let window_start = (ev.timestamp / self.window_size) * self.window_size;
            let entry = windows.entry(window_start).or_insert(WindowAggregate {
                start: window_start,
                end: window_start + self.window_size,
                sum: 0,
                count: 0,
            });
            entry.sum += ev.value;
            entry.count += 1;
        }
        windows.into_values().collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn small_example_aggregates_into_three_windows() {
        let w = StreamingSql::small_example();
        let out = w.run();
        assert_eq!(out.len(), 3);
        assert_eq!(out[0].sum, 35);
        assert_eq!(out[1].sum, 10);
        assert_eq!(out[2].sum, 100);
    }
}
