//! Stretch workload (docs/execution-modalities.md): reactive UI update propagation.
//!
//! Models RxJS-style observable chain:
//!
//!   click_event -> map(extract_xy) -> filter(in_bounds) -> render
//!
//! Each event flows through the chain as it arrives. Streaming-graph
//! execution: per-record progress, no completion barrier.

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClickEvent {
    pub x: i32,
    pub y: i32,
    pub button: u8,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RenderCommand {
    pub x: i32,
    pub y: i32,
}

pub struct ReactiveUiPipeline {
    pub events: Vec<ClickEvent>,
    pub bounds_x: (i32, i32),
    pub bounds_y: (i32, i32),
}

impl ReactiveUiPipeline {
    pub fn small_example() -> Self {
        Self {
            events: vec![
                ClickEvent {
                    x: 10,
                    y: 20,
                    button: 0,
                },
                ClickEvent {
                    x: -5,
                    y: 7,
                    button: 0,
                },
                ClickEvent {
                    x: 15,
                    y: 30,
                    button: 1,
                },
                ClickEvent {
                    x: 100,
                    y: 5,
                    button: 0,
                },
            ],
            bounds_x: (0, 50),
            bounds_y: (0, 50),
        }
    }

    fn map_extract(&self, ev: &ClickEvent) -> (i32, i32) {
        (ev.x, ev.y)
    }

    fn filter_in_bounds(&self, xy: &(i32, i32)) -> bool {
        let (x, y) = *xy;
        x >= self.bounds_x.0 && x <= self.bounds_x.1 && y >= self.bounds_y.0 && y <= self.bounds_y.1
    }

    pub fn run(&self) -> Vec<RenderCommand> {
        let mut out = Vec::new();
        for ev in &self.events {
            let xy = self.map_extract(ev);
            if self.filter_in_bounds(&xy) {
                out.push(RenderCommand { x: xy.0, y: xy.1 });
            }
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn small_example_filters_oob() {
        let p = ReactiveUiPipeline::small_example();
        let out = p.run();
        assert_eq!(
            out,
            vec![
                RenderCommand { x: 10, y: 20 },
                RenderCommand { x: 15, y: 30 },
            ]
        );
    }
}
