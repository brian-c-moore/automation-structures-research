//! Stretch workload (docs/execution-modalities.md): render-graph per-frame execution.
//!
//! Models a Frostbite/Unreal-style frame graph:
//!
//!   gbuffer_pass -> lighting_pass -> post_fx -> present
//!
//! Each frame the graph is rebuilt and executed. Streaming graph
//! variant where input is a vsync tick.

#[derive(Debug, Clone)]
pub struct FramePass {
    pub name: String,
    pub depends_on: Vec<String>,
    pub cost_ms: f32,
}

#[derive(Debug, Clone)]
pub struct FrameGraph {
    pub passes: Vec<FramePass>,
}

impl FrameGraph {
    pub fn typical() -> Self {
        Self {
            passes: vec![
                FramePass {
                    name: "gbuffer".into(),
                    depends_on: vec![],
                    cost_ms: 2.5,
                },
                FramePass {
                    name: "lighting".into(),
                    depends_on: vec!["gbuffer".into()],
                    cost_ms: 3.1,
                },
                FramePass {
                    name: "post_fx".into(),
                    depends_on: vec!["lighting".into()],
                    cost_ms: 1.4,
                },
                FramePass {
                    name: "present".into(),
                    depends_on: vec!["post_fx".into()],
                    cost_ms: 0.2,
                },
            ],
        }
    }

    /// Execute the frame graph in topological order. Returns total
    /// frame time in ms.
    pub fn render_one_frame(&self) -> f32 {
        // Precondition: passes are pre-sorted in dependency order.
        let mut completed: Vec<String> = Vec::new();
        let mut total = 0.0;
        for p in &self.passes {
            for dep in &p.depends_on {
                assert!(
                    completed.iter().any(|c| c == dep),
                    "render-graph dependency {} of pass {} not yet completed",
                    dep,
                    p.name
                );
            }
            total += p.cost_ms;
            completed.push(p.name.clone());
        }
        total
    }

    /// Run for N frames. Models the per-frame rebuild semantics: each
    /// frame is an independent execution of the graph.
    pub fn render_n_frames(&self, n: usize) -> Vec<f32> {
        (0..n).map(|_| self.render_one_frame()).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn typical_renders_each_frame_consistently() {
        let g = FrameGraph::typical();
        let frames = g.render_n_frames(3);
        assert_eq!(frames.len(), 3);
        assert!(frames.iter().all(|&t| (t - frames[0]).abs() < 1e-6));
    }
}
