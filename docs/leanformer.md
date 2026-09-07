# LeanFormer

## A Feasibility Experiment in an Unfamiliar Domain

---

## 1. What This Experiment Was

LeanFormer tested whether Domain Abstraction Collapse (DAC) could turn a system description into an implementation plan using the hypothesized catalog. Machine learning was chosen because it was outside the author's research background.

At the time, the catalog had sixteen entries and none had been formally tested. The design was implemented and the artifact ran, supporting further research. Later formal work tested and reclassified the catalog. LeanFormer remains unchanged; a separate reconstruction maps it to the current catalog ([research.md](research.md)).

The experiment supports feasibility for this construction and the local checks recorded below. Later literature comparison found overlap with LoRA-style low-rank deltas [1], sparse attention, and hierarchical training. Language-model capability, comparative efficiency, interference against LoRA stacking, and confidence calibration remain unmeasured.

Two transfers from systems engineering carried the design. Catastrophic forgetting was restated as destructive writes to shared mutable state, leading to an immutable base plus registry-governed overlays and explicit write boundaries. The training loop was restated as orchestration under resource governance, leading to Kubernetes-like budget allocation, staged activation, convergence-driven reconciliation, and audit.

## 2. Construction Procedure

The experiment used four passes:

1. Describe the pipeline's resource allocations, state changes, routing choices, convergence decisions, side effects, and evidence requirements without assigning DAC names.
2. Map each responsibility to the hypothesized catalog and keep unmatched responsibilities as residuals.
3. Review runtime assumptions, domain functions, ownership points, and composition seams before implementation.
4. Reconstruct the pipeline, instrument its obligations, and compare the resulting design with ML literature after the structural design was in place.

The experiment separated structure from domain function. The catalog supplied construction shapes and obligation locations. ML-specific choices supplied the loss, optimizer, thresholds, scoring functions, data, and training policy.

The artifact included a 39M-parameter run and a 204M-parameter governed training run. Sections 3 through 6 report the measurements as evidence about the artifact, with comparison gaps kept separate from the feasibility claim.

## 3. Six Problems, Stripped and Rebuilt

Each problem follows the same arc: the problem in ML vocabulary, the same problem with the vocabulary stripped, the structural decomposition, and the recorded result.

### 3.1 Parameter Inefficiency

In ML vocabulary: the design sought to reduce dense parameter storage through low-rank factorization.

Stripped of vocabulary: a system allocates a fixed compute budget uniformly to consumers without regard for whether each consumer is producing distinct work.

Decomposition: `Budget<Parameters>` with low-rank factorization. The later literature comparison found a LoRA-shaped construction [1], used here as a primary architectural choice rather than a fine-tuning adapter.

Result: the 39M run recorded a 3.9x low-rank parameter-accounting ratio, and the 204M run recorded 3.94x under the same accounting. A 76M dense configuration with the same layer geometry was the available architectural comparison; no test established equal capacity or quality.

### 3.2 Attention Cost

In ML vocabulary: full attention computes O(N^2) pairwise scores. Linear attention [2] and sparse attention are alternative approaches to reducing that cost.

Stripped of vocabulary: scoring N candidates against N seats requires N^2 comparisons. Sampling candidates before scoring reduces the comparisons; its effect on output quality must be measured separately.

Decomposition: `Sampler<AttentionMask>` + CompetitiveSelection (soft). The sampler reduces the candidate set before scoring. The later literature comparison found the neighboring sparse-attention family.

Result: 88% attention sparsity at 39M. The capability impact of the sparsity was not measured against a dense baseline.

### 3.3 Catastrophic Forgetting

In ML vocabulary: training a model on task B after task A degrades task A performance, because the same parameters are updated for both. The original capability is overwritten.

Stripped of vocabulary: a system updates a shared resource for two distinct purposes without any architectural separation between the resources used for each purpose.

Decomposition: `ResourceRegistry<BeliefID, DeltaWeights>` + `Budget<Parameters>` + AuditSink. Frozen base weights are the structural backbone; new knowledge is stored as additive low-rank deltas indexed by belief ID. Belief injection is an atomic registry insertion. Belief removal is an atomic registry deletion that restores the recorded base tensors bit for bit. The construction is structurally close to LoRA adapter stacking, with one architectural difference: the registry enforces non-overlapping parameter address ranges across deltas. That establishes storage and write-range isolation, not behavioral noninterference through shared activations or outputs, and it does not restore optimizer state or other unrecorded process state.

| Pattern | Composition |
|---|---|
| Frozen base | `ResourceRegistry<TensorID, FrozenWeights>`, immutable after init |
| Belief delta | `Budget<Parameters>` + `ResourceRegistry<BeliefID, DeltaWeights>` with atomic write boundary |
| Routing layer | CompetitiveSelection (ranked) over belief deltas |
| Combined inference | Base computation + active deltas applied additively |
| Belief removal | Delete from ResourceRegistry, restore base weights bit for bit |

Result: 84% belief injection success across 100 beliefs at 39M. The recorded set of 100 belief removals restored 406 base tensors bit for bit. Comparative interference against LoRA stacking remains unmeasured.

### 3.4 Knowledge Composition

In ML vocabulary: combining multiple pieces of knowledge into a coherent answer is an open problem. Mechanistic interpretability work [3] suggests that knowledge is distributed across attention heads in ways that are difficult to compose deliberately.

Stripped of vocabulary: a routing system needs to combine information from multiple address ranges into a single output, where the relevance of each range to the query is determined by a similarity comparison.

Decomposition: a semantic routing layer using CompetitiveSelection (ranked) to identify which belief deltas are relevant to a given input, scored by cosine similarity between the input embedding and each delta's address vector. Selected deltas activate for the forward pass; unselected deltas stay dormant.

Result: 86% routing accuracy on a held-out test set against a 5-way clustering of 100 beliefs (chance around 20%). In the recorded simultaneous-injection run, 64% of the 100 beliefs met the improvement criterion. The measurement did not establish pairwise noninterference.

### 3.5 Confabulation

In ML vocabulary: the design sought a signal for cases where the model had not reached a stable output.

Stripped of vocabulary: a process that produces an output without converging needs a way to signal that it has not converged, separately from the output itself.

Decomposition: a per-layer ConvergenceGovernor checks whether further computation is likely to change the output. It permits early exit on convergence and flags non-convergence when full depth is reached. Whether that flag predicts accuracy is a separate measurement.

Result: mean exit depth of 11.3/12 at 39M, with two distinct exit depths used. At 204M the mechanism did not activate at all (20/20 throughout). The recorded runs do not establish whether threshold or training changes would produce useful early exit, and they do not establish that the confidence signal correlates with output accuracy.

### 3.6 Training Process Inefficiency

In ML vocabulary: in the training design examined here, gradient and evaluation work followed uniform schedules without relevance-aware allocation.

Stripped of vocabulary: a resource allocator gives consumers equal shares despite differences in useful work. Scheduling and rendering systems provide examples of allocation adjusted to observed need.

Decomposition: `FederatedBudget<GradientCompute>` allocates a master budget across parameter groups; QualityHierarchy orders group activation; ConvergenceGovernor tracks group state; ranked CompetitiveSelection gates gradient routing; `Signal<GroupConverged>` publishes transitions; and AuditSink records the configured governance events in a hash-chained log.

In the 4.8M-parameter preliminary run (300 steps, WikiText-2), the governance components activated, the governors produced 15 transitions across 8 groups, and 7 groups reached CONVERGED. The hierarchy activated in the recorded L0-to-L3 order. No FederatedBudget violation or audit-chain break was recorded.

The 204M-parameter run exercised the governed pipeline for 7,228 optimizer steps. No FederatedBudget violation appeared in the 722 audit records, which also show dynamic allocation changes during training. The governors produced 18 recorded state transitions across 8 parameter groups with no state skip under the configured transition rules. The audit check reported no chain break across its 722 entries.

Best validation perplexity reached 57.6 at step 2,000, followed by severe overfitting. The local governance checks reported no violation during the later portion of the run, which separates the recorded control properties from language-model quality. Addressable parameter-capacity measurement reported 53,760 available dimensions across 20 layers (2,688 per layer), a theoretical maximum of 3,360 rank-16 knowledge deltas, reproduced on two machines.

Two governed subsystems produced no meaningful signal in the 204M run. Adaptive depth remained at 20/20, and tiered sampling assigned the Failing tier to the sampled initialization set without re-scoring.

The runs measured local properties of the artifact. Separate TLA+ configurations checked the listed composition properties. Section 5 distinguishes those results from capability measurements.

## 4. The B=0 Initialization Episode

The B=0 failure supplied a diagnostic case for the vocabulary-stripping process itself.

LeanFormer's low-rank layers initialize B matrices to zero under the recorded LoRA setup, so the parameter groups began with near-zero gradient flow before meaningful training signal existed. The governors responded to that reading and produced the early hierarchy activations reported in the run record.

The L3 activation at step 2,773 was qualitatively different. It occurred at a non-round step number, after the attention output and feed-forward projection groups had received more than 2,300 steps of real gradient flow following the output head's activation. That activation was driven by post-learning convergence in those groups, not by a calibration artifact from initialization.

The same low gradient reading could mean either cold start or post-learning convergence. That ambiguity suggested adding phase state, as other systems use depth buffers, heartbeats, timeouts, or versions to distinguish otherwise similar observations. The proposed governor records whether gradient magnitude has crossed its threshold, tracks COLD, WARMING, ACTIVE_LEARNING, and DECLINING phases, and excludes cooling from COLD. The historical TLC campaign checked `NoCoolingFromCold` and reproduced the failure in the phase-unaware model.

The diagnosis used an established phase-tracking pattern. DAC supplied the comparison that led to it; diagnosis time was not compared with a domain-specific approach.

## 5. Summary of Measurements

Architecture results are from the 39M-parameter model, with a 76M dense configuration as an architectural comparison rather than a capacity-equivalent baseline, trained on 500K OpenWebText samples for one epoch. Training governance results include the 4.8M preliminary run (300 steps, WikiText-2) and the 204M run (7,228 steps, reasoning corpus, NVIDIA L4).

Result columns use "Measured" for observations without a baseline and "Checked" for a named property evaluated over the recorded artifact.

| Mechanism | Metric | Result | Status |
|-----------|--------|--------|--------|
| Low-rank parameter ratio | Recorded low-rank accounting ratio | 3.9x (39M); 3.94x (204M) | Measured (no capacity-equivalence baseline) |
| Sparse attention | Attention sparsity | 88% | Measured (39M) |
| Gated feed-forward | FF sparsity | 80% | Measured (39M) |
| Belief injection | Success rate | 84% across 100 beliefs | Measured (39M, no baseline) |
| Semantic routing | Routing accuracy | 86%, 5-way clustering, chance ~20% | Measured (39M) |
| Belief coexistence | Simultaneous improvement | 64% of 100 beliefs | Measured (39M) |
| Base weight restoration | Bit-for-bit fidelity | Full recorded tensor set | Checked (39M) |
| Base weight immutability | Tensor integrity | 406 tensors checked | Checked (39M) |
| Adaptive depth | Mean exit depth | 11.3/12, 2 unique depths (39M); 20/20 not activated (204M) | Partial |
| Governed training | Budget invariant | 0 violations / 300 steps (4.8M); 0 violations / 722 records (204M) | Checked |
| Governed training | Audit chain integrity | 300 records checked (4.8M); 722 records, SHA-256 chain intact (204M) | Checked |
| Convergence governors | State transitions | 15 transitions, 7/8 converged (4.8M); 18 transitions, no invalid transition recorded (204M) | Checked |
| Hierarchy activation | Coarse-to-fine ordering | L0 then L1 then L2 then L3 via convergence signal | Checked (4.8M, 204M) |
| Hierarchy activation | Post-learning convergence classification | Step 2,773 (non-round, after 2,300+ steps of recorded gradient flow) | Measured (204M) |
| Hierarchy activation | L1/L2 timing | Steps 200/400 (B=0 initialization artifact, disclosed) | Disclosed artifact |
| B=0 diagnosis | DAC applied to own failure | Observational degeneracy identified; phase-aware model checked in the historical TLC configuration | Measured (no controlled comparison) |
| Budget reallocation | Dynamic budget shifts | Converged groups drop to 0.012, active get up to 0.40 | Measured (204M) |
| Gradient routing | Gate activation | 0.34-0.69 recorded gate density | Measured (204M) |
| Language modeling | Best val PPL | 57.6 at step 2,000 (204M) | Measured (not LM-competitive) |
| Language modeling | Final val PPL | 1,463.9 (overfit, single epoch, governance invariants held throughout) | Expected |
| Addressable parameter capacity | Available dims | 53,760 (3,360 max rank-16 deltas), confirmed on two machines | Measured (204M; no independent-knowledge claim) |
| Tiered sampling | Tier distribution | 100% assigned Failing in the pre-training score pass | Not functional |
| Training time | Wall clock | 140.9h on NVIDIA L4 | Measured (204M) |

## 6. What the Structural Output Covered

DAC produced the structural skeleton and obligation locations. Domain knowledge supplied the low-rank formulation, routing metric, loss, optimizer, thresholds, allocation policy, data, and training recipe. A build plan is incomplete until those domain functions and runtime assumptions are attached to the structures.

The experiment transferred immutable-overlay state management and resource-governed orchestration from systems engineering into ML. It did not test transfer in the reverse direction.

## 7. Relationship to the Current Catalog

The sixteen hypothesized entries this experiment used are not the current catalog. The formal research that followed tested each candidate, added entries from an out-of-family algorithm corpus, and reclassified others as named compositions. The current-catalog reconstruction, located by [research.md](research.md), maps the frozen LeanFormer design onto the evolved catalog and records changed classifications, domain functions, runtime relies, ownership seams, and residuals. It is an audit of this experiment, not a second one.

## 8. What Remains Unmeasured

Dense-versus-sparse attention capability, belief-delta interference against LoRA stacking, language-model efficacy, confidence calibration, and further training are outside the feasibility claim and were not measured. The measurements in Section 5 are evidence about this artifact at its recorded scales, and nothing here compares LeanFormer against standard ML practice on capability.

---

## References

[1] Hu, E.J. et al. (2021). LoRA: Low-Rank Adaptation of Large Language Models. arXiv:2106.09685.

[2] Katharopoulos, A. et al. (2020). Transformers are RNNs: Fast Autoregressive Transformers with Linear Attention. ICML 2020.

[3] Meng, K. et al. (2022). Locating and Editing Factual Associations in GPT. NeurIPS 2022.
