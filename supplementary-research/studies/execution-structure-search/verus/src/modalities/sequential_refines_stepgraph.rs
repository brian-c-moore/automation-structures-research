// SequentialRefinesStepGraph.
//
// Bounded implementation-level witness: a Sequential program of four steps
// maps to four linearly chained StepGraph nodes with parallelism degree one.
// This file does not claim a maintained TLA+/TLAPS counterpart or general
// refinement beyond the written state mapping and two checked transitions.
//
// `pc` (program counter) and `active` (currently executing) are the
// concrete state; the abstract `node_state` is derived via the
// refinement-mapping function. At each step boundary,
// the refinement invariant `sgstate == ExpectedSGOf(pc, active)` holds
// by construction.

use vstd::prelude::*;

verus! {

pub const STEPS: usize = 4;

/// Node states: 0=NotReady, 1=Ready, 2=Running, 3=Completed. Numeric rather
/// than symbolic for SMT tractability; the TLA+ carrier uses model values.
pub const NOT_READY: u64 = 0;
pub const READY:     u64 = 1;
pub const RUNNING:   u64 = 2;
pub const COMPLETED: u64 = 3;

/// Refinement mapping: derive node n's state from (pc, active).
/// Direct translation of the TLA+ `ExpectedSGOf(p, a)` mapping.
pub open spec fn expected_state(pc: int, active: bool, n: int) -> u64 {
    if n < pc {
        COMPLETED
    } else if n == pc && !active && pc > 0 {
        COMPLETED
    } else if n == pc + 1 && !active {
        READY
    } else if n == pc && active {
        RUNNING
    } else if n == 1 && pc == 0 && !active {
        READY
    } else {
        NOT_READY
    }
}

/// BeginStep: advance pc and set active. The refinement mapping
/// derives the new abstract state automatically.
pub fn begin_step(pc: &mut usize, active: &mut bool)
    requires *old(pc) < STEPS, !*old(active),
    ensures
        *final(pc) == *old(pc) + 1,
        *final(active) == true,
        // Refinement invariant: the derived state for the active node
        // is RUNNING.
        expected_state(*final(pc) as int, *final(active), *final(pc) as int) == RUNNING,
{
    *active = true;
    *pc = *pc + 1;
}

/// CompleteStep: clear active. The active node transitions to COMPLETED.
pub fn complete_step(pc: &mut usize, active: &mut bool)
    requires *old(active), *old(pc) > 0,
    ensures
        *final(pc) == *old(pc),
        *final(active) == false,
        // Refinement invariant: pc's node is now COMPLETED.
        expected_state(*final(pc) as int, *final(active), *final(pc) as int) == COMPLETED,
{
    *active = false;
}

}
