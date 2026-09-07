// CT-discipline: ct_select is the canonical branchless conditional
// select primitive used throughout CT-disciplined cryptographic code.
// Selects between two values based on a boolean (encoded as 0/1) with
// no data-dependent control flow.
//
// Spec: ct_select(cond, a, b) returns a if cond == 1, b if cond == 0.

use vstd::prelude::*;

verus! {

pub open spec fn ct_select_u64_spec(cond: u8, a: u64, b: u64) -> u64 {
    if cond == 1 { a } else { b }
}

/// Branchless conditional select on u64. Constant time: same operations
/// regardless of `cond` value.
#[verifier::external_body]
pub fn ct_select_u64(cond: u8, a: u64, b: u64) -> (out: u64)
    requires cond <= 1,
    ensures out == ct_select_u64_spec(cond, a, b),
{
    let mask = (0u64).wrapping_sub(cond as u64);
    (a & mask) | (b & !mask)
}

pub open spec fn ct_select_u8_spec(cond: u8, a: u8, b: u8) -> u8 {
    if cond == 1 { a } else { b }
}

#[verifier::external_body]
pub fn ct_select_u8(cond: u8, a: u8, b: u8) -> (out: u8)
    requires cond <= 1,
    ensures out == ct_select_u8_spec(cond, a, b),
{
    let mask = 0u8.wrapping_sub(cond);
    (a & mask) | (b & !mask)
}

}
