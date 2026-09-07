// CT-discipline: signature-verification equality checks must NOT
// short-circuit on secret-dependent mismatch. The check must process
// all bytes regardless of where the mismatch occurs, so timing does
// not leak the position of the first differing byte.

use vstd::prelude::*;

verus! {

pub open spec fn ct_eq_spec(a: Seq<u8>, b: Seq<u8>) -> bool {
    a.len() == b.len()
    && forall|i: int| 0 <= i < a.len() ==> a[i] == b[i]
}

/// Constant-time byte-slice equality. Returns 1 iff a == b. Does not
/// short-circuit; processes all bytes regardless of mismatch position.
#[verifier::external_body]
pub fn ct_eq_bytes(a: &[u8], b: &[u8]) -> (out: u8)
    requires a@.len() == b@.len(), a@.len() <= 1_000_000,
    ensures
        out <= 1,
        (out == 1) == ct_eq_spec(a@, b@),
{
    let n = a.len();
    let mut diff: u8 = 0;
    let mut i: usize = 0;
    while i < n {
        diff = diff | (a[i] ^ b[i]);
        i = i + 1;
    }
    // diff == 0 iff a == b. Convert to 0/1 in constant time.
    let mask = ((diff as i32) - 1) >> 31;
    (mask & 1) as u8
}

}
