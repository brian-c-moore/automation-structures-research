//! Output-equivalence relations for the executable comparison. Every
//! algorithm uses this one relation set.

use crate::value::Value;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Equiv {
    /// Unique correct output: compare directly.
    Exact,
    /// Order-insensitive collection: compare as a sorted multiset of
    /// integers.
    MultisetInt,
    /// Collection of integer lists, order of inner and outer
    /// insignificant (subsets, combinations, permutations, anagram
    /// groups): canonicalize both levels then compare.
    SetOfIntLists,
    /// Boolean answer.
    BoolEq,
}

fn canon(v: &Value, rel: Equiv) -> Value {
    match rel {
        Equiv::Exact | Equiv::BoolEq => v.clone(),
        Equiv::MultisetInt => {
            let mut xs = v.as_int_vec();
            xs.sort_unstable();
            Value::ints(&xs)
        }
        Equiv::SetOfIntLists => {
            let mut outer: Vec<Vec<i64>> = v
                .as_list()
                .iter()
                .map(|inner| {
                    let mut xs = inner.as_int_vec();
                    xs.sort_unstable();
                    xs
                })
                .collect();
            outer.sort();
            Value::List(outer.into_iter().map(|xs| Value::ints(&xs)).collect())
        }
    }
}

/// True iff `a` and `b` are equivalent under `rel`.
pub fn equiv(a: &Value, b: &Value, rel: Equiv) -> bool {
    canon(a, rel) == canon(b, rel)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn multiset_ignores_order() {
        assert!(equiv(
            &Value::ints(&[3, 1, 2]),
            &Value::ints(&[1, 2, 3]),
            Equiv::MultisetInt
        ));
    }
    #[test]
    fn set_of_lists_ignores_both_levels() {
        let a = Value::List(vec![Value::ints(&[2, 1]), Value::ints(&[3])]);
        let b = Value::List(vec![Value::ints(&[3]), Value::ints(&[1, 2])]);
        assert!(equiv(&a, &b, Equiv::SetOfIntLists));
    }
}
