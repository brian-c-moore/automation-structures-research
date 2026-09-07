use crate::crdt::{
    DocumentView, Dot, JsonPath, JsonScalar, Operation, OperationAction, ReplicaState,
};
use std::collections::{BTreeMap, BTreeSet};

/// Structure-free evaluator over the issued-operation registry.
///
/// This code does not read any merged replica payload and does not call the
/// construction materializer. It derives causally maximal path operations by
/// comparing every issued operation with every other issued operation.
pub fn evaluate_issued_operations(issued: &[Operation]) -> Result<DocumentView, String> {
    let mut identities = BTreeMap::new();
    for operation in issued {
        if let Some(existing) = identities.insert(operation.id.clone(), operation.clone()) {
            if existing != *operation {
                return Err(format!(
                    "operation identity {}:{} has conflicting content",
                    operation.id.replica, operation.id.counter
                ));
            }
        }
    }

    let mut paths = BTreeSet::new();
    for operation in issued {
        paths.insert(operation.path.clone());
    }

    let mut view = DocumentView::new();
    for path in paths {
        let mut values = BTreeSet::new();
        for candidate in issued.iter().filter(|operation| operation.path == path) {
            let dominated = issued.iter().any(|other| {
                other.path == path
                    && other.id != candidate.id
                    && other.dependencies.contains(&candidate.id)
            });
            if dominated {
                continue;
            }
            if let OperationAction::Assign(value) = &candidate.action {
                values.insert(value.clone());
            }
        }
        if !values.is_empty() {
            view.insert(JsonPath(path.0.clone()), values);
        }
    }
    Ok(view)
}

pub fn exact_issued_state(issued: &[Operation]) -> BTreeMap<Dot, BTreeSet<Operation>> {
    let mut state = BTreeMap::new();
    for operation in issued {
        state
            .entry(operation.id.clone())
            .or_insert_with(BTreeSet::new)
            .insert(operation.clone());
    }
    state
}

/// Independently reconstruct the least upper bound of two replica payloads.
///
/// The construction reaches set union through `Reduction`. This evaluator
/// deliberately does not call the construction's merge helper.
pub(crate) fn reconstruct_lub_union(left: &ReplicaState, right: &ReplicaState) -> ReplicaState {
    let mut operations = BTreeMap::<Dot, BTreeSet<Operation>>::new();
    for operation in left.operations().chain(right.operations()) {
        operations
            .entry(operation.id.clone())
            .or_default()
            .insert(operation.clone());
    }
    ReplicaState { operations }
}

pub fn singleton_view(
    path: JsonPath,
    values: impl IntoIterator<Item = JsonScalar>,
) -> DocumentView {
    let values = values.into_iter().collect::<BTreeSet<_>>();
    BTreeMap::from([(path, values)])
}
