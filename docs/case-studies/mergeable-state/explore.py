"""Finite design exploration for the problem-first DAC writeup.

These pure domain models do not implement or verify automation-structures.
Run with Python 3.10+: python explore.py [--output results.json]
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
from itertools import product
import json
from pathlib import Path


@dataclass(frozen=True)
class Move:
    identity: tuple[int, str]
    child: str
    parent: str
    dependencies: frozenset[tuple[int, str]] = frozenset()


def valid_tree(parent: dict[str, str | None]) -> bool:
    """Candidate-side predicate, checked by following parent paths."""
    if parent.get("root", "missing") is not None:
        return False
    for node in parent:
        cursor, seen = node, set()
        while cursor is not None:
            if cursor in seen or cursor not in parent:
                return False
            seen.add(cursor)
            cursor = parent[cursor]
        if "root" not in seen:
            return False
    return True


def reference_tree(parent: dict[str, str | None]) -> bool:
    """Separate observation check: expand reachable children from the root.

    It shares the parent-map representation but neither the path walk nor
    the replay implementation. It checks validity, not full replay semantics.
    """
    if parent.get("root", "missing") is not None:
        return False
    if any(p is None for n, p in parent.items() if n != "root"):
        return False
    reached = {"root"}
    while True:
        expanded = reached | {n for n, p in parent.items() if p in reached}
        if expanded == reached:
            return reached == set(parent)
        reached = expanded


def replay(base, delivered, *, arrival_order=False, check_before=False):
    """Pure reference design: fixed universe, deterministic move replay.

    A dependency denotes required prior observation, not required success.
    Rejection leaves the tree unchanged. Every complete operation receives
    an outcome. Missing dependencies leave an operation pending.
    """
    if not valid_tree(base):
        raise ValueError("invalid base")
    events = {}
    for op in delivered:
        if op.identity in events and events[op.identity] != op:
            raise ValueError("conflicting content under one identity")
        if any(dep >= op.identity for dep in op.dependencies):
            raise ValueError("order must extend dependency order")
        events[op.identity] = op
    ordering = list(events) if arrival_order else sorted(events)
    state = dict(base)
    outcomes, processed, prefixes = {}, set(), []
    for identity in ordering:
        op = events[identity]
        if not op.dependencies <= processed:
            outcomes[identity] = "pending"
            continue
        if op.child == "root" or op.child not in state or op.parent not in state:
            outcomes[identity] = "rejected-target"
        else:
            candidate = state | {op.child: op.parent}
            if valid_tree(state if check_before else candidate):
                state = candidate
                outcomes[identity] = "applied"
            else:
                outcomes[identity] = "rejected-cycle"
        processed.add(identity)
        prefixes.append(dict(state))
    return state, outcomes, frozenset(events), prefixes


def view_of(result):
    return result[:3]


def observe_list(successor):
    seen, cursor = [], 1
    while cursor is not None and cursor not in seen:
        if cursor not in successor:
            return {"path": seen, "end": "missing", "valid": False}
        seen.append(cursor)
        cursor = successor[cursor]
    return {
        "path": seen,
        "end": "null" if cursor is None else "cycle",
        "valid": cursor is None and set(seen) == set(successor),
    }


def explore():
    initial = {1: 2, 2: 3, 3: 4, 4: None}
    writes_a = {1: 3, 2: 4, 3: 2}
    writes_b = {2: 4, 3: None, 4: 3}
    local_a, local_b = initial | writes_a, initial | writes_b
    merged_ab, merged_ba = local_a | writes_b, local_b | writes_a
    assert observe_list(local_a)["valid"] and observe_list(local_b)["valid"]
    assert not observe_list(merged_ab)["valid"]
    assert not observe_list(merged_ba)["valid"]
    source = {"A_then_B": observe_list(merged_ab), "B_then_A": observe_list(merged_ba)}

    nodes = ("root", "A", "B", "C")
    choices = [tuple(n for n in nodes if n != child) for child in nodes[1:]]
    trees = []
    for parents in product(*choices):
        candidate = {"root": None} | dict(zip(nodes[1:], parents))
        assert valid_tree(candidate) == reference_tree(candidate)
        if reference_tree(candidate):
            trees.append(candidate)

    case_count, delivery_count, prefix_count, rejection_count = 0, 0, 0, 0
    for base in trees:
        locally_valid = [
            (child, parent)
            for child in nodes[1:]
            for parent in nodes
            if child != parent and reference_tree(base | {child: parent})
        ]
        for (child_a, parent_a), (child_b, parent_b) in product(locally_valid, repeat=2):
            a = Move((1, "A"), child_a, parent_a)
            b = Move((1, "B"), child_b, parent_b)
            expected = replay(base, [a, b])
            assert expected[2] == frozenset((a.identity, b.identity))
            assert len(expected[1]) == 2 and "pending" not in expected[1].values()
            rejection_count += sum(s.startswith("rejected") for s in expected[1].values())
            case_count += 1
            for delivery in ([a, b], [b, a], [a, b, a], [b, a, b]):
                result = replay(base, delivery)
                assert view_of(result) == view_of(expected)
                for state in result[3]:
                    assert reference_tree(state)
                    prefix_count += 1
                # Check each delivery prefix, including temporary divergence.
                for end in range(1, len(delivery) + 1):
                    assert reference_tree(replay(base, delivery[:end])[0])
                delivery_count += 1

    base = {"root": None, "A": "root", "B": "root", "C": "root"}
    a = Move((1, "A"), "A", "B")
    b = Move((1, "B"), "B", "A")
    naive = base | {a.child: a.parent, b.child: b.parent}
    assert not reference_tree(naive)
    children = {n: {child for child, parent in naive.items() if parent == n} for n in naive}
    assert all(child in children[parent] for child, parent in naive.items() if parent is not None)

    normal = replay(base, [a, b])
    first_b = replay(base, [b])
    assert first_b[1][b.identity] == "applied"
    assert normal[1][b.identity] == "rejected-cycle"
    assert normal[1][a.identity] == "applied"
    assert reference_tree(normal[0])

    # Intact candidates can remain valid while a broken order causes divergence.
    arrival_ab = replay(base, [a, b], arrival_order=True)
    arrival_ba = replay(base, [b, a], arrival_order=True)
    assert reference_tree(arrival_ab[0]) and reference_tree(arrival_ba[0])
    assert arrival_ab[0] != arrival_ba[0]
    wrong_guard = replay(base, [a, b], check_before=True)
    assert not reference_tree(wrong_guard[0])

    # Losing an operation can leave even the final tree unchanged: outcomes and
    # issued-operation accounting must remain observable independently of it.
    dropped = replay(base, [a])
    assert dropped[0] == normal[0]
    assert dropped[2] != normal[2] and dropped[1] != normal[1]

    dep = Move((2, "A"), "A", "B", frozenset((b.identity,)))
    waiting = replay(base, [dep])
    complete = replay(base, [dep, b])
    assert waiting[1][dep.identity] == "pending" and waiting[0] == base
    assert complete[1][dep.identity] == "rejected-cycle"
    assert view_of(complete) == view_of(replay(base, [b, dep, b]))

    identity_control = False
    try:
        replay(base, [a, Move(a.identity, "C", "B")])
    except ValueError as error:
        identity_control = str(error) == "conflicting content under one identity"
    assert identity_control

    # Validity, agreement, and finality are different observations.
    refused_a, refused_b = replay(base, [a])[0], replay(base, [b])[0]
    assert reference_tree(refused_a) and reference_tree(refused_b)
    assert refused_a != refused_b
    collection_a, collection_b = {"x"}, {"y"}
    count_a, count_b = 1, 1
    assert len(collection_a) == count_a and len(collection_b) == count_b
    assert len(collection_a | collection_b) != count_b

    controls = {
        "stale_raw_list_writes": "invalid in both transaction orders",
        "arrival_order_replay": "valid states diverge",
        "check_before_candidate": "cycle escapes",
        "drop_issued_operation": "tree agrees but outcome and input accounting fail",
        "conflicting_identity_content": "rejected",
        "derive_views_only": "inverse views agree but a cycle remains",
        "independent_cached_count": "count differs from collection cardinality",
    }
    return {
        "kind": "finite domain design exploration; no catalog implementation or formal proof",
        "profile": {
            "nodes": list(nodes), "root": "root", "replicas": ["A", "B"],
            "operations_per_enumerated_case": 2,
            "edits": "fixed-universe reparent, no create/delete, no semantic prerequisites",
            "order": "logical counter then replica identity",
            "policy": "replay from base; reject a move if its candidate is not a rooted tree",
        },
        "source_list_witness": source,
        "enumeration": {
            "valid_initial_trees": len(trees),
            "locally_valid_operation_pairs": case_count,
            "delivery_scenarios": delivery_count,
            "replay_prefix_validity_checks": prefix_count,
            "rejected_operations_in_canonical_pair_runs": rejection_count,
        },
        "witnesses": {
            "late_operation": "B changes from applied to rejected-cycle after earlier A arrives",
            "missing_dependency": "dependent edit waits, then receives its deterministic outcome",
            "refusal": "both replicas remain valid but different",
        },
        "controls": controls,
        "limits": [
            "finite enumeration plus named witnesses; no unbounded theorem",
            "validity reference is separate; replay policy has no independent full semantic oracle",
            "no memory concurrency, durable storage, transport, reclamation, or external effects",
            "no Rust structure binding, kernel integration, or implementation conformance",
        ],
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if not __debug__:
        raise SystemExit("Assertions are required; do not use Python -O.")
    result = explore()
    result["source_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        if args.output.resolve() == Path(__file__).resolve():
            raise SystemExit("Output must not overwrite the source.")
        args.output.write_text(rendered, encoding="utf-8")
    print(rendered, end="")


if __name__ == "__main__":
    main()
