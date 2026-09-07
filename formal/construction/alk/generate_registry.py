#!/usr/bin/env python3
"""Validate the obligation-schema registry and generate its TLA+ data module."""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import pathlib
import re
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[3]
REGISTRY = pathlib.Path(__file__).resolve().parent / "ALK_REGISTRY.json"
RECORD_ROOT = ROOT / "formal" / "construction" / "derivations" / "records"
TLA_OUTPUT = pathlib.Path(__file__).resolve().parent / "tla" / "ALKRetainedRegistryData.tla"

KINDS = ("abstraction-primitive", "named-composition", "execution-modality")
ROLES = ("primary", "contributing", "support", "derived", "selected_policy")
CREDITED_STATUSES = {"primary", "contributing", "selected-policy"}
DERIVED_STATUSES = {"derived", "derived-support", "derived-conditional"}
STATUS_ROLE = {
    "primary": "primary",
    "contributing": "contributing",
    "support": "support",
    "derived": "derived",
    "derived-support": "derived",
    "derived-conditional": "derived",
    "selected-policy": "selected_policy",
}


def fail(message: str) -> None:
    raise ValueError(message)


def require_keys(value: dict[str, Any], keys: set[str], where: str) -> None:
    missing = sorted(keys - value.keys())
    extra = sorted(value.keys() - keys)
    if missing or extra:
        fail(f"{where}: key mismatch missing={missing!r} extra={extra!r}")


def strings(value: Any, where: str, *, nonempty: bool = False) -> list[str]:
    if not isinstance(value, list) or (nonempty and not value):
        fail(f"{where}: expected {'nonempty ' if nonempty else ''}string list")
    if any(not isinstance(item, str) or not item for item in value):
        fail(f"{where}: expected nonempty strings")
    if len(value) != len(set(value)):
        fail(f"{where}: duplicate values")
    return value


def file_text(path_text: str, where: str) -> str:
    path = pathlib.PurePosixPath(path_text)
    if path.is_absolute() or ".." in path.parts:
        fail(f"{where}: path must be repository-relative")
    resolved = ROOT / path
    if not resolved.is_file():
        fail(f"{where}: missing file {path_text}")
    return resolved.read_text(encoding="utf-8")


def operator_present(text: str, operator: str) -> bool:
    return re.search(
        rf"(?m)^\s*{re.escape(operator)}(?:\([^\n]*\))?\s*==", text
    ) is not None


def theorem_present(text: str, theorem: str) -> bool:
    return re.search(
        rf"(?m)^\s*(?:THEOREM|LEMMA)\s+{re.escape(theorem)}\s*==", text
    ) is not None


def load_records() -> dict[str, dict[str, Any]]:
    result: dict[str, dict[str, Any]] = {}
    for path in sorted(RECORD_ROOT.glob("*.json")):
        record = json.loads(path.read_text(encoding="utf-8"))
        name = record.get("structure")
        if not isinstance(name, str) or not name or path.stem != name:
            fail(f"{path.relative_to(ROOT).as_posix()}: filename/structure mismatch")
        if name in result:
            fail(f"duplicate derivation record for {name}")
        result[name] = record
    return result


def validate_registry(data: dict[str, Any], *, check_sources: bool = True) -> dict[str, Any]:
    require_keys(
        data,
        {
            "schema",
            "catalog_boundary",
            "counts",
            "carrier_kinds",
            "connective_roles",
            "assumption_sets",
            "profiles",
            "schemas",
            "clauses",
        },
        "registry",
    )
    if data["schema"] != "alk-obligation-schema-registry-v3":
        fail("registry: unexpected schema")

    boundary = data["catalog_boundary"]
    require_keys(
        boundary,
        {"normalization", "qualifier_vocabulary", "outcome_vocabulary", "claim_layer"},
        "catalog_boundary",
    )
    qualifiers = set(strings(boundary["qualifier_vocabulary"], "qualifier_vocabulary"))
    outcomes = set(strings(boundary["outcome_vocabulary"], "outcome_vocabulary"))
    claim_layer = boundary["claim_layer"]
    require_keys(
        claim_layer,
        {"qualifiers_field", "outcomes_field", "guarantee_kind_field"},
        "catalog_boundary.claim_layer",
    )
    if claim_layer != {
        "qualifiers_field": "qualifiers",
        "outcomes_field": "outcomes",
        "guarantee_kind_field": None,
    }:
        fail("catalog boundary must keep qualifiers/outcomes separate and issue no guarantees")
    if {"conditional", "lost"} & outcomes or {"lost"} & qualifiers:
        fail("qualifier/outcome vocabulary is conflated")

    carrier_kinds = data["carrier_kinds"]
    require_keys(carrier_kinds, set(KINDS), "carrier_kinds")
    carriers: list[str] = []
    kind_of: dict[str, str] = {}
    for kind in KINDS:
        names = strings(carrier_kinds[kind], f"carrier_kinds.{kind}", nonempty=True)
        for name in names:
            if name in kind_of:
                fail(f"carrier {name}: kind categories overlap")
            kind_of[name] = kind
            carriers.append(name)
    strings(data["connective_roles"], "connective_roles", nonempty=True)

    assumptions = data["assumption_sets"]
    if not isinstance(assumptions, dict) or not assumptions:
        fail("assumption_sets: expected nonempty object")
    if any(not isinstance(key, str) or not key or not isinstance(value, str) or not value
           for key, value in assumptions.items()):
        fail("assumption_sets: keys and statements must be nonempty strings")

    profiles = data["profiles"]
    if not isinstance(profiles, dict) or not profiles:
        fail("profiles: expected nonempty object")
    for profile_id, profile in profiles.items():
        require_keys(
            profile,
            {
                "carrier",
                "catalog_mode",
                "proof_profile",
                "public_carriers",
                "predicate_modules",
                "configurations",
                "parameters",
            },
            f"profile {profile_id}",
        )
        if profile["carrier"] not in kind_of:
            fail(f"profile {profile_id}: unknown carrier")
        for field in ("catalog_mode", "proof_profile"):
            if not isinstance(profile[field], str) or not profile[field]:
                fail(f"profile {profile_id}: invalid {field}")
        strings(profile["public_carriers"], f"profile {profile_id}.public_carriers")
        modules = strings(
            profile["predicate_modules"],
            f"profile {profile_id}.predicate_modules",
            nonempty=True,
        )
        configurations = strings(
            profile["configurations"], f"profile {profile_id}.configurations"
        )
        parameters = strings(profile["parameters"], f"profile {profile_id}.parameters")
        if check_sources:
            module_text = "\n".join(
                file_text(path, f"profile {profile_id}.predicate_modules") for path in modules
            )
            for path in configurations:
                file_text(path, f"profile {profile_id}.configurations")
            missing_parameters = [value for value in parameters if value not in module_text]
            if missing_parameters:
                fail(f"profile {profile_id}: parameters absent from modules {missing_parameters!r}")

    clauses = data["clauses"]
    if not isinstance(clauses, dict) or not clauses:
        fail("clauses: expected nonempty object")
    local_names: list[str] = []
    for occurrence, clause in clauses.items():
        require_keys(
            clause,
            {
                "profile",
                "predicate",
                "proof_roots",
                "status",
                "temporal_form",
                "concern",
                "assumption_set",
                "qualifiers",
                "outcomes",
                "compatibility_names",
                "derived_from",
                "derivation_proof_roots",
            },
            f"clause {occurrence}",
        )
        if occurrence.count("!") != 1:
            fail(f"clause {occurrence}: occurrence must be Carrier!Clause")
        carrier, local = occurrence.split("!", 1)
        local_names.append(local)
        if carrier not in kind_of:
            fail(f"clause {occurrence}: unknown carrier")
        profile_id = clause["profile"]
        if profile_id not in profiles or profiles[profile_id]["carrier"] != carrier:
            fail(f"clause {occurrence}: profile/carrier mismatch")
        if clause["status"] not in STATUS_ROLE:
            fail(f"clause {occurrence}: unknown status {clause['status']!r}")
        if clause["temporal_form"] not in {"state-safety", "action-safety", "liveness"}:
            fail(f"clause {occurrence}: unknown temporal form")
        if not isinstance(clause["concern"], str) or not clause["concern"]:
            fail(f"clause {occurrence}: missing concern")
        if clause["assumption_set"] not in assumptions:
            fail(f"clause {occurrence}: unknown assumption set")
        if not set(strings(clause["qualifiers"], f"clause {occurrence}.qualifiers")) <= qualifiers:
            fail(f"clause {occurrence}: unknown qualifier")
        if not set(strings(clause["outcomes"], f"clause {occurrence}.outcomes")) <= outcomes:
            fail(f"clause {occurrence}: unknown outcome")
        strings(clause["compatibility_names"], f"clause {occurrence}.compatibility_names")
        derived_from = strings(clause["derived_from"], f"clause {occurrence}.derived_from")
        derivation_roots = clause["derivation_proof_roots"]
        if not isinstance(derivation_roots, list):
            fail(f"clause {occurrence}.derivation_proof_roots: expected list")
        if clause["status"] in DERIVED_STATUSES and (not derived_from or not derivation_roots):
            fail(f"clause {occurrence}: derived clause lacks source or derivation proof")
        if clause["status"] not in DERIVED_STATUSES and (derived_from or derivation_roots):
            fail(f"clause {occurrence}: non-derived clause carries a derivation binding")

        predicate = clause["predicate"]
        require_keys(predicate, {"path", "operator"}, f"clause {occurrence}.predicate")
        roots = clause["proof_roots"]
        if not isinstance(roots, list) or not roots:
            fail(f"clause {occurrence}: proof_roots must be nonempty")
        if check_sources:
            predicate_text = file_text(predicate["path"], f"clause {occurrence}.predicate")
            if not operator_present(predicate_text, predicate["operator"]):
                fail(f"clause {occurrence}: predicate operator is not defined")
        for index, root in enumerate([*roots, *derivation_roots]):
            require_keys(root, {"path", "theorem"}, f"clause {occurrence}.proof[{index}]")
            if check_sources:
                proof_text = file_text(root["path"], f"clause {occurrence}.proof[{index}]")
                if not theorem_present(proof_text, root["theorem"]):
                    fail(f"clause {occurrence}: theorem {root['theorem']} is not defined")

    for occurrence, clause in clauses.items():
        unknown = set(clause["derived_from"]) - clauses.keys()
        if unknown:
            fail(f"clause {occurrence}: unknown derived_from values {sorted(unknown)!r}")

    schemas = data["schemas"]
    if not isinstance(schemas, dict) or not schemas:
        fail("schemas: expected nonempty object")
    seen_roles: dict[str, list[tuple[str, str]]] = {name: [] for name in clauses}
    for schema_id, schema in schemas.items():
        require_keys(
            schema,
            {"carrier", "profile", "clauses", "depends_on_schemas"},
            f"schema {schema_id}",
        )
        carrier = schema["carrier"]
        profile_id = schema["profile"]
        if carrier not in kind_of:
            fail(f"schema {schema_id}: unknown carrier")
        if profile_id not in profiles or profiles[profile_id]["carrier"] != carrier:
            fail(f"schema {schema_id}: profile/carrier mismatch")
        bindings = schema["clauses"]
        require_keys(bindings, set(ROLES), f"schema {schema_id}.clauses")
        schema_occurrences: list[str] = []
        for role in ROLES:
            values = strings(bindings[role], f"schema {schema_id}.clauses.{role}")
            schema_occurrences.extend(values)
            for occurrence in values:
                if occurrence not in clauses:
                    fail(f"schema {schema_id}: unknown clause {occurrence}")
                if occurrence.split("!", 1)[0] != carrier:
                    fail(f"schema {schema_id}: cross-carrier clause {occurrence}")
                if clauses[occurrence]["profile"] != profile_id:
                    fail(f"schema {schema_id}: cross-mode/profile clause {occurrence}")
                seen_roles[occurrence].append((schema_id, role))
        if len(schema_occurrences) != len(set(schema_occurrences)):
            fail(f"schema {schema_id}: duplicate clause binding")
        strings(schema["depends_on_schemas"], f"schema {schema_id}.depends_on_schemas")

    for schema_id, schema in schemas.items():
        unknown = set(schema["depends_on_schemas"]) - schemas.keys()
        if unknown or schema_id in schema["depends_on_schemas"]:
            fail(f"schema {schema_id}: invalid schema dependencies {sorted(unknown)!r}")

    for occurrence, bindings in seen_roles.items():
        if not bindings:
            fail(f"clause {occurrence}: no schema binding")
        expected_role = STATUS_ROLE[clauses[occurrence]["status"]]
        if any(role != expected_role for _, role in bindings):
            fail(f"clause {occurrence}: status/schema role mismatch {bindings!r}")
        if expected_role != "support" and len(bindings) != 1:
            fail(f"clause {occurrence}: duplicate non-support binding")

    records = load_records() if check_sources else {}
    if check_sources:
        if set(records) != set(carriers):
            fail("derivation records do not match registry carrier membership")
        for carrier, record in records.items():
            if record.get("kind") != kind_of[carrier]:
                fail(f"{carrier}: derivation-record kind mismatch")
            expected = [
                occurrence.split("!", 1)[1]
                for occurrence in clauses
                if occurrence.startswith(carrier + "!")
            ]
            if record.get("obligations") != expected:
                fail(f"{carrier}: derivation-record clause list is stale")

    counts = data["counts"]
    expected_counts = {
        "primitives": len(carrier_kinds["abstraction-primitive"]),
        "named_compositions": len(carrier_kinds["named-composition"]),
        "execution_modalities": len(carrier_kinds["execution-modality"]),
        "connective_roles": len(data["connective_roles"]),
        "profiles": len(profiles),
        "obligation_schemas": len(schemas),
        "clause_occurrences": len(clauses),
        "credited_clause_occurrences": sum(
            clause["status"] in CREDITED_STATUSES for clause in clauses.values()
        ),
        "distinct_local_clause_names": len(set(local_names)),
    }
    if counts != expected_counts:
        fail(f"registry counts are stale: expected {expected_counts!r}")
    return {"kind_of": kind_of, "seen_roles": seen_roles, **expected_counts}


def q(value: str) -> str:
    return '"' + value.replace("\\", "\\\\").replace('"', '\\"') + '"'


def tla_set(values: list[str]) -> str:
    return "{" + ", ".join(q(value) for value in values) + "}"


def tla_function(name: str, domain: str, cases: list[tuple[str, str]]) -> str:
    rendered = "\n          [] ".join(
        f"item = {q(key)} -> {value}" for key, value in cases
    )
    return f"{name} ==\n    [item \\in {domain} |->\n        CASE {rendered}]\n"


def proof_root_ids(clause: dict[str, Any]) -> list[str]:
    return [
        pathlib.PurePosixPath(root["path"]).stem + "!" + root["theorem"]
        for root in clause["proof_roots"]
    ]


def generate_tla(data: dict[str, Any]) -> str:
    summary = validate_registry(data)
    kinds = data["carrier_kinds"]
    carriers = [name for kind in KINDS for name in kinds[kind]]
    clauses = data["clauses"]
    clause_names = list(clauses)
    schemas = data["schemas"]
    schema_names = list(schemas)
    profiles = data["profiles"]
    local_names = sorted({name.split("!", 1)[1] for name in clause_names})
    credited = [name for name, value in clauses.items() if value["status"] in CREDITED_STATUSES]
    support = [name for name, value in clauses.items() if value["status"] == "support"]
    derived = [name for name, value in clauses.items() if value["status"] in DERIVED_STATUSES]
    selected = [name for name, value in clauses.items() if value["status"] == "selected-policy"]
    source_digest = hashlib.sha256(REGISTRY.read_bytes()).hexdigest()

    kind_cases = [(name, q(kind)) for kind in KINDS for name in kinds[kind]]
    occurrence_carrier_cases = [(name, q(name.split("!", 1)[0])) for name in clause_names]
    occurrence_local_cases = [(name, q(name.split("!", 1)[1])) for name in clause_names]
    carrier_clause_cases = [
        (carrier, tla_set([name for name in clause_names if name.startswith(carrier + "!")]))
        for carrier in carriers
    ]
    clause_status_cases = [(name, q(value["status"])) for name, value in clauses.items()]
    temporal_form_cases = [(name, q(value["temporal_form"])) for name, value in clauses.items()]
    concern_cases = [(name, q(value["concern"])) for name, value in clauses.items()]
    profile_cases = [(name, q(value["profile"])) for name, value in clauses.items()]
    predicate_path_cases = [(name, q(value["predicate"]["path"])) for name, value in clauses.items()]
    predicate_operator_cases = [(name, q(value["predicate"]["operator"])) for name, value in clauses.items()]
    proof_cases = [(name, tla_set(proof_root_ids(value))) for name, value in clauses.items()]
    assumption_cases = [(name, q(value["assumption_set"])) for name, value in clauses.items()]
    qualifier_cases = [(name, tla_set(value["qualifiers"])) for name, value in clauses.items()]
    outcome_cases = [(name, tla_set(value["outcomes"])) for name, value in clauses.items()]
    compatibility_cases = [(name, tla_set(value["compatibility_names"])) for name, value in clauses.items()]
    derived_from_cases = [(name, tla_set(value["derived_from"])) for name, value in clauses.items()]
    schema_carrier_cases = [(name, q(value["carrier"])) for name, value in schemas.items()]
    schema_profile_cases = [(name, q(value["profile"])) for name, value in schemas.items()]
    schema_mode_cases = [
        (name, q(profiles[value["profile"]]["catalog_mode"])) for name, value in schemas.items()
    ]
    schema_clause_cases = [
        (
            name,
            tla_set([
                clause
                for role in ROLES
                for clause in value["clauses"][role]
            ]),
        )
        for name, value in schemas.items()
    ]
    schema_dependency_cases = [
        (name, tla_set(value["depends_on_schemas"])) for name, value in schemas.items()
    ]
    clause_schema_cases = [
        (name, tla_set([schema for schema, _ in summary["seen_roles"][name]]))
        for name in clause_names
    ]

    return f'''---- MODULE ALKRetainedRegistryData ----
\\* Generated by formal/construction/alk/generate_registry.py. Do not edit by hand.

RegistrySourceDigest == {q(source_digest)}

RegistryPrimitiveNames == {tla_set(kinds["abstraction-primitive"])}

RegistryCompositionNames == {tla_set(kinds["named-composition"])}

RegistryExecutionModalityNames == {tla_set(kinds["execution-modality"])}

RegistryConnectiveNames == {tla_set(data["connective_roles"])}

RegistryStructureNames == RegistryPrimitiveNames \\cup RegistryCompositionNames

RegistryAllCarrierNames == RegistryStructureNames \\cup RegistryExecutionModalityNames

RegistryProfileNames == {tla_set(list(profiles))}

RegistryObligationSchemaNames == {tla_set(schema_names)}

RegistryClauseOccurrenceNames == {tla_set(clause_names)}

RegistryCreditedClauseOccurrences == {tla_set(credited)}

RegistrySupportClauseOccurrences == {tla_set(support)}

RegistryDerivedClauseOccurrences == {tla_set(derived)}

RegistrySelectedPolicyClauseOccurrences == {tla_set(selected)}

RegistryClauseLocalNames == {tla_set(local_names)}

RegistryTemporalForms == {tla_set(sorted({value["temporal_form"] for value in clauses.values()}))}

RegistryEngineeringConcerns == {tla_set(sorted({value["concern"] for value in clauses.values()}))}

RegistryClauseStatuses == {tla_set(sorted({value["status"] for value in clauses.values()}))}

{tla_function("RegistryKindOf", "RegistryAllCarrierNames", kind_cases)}
{tla_function("RegistryOccurrenceCarrier", "RegistryClauseOccurrenceNames", occurrence_carrier_cases)}
{tla_function("RegistryClauseLocalNameOf", "RegistryClauseOccurrenceNames", occurrence_local_cases)}
{tla_function("RegistryCarrierClauseOccurrences", "RegistryAllCarrierNames", carrier_clause_cases)}
{tla_function("RegistryClauseStatusOf", "RegistryClauseOccurrenceNames", clause_status_cases)}
{tla_function("RegistryClauseTemporalFormOf", "RegistryClauseOccurrenceNames", temporal_form_cases)}
{tla_function("RegistryClauseConcernOf", "RegistryClauseOccurrenceNames", concern_cases)}
{tla_function("RegistryClauseProfileOf", "RegistryClauseOccurrenceNames", profile_cases)}
{tla_function("RegistryClausePredicatePathOf", "RegistryClauseOccurrenceNames", predicate_path_cases)}
{tla_function("RegistryClausePredicateOperatorOf", "RegistryClauseOccurrenceNames", predicate_operator_cases)}
{tla_function("RegistryClauseProofRootsOf", "RegistryClauseOccurrenceNames", proof_cases)}
{tla_function("RegistryClauseAssumptionSetOf", "RegistryClauseOccurrenceNames", assumption_cases)}
{tla_function("RegistryClauseQualifiersOf", "RegistryClauseOccurrenceNames", qualifier_cases)}
{tla_function("RegistryClauseOutcomesOf", "RegistryClauseOccurrenceNames", outcome_cases)}
{tla_function("RegistryClauseCompatibilityNamesOf", "RegistryClauseOccurrenceNames", compatibility_cases)}
{tla_function("RegistryClauseDerivedFrom", "RegistryClauseOccurrenceNames", derived_from_cases)}
{tla_function("RegistrySchemaCarrier", "RegistryObligationSchemaNames", schema_carrier_cases)}
{tla_function("RegistrySchemaProfile", "RegistryObligationSchemaNames", schema_profile_cases)}
{tla_function("RegistrySchemaCatalogMode", "RegistryObligationSchemaNames", schema_mode_cases)}
{tla_function("RegistrySchemaClauses", "RegistryObligationSchemaNames", schema_clause_cases)}
{tla_function("RegistrySchemaDependencies", "RegistryObligationSchemaNames", schema_dependency_cases)}
{tla_function("RegistryClauseSchemasOf", "RegistryClauseOccurrenceNames", clause_schema_cases)}

\\* Compatibility projections for the earlier occurrence-shaped construction model.
\\* The construction model consumes the schema and predicate bindings directly.
RegistryObligationOccurrenceNames == RegistryClauseOccurrenceNames
RegistryEquivalentOccurrencePairs == {{}}
RegistryObligationLocalNames == RegistryClauseLocalNames
RegistryCanonicalRequirementNames == RegistryClauseLocalNames
RegistryNormalizedObligationNames == RegistryClauseOccurrenceNames
RegistryObligationPropertyClasses == {{"safety", "liveness"}}
RegistryOccurrenceStructure == RegistryOccurrenceCarrier
RegistryObligationLocalNameOf == RegistryClauseLocalNameOf
RegistryCanonicalRequirementNameOf == RegistryClauseLocalNameOf
RegistryCarrierObligationOccurrences == RegistryCarrierClauseOccurrences
RegistryNormalizedKeyOf == [item \\in RegistryClauseOccurrenceNames |-> item]
RegistryObligationPropertyClassOf ==
    [item \\in RegistryClauseOccurrenceNames |->
        IF RegistryClauseTemporalFormOf[item] = "liveness"
        THEN "liveness"
        ELSE "safety"]

RegistryCounts ==
    [primitives |-> {summary["primitives"]},
     compositions |-> {summary["named_compositions"]},
     modalities |-> {summary["execution_modalities"]},
     connectives |-> {summary["connective_roles"]},
     profiles |-> {summary["profiles"]},
     obligationSchemas |-> {summary["obligation_schemas"]},
     clauseOccurrences |-> {summary["clause_occurrences"]},
     creditedClauseOccurrences |-> {summary["credited_clause_occurrences"]},
     localClauseNames |-> {summary["distinct_local_clause_names"]}]

====
'''


def run_self_tests(data: dict[str, Any]) -> int:
    tests: list[tuple[str, Any]] = []

    missing = copy.deepcopy(data)
    missing["clauses"].pop("Budget!SafetyInvariant")
    tests.append(("missing-clause", missing))

    wrong = copy.deepcopy(data)
    wrong["clauses"]["Budget!SafetyInvariant"]["predicate"]["operator"] = "MissingOperator"
    tests.append(("wrong-predicate", wrong))

    duplicate = copy.deepcopy(data)
    duplicate["schemas"]["AS-BUD-CAP"]["clauses"]["primary"].append(
        "Budget!SafetyInvariant"
    )
    tests.append(("duplicate-binding", duplicate))

    cross_mode = copy.deepcopy(data)
    cross_mode["clauses"]["CompetitiveSelection!RankedBoundedMultiplicity"]["profile"] = (
        "competitive-hard"
    )
    tests.append(("cross-mode-binding", cross_mode))

    conflated = copy.deepcopy(data)
    conflated["clauses"]["Budget!SafetyInvariant"]["qualifiers"] = ["lost"]
    tests.append(("qualifier-outcome-conflation", conflated))

    passed = 0
    for name, mutant in tests:
        try:
            validate_registry(mutant, check_sources=name == "wrong-predicate")
        except ValueError:
            passed += 1
        else:
            fail(f"self-test {name}: mutant escaped rejection")
    return passed


def check_contract(root: pathlib.Path | None = None) -> str:
    if root is not None and root.resolve() != ROOT.resolve():
        fail("registry checker root disagrees with generator root")
    data = json.loads(REGISTRY.read_text(encoding="utf-8"))
    summary = validate_registry(data)
    expected = generate_tla(data).encode("utf-8")
    if not TLA_OUTPUT.is_file() or TLA_OUTPUT.read_bytes() != expected:
        fail(f"stale generated registry output: {TLA_OUTPUT.relative_to(ROOT).as_posix()}")
    controls = run_self_tests(data)
    digest = hashlib.sha256(expected).hexdigest()
    return (
        "ALK_REGISTRY_CONTRACT|"
        f"schemas={summary['obligation_schemas']}|clauses={summary['clause_occurrences']}|"
        f"credited={summary['credited_clause_occurrences']}|controls={controls}|sha256={digest}"
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true", help="fail if generated output differs")
    parser.add_argument("--self-test", action="store_true", help="run rejection controls")
    args = parser.parse_args()
    try:
        data = json.loads(REGISTRY.read_text(encoding="utf-8"))
        validate_registry(data)
        content = generate_tla(data).encode("utf-8")
        if args.check:
            if not TLA_OUTPUT.is_file() or TLA_OUTPUT.read_bytes() != content:
                fail(f"stale generated registry output: {TLA_OUTPUT.relative_to(ROOT).as_posix()}")
        else:
            TLA_OUTPUT.parent.mkdir(parents=True, exist_ok=True)
            TLA_OUTPUT.write_bytes(content)
        controls = run_self_tests(data) if args.self_test else 0
    except (OSError, ValueError, json.JSONDecodeError) as error:
        print(f"alk_registry: FAIL: {error}", file=sys.stderr)
        return 1
    mode = "checked" if args.check else "generated"
    print(f"alk_registry: PASS ({mode}; controls={controls})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
