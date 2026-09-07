#!/usr/bin/env python3
"""Generate and check derivation data modules from the checked records."""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[3]
DERIVATION_ROOT = pathlib.Path(__file__).resolve().parent
RECORD_ROOT = DERIVATION_ROOT / "records"
GENERATED_ROOT = DERIVATION_ROOT / "generated"


def q(value: str) -> str:
    return '"' + value.replace("\\", "\\\\").replace('"', '\\"') + '"'


def tla_value(value: Any) -> str:
    if isinstance(value, bool):
        return "TRUE" if value else "FALSE"
    if isinstance(value, int):
        return str(value)
    if isinstance(value, str):
        return q(value)
    if isinstance(value, list):
        return "<<" + ", ".join(tla_value(item) for item in value) + ">>"
    raise TypeError(f"unsupported TLA+ value: {value!r}")


def tla_set(values: list[Any]) -> str:
    if not values:
        return "{}"
    return "{" + ", ".join(tla_value(value) for value in values) + "}"


def tla_function(
    name: str, mapping: dict[str, Any], *, list_values_are_sets: bool = False
) -> str:
    keys: list[Any] = []
    decoded: list[tuple[Any, Any]] = []
    for raw_key, value in mapping.items():
        key: Any = json.loads(raw_key) if raw_key.startswith("[") else raw_key
        keys.append(key)
        decoded.append((key, value))
    if not decoded:
        return f'{name} == [key \\in {{}} |-> "unused"]\n'

    def render(value: Any) -> str:
        if list_values_are_sets and isinstance(value, list):
            return tla_set(value)
        return tla_value(value)

    default = decoded[-1][1]
    cases = "\n          [] ".join(
        f"key = {tla_value(key)} -> {render(value)}" for key, value in decoded
    )
    return (
        f"{name} ==\n"
        f"    [key \\in {tla_set(keys)} |->\n"
        f"        CASE {cases}\n"
        f"          [] OTHER -> {render(default)}]\n"
    )


def case_ids(record: dict[str, Any], case_class: str) -> list[str]:
    return [case["id"] for case in record["cases"][case_class]]


def validate_record(record: dict[str, Any], source: pathlib.Path) -> None:
    required = {
        "module", "structure", "kind", "property_classes", "state_fields",
        "observation_fields", "implementation_state_fields",
        "implementation_state_map", "observation_map", "canonical_actions",
        "system_actions", "environment_actions", "failure_actions",
        "commit_actions", "executable_actions", "action_map", "obligations",
        "violations", "violation_of", "actors", "claimant", "owner_of",
        "delegate_of", "assurance_at", "relies", "guarantees",
        "runtime_providers", "failure_ceilings", "execution_carriers",
        "local_theorems", "executable_pointers", "library_premises",
        "deployment_premises", "residuals", "evidence_ceilings", "cases",
        "applicable_families", "discharged_families", "transfer_classes",
        "refinement_status", "witness",
    }
    missing = sorted(required - record.keys())
    if missing:
        raise ValueError(f"{source}: missing keys {missing}")
    if record["module"] != record["structure"]:
        raise ValueError(f"{source}: module/structure identity mismatch")
    if set(record["action_map"]) != set(record["canonical_actions"]):
        raise ValueError(f"{source}: action map is not action-total")
    if set(record["violation_of"]) != set(record["obligations"]):
        raise ValueError(f"{source}: violation map is not obligation-total")
    if set(record["owner_of"]) != set(record["canonical_actions"]):
        raise ValueError(f"{source}: owner map is not action-total")
    for case_class in ("valid", "boundary", "misuse", "failure"):
        if not record["cases"].get(case_class):
            raise ValueError(f"{source}: {case_class} cases are empty")


def generate_tla(record: dict[str, Any]) -> str:
    module = record["module"] + "DerivationData"
    witness = record["witness"]
    parts = [
        f"---- MODULE {module} ----\n",
        "EXTENDS StructureDerivationSchema\n\n",
        "\\* Generated from the checked derivation record. Do not edit by hand.\n\n",
        tla_function("ImplementationStateMap", record["implementation_state_map"]),
        "\n",
        tla_function("ObservationMap", record["observation_map"]),
        "\n",
        tla_function("ActionMap", record["action_map"], list_values_are_sets=True),
        "\n",
        tla_function("ViolationOf", record["violation_of"]),
        "\n",
        tla_function("OwnerOf", record["owner_of"]),
        "\n",
        tla_function("DelegateOf", record["delegate_of"], list_values_are_sets=True),
        "\n",
        tla_function("AssuranceAt", record["assurance_at"]),
        "\n",
        tla_function("WitnessPersistentObserve", witness["persistent_observe"]),
        "\n",
        tla_function("WitnessRank", witness["rank"]),
        "\n",
        tla_function("WitnessFairnessOwnerOf", witness["fairness_owner_of"]),
        "\n",
        tla_function("WitnessActionSteps", witness["action_steps"], list_values_are_sets=True),
        "\n",
    ]
    fields: list[tuple[str, str]] = [
        ("structure", q(record["structure"])),
        ("kind", q(record["kind"])),
        ("propertyClasses", tla_set(record["property_classes"])),
        ("stateFields", tla_set(record["state_fields"])),
        ("observationFields", tla_set(record["observation_fields"])),
        ("implementationStateFields", tla_set(record["implementation_state_fields"])),
        ("implementationStateMap", "ImplementationStateMap"),
        ("observationMap", "ObservationMap"),
        ("canonicalActions", tla_set(record["canonical_actions"])),
        ("systemActions", tla_set(record["system_actions"])),
        ("environmentActions", tla_set(record["environment_actions"])),
        ("failureActions", tla_set(record["failure_actions"])),
        ("commitActions", tla_set(record["commit_actions"])),
        ("executableActions", tla_set(record["executable_actions"])),
        ("actionMap", "ActionMap"),
        ("obligations", tla_set(record["obligations"])),
        ("violations", tla_set(record["violations"])),
        ("violationOf", "ViolationOf"),
        ("actors", tla_set(record["actors"])),
        ("claimant", q(record["claimant"])),
        ("ownerOf", "OwnerOf"),
        ("delegateOf", "DelegateOf"),
        ("assuranceAt", "AssuranceAt"),
        ("relies", tla_set(record["relies"])),
        ("guarantees", tla_set([item["id"] for item in record["guarantees"]])),
        ("runtimeProviders", tla_set(record["runtime_providers"])),
        ("failureCeilings", tla_set(record["failure_ceilings"])),
        ("executionCarriers", tla_set(record["execution_carriers"])),
        ("localTheorems", tla_set(record["local_theorems"])),
        ("executablePointers", tla_set(record["executable_pointers"])),
        ("libraryPremises", tla_set(record["library_premises"])),
        ("deploymentPremises", tla_set(record["deployment_premises"])),
        ("residuals", tla_set(record["residuals"])),
        ("evidenceCeilings", tla_set(record["evidence_ceilings"])),
        ("validCases", tla_set(case_ids(record, "valid"))),
        ("boundaryCases", tla_set(case_ids(record, "boundary"))),
        ("misuseCases", tla_set(case_ids(record, "misuse"))),
        ("failureCases", tla_set(case_ids(record, "failure"))),
        ("globalAssumptions", "GlobalModelingAssumptionNames"),
        ("conformanceConditions", "ConformanceConditions"),
        ("applicableFamilies", tla_set(record["applicable_families"])),
        ("dischargedFamilies", tla_set(record["discharged_families"])),
        ("transferClasses", tla_set(record["transfer_classes"])),
        ("refinementStatus", q(record["refinement_status"])),
        ("witnessStates", tla_set(witness["states"])),
        ("witnessInitial", tla_set(witness["initial"])),
        ("witnessObligationStates", tla_set(witness["obligation_states"])),
        ("witnessViolationStates", tla_set(witness["violation_states"])),
        ("witnessSystemSteps", tla_set(witness["system_steps"])),
        ("witnessEnvironmentSteps", tla_set(witness["environment_steps"])),
        ("witnessActionSteps", "WitnessActionSteps"),
        ("witnessRelySteps", tla_set(witness["rely_steps"])),
        ("witnessCommitSteps", tla_set(witness["commit_steps"])),
        ("witnessFailureSteps", tla_set(witness["failure_steps"])),
        ("witnessInterferenceSteps", tla_set(witness["interference_steps"])),
        ("witnessCheckActMode", q(witness["check_mode"])),
        ("witnessCheckResultStates", tla_set(witness["check_result_states"])),
        ("witnessPredicateStates", tla_set(witness["predicate_states"])),
        ("witnessActors", tla_set(witness["actors"])),
        ("witnessProviders", tla_set(witness["providers"])),
        ("witnessClaimant", q(witness["claimant"])),
        ("witnessCommitOwner", q(witness["commit_owner"])),
        ("witnessCommitDelegate", q(witness["commit_delegate"])),
        ("witnessAssuranceProvider", q(witness["assurance_provider"])),
        ("witnessAssurancePosition", q(witness["assurance_position"])),
        ("witnessPreventionControllers", tla_set(witness["prevention_controllers"])),
        ("witnessUnavailableProviders", tla_set(witness["unavailable_providers"])),
        ("witnessPersistentObserve", "WitnessPersistentObserve"),
        ("witnessPersistentEvidence", tla_value(witness["persistent_evidence"])),
        ("witnessRecoveryAvailable", tla_value(witness["recovery_available"])),
        ("witnessActiveStates", tla_set(witness["active_states"])),
        ("witnessClosedStates", tla_set(witness["closed_states"])),
        ("witnessProgressSteps", tla_set(witness["progress_steps"])),
        ("witnessOtherSteps", tla_set(witness["other_steps"])),
        ("witnessHandoffSteps", tla_set(witness["handoff_steps"])),
        ("witnessRankBound", tla_value(witness["rank_bound"])),
        ("witnessRank", "WitnessRank"),
        ("witnessFairnessOwners", tla_set(witness["fairness_owners"])),
        ("witnessFairnessOwner", q(witness["fairness_owner"])),
        ("witnessFairnessOwnerOf", "WitnessFairnessOwnerOf"),
    ]
    parts.append("Derivation ==\n    [")
    for index, (name, value) in enumerate(fields):
        prefix = "" if index == 0 else "     "
        suffix = "," if index + 1 < len(fields) else "]"
        parts.append(f"{prefix}{name} |-> {value}{suffix}\n")
    parts.append("\n====\n")
    return "".join(parts)


def expected_outputs() -> dict[pathlib.Path, bytes]:
    outputs: dict[pathlib.Path, bytes] = {}
    sources = sorted(RECORD_ROOT.glob("*.json"))
    if not sources:
        raise ValueError("no derivation records found")
    for source in sources:
        record = json.loads(source.read_text(encoding="utf-8"))
        validate_record(record, source)
        output = GENERATED_ROOT / f"{record['module']}DerivationData.tla"
        if output in outputs:
            raise ValueError(f"duplicate generated output {output.name}")
        outputs[output] = generate_tla(record).encode("utf-8")
    return outputs


def check_contract(root: pathlib.Path | None = None) -> str:
    if root is not None and root.resolve() != ROOT.resolve():
        raise ValueError("derivation generator root disagrees with requested root")
    outputs = expected_outputs()
    stale = [path for path, content in outputs.items() if not path.is_file() or path.read_bytes() != content]
    if stale:
        names = ", ".join(path.relative_to(ROOT).as_posix() for path in stale)
        raise ValueError(f"stale generated derivation data: {names}")
    digest = hashlib.sha256(b"".join(outputs[path] for path in sorted(outputs))).hexdigest()
    return f"DERIVATION_ARTIFACT_CONTRACT|records={len(outputs)}|sha256={digest}"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true", help="fail if generated outputs differ")
    args = parser.parse_args()
    try:
        outputs = expected_outputs()
        if args.check:
            check_contract()
        else:
            GENERATED_ROOT.mkdir(parents=True, exist_ok=True)
            for path, content in outputs.items():
                path.write_bytes(content)
    except (OSError, ValueError, TypeError, json.JSONDecodeError) as error:
        print(f"derivation_artifacts: FAIL: {error}", file=sys.stderr)
        return 1
    mode = "checked" if args.check else "generated"
    print(f"derivation_artifacts: PASS ({mode}; records={len(outputs)})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
