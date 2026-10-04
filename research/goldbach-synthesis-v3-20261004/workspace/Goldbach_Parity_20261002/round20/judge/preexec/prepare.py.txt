"""Metadata-only freezer: never calls subprocess or a mathematical producer."""
import sys
sys.dont_write_bytecode = True
import ast
from collections import Counter
from pathlib import Path
import audit

HERE, ROUND, BASE = audit.HERE, audit.ROUND, audit.BASE
ROOT_OBSERVATION = BASE / ".arbor/sessions/parity/.coordinator/messages/round20_author_finals_root_observation.json"
ROOT_OBSERVATION_SHA = "715e6db355426a2da9f013a6107423886811e03cd815301701d20bbf5bd87ba1"


def add(bindings, path, expected=None):
    path = Path(path).resolve()
    digest = audit.sha(path)
    if expected is not None:
        assert digest == expected, ("frozen_binding_changed", str(path))
    name = path.relative_to(BASE).as_posix() if path.is_relative_to(BASE) else str(path)
    assert name not in bindings or bindings[name] == digest
    bindings[name] = digest


def main():
    assert not (HERE / "preparation.json").exists(), "No preparation overwrite"
    assert not (HERE / "audit_started.json").exists()
    assert audit.sha(ROOT_OBSERVATION) == ROOT_OBSERVATION_SHA
    root = audit.load(ROOT_OBSERVATION)
    final_inputs = {}
    for name, digest in root["checked_bindings"].items():
        add(final_inputs, name, digest)
    add(final_inputs, ROOT_OBSERVATION, ROOT_OBSERVATION_SHA)
    required = ["agent1_switched_composite.md", "agent2_friable.md", "agent3_formalisation.md",
                "agent4_formalisation.md", "agent4_geometry_final.md", "role6/final.md",
                "role1/final_receipt.json", "role2/final_receipt.json", "role3/final_receipt.json",
                "role3/final_manifest.json", "role4/final_receipt.json", "role4/output_manifest.json",
                "role4_geometry/geometry_final_receipt.json", "role6/final_receipt.json",
                "role6/final_manifest.json", "ideation_failure_feedback20_final.md",
                "role12_feedback/final_receipt.json", "role12_feedback/final_manifest.json"]
    for name in required:
        add(final_inputs, ROUND / name)
    geometry = audit.load(ROUND / "role4_geometry/geometry_final_receipt.json")
    for name, digest in geometry["bindings"].items():
        add(final_inputs, ROUND / "role4_geometry" / name, digest)
    p3 = audit.load(ROUND / "role3/preparation.json")
    final3 = audit.load(ROUND / "role3/final_manifest.json")
    final4 = audit.load(ROUND / "role4/final_receipt.json")
    assert final3["actual_lean_exit_zero"] == 6 and final3["victory"] is False
    assert final4["logical_ROLE4_total_PASS"] == 10 and final4["victory"] is False
    historical = dict(p3["historical_dependencies_sha256"])
    for name, digest in audit.load(ROUND / "role4/dependencies_readonly.json")["bindings"].items():
        assert name not in historical or historical[name] == digest
        historical[name] = digest
    audit.verify(historical)
    historical_modules = {}
    for relative, digest in historical.items():
        if relative.endswith(".lean"):
            olean = str(Path(relative).with_suffix(".olean")).replace("\\", "/")
            assert olean in historical
            historical_modules[Path(relative).stem] = {"source": relative, "source_sha256": digest,
                "olean": olean, "olean_sha256": historical[olean]}
    order = ["round20/role3/" + name + ".lean" for name in p3["new_module_order"]]
    order += ["round20/role4/" + name + ".lean" for name in
              ("FriablePhysicalPrefix", "FriableEulerRankin", "FriableKernelEnvelope", "FriablePrimeHarmonic",
               "FriableTotientEnvelope", "FriablePhysicalPayment", "FriablePhysicalDemand",
               "FriableDemandAggregation")]
    order += ["round20/role4_geometry/FriableSourceGeometry.lean", "round20/role4/FriableSourceBudget.lean"]
    assert len(order) == len(set(order)) == 16
    specs, source_hashes, counts, built = {}, {}, Counter(), set()
    author_sources = {row["source"]: row["source_sha256"] for row in final3["modules"]}
    author_sources.update({Path(row["source"]).relative_to(BASE).as_posix(): row["source_sha256"]
                           for row in final4["successful_modules"]})
    for relative in order:
        source = audit.bound(relative)
        spec = audit.declarations(source)
        assert spec["source_sha256"] == author_sources[relative]
        specs[relative], source_hashes[relative] = spec, spec["source_sha256"]
        for dependency in spec["imports"]:
            assert dependency == "Mathlib" or dependency.startswith("Mathlib.") or dependency in built or dependency in historical_modules
        built.add(source.stem)
        counts.update(spec["declaration_counts"])
    numeric = audit.load(ROUND / "role6/final_manifest.json")["sha256"]
    assert len(numeric) == 677
    audit.verify(numeric)
    registry = audit.load(ROUND / "previous_artifacts_sha256.json")
    previous = registry["sha256"]
    assert len(previous) == registry["file_count"] == 1808
    audit.verify(previous)
    add(final_inputs, ROUND / "previous_artifacts_sha256.json")
    runtime = {}
    for name in (p3["python_executable"], p3["lean_executable"], p3["mathlib_HEAD_path"]):
        add(runtime, name)
    ml = Path(p3["mathlib_HEAD_path"]).parent.parent
    add(runtime, ml / "Mathlib.lean", p3["mathlib_root_source_sha256"])
    add(runtime, ml / ".lake/build/lib/Mathlib.olean", p3["mathlib_root_olean_sha256"])
    code_hashes = {}
    for name in ("audit.py", "run_once.py", "prepare.py"):
        ast.parse((HERE / name).read_text(encoding="utf-8"), filename=name)
        code_hashes[name] = audit.sha(HERE / name)
    banks = {}
    for bank in ("friable", "composite"):
        receipt = audit.load(ROUND / ("role6_" + bank) / "canonical_attempt01/receipt.json")
        assert receipt["exit_code"] == 0 and receipt["routine_replays"] == 0
        assert receipt["canonical_subprocess_count"] == 1 and receipt["after_preservation_pass"] is True
        result = "round20/" + bank + ".json"
        assert audit.sha(audit.bound(result)) == receipt["result_sha256"]
        banks[bank] = {"result": result, "canonical_receipt": "round20/role6_" + bank + "/canonical_attempt01/receipt.json",
                       "exit_field": "exit_code", "result_hash_field": "result_sha256",
                       "status": "PASS_NEW_" + bank.upper() + "20_FINITE_IDENTITIES_SOURCE_GUARDS_FALSE"}
    hist_dirs = sorted({str(audit.bound(name).parent) for name in historical if name.endswith(".olean")}, reverse=True)
    prep = {"status": "READY_AFTER_ALL_FROZEN_FINALS_NOT_EXECUTED", "round": 20, "role": 5,
            "prepared_utc": audit.now(), "all_required_FINALs_frozen": True,
            "new_module_count": 16, "new_module_source_order": order,
            "new_module_sources_sha256": source_hashes, "module_specifications": specs,
            "static_explicit_declaration_counts_NOT_independent_PASS": dict(counts),
            "static_axiom_print_count_NOT_independent_PASS": sum(len(row["requested_axiom_prints"]) for row in specs.values()),
            "final_input_sha256": final_inputs, "historical_dependencies_sha256": historical,
            "historical_module_sources": historical_modules, "historical_library_dirs": hist_dirs,
            "cache_library_dirs": p3["cache_library_dirs"], "numeric_frozen_sha256": numeric,
            "previous_artifacts_sha256": previous, "original_documents_sha256": p3["original_documents_sha256"],
            "runtime_bindings_sha256": runtime, "python_executable": p3["python_executable"],
            "python_sha256": p3["python_sha256"], "lean_executable": p3["lean_executable"],
            "lean_sha256": p3["lean_sha256"], "compiler_version_metadata": "Lean4.15.0 commit11651562caae; mathlib9837ca9d65d9de6fad1ef4381750ca688774e608; no version-probe invocation",
            "judge_code_sha256": code_hashes, "numeric_banks": banks,
            "author_build_ledgers": ["round20/" + name for name in
                ("role3/build_receipt.json", "role4/build_receipt.json", "role4/extension_build_receipt.json",
                 "role4/aggregation_build_receipt.json", "role4/source_budget_build_receipt.json",
                 "role4_geometry/geometry_build_receipt.json")],
            "semantic_obligations": ["B6 variation/endpoints and source AP window bijection unproved",
                "SD and effective BV/source constants unproved", "principal source comparison and weighted aggregation unproved",
                "M0 in reference_price is arbitrary, not a proved source reference bridge",
                "F0 minus F1 nonfriable reciprocal unpaid", "H19 to whole source support bridge unproved",
                "full ledger, singletons/e1/p0/faces/nonbulk/medium/long/Gamma/TA/capacities unpaid",
                "no parity bypass and no global D_N target theorem"],
            "author20_oleans_in_LEAN_PATH": False, "actual_independent_Lean_invocations": 0,
            "new_mathematical_python_invocations": 0, "numeric_producer_or_sign_replays": 0,
            "score": 0, "victory": False}
    audit.exclusive(HERE / "preparation.json", prep)
    audit.exclusive(HERE / "preparation_metadata_receipt.json", {"status": "PREPARATION_METADATA_ONLY",
        "finished_utc": audit.now(), "preparation_sha256": audit.sha(HERE / "preparation.json"),
        "judge_code_sha256": code_hashes, "new_module_count": 16, "static_counts": dict(counts),
        "new_compiler_or_mathematical_execution": False})
    print({"preparation_sha256": audit.sha(HERE / "preparation.json"), "code_sha256": code_hashes,
           "static_counts": dict(counts), "final_bindings": len(final_inputs), "historical_bindings": len(historical),
           "numeric_bindings": len(numeric), "previous_bindings": len(previous), "compiled": False})


if __name__ == "__main__":
    main()
