"""Metadata preparation only, after independent reading of every frozen FINAL.

No Lean, audit, producer, kernel, numerical computation or replay is launched.
This script cannot authorize the later Judge canonical attempt.
"""
import sys
sys.dont_write_bytecode = True
import hashlib
import json
import re
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROUND = HERE.parent
BASE = ROUND.parent
COORDINATOR = BASE / ".arbor/sessions/parity/.coordinator"
PYTHON = Path(r"C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe")
LEAN = Path(r"C:\Users\Utilisateur\.elan\toolchains\leanprover--lean4---v4.15.0\bin\lean.exe")
CACHE = Path(r"D:\Users\Utilisateur\Desktop\Maths\q356-canonical-binding-replay\.lake\packages")
AUDIT_SHA = "8aabf796e9ec5cf135ab5c1bf76f9f3eb791e02b9f681153c7216e30df967117"
LAUNCHER_SHA = "f7e22678da62c0fb1613c463bf5cb9f539e2cec88cf2db869b63c533486e36bd"
PYTHON_SHA = "4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c"
LEAN_SHA = "8a1ef18583d74d917194bba4743ce9765bad64b00c52bada002ee44796fb9e08"
MODULES = [
    "role3/RankCalibrationFace.lean",
    "role3/RankCalibrationPrice.lean",
    "role3/RankCalibrationArithmetic.lean",
    "role3/RankCalibrationUnitLoss.lean",
    "role3/RankCalibrationEuler.lean",
    "role3/RankCalibrationEstimator.lean",
    "role4/TerminalPrimeExtraction.lean",
    "role4/BalancedResourceSwitch.lean",
    "role4/SignedHyperbolicCRT.lean",
    "role4/NonSSBracketSwitch.lean",
    "role4/RankTwoHarmonic.lean",
]
FINAL_RECEIPTS = ["role1/final_receipt.json", "role2/final_receipt.json",
                  "role3/final_receipt.json", "role4/final_receipt.json",
                  "role6_nonss/final_receipt.json", "role6_rank/final_receipt.json",
                  "role1_gap_review/final_receipt.json"]
ROOT_OBSERVATIONS = [
    "messages/round19_judge_content_plan.md",
    "messages/round19_nonss_finish_root_observation.json",
    "messages/round19_rank_finish_root_observation.json",
    "messages/round19_final4_root_observation.json",
    "messages/round19_final3_root_observation.json",
    "messages/round19_formal3_compile_authorization.json",
]
GAPS = [
    "Actual real IE coefficient and rankMainMass positivity are validated on guarded paper only; not formally proved by these Lean modules or supplied free.",
    "Face P=1771 requires gcd(P,N)=1 and is not a covering theorem for all even N.",
    "NonSS reindexings retain the declared composite ResourceCell guards; full original support including prime/singleton and e1/p0 incidence cases still needs its ledger bridge.",
    "K14 and conversion to ordinary unmasked APs, N exceptions and source endpoints remain open.",
    "A single expansion multiplicity <=32 does not alone discharge the combined AP families <=40/64.",
    "K18 with constants and onset BV, aggregate analytic errors and Gamma_rank remain open.",
    "The medium and long channels remain literal sums; they have not been quantitatively paid.",
    "New composite rho/Selberg source, analytic H7/H9 and written local rank3short onset 10^40 remain open.",
    "Fixed source onset 10^24 and segment 10^24..10^40 are preserved and not discharged.",
    "Ranks >=4, T_A, parent comparisons, unique physical capacities and full fixed D_N ledger remain open.",
    "Neither the finite signs nor a negative principal price give the required D_N target.",
]


def sha(path):
    value = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1 << 20), b""):
            value.update(block)
    return value.hexdigest()


def load(path):
    return json.loads(Path(path).read_text(encoding="utf-8-sig"))


def relative(path):
    path = Path(path).resolve()
    assert path.is_relative_to(BASE.resolve()) and path.is_file()
    return path.relative_to(BASE).as_posix()


def main():
    assert sys.argv[1:] == ["--metadata-freeze-after-full-FINAL-review"]
    assert not (HERE / "preparation.json").exists()
    assert not (HERE / "authorization.json").exists()
    assert not (HERE / "audit_started.json").exists()
    assert sha(HERE / "audit.py") == AUDIT_SHA
    assert sha(HERE / "run_once.py") == LAUNCHER_SHA
    assert sha(PYTHON) == PYTHON_SHA and sha(LEAN) == LEAN_SHA
    reviews = load(HERE / "final_read_review.json")
    assert reviews["status"] == "ALL_REQUIRED_FINALS_FULLY_READ_METADATA_ONLY"
    assert reviews["Judge_audit_Lean_probe_invocations"] == 0
    module_order = [relative(ROUND / item) for item in MODULES]
    source_hashes = {item: sha(BASE / item) for item in module_order}
    assert reviews["final_new_source_sha256"] == source_hashes
    for item in FINAL_RECEIPTS:
        receipt = load(ROUND / item)
        assert "FINAL" in receipt["status"], ("FINAL_receipt_absent", item)
        assert receipt.get("victory", False) is False
        assert sha(ROUND / item) == reviews["final_receipt_sha256"]["round19/" + item]
    inputs = {}
    for path in sorted(ROUND.rglob("*")):
        if not path.is_file() or path.is_relative_to(HERE) or path == ROUND / "agent5.md":
            continue
        assert "__pycache__" not in path.parts
        inputs[relative(path)] = sha(path)
    for item in ROOT_OBSERVATIONS:
        path = COORDINATOR / item
        inputs[relative(path)] = sha(path)
    for name in ("final_read_review.json", "PREPARATION_REVIEW.md", "freeze_inputs.py", "authorization_schema.json"):
        inputs[relative(HERE / name)] = sha(HERE / name)
    historical_dirs = [BASE / "round18/judge/build", BASE / "round16/judge/build",
                       BASE / "round13/role4/dependencies"]
    historical = {relative(path): sha(path) for directory in historical_dirs
                  for path in sorted(directory.iterdir()) if path.suffix in {".lean", ".olean"}}
    libs = [CACHE / name / ".lake/build/lib" for name in
            ("aesop", "batteries", "importGraph", "LeanSearchClient", "mathlib", "plausible", "proofwidgets", "Qq")]
    assert all(path.is_dir() for path in libs)
    head = CACHE / "mathlib/.git/HEAD"
    assert head.read_text(encoding="utf-8").strip() == "9837ca9d65d9de6fad1ef4381750ca688774e608"
    specs = {}
    for item in module_order:
        source = (BASE / item).read_text(encoding="utf-8")
        namespaces = re.findall(r"^namespace (GoldbachRound19\.[\w.]+)$", source, flags=re.M)
        assert len(namespaces) == 1, item
        namespace = namespaces[0]
        generated = [namespace + "." + name for name in
                     re.findall(r"^#print axioms (\w+\.ext)$", source, flags=re.M)]
        specs[item] = {"namespace": namespace, "generated_axiom_prints": generated}
    assert sum(len(value["generated_axiom_prints"]) for value in specs.values()) == 2
    launcher_failures = [relative(path) for path in sorted((ROUND / "role4").glob("launcher_failed*.json"))]
    numeric = {}
    for name, role, result, status in (
        ("nonss", "role6_nonss", "nonss.json", "PASS_NEW_FINITE_IDENTITIES_ONLY"),
        ("rank", "role6_rank", "allrang.json", "PASS_NEW_ALL_RANK_FINITE_IDENTITIES_ONLY"),
    ):
        numeric[name] = {"result": "round19/" + result,
                         "canonical_receipt": "round19/" + role + "/canonical_attempt01/receipt.json",
                         "final_receipt": "round19/" + role + "/final_receipt.json",
                         "exit_code_field": "exit_code", "result_sha256_field": "result_sha256",
                         "bindings_field": "bindings", "bindings_relative_to": "round19",
                         "required_stored_fields": {"status": status, "N": 100000000}}
    prep = {"status": "READY_AFTER_FROZEN_FINALS_NOT_EXECUTED", "round": 19, "role": 5,
            "prepared_utc": datetime.now(timezone.utc).isoformat(), "all_required_FINALs_frozen": True,
            "final_read_review_sha256": sha(HERE / "final_read_review.json"),
            "metadata_freezer_sha256": sha(Path(__file__)),
            "metadata_operation": "Hash and describe already frozen inputs only; no Judge or producer launch",
            "Judge_audit_Lean_probe_invocations_in_preparation": 0,
            "root_full_read_current_judge_sources_confirmed": True,
            "judge_source_delta_after_root_full_read": False,
            "judge_code_sha256": {"audit.py": AUDIT_SHA, "run_once.py": LAUNCHER_SHA},
            "final_input_sha256": inputs, "historical_dependencies_sha256": historical,
            "new_module_source_order": module_order, "new_module_sources_sha256": source_hashes,
            "new_module_count": len(module_order), "module_specifications": specs,
            "numeric_banks": numeric,
            "author_build_ledgers": ["round19/role3/build_receipt.json", "round19/role4/build_receipt.json"],
            "author_launcher_failure_receipts": launcher_failures,
            "historical_library_dirs": [str(path) for path in historical_dirs],
            "cache_library_dirs": [str(path) for path in libs], "mathlib_HEAD_path": str(head),
            "mathlib_HEAD_sha256": sha(head), "mathlib_commit": "9837ca9d65d9de6fad1ef4381750ca688774e608",
            "python_executable": str(PYTHON), "python_sha256": PYTHON_SHA,
            "lean_executable": str(LEAN), "lean_sha256": LEAN_SHA,
            "compiler_version_metadata": {"known_version": "Lean 4.15.0", "known_commit": "11651562caae",
                                          "historical_metadata_source": "round19/PROBE_BLOCK.md",
                                          "historical_metadata_source_sha256": sha(ROUND / "PROBE_BLOCK.md"),
                                          "new_version_probe_invocations": 0},
            "original_documents_sha256": load(BASE / "INPUT_HASHES.json"),
            "semantic_obligations": GAPS, "score": 0, "victory": False,
            "independent_audit_yet_executed": False, "root_unique_canonical_gate_required": True}
    with (HERE / "preparation.json").open("x", encoding="utf-8", newline="\n") as stream:
        stream.write(json.dumps(prep, ensure_ascii=False, sort_keys=True, indent=2) + "\n")
    print(json.dumps({"status": prep["status"], "preparation_sha256": sha(HERE / "preparation.json"),
                      "FINAL_input_files": len(inputs), "historical_source_olean_files": len(historical),
                      "new_modules": len(module_order), "Judge_Lean_audit_probes": 0}), flush=True)


if __name__ == "__main__":
    main()
