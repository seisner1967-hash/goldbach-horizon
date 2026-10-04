"""Record frozen source and annex byte bindings, no proof or producer execution."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path

B = Path(r"D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002")
C = B / ".arbor/sessions/parity/.coordinator"
W = B / "round20/role3"
F = B / "round20/role6_friable"
def sha(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()

prep_path = W / "preparation.json"
assert sha(prep_path) == "37c3275b9daff66e8734905be5f6f983ed610ad6f3a51d62e12835a1af87c72e"
prep = json.loads(prep_path.read_text(encoding="utf-8"))
assert sha(W / "build_once.py") == prep["launcher_sha256"] == "323fbb9474088a8b09d909815653cfc3137b8c5623c2f5fb94556cbb0433c7d3"
reads = {
    "OddBonferroniArithmetic": "92ffce", "LeastFactorComposite": "9c74aa",
    "SwitchedSelbergWeight": "164dad", "PhysicalCompositeSubtraction": "82952e",
    "CompositeAPConductor": "f6899b", "SwitchedIncidenceEstimator": "00230b",
}
assert len(prep["written_modules"]) == 6
for module in prep["written_modules"]:
    assert sha(B / module["path"]) == module["sha256"]
for relative, expected in prep["historical_dependencies_sha256"].items():
    assert sha(B / relative) == expected, relative
assert len(prep["historical_dependencies_sha256"]) == 16
for relative, expected in prep["paper_inputs_sha256"].items():
    assert sha(B / relative) == expected, relative
assert not (W / "build_receipt.json").exists()
manifest_path = F / "final_manifest.json"
assert sha(manifest_path) == "1ae836273667f20ea28b3e9bd35cc81e17c1d55ac523ecc165376caffb4425ba"
manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
assert len(manifest["sha256"]) == manifest["binding_count"] == 65
for path, expected in manifest["sha256"].items():
    assert sha(path) == expected, path
assert sha(F / "final.md") == "fea1dca1f27eb517f87b09d65455ba98e2e8b26fade6f3623cea5ebda1392c9d"
assert sha(F / "final_receipt.json") == "aaf671b7f891cd5d7f1337e5df4695852bc4d6843f0b087610054229a072d3bd"
obs = {
    "round": 20, "observed_at_utc": datetime.now(timezone.utc).isoformat(),
    "formal3": {"status": "CURRENT_SIX_SOURCE_FULL_READ_COMPILER_GATE_CLOSED",
        "node": "13.12", "preparation_full_root_read": "abb4d2", "launcher_full_root_read": "46a8a7",
        "preparation_sha256": sha(prep_path), "launcher_sha256": sha(W / "build_once.py"),
        "modules": [{**m, "full_root_read_chunk": reads[m["module"]]} for m in prep["written_modules"]],
        "historical_readonly_bindings_verified": 16,
        "written_defs_not_PASS_counts": sum(m["definitions"] for m in prep["written_modules"]),
        "written_thms_not_PASS_counts": sum(m["theorems"] for m in prep["written_modules"]),
        "written_prints_not_compiler_audits": sum(m["axiom_prints"] for m in prep["written_modules"]),
        "actual_lean_executions": 0, "canonical_composite_numeric_pass_observed": False,
        "scope_correction_is_preEXEC_static_not_real_Lean_failure": True,
        "unpaid_obligations": prep["semantic_limits"]},
    "friable_final_annex": {"status": "FINAL_FINITE_ANNEX_BINDINGS_VERIFIED_NOT_GLOBAL_ROLE6",
        "report_full_root_read": "46cd4b", "receipt_full_root_read": "706605",
        "manifest_full_root_read": "c2d124", "manifest_sha256": sha(manifest_path),
        "receipt_sha256": sha(F / "final_receipt.json"), "report_sha256": sha(F / "final.md"),
        "bindings_verified": 65, "all_are_stored_bytes_no_math_reexecution": True},
    "root_mathematical_execution": False, "root_lean_execution": False, "victory": False,
}
path = C / "messages/round20_formal3_source_and_friable_final_root_observation.json"
with path.open("x", encoding="utf-8", newline="\n") as stream:
    json.dump(obs, stream, ensure_ascii=False, indent=2)
    stream.write("\n")
cp_path = C / "checkpoint.json"
cp = json.loads(cp_path.read_text(encoding="utf-8"))
for item in cp["in_flight_executors"]:
    if item["role"] == 3:
        item["status"] = "SIX_CURRENT_SOURCES_FULL_REVIEWED_AWAITING_NEW_COMPOSITE_BANK_PASS_NO_LEAN"
cp["last_progress"] += " Root6Role3 FULL92ffce/9c74aa/164dad/82952e/f6899b/00230b andlauncher46a8a7/prepabb4d2,6source16readonlybindings verified.50defs91thms141prints onlywritten, noLean. Friable FINALannex65bindings verifiedFULL46cd4b/706605/c2d124. GlobalROLE6/compositepending, noWin."
cp_path.write_text(json.dumps(cp, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"path": str(path), "sha256": sha(path), "source_bindings": 6,
                  "readonly_dependencies": 16, "friable_final_bindings": 65,
                  "formal3_compiler_gate": "CLOSED", "victory": False}))
