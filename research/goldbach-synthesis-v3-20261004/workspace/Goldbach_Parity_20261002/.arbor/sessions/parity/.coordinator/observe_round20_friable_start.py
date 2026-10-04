"""Read-only START and snapshot byte audit; no mathematical computation."""
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path

B = Path(r"D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002")
C = B / ".arbor/sessions/parity/.coordinator"
OWN = B / "round20/role6_friable"
OUT = OWN / "canonical_attempt01"

def sha(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as f:
        for block in iter(lambda: f.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()

start_path = OUT / "started.json"
start = json.loads(start_path.read_text(encoding="utf-8"))
prep_path = OWN / "preparation.json"
prep = json.loads(prep_path.read_text(encoding="utf-8"))
gate_path = C / "messages/round20_friable_authorization.json"
gate = json.loads(gate_path.read_text(encoding="utf-8"))
assert (start["round"], start["role"], start["node"], start["attempt"]) == (20, 6, "14.5", 1)
assert start["authorization"] == gate["authorization"]
assert sha(gate_path) == start["root_authorization_sha256"]
assert sha(prep_path) == gate["preparation_sha256"]
assert start["launcher_command"] == prep["future_launcher_command"]
assert start["subprocess_command"] == [prep["runtime"], "-B", "-X", "utf8", str(OUT / "inputs/friable_checks.py")]
assert start["cwd"] == str(OUT)
assert start["environment_changes"]["PYTHONPATH"] == str(OUT / "inputs")
assert sha(start["runtime"]) == start["runtime_sha256"] == prep["runtime_sha256"]
manifest_path = Path(start["input_manifest_path"])
assert sha(manifest_path) == start["input_manifest_sha256"]
manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
assert manifest["phase"] == "PREEXEC" and manifest["all_captures_before_child_start"] is True
assert manifest["bindings"] == start["captures_preexec"]
assert len(start["captures_preexec"]) == 27
captures = []
for name, record in start["captures_preexec"].items():
    snapshot = Path(record["snapshot"])
    assert snapshot.is_relative_to(OUT / "inputs"), str(snapshot)
    assert sha(snapshot) == record["sha256"] == sha(record["original"]), name
    assert snapshot.stat().st_size == record["bytes"], name
    captures.append({"name": name, **record, "snapshot_and_current_original_bytes_verified": True})
observation = {
    "round": 20, "node": "14.5", "observed_at_utc": datetime.now(timezone.utc).isoformat(),
    "status": "ACTUAL_NEW_CANONICAL_START_OBSERVED_NO_FINISH_VERDICT",
    "actual_started_at_utc": start["started_at_utc"], "started_path": str(start_path),
    "started_sha256": sha(start_path), "authorization_sha256": sha(gate_path),
    "manifest_sha256": sha(manifest_path), "captures_verified": captures,
    "capture_count": len(captures), "runtime_hash_verified": True,
    "actual_subprocess_command": start["subprocess_command"],
    "root_mathematical_execution": False, "root_lean_execution": False,
    "exit_code_observed": None, "numeric_pass_observed": False,
    "compiler_gate": "CLOSED_PENDING_ACTUAL_CANONICAL_PASS", "victory": False,
}
path = C / "messages/round20_friable_start_root_observation.json"
with path.open("x", encoding="utf-8", newline="\n") as f:
    json.dump(observation, f, ensure_ascii=False, indent=2)
    f.write("\n")
cp_path = C / "checkpoint.json"
cp = json.loads(cp_path.read_text(encoding="utf-8"))
cp["phase"] = "ROUND20_FRIABLE_ACTUAL_NEW_NUMERIC_RUNNING_COMPILERS_CLOSED"
cp["last_progress"] += " Actual friable20 canonical START and27PREEXEC captures/rootgate/runtime metadata verified; no numericPASS/finish or compiler gate yet. Root no mathematical execution."
cp_path.write_text(json.dumps(cp, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"path": str(path), "sha256": sha(path), "actual_start": start["started_at_utc"],
                  "captures_verified": 27, "numeric_pass_observed": False, "victory": False}))
