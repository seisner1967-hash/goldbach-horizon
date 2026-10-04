"""Coordinator metadata gate after actual FULL reads; no preflight execution."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json

B = Path(r"D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002")
C = B / ".arbor/sessions/parity/.coordinator"
R = B / "round20"
P = Path(r"C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe")
def sha(p):
    h = hashlib.sha256()
    with p.open("rb") as f:
        for b in iter(lambda: f.read(1048576), b""):
            h.update(b)
    return h.hexdigest()
fixed = {
    R / "conservation.py": "3ba33a73930680baea64af533cfa180472d2832f75ab14c85014b9084a894d28",
    R / "role6/run_conservation_once.py": "0922805c7ff3b609a8ae01685ac72c27d61c9bdceaa6d7bb151dd1708dec2921",
    R / "role6/preparation.json": "0a879e51e9b3460a298ff591b6e0b7ad4d34c3006283b1d8942d56f993b9cbf2",
    R / "previous_artifacts_sha256.json": "9f238497b57a2dc7e46e26a67cb5e6a468be8f4e6a73525449a87406304a36b5",
    R / "PROBE_BLOCK.md": "69df06d7abc3619ba51465b74912f6bf32a2f49f901d72533c4ba9945777685e",
    B / "round19/controller_manifest.json": "299a605efaa7cf6721e3b65bfea8af976bcbfcdbb1bc841eee6f4a0d9d9d4d08",
    B / "INPUT_HASHES.json": "5f3f8498fc1343b69ade24634d0253ec662c090641a852465e6b70059b005460",
    P: "4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c",
}
for p, expected in fixed.items():
    assert sha(p) == expected, str(p)
prep = json.loads((R / "role6/preparation.json").read_text(encoding="utf-8-sig"))
assert prep["status"] == "PREPARED_UNSTARTED_AWAITING_DISTINCT_ROOT_AUTHORIZATION"
assert prep["preflight_subprocess_invocations"] == 0
assert prep["Lean_executions"] == 0 and prep["mathematical_executions"] == 0
registry = json.loads((R / "previous_artifacts_sha256.json").read_text(encoding="utf-8-sig"))
assert registry["file_count"] == len(registry["sha256"]) == 1808
gate_path = C / "messages/round20_conservation_authorization.json"
assert not gate_path.exists()
assert not (R / "conservation.json").exists()
assert not (R / "role6/conservation_attempt01_started.json").exists()
gate = {
    "authorization": "ROOT20_CONSERVATION_AUTHORIZED_FULL_SOURCE_READ_CANONICAL_ATTEMPT01",
    "root_authorized": True, "round": 20, "role": 6, "attempt": 1,
    "all_preflight_sources_fully_read": True,
    "new_metadata_preflight_only": True,
    "source_sha256": fixed[R / "conservation.py"],
    "launcher_sha256": fixed[R / "role6/run_conservation_once.py"],
    "preparation_sha256": fixed[R / "role6/preparation.json"],
    "original_hash_map_sha256": fixed[B / "INPUT_HASHES.json"],
    "authorized_at_utc": datetime.now(timezone.utc).isoformat(),
    "actual_root_full_reads": {"source": "745788", "launcher": "8c8547", "preparation": "8f0294"},
    "metadata_checks": {str(p): digest for p, digest in fixed.items()},
    "historical_preflight_replay_authorized": False,
    "mathematical_or_Lean_execution_authorized": False,
    "victory": False,
}
with gate_path.open("x", encoding="utf-8", newline="\n") as f:
    json.dump(gate, f, indent=2, sort_keys=True, ensure_ascii=False)
    f.write("\n")
print(json.dumps({"gate": str(gate_path), "sha256": sha(gate_path), "status": "AUTHORIZED_NEW_METADATA_PREFLIGHT_ONLY", "protected_binding_count": 1808}, indent=2))
