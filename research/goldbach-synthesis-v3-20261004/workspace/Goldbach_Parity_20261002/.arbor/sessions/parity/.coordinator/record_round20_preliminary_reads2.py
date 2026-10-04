"""Coordinator metadata only: record mutable-source reads, no math execution."""
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path

B = Path(r"D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002")
C = B / ".arbor/sessions/parity/.coordinator"
entries = [
    ("round20/role6_composite/outward.py", "dc8689", "9823d58d56a8854759cd05268c9fe4fe80b9943b34b190dd129618abbf1b43a8"),
    ("round20/role6_friable/core.py", "fd3028", "11f76ce3016df6afaa8fd802bd3e0ed4c57209b63febc7d0c6a9e0684ccd1cb3"),
    ("round20/role6_friable/annexes.py", "24e1dc", "76c3f1339a4042301d198abf547b3958a274e6f90ed9e63ac01256ad78167868"),
    ("round20/role3/SwitchedIncidenceEstimator.lean", "79016e", "ab1de7a846cab542b94b891f68671760492bd44ae19366f09862f72013f65301"),
    ("round20/role4/FriablePrimeHarmonic.lean", "332e29", "6b2920aba4d5f43a5990e415c7fd59e9407c1ef7ec29b49c5b2678377217caaf"),
    ("round20/role3/PhysicalCompositeSubtraction.lean", "f4060c", None),
    ("round20/role4/FriablePhysicalPrefix.lean", "5de128", None),
]
observations = []
for relative, chunk, earlier in entries:
    data = (B / relative).read_bytes()
    current = hashlib.sha256(data).hexdigest()
    observations.append({"path": relative, "full_root_read_chunk": chunk,
                         "bytes_observed": len(data), "sha256_observed_now": current,
                         "earlier_postread_sha256": earlier,
                         "same_as_earlier_postread_hash": None if earlier is None else current == earlier,
                         "source_mutable_before_first_execution": True})
out = C / "messages/round20_preliminary_root_reads2.json"
receipt = {"round": 20, "actual_time_utc": datetime.now(timezone.utc).isoformat(),
           "status": "PRELIMINARY_READ_ONLY_NOT_EXECUTION_AUTHORIZATION",
           "observations": observations, "root_mathematical_execution": False,
           "root_lean_execution": False, "root_numeric_execution": False,
           "compiler_gates": "CLOSED", "numeric_gates": "CLOSED", "victory": False}
with out.open("x", encoding="utf-8", newline="\n") as f:
    json.dump(receipt, f, ensure_ascii=False, indent=2)
    f.write("\n")
print(json.dumps({"path": str(out), "sha256": hashlib.sha256(out.read_bytes()).hexdigest(),
                  "observations": len(observations),
                  "changed_since_earlier_hash": [r["path"] for r in observations if r["same_as_earlier_postread_hash"] is False],
                  "executions": {"math": 0, "lean": 0, "numeric": 0}, "victory": False}))
