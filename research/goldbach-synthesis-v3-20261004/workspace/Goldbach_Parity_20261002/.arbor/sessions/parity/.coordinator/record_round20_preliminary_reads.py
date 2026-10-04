"""Record preliminary source reads/metadata hashes; no compiler or producer."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
B = Path(r"D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002")
C = B / ".arbor/sessions/parity/.coordinator"
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
items = [
    ("round20/role3/OddBonferroniArithmetic.lean", "1632d0", "19744aea379a901c303e4b50611916f4d8ac81582914eef58cec64a0b1749693"),
    ("round20/role3/LeastFactorComposite.lean", "7232d2", "3da564e432950544344e52b9dae66cd6bf401abf323a7eb10e7d89897c9b5cc8"),
    ("round20/role3/SwitchedSelbergWeight.lean", "b368f9", "d729f7beeaf9d88cdb5f186281b7a6e5cde36176c5230fce0c4822d75e870be0"),
    ("round20/role3/PhysicalCompositeSubtraction.lean", "982f93", None),
    ("round20/role3/CompositeAPConductor.lean", "d1d3e8", None),
    ("round20/role4/FriablePhysicalPrefix.lean", "a76f69", "131db9e6bffb1cfb1ba374337dbdea8a55486f5f40c32d4c0f16e520f7fb4e71"),
    ("round20/role4/FriableEulerRankin.lean", "9b9f60", "5bed718fdb946c1e1574a6d4de3789e30397071f49089e5df1624e14ad38a9b1"),
    ("round20/role4/build.py", "88457b", "89dea53493843f1196bdcdb2fd8ad376649870db665b1e8aef532e1bd6c8616a"),
    ("round20/role4/preparation.json", "2fa47c", None),
    ("round20/role4/dependencies_readonly.json", "d5fd1f", "4c84a5c9851711c1acb44af92bf717b0cff39e4e752ff96d9e81b85e0543882d"),
    ("round20/role6_composite/outward.py", "9d5af0", "d1786c0583bd83572c36746e52d992e0c4b92eb826ad39bcd494c32eea16a41b"),
    ("round20/role6_composite/arithmetic.py", "ddaf18", "131a38a8bf82a46fbc954455d63b6de8ac3055b7b73199b1c555826d04f9cbbc"),
]
reads = [{"path": rel, "full_read_chunk": chunk, "earlier_postread_hash": expected, "current_observed_sha256": sha(B / rel), "matches_earlier_postread_hash": sha(B / rel) == expected if expected else None} for rel, chunk, expected in items]
deps = json.loads((B / "round20/role4/dependencies_readonly.json").read_text(encoding="utf-8-sig"))["bindings"]
for rel, digest in deps.items(): assert sha(B / rel) == digest, rel
out = C / "messages/round20_preliminary_root_reads.json"
record = {"status": "PRELIMINARY_WRITER_STAGE_READS_NOT_COMPILE_AUTHORIZATION", "observed_at_utc": datetime.now(timezone.utc).isoformat(), "reads": reads, "role3_independent_paper_review_full_chunk": "79a022", "role4_historical_bindings_checked": 18, "postread_digests_not_PREEXEC_attestation": True, "all_sources_may_still_be_written_before_first_compile": True, "Lean_PASS_count20": 0, "numeric_bank_executions20": 0, "compile_gates20_closed": True, "math_execution_by_root": False, "victory": False}
with out.open("x", encoding="utf-8", newline="\n") as f:
    json.dump(record, f, indent=2, ensure_ascii=False); f.write("\n")
print(json.dumps({"root_reads_receipt_sha256": sha(out), "preliminary_files": len(reads), "role4_historical_bindings_verified": len(deps), "staged_hash_changes": [r["path"] for r in reads if r["matches_earlier_postread_hash"] is False], "victory": False}, indent=2))
