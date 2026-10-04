"""Root metadata gate after FULL reads; does not execute mathematical code."""
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path

B = Path(r"D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002")
C = B / ".arbor/sessions/parity/.coordinator"
OWN = B / "round20/role6_friable"
PREP = OWN / "preparation.json"
PREP_SHA = "d1f36f2dc00c2d5d26a44e226471fa1ed9bc221f71cdecf661aba0bd174b759a"

def sha(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as f:
        for block in iter(lambda: f.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()

assert sha(PREP) == PREP_SHA
prep = json.loads(PREP.read_text(encoding="utf-8"))
assert prep["status"] == "PREPARED_FULL_NEW_FRIABLE20_UNSTARTED_ROOT_GATE_CLOSED"
assert (prep["round"], prep["role"], prep["node"], prep["attempt"]) == (20, 6, "14.5", 1)
assert len(prep["code_sha256"]) == 7 and len(prep["frozen_input_sha256"]) == 18
for name, expected in prep["code_sha256"].items():
    assert sha(prep["source_paths"][name]) == expected, name
for path, expected in prep["frozen_input_sha256"].items():
    assert sha(path) == expected, path
assert sha(prep["runtime"]) == prep["runtime_sha256"]
assert not (OWN / "canonical_attempt01").exists()
assert not (OWN / "canonical_attempt01_reserved.json").exists()
assert not (B / "round20/friable.json").exists()
gate = dict(prep["required_authorization_fields"])
gate["preparation_sha256"] = PREP_SHA
gate.update({
    "authorized_at_utc": datetime.now(timezone.utc).isoformat(),
    "status": "ROOT20_FRIABLE_UNIQUE_NEW_CANONICAL_AUTHORIZED_AFTER_FULL_READ",
    "full_root_read_chunks": {
        "friable_checks.py": "df020a", "bank.py": "dc0139",
        "core.py": "b7eae1", "annexes.py": "24e1dc",
        "outward.py": "dc8689", "arithmetic.py": "ddaf18",
        "run_once.py": "e69904", "preparation.json": "4ef435"},
    "code_bindings_verified": 7, "frozen_input_bindings_verified": 18,
    "runtime_hash_verified": True,
    "authorized_launcher_command": prep["future_launcher_command"],
    "canonical_attempts_authorized": 1, "routine_replay_authorized": False,
    "root_numeric_execution": False, "root_lean_execution": False,
    "child_imports": "Only new PREEXEC snapshot modules, UTF8, -B, PYTHONNOUSERSITE",
    "actual_review": [
        "All1001 integerq and allperq e1..cap beforeprime andfriable masks; overflow recorded",
        "Actual ResourceCell/nonSS/strata, repeated factor multiset and real prefix divisor",
        "OriginalQ and exact strict R; allnew mu/phi/SPF1..Q; W coefficients retained by exact prefix and zero-term removal",
        "Actual D/wholeUa/cofactor vectors; no mu-squared mask on raw vonMangoldt firstaxis",
        "All F1 reciprocal q once; outer-mu-zero resources and tau retained; m0 firstaxis zeros recorded",
        "F0minusF1 nonfriablem1 explicitly unpaid; theta/raw alternative absolute unions without double consumption",
        "Actual affine classes including nonunits, literalplus1, empty e windows and observed-divisor/sourceBand distinction",
        "All2401 finite Euler exponenttuples, full1..64/112 integers, positive infinite tails distinct",
        "All4096 finite totient identities, exact exchange and telescope; no finite source-payment certification",
        "Directed integer 128bit atanh48 + positive tail, exact coefficient signs/zeros, no floats/unresolved nonzero kernels",
        "Concrete falsifiers/NONE_IN_DOMAIN; sourceY1 and undefined sigma explicitly separate from Ytest4096",
        "Exclusive PREEXEC captures, realSTART/binarylog/exit, failure evidence retained, no automatic retries"
    ],
    "author_compiler_gate": "STILL_CLOSED_UNTIL_ACTUAL_CANONICAL_PASS_ROOT_OBSERVED",
    "source_budget_certified": False, "victory": False,
})
path = Path(prep["required_authorization_path"])
assert path == C / "messages/round20_friable_authorization.json"
with path.open("x", encoding="utf-8", newline="\n") as f:
    json.dump(gate, f, ensure_ascii=False, indent=2)
    f.write("\n")
cp_path = C / "checkpoint.json"
cp = json.loads(cp_path.read_text(encoding="utf-8"))
cp["phase"] = "ROUND20_FRIABLE_UNIQUE_NUMERIC_GATE_OPEN_COMPOSITE_AND_COMPILERS_CLOSED"
cp["last_progress"] += " Root FULL friable bankdc0139/coreb7eae1/annex24e1dc/outwarddc8689/entrydf020a/lancee69904/prep4ef435;7codes18inputs/runtime hashes verified. One new14.5 canonicalattempt01 authorized; no actual mathematicalSTART observed yet, no compile authorization, noWin."
for item in cp["in_flight_executors"]:
    if item["role"] == 6:
        item["status"] = "FRIABLE14.5_ONE_NEW_NUMERIC_AUTHORIZED_COMPOSITE13.12_GATE_CLOSED"
cp.setdefault("artifacts", []).append(".arbor/sessions/parity/.coordinator/messages/round20_friable_authorization.json")
cp_path.write_text(json.dumps(cp, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"gate": str(path), "sha256": sha(path), "verified_codes": 7,
                  "verified_inputs": 18, "authorized_canonical_attempts": 1,
                  "root_numeric_executions": 0, "root_lean_executions": 0, "victory": False}))
