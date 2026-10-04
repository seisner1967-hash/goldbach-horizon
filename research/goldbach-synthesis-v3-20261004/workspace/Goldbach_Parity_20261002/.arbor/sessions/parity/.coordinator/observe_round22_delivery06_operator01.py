"""ROOT metadata only: freeze documentary reads; no mathematical evaluation."""
import argparse
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path

BASE = Path(r"D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002")
COORD = BASE / ".arbor/sessions/parity/.coordinator"
BINDINGS = [
    ("round22/role3/continuous_contract_delivery22_revision06.txt", "13ef5696833c70422a7378239548916b503bf52d7e743fd0f3959fee7c101c8f", "c75da6"),
    ("round22/role3/continuous_contract_delivery22_revision06_read_receipts.json", "2f799d2b13c8758f9cd09dff16805a285a7d68fe88b083360298d57cf75488d7", "c75da6"),
    ("round22/role4/operator_phase_obstacle_paper01/operator_phase_obstacle22.md", "b6d745a1b01483582bebd7c46ebd48be2a77f522fec48fc7ac4a19fa78592346", "0a39c3"),
    ("round22/judge5/operator_phase_obstacle_source_review01.md", "a17c8482aa9f6fa32b90e325be72aa256e8392e8b2f3f5c7b79fb6582256a139", "0a39c3"),
]

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--ROOT-full-reads", required=True)
    args = parser.parse_args()
    checkpoint = COORD / "checkpoint.json"
    cp = json.loads(checkpoint.read_text(encoding="utf-8"))
    official = cp["official_auxiliary_validation"]
    assert (official["modules"], official["declarations"]) == (83, 1397)
    out = COORD / "messages/round22_delivery06_operator01_observation.json"
    assert not out.exists(), "Unique metadata observation already exists"
    bound = []
    for rel, expected, full in BINDINGS:
        path = BASE / rel
        data = path.read_bytes()
        actual = hashlib.sha256(data).hexdigest()
        assert actual == expected, rel
        bound.append({"path": str(path), "bytes": len(data), "sha256": actual, "ROOT_FULL": full})
    delivery = json.loads((BASE / BINDINGS[1][0]).read_text(encoding="utf-8-sig"))
    assert delivery["official_modules"] == 83 and delivery["official_auxiliary_declarations_including_definitions"] == 1397
    assert delivery["full_native_coefficient_N_result_present"] is False
    assert delivery["D_N"] is False and delivery["WIN"] is False
    obs = {
        "schema": "ROUND22_ROOT_DELIVERY06_OPERATOR01_DOCUMENTARY_OBSERVATION",
        "utc": datetime.now(timezone.utc).isoformat(),
        "ROOT_full_reads": args.ROOT_full_reads,
        "bindings": bound,
        "official_modules": 83, "official_auxiliary_declarations": 1397,
        "new_mathematical_credit": 0, "new_compiler_invocations": 0, "new_numeric_invocations": 0,
        "operator_review": "INDEPENDENT_PAPER_COHERENT_UNDER_EXPLICIT_DEBTS_NO_NEW_SUFFICIENT_SIGN",
        "numeric04_status": "CLOSED_STOP_NO_MATHEMATICAL_VERDICT",
        "numeric05_status": "CHECKER_ONLY_SOURCE_PREPARATION_NOT_EXECUTED",
        "mellin26_status": "TOOLS_SOURCE_PREPARATION_NOT_EXECUTED",
        "D_N": False, "WIN": False,
    }
    with out.open("x", encoding="utf-8") as stream:
        json.dump(obs, stream, ensure_ascii=False, indent=2)
        stream.write("\n")
    cp["continuous_contract_delivery06_operator01"] = obs
    cp["phase"] = "ROUND22_CHECKER05_AND_MELLIN26_SOURCE_ONLY"
    cp["in_flight_executors"] = [
        {"role": 3, "agent": "/root/round22_formal3_prepare", "status": "CHECKER05_PARENT_SOURCE_ONLY"},
        {"role": 4, "agent": "/root/round22_formal4_trace", "status": "CHECKER05_STATIC_REQUIREMENTS_SOURCE_ONLY"},
        {"role": 5, "agent": "/root/round22_judge5_independent", "status": "BATCH26_TOOLS_SOURCE_ONLY"},
    ]
    artifacts = cp.setdefault("artifacts", [])
    for rel in [x[0] for x in BINDINGS] + [str(out.relative_to(BASE))]:
        if rel not in artifacts:
            artifacts.append(rel)
    cp["last_progress"] = "Documentary revision06 and independent operator PAPER01 observed; official83/1397 unchanged. Numeric04 stopped with no verdict. Distinct checker05 and Mellin26 remain SOURCE, no runtime authorized here. D_N/WIN open."
    checkpoint.write_text(json.dumps(cp, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    with (COORD / "messages.jsonl").open("a", encoding="utf-8") as stream:
        stream.write(json.dumps(obs, ensure_ascii=False) + "\n")
    print(json.dumps({"observation": str(out), "official": [83, 1397], "new_credit": 0, "compiler": 0, "numeric": 0}, ensure_ascii=False))

if __name__ == "__main__":
    main()
