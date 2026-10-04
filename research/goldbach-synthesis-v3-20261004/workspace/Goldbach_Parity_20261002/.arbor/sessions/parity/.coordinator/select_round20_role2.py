"""New friable-layer selection20: metadata only, no proof/numeric execution."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import subprocess
import sys
B = Path(r"D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002")
C = B / ".arbor/sessions/parity/.coordinator"
R = B / "round20"
H = Path(r"C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py")
def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):
    return json.loads(p.read_text(encoding="utf-8-sig"))
fixed = {
    R / "agent2_friable.md": "5635cff82cbd5e6e395dfef3617f8d2d89ead40f6dbbdfffa943bf0f6a785be5",
    R / "role2/numeric_contract.md": "331417f2f63c2080900787c03f325279728d3eae33769aa38c56a3334bec8ed9",
    R / "role2/read_input_sha256.json": "f7dc265c2531d17e2c8dc2c69ce72b979114c70f4f330f3227741ab147d6b265",
    R / "role2/final_receipt.json": "ac9dab67bf69abc898b66212992be434de087e5a34cab343e01230e8a99e8dcb",
}
for p, digest in fixed.items():
    assert sha(p) == digest, str(p)
fr = read(R / "role2/final_receipt.json")
for item in fr["outputs"]:
    p = Path(item["path"])
    assert p.stat().st_size == item["bytes"] and sha(p) == item["sha256"]
assert fr["victory"] is False and all(v == 0 for v in fr["counts"].values())
immutable_inputs = []
mutable_observations = []
for item in read(R / "role2/read_input_sha256.json")["inputs"]:
    p = Path(item["path"])
    actual = sha(p)
    if p == C / "idea_tree.json":
        mutable_observations.append({**item, "current_sha256": actual, "historical_metadata_observation_only": True, "not_PREEXEC_or_protected_binding": True})
    else:
        assert actual == item["sha256"], str(p)
        immutable_inputs.append(item)
assert len(mutable_observations) == 1
assert read(C / "messages/round20_conservation_root_observation.json")["stored_inventory_entries_verified"] == 1808
report = R / "agent2_friable.md"
labels = ["Mechanism:", "Hypothesis:", "Observable:", "Conflicts:"]
lines = [s for s in report.read_text(encoding="utf-8-sig").splitlines() if any(s.startswith(t) for t in labels)]
assert lines == fr["four_line_hypothesis"] and len(lines) == 4
assert all(s.startswith(t) for s, t in zip(lines, labels))
node = "14.5"
out = C / "messages/round20_role2_selection.json"
assert not out.exists() and node not in read(C / "idea_tree.json")["nodes"]
context = """Read PROBE20, frozen FINAL2_20 FULL, role2/numeric_contract.md and feedback19. Protect1808/sourceu>=1e24/fullledger. New actual friable payment only on declared NonSS.physicalDomain/StructuralSupport19: cap e*q+Q+1<=N,e>p0 force actual resources>=M>=D. Multiset prefix actual primeFactorsList with repeats gives d|n,D<=d<DY; exact two affine classes, incompatible p0/N nonunits and every+1. Derive actual finite-prime Euler geometric/tau sums with local summability only (NOT global zeta at1-sigma), Eminus positive p-series<=1+1/sigma -> sum1/p<=3ell -> Eplusu27 -> S_Du^-37; no small sum as hypothesis. Derive finite totient identity/TK<=3(1+logX), actual harmonicKernel/sourceBracket abs raw/theta envelopes, cofactor identity using audited source without new untrackedimport. F2ABS(theta) OR ABS(raw) alternatives, F3 unique physical F1 reciprocals once and F4u1e24 sourcewrapper ifproved. F0minusF1 nonfriablem1 remainsUNPAID, sourceHbridge/remaining allranks/mediumlong/Gamma/T_A/fullledger open. Independent geometric or TK provisional guard must be named and no unconditional payment credit untilderived. Judge19/18/16/13build imports readonly; nooldPASS/compiler/kernelreplay. NEW numerical contract ALL1001q1800100..1801100/allintegercores beforemasks, fulltruePF/strata/rawPP, Ysource1withguardsFALSE/sigmaundefined vsYtest4096, actualprefix/classes/+1/newD/Wactivevertices/physicalunique m1/remainingm1unpaid. Independent Euler2401exponenttuplesY7/K6 plusFULL1..64 and1..112/totient1..4096 arefiniteonly, no sourcebudget certification. StrictFractions/rational log/root intervals,nofloat/unresolved. New numericalsources/preparation only until FULLsource+lance+prep rootreview and concrete uniquegate. New Lean sourcewritingnowauthorized, eachactualcompile waits newcanonical14.5bankPASS rootinspect+concretecompilegate; no rootcompilerexecution. PreserveeveryrealFAIL/sourcePREEXEC/log/exit, repairsafterFAIL only, no unchangedPASSreplay. PlannedJudge20 evalcmd is notcreated/gatedyet and is never an authorization; no inheritedJudge19execution. Ownedround20directories provideisolation, noGitstateactionsneeded. Auxiliary modules/localpayment neverWin."""
insight = "Frozen FINAL2_20 FULL830ce4+F2ABSdelta9f57ee, contractbdd40c/input5cc01b/receipt08311b andimmutableinputs verified; mutabletreeSHA recordedobservation only. Fresh35constraints FULL6dead8,13.12running, maxdepth2. Actual newfriable layer paper derives Eminus/p-series3ell,Eplusu27,S_Du^-37,F2/F3/F4 atsource1e24 with capresources/M/D, repeatedPF/two+1/uniqueF1 reciprocals. No free sum/capacity/targetpremise. F0minusF1 nonfriablem1 andsourcebridge/complement/fullledger unpaid. Newbank1001q/Ysource1false/Ytest4096 finiteonly. Sourcewriting/preparationnow, no math/Leanuntilgates, noWin."
calls = []
def invoke(cmd, *args):
    argv = [sys.executable, "-B", "-X", "utf8", str(H), cmd, "--cwd", str(B), "--run-name", "parity", *args]
    p = subprocess.run(argv, capture_output=True, text=True, encoding="utf-8")
    calls.append({"command": argv, "exit_code": p.returncode, "stdout": p.stdout, "stderr": p.stderr})
    if p.returncode:
        print(p.stdout, p.stderr)
        raise SystemExit(p.returncode)
invoke("add", "--parent-id", "14", "--hypothesis", "\n".join(lines))
assert read(C / "idea_tree.json")["nodes"][node]["hypothesis"] == "\n".join(lines)
invoke("update", "--node-id", node, "--status", "running", "--insight", insight)
invoke("prompt-executor", "--node-id", node, "--workdir", str(B), "--additional-context", context)
record = {"status": "ROUND20_ROLE2_SELECTED_NEW_SOURCE_PREPARATION_ONLY", "role": 2, "node": node, "selected_at_utc": datetime.now(timezone.utc).isoformat(), "fixed_bindings": {str(p): digest for p, digest in fixed.items()}, "root_full_report_reads": ["830ce4", "9f57ee"], "root_full_contract_read": "bdd40c", "root_full_metadata_reads": ["5cc01b", "08311b"], "fresh_constraints_full_read_chunk": "6dead8", "immutable_inputs_verified": immutable_inputs, "mutable_input_observations": mutable_observations, "protected_artifacts": 1808, "helper_metadata_calls": calls, "formal_sourcewriting_authorized": True, "numerical_source_preparation_authorized": True, "numerical_execution_authorized": False, "Lean_execution_authorized": False, "compiler_waits_new_canonical_numeric_PASS_rootgate": True, "victory": False}
with out.open("x", encoding="utf-8", newline="\n") as f:
    json.dump(record, f, indent=2, sort_keys=True, ensure_ascii=False)
    f.write("\n")
cp_path = C / "checkpoint.json"
cp = read(cp_path)
cp["phase"] = "ROUND20_BOTH_SELECTED_NEW_NUMERIC_FORMAL_PREPARATION"
cp["current_nodes"] = list(dict.fromkeys(cp.get("current_nodes", []) + [node]))
cp["previous_goal_turn_evidence"].extend(["round20/agent2_friable.md", "round20/role2/final_receipt.json", str(out.relative_to(B)).replace("\\", "/"), f".arbor/sessions/parity/experiments/{node}/executor_prompt.md"])
cp["last_progress"] += " " + insight
cp_path.write_text(json.dumps(cp, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
print(json.dumps({"node": node, "selection_receipt_sha256": sha(out), "immutable_inputs_count": len(immutable_inputs), "mutable_tree_observations_count": 1, "helper_exit_codes": [i["exit_code"] for i in calls], "math_execution": False, "victory": False}, indent=2))
