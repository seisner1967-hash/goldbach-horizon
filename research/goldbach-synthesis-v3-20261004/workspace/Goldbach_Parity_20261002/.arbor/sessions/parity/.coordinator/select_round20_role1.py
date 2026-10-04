"""One new concept selection20, coordinator metadata only, no math execution."""
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
report = R / "agent1_switched_composite.md"
manifest = R / "role1/input_manifest.json"
final = R / "role1/final_receipt.json"
assert sha(report) == "1c52ccfe6aaf393fe02b606ecbaeb56ae62810f0b93d6db604672ba560a241d9"
assert sha(manifest) == "8cf3aaadd8984d8ce238cd994d2b7094c7ae121967f7e4785c7d850f04591a7f"
assert sha(final) == "569865f04368b6feb9fc152efcc32ec15564baccc78f7c5cb57eef7e8008b988"
fm, fr = read(manifest), read(final)
for item in fm["input_bindings"]:
    p = Path(item["path"])
    assert sha(p) == item["sha256"] and p.stat().st_size == item["bytes"], str(p)
assert len(fm["input_bindings"]) == 17
assert fr["victory"] is False and fr["lean_invocations"] == 0
assert read(C / "messages/round20_conservation_root_observation.json")["status"] == "ROOT_OBSERVED_ACTUAL_UNIQUE_PREFLIGHT20_PASS_NO_REPLAY"
annex = R / "role6/conservation_final_receipt.json"
assert sha(annex) == "1116d2b99b4c66d6d5f04ef8d46475462f7560b233a5797346c351a9329d7c34"
af = read(annex)
assert af["actual_exit_code"] == 0 and af["actual_new_preflight_subprocess_count"] == 1
assert len(af["new_file_sha256"]) == 17
for name, digest in af["new_file_sha256"].items():
    assert sha(R / name) == digest, name
labels = ["Mechanism:", "Hypothesis:", "Observable:", "Conflicts:"]
lines = [s for s in report.read_text(encoding="utf-8-sig").splitlines() if any(s.startswith(t) for t in labels)]
assert len(lines) == 4 and all(s.startswith(t) for s, t in zip(lines, labels))
hyp = "\n".join(lines)
node = "13.12"
out = C / "messages/round20_role1_selection.json"
assert not out.exists() and node not in read(C / "idea_tree.json")["nodes"]
context = """Read PROBE20, frozen FINAL1_20 FULL, feedback19 and this selection. Protect1808, sourceu>=1e24 and fullledger unchanged. Build actual odd Bonferroni arithmetic weights on primeFactors/divisors, leastfactor composite/p^2/repeats and physical q-prime subtraction with negative nonminimal cells/slack/tail. Derive shared-lcm/gcd AP conductors, real endpoints and incompatible modules. Lambda section10 is actual Mobius/Selberg rational construction, p0 is canonical leastMissingOddPrime, its positive first principal is compensated by the cost of excluding p0: no netGamma credit presumed. If B6 analytic variation notproved, retain exact actual remainder identity; no free smallGamma/SD/targetbound. Historical Judge19/18/16/13 imports readonly; no acquired recompilation. NEW numerical contract section12: N1e8, ALL24m candidates24m<j<=48m and every physical triple/q including empty intervals, no jprime filter, actual lambda at z_test11/19,P_test17,K0/1, sourcez2/P1finite distinct, exact AP/classes/nonunits/+1, rawproperpowers/M0 literal/affineSN enclosure/slack/tails. Test x48m violates sourcex<=N/4: publish guardFALSE, never analyticalonset promotion. No old rank19 bank/bitmap/W/D/PASS/logsign replay. New producer/sourcewriting preparation authorized now, no mathematical execution until FULL numericcode+launcher inspected and distinctrootgate. New Lean sourcewriting nowauthorized; each actual compile waits corresponding canonicalNEWbankPASS rootinspected and concretecompilegate. Every genuine FAIL exactsource/log/exit retained, corrections afterFAIL only, no unchangedPASSreplay. Auxiliary compilation is notWin; principal/SD/largep/fullledger remainopen."""
insight = "Frozen FINAL1_20 FULL rootread885756+8144d4+finaldelta064583, receipt2491f6/manifest9acff4 and17 inputs verified. Unique1808 conservationPASS and17annexbindings observed. Fresh35constraints FULLd742e5 beforeselection. New actual constructed Bonferroni lowerweight/composite subtraction and APconductor/slack/tail, q remainsprime; canonicalp0 positive main retains Eulercompensation. Sourcevariation/SD/favorablecompleteprincipal/fullGamma/ledger remainopen, noWin. Newnumericcontract24m..48m distinctfinite/source guards; sourcewriting only until gates."
calls = []
def invoke(cmd, *args):
    argv = [sys.executable, "-B", "-X", "utf8", str(H), cmd, "--cwd", str(B), "--run-name", "parity", *args]
    p = subprocess.run(argv, capture_output=True, text=True, encoding="utf-8")
    calls.append({"command": argv, "exit_code": p.returncode, "stdout": p.stdout, "stderr": p.stderr})
    if p.returncode:
        print(p.stdout, p.stderr)
        raise SystemExit(p.returncode)
invoke("add", "--parent-id", "13", "--hypothesis", hyp)
assert read(C / "idea_tree.json")["nodes"][node]["hypothesis"] == hyp
invoke("update", "--node-id", node, "--status", "running", "--insight", insight)
invoke("prompt-executor", "--node-id", node, "--workdir", str(B), "--additional-context", context)
record = {"status": "ROUND20_ROLE1_SELECTED_NEW_SOURCE_PREPARATION_ONLY", "node": node, "role": 1, "selected_at_utc": datetime.now(timezone.utc).isoformat(), "report_sha256": sha(report), "manifest_sha256": sha(manifest), "final_receipt_sha256": sha(final), "root_full_report_reads": ["885756", "8144d4", "064583"], "root_full_metadata_reads": ["9acff4", "2491f6"], "fresh_constraints_full_read_chunk": "d742e5", "role1_input_bindings_verified": 17, "preflight_annex_bindings_verified": 17, "preflight_annex_full_reads": ["f2ee02", "1a2280"], "protected_artifacts": 1808, "helper_metadata_calls": calls, "numerical_source_preparation_authorized": True, "numerical_execution_authorized": False, "formal_sourcewriting_authorized": True, "Lean_execution_authorized": False, "compiler_waits_new_canonical_numeric_PASS_rootgate": True, "victory": False}
with out.open("x", encoding="utf-8", newline="\n") as f:
    json.dump(record, f, indent=2, sort_keys=True, ensure_ascii=False)
    f.write("\n")
cp_path = C / "checkpoint.json"
cp = read(cp_path)
cp["phase"] = "ROUND20_ROLE1_SELECTED_NEW_NUMERIC_FORMAL_PREPARATION_ROLE2_PENDING"
cp["current_nodes"] = list(dict.fromkeys(cp.get("current_nodes", []) + [node]))
cp["previous_goal_turn_evidence"].extend(["round20/agent1_switched_composite.md", "round20/role1/final_receipt.json", str(out.relative_to(B)).replace("\\", "/"), f".arbor/sessions/parity/experiments/{node}/executor_prompt.md"])
cp["last_progress"] += " " + insight
cp_path.write_text(json.dumps(cp, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
print(json.dumps({"selected_node": node, "selection_receipt_sha256": sha(out), "helper_exit_codes": [i["exit_code"] for i in calls], "math_execution": False, "victory": False}, indent=2))
