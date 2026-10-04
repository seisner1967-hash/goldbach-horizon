"""Create fresh batch02 orchestration SOURCE ONLY from conserved metadata helpers."""
from pathlib import Path

OWN = Path(__file__).resolve().parent
old_builder = (OWN / "prepare_judge22_batch01.py").read_text(encoding="utf-8")
shared = old_builder[old_builder.index("def sha(path):"):old_builder.index("def main():")]
new_builder_header = '''"""Freeze batch02 source/dependency metadata only; no Lean or maths."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re

BASE = Path(r"D:\\Users\\Utilisateur\\Desktop\\Maths\\Goldbach_Parity_20261002")
OWN = BASE / "round22" / "judge5"
SOURCES = OWN / "batch02_sources"
CACHE = Path(r"D:\\Users\\Utilisateur\\Desktop\\Maths\\q356-canonical-binding-replay\\.lake\\packages")
PACKAGES = ("aesop", "batteries", "importGraph", "LeanSearchClient", "mathlib", "plausible", "proofwidgets", "Qq")
LEAN_ROOT = Path(r"C:\\Users\\Utilisateur\\.elan\\toolchains\\leanprover--lean4---v4.15.0")
PYTHON = Path(r"C:\\Users\\Utilisateur\\.cache\\codex-runtimes\\codex-primary-runtime\\dependencies\\python\\python.exe")
AUTHOR_SPECS = (
    ("EpsteinUnfold22", BASE / "round22/role3/stage03/revision04", "stage03_attempt04",
     "79384d3502ab8042b44104e0ba4e56087c47430c267c2b9f16f9c6f228426aea", ["EpsteinFinite22"], "Epstein22"),
    ("EpsteinTail22", BASE / "round22/role3/stage04", "stage04_attempt01",
     "5f9d3f180df2e165d43aebfe2e72b963091bb2b90fdfa4e786a66cc82745af8e", ["EpsteinUnfold22"], "Epstein22"),
    ("GammaPrerequisites22", BASE / "round22/role4/revision02", "gamma_attempt3",
     "9f5e5fe14d18e2b7c3ab364e461bfcc01d29ee4ef4af6d627d6ad9fcd102fbe7", [], "GoldbachContinuous22"),
)
BANKS = (
    (BASE / "round22/role6/actual_epstein22/epstein_result22.json", "e9e72edeaf787644aa6a0f341992ec82270428d14e876ac4b7be00d5cc3e508a", "EPSTEIN_UNFOLDING_AUX_PASS"),
    (BASE / "round22/role6/gamma_h2/actual_gamma22/gamma_result22.json", "595b15340efe03bd215eebe7f6d526cd1f2f5d07865f074a3b7927687beb967a", "GAMMA_ROTATED_LAPLACE_AUX_PASS"),
)

'''
new_builder_main = '''def main():
    stamp = datetime.now(timezone.utc).isoformat()
    SOURCES.mkdir(exist_ok=False)
    bindings, rows, queue = {}, [], []
    for module, folder, attempt, expected_sha, dependencies, namespace in AUTHOR_SPECS:
        src, actual = folder / (module + ".lean"), folder / attempt
        receipt_path = actual / "receipt.json"
        receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
        if module == "GammaPrerequisites22":
            provenance = {"status": receipt["status"], "exit_code": receipt["exit_code"],
                          "source_sha256": receipt["source_sha256"], "log_sha256": receipt["stdout_sha256"],
                          "olean_sha256": receipt["olean_sha256"], "invocations": receipt["compiler_invocations_this_launcher"]}
            if receipt["changed_immutable_inputs"] or receipt["archive_after"]["changed"]:
                raise RuntimeError("Gamma author conservation failed")
            log = actual / "stdout.log"
            artifacts = [receipt_path, log, actual / "stderr.log", actual / "START.json", actual / "preexec.json", actual / "exit.json"]
            if provenance["status"] != "AUTHOR_GAMMA_H2_COMPILE_PASS_PENDING_INDEPENDENT_JUDGE":
                raise RuntimeError("Gamma is not an author PASS")
        else:
            if receipt["status"] != "AUTHOR_STAGE_AUX_PASS" or not receipt["all_source_inputs_unchanged"]:
                raise RuntimeError("G0 module is not a conserved author PASS")
            provenance = dict(receipt["rows"][0], invocations=receipt["actual_child_invocations"])
            log = actual / (module + ".log")
            artifacts = [receipt_path, log, actual / "START.json", actual / "PREEXEC.json", actual / "POSTEXEC.json"]
        if (sha(src) != expected_sha or provenance["source_sha256"] != expected_sha
                or provenance["exit_code"] != 0 or provenance["invocations"] != 1
                or sha(log) != provenance["log_sha256"]):
            raise RuntimeError("Author provenance binding mismatch: " + module)
        target = SOURCES / src.name
        target.write_bytes(src.read_bytes())
        code = lean_code(target)
        declarations = re.findall(r"^(theorem|def)\\s+(\\w+)", code, re.MULTILINE)
        prints = re.findall(r"^#print axioms " + namespace + r"\\.(\\w+)$", code, re.MULTILINE)
        if ([name for _, name in declarations] != prints
                or re.search(r"\\b(?:sorry|admit|axiom|native_decide|unsafe)\\b", code)):
            raise RuntimeError("Exact axiom coverage or forbidden-token check failed")
        rows.append({"module": module, "source": str(target), "source_sha256": sha(target),
            "author_source": str(src), "author_receipt": str(receipt_path), "author_provenance": provenance,
            "dependencies": dependencies, "namespace": namespace,
            "declarations": [{"kind": kind, "qualified_name": namespace + "." + name} for kind, name in declarations],
            "qualified_prints": [namespace + "." + name for name in prints],
            "theorem_count": sum(kind == "theorem" for kind, _ in declarations),
            "definition_count": sum(kind == "def" for kind, _ in declarations),
            "compiler_options": ["-DmaxHeartbeats=1000000"] if module == "GammaPrerequisites22" else [],
            "source_forbidden_tokens": [], "scope": "AUXILIARY_CONTINUOUS_ANALYSIS_ONLY"})
        queue.extend(imports(target))
        for path in [src, target] + artifacts:
            bindings[str(path)] = sha(path)
    closed = set()
    for path in OWN.glob("batch01_*"):
        if path.is_dir():
            closed.update(item for item in path.rglob("*") if item.is_file())
        elif path.is_file():
            closed.add(path)
    closed.update(OWN / name for name in ("prepare_judge22_batch01.py", "run_judge22_batch01_once.py", "adjudicate_judge22_batch01_metadata.py"))
    old_rows = [{"path": str(path), "sha256": sha(path)} for path in sorted(closed)]
    write_new(OWN / "batch02_batch01_bindings.json", {"schema": "ROUND22_JUDGE5_BATCH01_READONLY_BINDINGS", "inputs": old_rows,
        "recompiled": False, "compiler_invocations": 0})
    for row in old_rows:
        bindings[row["path"]] = row["sha256"]
    old_receipt = json.loads((OWN / "batch01_attempt01/receipt.json").read_text(encoding="utf-8"))
    if old_receipt["status"] != "INDEPENDENT_BATCH01_AUX_PASS":
        raise RuntimeError("Closed judge dependencies lack independent PASS")
    for module, expected in (("EpsteinKernel22", "9bf2da2b6cb3a5780868c51916afdf173e79a971d56fdf7a52c6b2abfa9def8d"),
                             ("EpsteinFinite22", "679f572be0d81f8c86bfa418fb460d5168774fc56b2b2537a9469ff0aca7a544")):
        path = OWN / "batch01_attempt01" / (module + ".olean")
        if sha(path) != expected:
            raise RuntimeError("Closed judge dependency changed")
        queue.extend(imports(OWN / "batch01_sources" / (module + ".lean")))
    local = {"EpsteinKernel22", "EpsteinFinite22"} | {row["module"] for row in rows}
    closure, seen, unresolved = [], set(), []
    while queue:
        module = queue.pop()
        if module in seen or module in local:
            continue
        seen.add(module)
        src, obj = resolve(module)
        if src is None or not src.is_file() or not obj.is_file():
            unresolved.append({"module": module, "source": str(src), "olean": str(obj)})
            continue
        item = {"module": module, "source": str(src), "source_sha256": sha(src), "olean": str(obj),
                "olean_sha256": sha(obj), "read_scope": "HASH_AND_IMPORT_METADATA_ONLY"}
        closure.append(item)
        bindings[str(src)], bindings[str(obj)] = item["source_sha256"], item["olean_sha256"]
        queue.extend(imports(src))
    write_new(OWN / "batch02_import_bindings.json", {"schema": "ROUND22_JUDGE5_IMPORT_BINDINGS_BATCH02", "module_count": len(closure),
        "unresolved": unresolved, "entries": sorted(closure, key=lambda item: item["module"]), "compiler_invocations": 0})
    reads = [
        (AUTHOR_SPECS[0][1] / "EpsteinUnfold22.lean", "FULL", "b76d19"),
        (AUTHOR_SPECS[1][1] / "EpsteinTail22.lean", "FULL", "529f97"),
        (AUTHOR_SPECS[2][1] / "GammaPrerequisites22.lean", "FULL", "21d3da"),
        (AUTHOR_SPECS[0][1] / AUTHOR_SPECS[0][2] / "receipt.json", "FULL", "1a8930"),
        (AUTHOR_SPECS[1][1] / AUTHOR_SPECS[1][2] / "receipt.json", "FULL", "f0fe7b"),
        (AUTHOR_SPECS[2][1] / AUTHOR_SPECS[2][2] / "receipt.json", "FULL", "3ce81a"),
        (AUTHOR_SPECS[0][1] / AUTHOR_SPECS[0][2] / "EpsteinUnfold22.log", "FULL", "f7f927"),
        (AUTHOR_SPECS[1][1] / AUTHOR_SPECS[1][2] / "EpsteinTail22.log", "FULL", "4d713b"),
        (AUTHOR_SPECS[2][1] / AUTHOR_SPECS[2][2] / "stdout.log", "FULL", "09f1cb"),
        (AUTHOR_SPECS[2][1] / AUTHOR_SPECS[2][2] / "START.json", "FULL", "411f52"),
        (BASE / "round22/role3/G0_final_catalog_v2.json", "FULL", "30d1e9; priordd032b truncated not FULL"),
        (BASE / "round22/role3/G0_raccord_final.md", "FULL", "1a4eea"),
        (BASE / "round22/role6/epstein_contract22.json", "FULL", "3f49cc"),
        (BASE / "round22/role6/gamma_h2/gamma_contract22.json", "FULL", "04a47b"),
        (BASE / "round22/USER_DIRECTIVE.md", "FULL IN PREVIOUS JUDGE TURN", "0cc8d5"),
        (BASE / "round22/PROBE_BLOCK.md", "FULL IN PREVIOUS JUDGE TURN", "0cc8d5"),
        (Path(r"C:\\Users\\Utilisateur\\.codex\\skills\\arbor-agent-executor\\SKILL.md"), "FULL IN PREVIOUS JUDGE TURN", "89d58e"),
        (Path(r"C:\\Users\\Utilisateur\\.codex\\skills\\arbor-agent-merge-eval\\SKILL.md"), "FULL IN PREVIOUS JUDGE TURN", "147a36"),
    ]
    bank_rows = []
    for path, expected, status in BANKS:
        data = json.loads(path.read_text(encoding="utf-8"))
        if sha(path) != expected or data["status"] != status:
            raise RuntimeError("Closed numeric bank provenance mismatch")
        bank_rows.append({"path": str(path), "sha256": expected, "status": status,
                          "case_count": len(data["cases"]), "read_scope": "PARSED_STATUS_PROJECTION_NOT_FULL_RAW_DISPLAY"})
        bindings[str(path)] = expected
    write_new(OWN / "batch02_read_receipts.json", {"schema": "ROUND22_JUDGE5_READ_RECEIPTS_BATCH02", "time_utc": stamp,
        "entries": [{"path": str(path), "sha256": sha(path), "scope": scope, "chunk": chunk} for path, scope, chunk in reads],
        "numeric_results": bank_rows, "result_scope": "Metadata status/case projections only; no result reproduced or recalculated",
        "compiler_invocations": 0, "mathematical_numeric_invocations": 0})
    write_new(OWN / "batch02_catalog.json", {"schema": "ROUND22_JUDGE5_MODULE_CATALOG_BATCH02", "time_utc": stamp,
        "modules": rows, "module_count": 3, "total_declarations": sum(len(row["declarations"]) for row in rows),
        "theorem_count": sum(row["theorem_count"] for row in rows), "definition_count": sum(row["definition_count"] for row in rows),
        "readonly_local_dependencies": ["EpsteinKernel22", "EpsteinFinite22"], "compiler_invocations": 0, "win": False})
    for path, _, _ in reads:
        bindings[str(path)] = sha(path)
    for name in ("prepare_judge22_batch02.py", "run_judge22_batch02_once.py", "write_batch02_metadata_sources.py",
                 "batch02_preparation.md", "batch02_read_receipts.json", "batch02_catalog.json", "batch02_import_bindings.json",
                 "batch02_batch01_bindings.json"):
        bindings[str(OWN / name)] = sha(OWN / name)
    for path in (BASE / "round22/previous_artifacts_sha256.json", LEAN_ROOT / "bin/lean.exe", PYTHON):
        bindings[str(path)] = sha(path)
    manifest = {"schema": "ROUND22_JUDGE5_PREPARED_MANIFEST_BATCH02", "time_utc": stamp,
        "status": "PREPARED_SOURCE_ONLY_GATE_CLOSED" if not unresolved else "PREPARATION_IMPORT_OPEN",
        "role": "ROLE5", "modules": [row["module"] for row in rows], "compiler_invocations": 0,
        "mathematical_numeric_invocations": 0, "import_module_count": len(closure), "unresolved_modules": unresolved,
        "immutable_inputs": [{"path": path, "sha256": digest} for path, digest in sorted(bindings.items())],
        "source_catalog_sha256": sha(OWN / "batch02_catalog.json"), "launcher_sha256": sha(OWN / "run_judge22_batch02_once.py"),
        "numeric_banks": bank_rows, "batch01_closed_files": len(old_rows),
        "batch01_dependency_directory": str(OWN / "batch01_attempt01"), "author_olean_used": False,
        "official_baseline_modules": 59, "official_baseline_auxiliaries": 993,
        "full_trace_certified": False, "D_N_paid": False, "win": False}
    write_new(OWN / "batch02_prepared_manifest.json", manifest)
    print(json.dumps({"status": manifest["status"], "modules": manifest["modules"], "declarations": 56,
        "imports": len(closure), "inputs": len(bindings), "batch01_closed_files": len(old_rows), "unresolved": unresolved,
        "manifest_sha256": sha(OWN / "batch02_prepared_manifest.json"), "catalog_sha256": manifest["source_catalog_sha256"],
        "launcher_sha256": manifest["launcher_sha256"], "compiler_invocations": 0, "mathematical_numeric_invocations": 0}))


if __name__ == "__main__":
    main()
'''
with (OWN / "prepare_judge22_batch02.py").open("x", encoding="utf-8", newline="\n") as stream:
    stream.write(new_builder_header + shared + new_builder_main)

launcher = (OWN / "run_judge22_batch01_once.py").read_text(encoding="utf-8")
launcher = launcher.replace("batch01", "batch02").replace("BATCH01", "BATCH02")
launcher = launcher.replace("Independent two-module Lean audit", "Independent three-module Lean audit")
launcher = launcher.replace('MODULES = ("EpsteinKernel22", "EpsteinFinite22")',
    'MODULES = ("EpsteinUnfold22", "EpsteinTail22", "GammaPrerequisites22")\nDEPENDENCY_DIR = OWN / "batch01_attempt01"')
launcher = launcher.replace('"compiler_invocations_maximum": 2', '"compiler_invocations_maximum": 3')
launcher = launcher.replace('"child_invocations_maximum": 2', '"child_invocations_maximum": 3')
launcher = launcher.replace('"numeric_verdict": "EPSTEIN_UNFOLDING_AUX_PASS",\n                "numeric_bank_path": str(NUMERIC_BANK), "numeric_bank_sha256": NUMERIC_BANK_SHA,\n                "numeric_bank_verified": True,',
    '"numeric_banks": manifest["numeric_banks"], "numeric_banks_verified": True,\n                "readonly_batch01_dependency_directory": str(DEPENDENCY_DIR),')
launcher = launcher.replace('    if sha(NUMERIC_BANK) != NUMERIC_BANK_SHA:\n        raise RuntimeError("Genuine numeric bank binding changed")',
    '    for bank in manifest["numeric_banks"]:\n        if sha(bank["path"]) != bank["sha256"]:\n            raise RuntimeError("Genuine numeric bank binding changed")\n    batch01_receipt = json.loads((DEPENDENCY_DIR / "receipt.json").read_text(encoding="utf-8"))\n    if batch01_receipt["status"] != "INDEPENDENT_BATCH01_AUX_PASS":\n        raise RuntimeError("Readonly judge dependencies are not independently certified")')
launcher = launcher.replace('    paths = [out] +', '    paths = [out, DEPENDENCY_DIR] +')
launcher = launcher.replace('commands = [[str(LEAN), "-o",', 'commands = [[str(LEAN)] + info["compiler_options"] + ["-o",')
launcher = launcher.replace('for module in MODULES]\n    write_new(out / "PREEXEC.json"',
    'for module, info in zip(MODULES, catalog["modules"])]\n    write_new(out / "PREEXEC.json"')
launcher = launcher.replace('                      OWN / "batch02_import_bindings.json", gate_path]',
    '                      OWN / "batch02_import_bindings.json", OWN / "batch02_batch01_bindings.json", gate_path]\n    capture_paths += [Path(bank["path"]) for bank in manifest["numeric_banks"]]\n    capture_paths += [Path(info["author_receipt"]) for info in catalog["modules"]]\n    capture_paths += [BASE / "round22/role3/G0_final_catalog_v2.json", BASE / "round22/role3/G0_raccord_final.md"]')
launcher = launcher.replace('"prepare_judge22_batch02.py", OWN / "batch02_source_audit.md"',
    '"prepare_judge22_batch02.py", OWN / "batch02_preparation.md"')
launcher = launcher.replace('len(rows) == len(MODULES)', 'len(rows) == len(MODULES)')
launcher = launcher.replace('"global_trace_certified": False, "D_N_paid": False, "victory": False}',
    '"batch01_recompiled": False, "readonly_local_dependencies": ["EpsteinKernel22", "EpsteinFinite22"],\n        "global_trace_certified": False, "D_N_paid": False, "victory": False}')
with (OWN / "run_judge22_batch02_once.py").open("x", encoding="utf-8", newline="\n") as stream:
    stream.write(launcher)
print("Fresh batch02 builder and launcher SOURCE files created; Lean invocations0; mathematics0")
