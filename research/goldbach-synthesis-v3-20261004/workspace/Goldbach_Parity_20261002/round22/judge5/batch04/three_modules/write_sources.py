"""Fresh three-module metadata source generation; old helpers are text only."""
from pathlib import Path

OWN = Path(__file__).resolve().parent
JUDGE = OWN.parents[1]
old_builder = (JUDGE / "batch03/prepare_metadata.py").read_text(encoding="utf-8")
helpers = old_builder[old_builder.index("def sha("):old_builder.index("def main(")]
header = '''"""Core/Beta/Integral byte/import preparation only; no Lean or maths."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
OWN = Path(__file__).resolve().parent
JUDGE = OWN.parents[1]
BASE = JUDGE.parents[1]
CACHE = Path(r"D:\\Users\\Utilisateur\\Desktop\\Maths\\q356-canonical-binding-replay\\.lake\\packages")
PACKAGES = ("aesop", "batteries", "importGraph", "LeanSearchClient", "mathlib", "plausible", "proofwidgets", "Qq")
LEAN_ROOT = Path(r"C:\\Users\\Utilisateur\\.elan\\toolchains\\leanprover--lean4---v4.15.0")
PYTHON = Path(r"C:\\Users\\Utilisateur\\.cache\\codex-runtimes\\codex-primary-runtime\\dependencies\\python\\python.exe")
SPECS = (
 ("GammaPsiCore22", "revision03", "psi_batch03_attempt01", "450962be9526866fa0ffebc39ef29a819d94b57a90000291337550e9f4dc7284", "350be4276efe5013e9530037cc3ad22aeee6ce17231d45ffb1ed1883a9b5a1bf", 15, 4, []),
 ("GammaPsiBetaLimit22", "revision04", "psi_batch04_attempt01", "b4adf3ac71dd7c9d0e6e78f83ce805ddc7eaf5e8f5978aa4c1d6b87bc8caceb8", "73580f763b089606dbe488720d86920658dacad1b100657c26b9c8cc2cf4209b", 20, 3, ["GammaPsiCore22"]),
 ("GammaPsiIntegral22", "revision04", "psi_batch04_attempt01", "3f254cdfeee333aa66eba719b944f64a693fa2e15f0265f340ace9c2a99f6aaf", "73580f763b089606dbe488720d86920658dacad1b100657c26b9c8cc2cf4209b", 9, 1, ["GammaPsiBetaLimit22"]),
)

'''
main_text = '''def main():
    stamp = datetime.now(timezone.utc).isoformat()
    if (OWN / "prepared_manifest.json").exists():
        raise RuntimeError("No repeat freeze")
    sources = OWN / "sources"
    sources.mkdir(exist_ok=False)
    rows, reads, bindings, queue = [], [], {}, ["Init"]
    for module, revision, attempt, source_sha, receipt_sha, nthm, ndef, dependencies in SPECS:
        folder = BASE / "round22/role3/h1_psi" / revision
        source, actual = folder / "source_final" / (module + ".lean"), folder / attempt
        receipt_path = actual / "receipt.json"
        receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
        row = next(item for item in receipt["rows"] if item["module"] == module)
        if (sha(source) != source_sha or sha(receipt_path) != receipt_sha or row["source_sha256"] != source_sha
                or row["exit_code"] != 0 or row["status"] != "AUTHOR_LEAN_AUX_PASS"
                or not row["exact_axiom_coverage_standard_only"] or not receipt["all_inputs_unchanged"]):
            raise RuntimeError("Author module PASS binding mismatch: " + module)
        log = actual / (module + ".log")
        if sha(log) != row["log_sha256"] or sha(actual / (module + ".olean")) != row["olean_sha256"]:
            raise RuntimeError("Author artifacts changed")
        target = sources / source.name
        target.write_bytes(source.read_bytes())
        code = lean_code(target)
        declarations = re.findall(r"^(theorem|def)\\s+(\\w+)", code, re.MULTILINE)
        prints = re.findall(r"^#print axioms GoldbachContinuous22\\.(\\w+)$", code, re.MULTILINE)
        qualified = ["GoldbachContinuous22." + name for name in prints]
        forbidden = re.findall(r"\\b(?:sorry|admit|axiom|native_decide|unsafe)\\b", code)
        if ([name for _, name in declarations] != prints or forbidden
                or sum(kind == "theorem" for kind, _ in declarations) != nthm
                or sum(kind == "def" for kind, _ in declarations) != ndef
                or [item["declaration"] for item in row["axiom_rows"]] != qualified):
            raise RuntimeError("Exact declaration/print coverage mismatch: " + module)
        rows.append({"module": module, "source": str(target), "source_sha256": source_sha,
            "author_source": str(source), "author_receipt": str(receipt_path), "author_log": str(log),
            "author_row": row, "author_batch_status": receipt["status"],
            "declarations": [{"kind": kind, "qualified_name": "GoldbachContinuous22." + name} for kind, name in declarations],
            "qualified_prints": qualified, "theorem_count": nthm, "definition_count": ndef,
            "source_forbidden_tokens": [], "compiler_options": ["-DmaxHeartbeats=1000000"], "dependencies": dependencies,
            "scope": "ACTUAL_GAMMA_PSI_INTEGRAL_AUXILIARY_ONLY"})
        for path in (source, target, receipt_path, log, actual / (module + ".olean"),
                     actual / (module + "_START.json"), actual / (module + "_FIN.json"),
                     actual / "START.json", actual / "PREEXEC.json", actual / "POSTEXEC.json"):
            bindings[str(path)] = sha(path)
        source_chunk = {"GammaPsiCore22": "39f4b0", "GammaPsiBetaLimit22": "b86ec5", "GammaPsiIntegral22": "5e55f1"}[module]
        receipt_chunk = "d36265" if revision == "revision03" else "009660"
        log_chunk = "5e079f" if revision == "revision03" else "5e55f1"
        reads += [(source, "FULL", source_chunk), (receipt_path, "FULL", receipt_chunk), (log, "FULL", log_chunk)]
        queue.extend(imports(target))
    closed = set()
    for path in JUDGE.iterdir():
        if (path.name.startswith(("batch01_", "batch02_")) or path.name == "batch03"
                or re.match(r"(?:prepare|run|adjudicate)_judge22_batch0[12]", path.name)
                or path.name == "write_batch02_metadata_sources.py"):
            closed.update(item for item in path.rglob("*") if item.is_file()) if path.is_dir() else closed.add(path)
    old_rows = [{"path": str(path), "sha256": sha(path)} for path in sorted(closed)]
    for item in old_rows:
        bindings[item["path"]] = item["sha256"]
    if json.loads((JUDGE / "batch03/batch03_attempt01/receipt.json").read_text(encoding="utf-8"))["status"] != "INDEPENDENT_BATCH03_AUX_PASS":
        raise RuntimeError("Previous independent stage not closed PASS")
    write_new(OWN / "closed_judge_bindings.json", {"schema": "ROUND22_JUDGE5_CLOSED_BATCHES_BINDINGS", "inputs": old_rows,
        "old_batches_recompiled": False, "compiler_invocations": 0})
    closure, seen, unresolved = [], set(), []
    local = {item[0] for item in SPECS}
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
    write_new(OWN / "import_bindings.json", {"schema": "ROUND22_JUDGE5_IMPORT_BINDINGS_BATCH04", "module_count": len(closure),
        "explicit_implicit_prelude_seed": "Init", "unresolved": unresolved,
        "entries": sorted(closure, key=lambda item: item["module"]), "compiler_invocations": 0})
    reads += [(BASE / ".arbor/sessions/parity/.coordinator/messages/round22_psi03_author_observation.json", "FULL", "d24b8c"),
        (CACHE / "mathlib/Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean", "TARGETED_DECLARATIONS_AND_CONTEXT", "d24b8c"),
        (JUDGE / "batch03/adjudication.json", "FULL", "94893b"), (JUDGE / "batch03/completion.md", "FULL", "94893b")]
    write_new(OWN / "read_receipts.json", {"schema": "ROUND22_JUDGE5_READ_RECEIPTS_BATCH04", "time_utc": stamp,
        "entries": [{"path": str(path), "sha256": sha(path), "scope": scope, "chunk": chunk} for path, scope, chunk in reads],
        "compiler_invocations": 0, "mathematical_numeric_invocations": 0, "numeric_bank_required": False,
        "all_import_mathematical_FULL_claim": False, "superseded_Core_only_draft_executed": False})
    write_new(OWN / "catalog.json", {"schema": "ROUND22_JUDGE5_MODULE_CATALOG_BATCH04", "time_utc": stamp,
        "modules": rows, "module_count": 3, "total_declarations": 52, "theorem_count": 44, "definition_count": 8,
        "readonly_local_dependencies": [], "compiler_invocations": 0, "win": False})
    archive_path = BASE / "round22/previous_artifacts_sha256.json"
    archives = json.loads(archive_path.read_text(encoding="utf-8"))
    if len(archives["sha256"]) != archives["file_count"] or archives["file_count"] != 3089:
        raise RuntimeError("Archive count changed")
    for relative, expected in archives["sha256"].items():
        if sha(BASE / relative) != expected:
            raise RuntimeError("Protected archive changed")
    for path, _, _ in reads:
        bindings[str(path)] = sha(path)
    for name in ("write_sources.py", "prepare_metadata.py", "run_once.py", "preparation.md", "read_receipts.json", "catalog.json",
                 "import_bindings.json", "closed_judge_bindings.json"):
        bindings[str(OWN / name)] = sha(OWN / name)
    for path in (archive_path, LEAN_ROOT / "bin/lean.exe", PYTHON):
        bindings[str(path)] = sha(path)
    manifest = {"schema": "ROUND22_JUDGE5_PREPARED_MANIFEST_BATCH04", "time_utc": stamp,
        "status": "PREPARED_SOURCE_ONLY_GATE_CLOSED" if not unresolved else "PREPARATION_IMPORT_OPEN", "role": "ROLE5",
        "modules": [item[0] for item in SPECS], "compiler_invocations": 0, "mathematical_numeric_invocations": 0,
        "import_module_count": len(closure), "implicit_Init_closure_included": True, "unresolved_modules": unresolved,
        "immutable_inputs": [{"path": path, "sha256": digest} for path, digest in sorted(bindings.items())],
        "source_catalog_sha256": sha(OWN / "catalog.json"), "launcher_sha256": sha(OWN / "run_once.py"),
        "numeric_banks": [], "closed_judge_files": len(old_rows), "protected_archive_count": 3089,
        "readonly_local_dependencies": [], "author_olean_used": False, "numeric_PASS_required": False,
        "official_baseline_requires_ROOT_observation": True, "previous_independent_pass_modules": 63,
        "previous_independent_pass_auxiliaries": 1057, "H1_paid": False, "C3_paid": False, "C5_paid": False, "D_N_paid": False, "win": False}
    write_new(OWN / "prepared_manifest.json", manifest)
    print(json.dumps({"status": manifest["status"], "modules": manifest["modules"], "declarations": 52, "theorems": 44, "definitions": 8,
        "imports": len(closure), "inputs": len(bindings), "old_judge_files": len(old_rows), "archives": 3089, "unresolved": unresolved,
        "manifest_sha256": sha(OWN / "prepared_manifest.json"), "launcher_sha256": manifest["launcher_sha256"],
        "catalog_sha256": manifest["source_catalog_sha256"], "compiler_invocations": 0, "mathematical_numeric_invocations": 0}))


if __name__ == "__main__":
    main()
'''
with (OWN / "prepare_metadata.py").open("x", encoding="utf-8", newline="\n") as stream:
    stream.write(header + helpers + main_text)

launcher = (JUDGE / "run_judge22_batch02_once.py").read_text(encoding="utf-8")
launcher = launcher.replace('BASE = OWN.parents[1]', 'JUDGE = OWN.parents[1]\nBASE = JUDGE.parents[1]')
launcher = launcher.replace('batch02', 'batch04').replace('BATCH02', 'BATCH04')
launcher = launcher.replace('"EpsteinUnfold22", "EpsteinTail22", "GammaPrerequisites22"', '"GammaPsiCore22", "GammaPsiBetaLimit22", "GammaPsiIntegral22"')
launcher = launcher.replace('DEPENDENCY_DIR = OWN / "batch01_attempt01"\n', '')
launcher = launcher.replace('OWN / "batch04_prepared_manifest.json"', 'OWN / "prepared_manifest.json"')
launcher = launcher.replace('OWN / "batch04_catalog.json"', 'OWN / "catalog.json"')
launcher = launcher.replace('OWN / "batch04_sources"', 'OWN / "sources"')
start = launcher.index('    required = {')
end = launcher.index('    for key, value in required.items():', start)
launcher = launcher[:start] + '''    required = {"schema": "ROUND22_JUDGE5_BATCH04_AUTHORIZATION", "role": "ROLE5", "authorized": True,
        "attempt": args.attempt, "modules": list(MODULES), "compiler_invocations_maximum": 3,
        "source_manifest_sha256": sha(manifest_path), "launcher_sha256": sha(Path(__file__)),
        "preparation_receipt_sha256": sha(OWN / "prepared_receipt.json"),
        "python_sha256": PYTHON_SHA, "lean_sha256": LEAN_SHA, "readonly_local_dependencies": [],
        "independent_audit": True, "author_olean_allowed": False, "no_win": True}
''' + launcher[end:]
start = launcher.index('    for bank in manifest["numeric_banks"]:')
end = launcher.index('    gate_sha = sha(gate_path)', start)
launcher = launcher[:start] + launcher[end:]
start = launcher.index('    capture_paths = [OWN /')
end = launcher.index('    copied = []', start)
launcher = launcher[:start] + '''    capture_paths = [OWN / "sources" / (module + ".lean") for module in MODULES]
    capture_paths += [OWN / name for name in ("write_sources.py", "prepare_metadata.py", "run_once.py", "preparation.md", "catalog.json",
        "read_receipts.json", "prepared_manifest.json", "prepared_receipt.json", "import_bindings.json", "closed_judge_bindings.json")]
    capture_paths += [gate_path]
    for info in catalog["modules"]:
        author_actual = Path(info["author_receipt"]).parent
        capture_paths += [Path(info["author_receipt"]), Path(info["author_log"]),
            author_actual / (info["module"] + "_START.json"), author_actual / (info["module"] + "_FIN.json")]
''' + launcher[end:]
launcher = launcher.replace('paths = [out, DEPENDENCY_DIR]', 'paths = [out]')
launcher = launcher.replace('    unchanged = before == post and archives_before == archives_post and gate_unchanged',
    '    captures_unchanged = all(sha(item["source"]) == item["sha256"] == sha(item["capture"]) for item in copied)\n    unchanged = before == post and archives_before == archives_post and gate_unchanged and captures_unchanged')
launcher = launcher.replace('"gate_unchanged": gate_unchanged})', '"gate_unchanged": gate_unchanged, "captures_unchanged": captures_unchanged})')
launcher = launcher.replace('"batch01_recompiled": False, "readonly_local_dependencies": ["EpsteinKernel22", "EpsteinFinite22"],',
    '"old_batches_recompiled": False, "readonly_local_dependencies": [], "capture_count": len(copied), "input_count": len(before),\n        "closed_judge_file_count": manifest["closed_judge_files"], "protected_archive_count": len(archives_before),\n        "numeric_bank_replayed": False, "numeric_PASS_used_as_proof": False, "H1_paid": False, "C3_paid": False, "C5_paid": False,')
launcher = launcher.replace('    write_new(out / "receipt.json",',
    '    write_new(out / "FIN.json", {"time_utc": now(), "attempt": args.attempt, "actual_child_invocations": len(rows), "status": "INDEPENDENT_BATCH04_AUX_PASS" if passed else "INDEPENDENT_BATCH04_FAILED"})\n    write_new(out / "receipt.json",')
assert "DEPENDENCY_DIR" not in launcher and "Epstein" not in launcher and "GammaPrerequisites22" not in launcher
with (OWN / "run_once.py").open("x", encoding="utf-8", newline="\n") as stream:
    stream.write(launcher)
print("WROTE_FRESH_THREE_MODULE_SOURCE_METADATA_ONLY_NO_OLD_EXECUTION")
