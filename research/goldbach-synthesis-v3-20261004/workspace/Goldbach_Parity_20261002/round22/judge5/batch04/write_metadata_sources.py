"""Write fresh metadata tools from reviewed helper source text; execute no old module."""
from pathlib import Path

OWN = Path(__file__).resolve().parent
PRIOR = OWN.parent / "batch03"

builder_text = (PRIOR / "prepare_metadata.py").read_text(encoding="utf-8")
helpers = builder_text[builder_text.index("def sha("):builder_text.index("def main(")]
header = '''"""Core19 preparation: byte/import/source metadata only, no compiler or maths."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re

OWN = Path(__file__).resolve().parent
JUDGE = OWN.parent
BASE = JUDGE.parents[1]
CACHE = Path(r"D:\\Users\\Utilisateur\\Desktop\\Maths\\q356-canonical-binding-replay\\.lake\\packages")
PACKAGES = ("aesop", "batteries", "importGraph", "LeanSearchClient", "mathlib", "plausible", "proofwidgets", "Qq")
LEAN_ROOT = Path(r"C:\\Users\\Utilisateur\\.elan\\toolchains\\leanprover--lean4---v4.15.0")
PYTHON = Path(r"C:\\Users\\Utilisateur\\.cache\\codex-runtimes\\codex-primary-runtime\\dependencies\\python\\python.exe")
AUTHOR = BASE / "round22/role3/h1_psi/revision03"
MODULE = "GammaPsiCore22"
SOURCE_SHA = "450962be9526866fa0ffebc39ef29a819d94b57a90000291337550e9f4dc7284"
RECEIPT_SHA = "350be4276efe5013e9530037cc3ad22aeee6ce17231d45ffb1ed1883a9b5a1bf"

'''
main_text = '''def main():
    stamp = datetime.now(timezone.utc).isoformat()
    if (OWN / "prepared_manifest.json").exists():
        raise RuntimeError("No repeat freeze")
    source = AUTHOR / "source_final" / (MODULE + ".lean")
    actual = AUTHOR / "psi_batch03_attempt01"
    author_receipt = actual / "receipt.json"
    receipt = json.loads(author_receipt.read_text(encoding="utf-8"))
    row = receipt["rows"][0]
    if (sha(source) != SOURCE_SHA or sha(author_receipt) != RECEIPT_SHA or row["module"] != MODULE
            or row["exit_code"] != 0 or row["status"] != "AUTHOR_LEAN_AUX_PASS"
            or not row["exact_axiom_coverage_standard_only"] or not receipt["all_inputs_unchanged"]):
        raise RuntimeError("Exact author Core PASS binding mismatch")
    if (sha(actual / (MODULE + ".log")) != row["log_sha256"]
            or sha(actual / (MODULE + ".olean")) != row["olean_sha256"]):
        raise RuntimeError("Author log/olean changed")
    sources = OWN / "sources"
    sources.mkdir(exist_ok=False)
    own_source = sources / source.name
    own_source.write_bytes(source.read_bytes())
    code = lean_code(own_source)
    declarations = re.findall(r"^(theorem|def)\\s+(\\w+)", code, re.MULTILINE)
    prints = re.findall(r"^#print axioms GoldbachContinuous22\\.(\\w+)$", code, re.MULTILINE)
    qualified = ["GoldbachContinuous22." + name for name in prints]
    forbidden = re.findall(r"\\b(?:sorry|admit|axiom|native_decide|unsafe)\\b", code)
    if ([name for _, name in declarations] != prints or len(declarations) != 19 or forbidden
            or sum(kind == "theorem" for kind, _ in declarations) != 15
            or sum(kind == "def" for kind, _ in declarations) != 4
            or [item["declaration"] for item in row["axiom_rows"]] != qualified):
        raise RuntimeError("19 declarations/prints not exact")
    closed, bindings = set(), {}
    for path in JUDGE.iterdir():
        if (path.name.startswith(("batch01_", "batch02_")) or path.name == "batch03"
                or re.match(r"(?:prepare|run|adjudicate)_judge22_batch0[12]", path.name)
                or path.name == "write_batch02_metadata_sources.py"):
            closed.update(item for item in path.rglob("*") if item.is_file()) if path.is_dir() else closed.add(path)
    old_rows = [{"path": str(path), "sha256": sha(path)} for path in sorted(closed)]
    for item in old_rows:
        bindings[item["path"]] = item["sha256"]
    if json.loads((JUDGE / "batch03/batch03_attempt01/receipt.json").read_text(encoding="utf-8"))["status"] != "INDEPENDENT_BATCH03_AUX_PASS":
        raise RuntimeError("Previous independent stage is not closed PASS")
    write_new(OWN / "closed_judge_bindings.json", {"schema": "ROUND22_JUDGE5_CLOSED_BATCHES_BINDINGS", "inputs": old_rows,
        "old_batches_recompiled": False, "compiler_invocations": 0})
    provenance = [source, own_source, author_receipt, actual / (MODULE + ".log"), actual / (MODULE + ".olean"),
        actual / (MODULE + "_START.json"), actual / (MODULE + "_FIN.json"), actual / "START.json",
        actual / "PREEXEC.json", actual / "POSTEXEC.json",
        BASE / ".arbor/sessions/parity/.coordinator/messages/round22_psi03_author_observation.json"]
    for path in provenance:
        bindings[str(path)] = sha(path)
    queue, seen, closure, unresolved = imports(own_source) + ["Init"], set(), [], []
    while queue:
        module = queue.pop()
        if module in seen:
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
    reads = [(source, "FULL", "39f4b0"), (author_receipt, "FULL", "d36265"),
        (actual / (MODULE + ".log"), "FULL", "5e079f"), (actual / (MODULE + "_START.json"), "FULL", "5e079f"),
        (provenance[-1], "FULL", "d24b8c"),
        (CACHE / "mathlib/Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean", "TARGETED_DECLARATIONS_AND_CONTEXT", "d24b8c"),
        (JUDGE / "batch03/adjudication.json", "FULL", "94893b"),
        (JUDGE / "batch03/completion.md", "FULL", "94893b")]
    write_new(OWN / "read_receipts.json", {"schema": "ROUND22_JUDGE5_READ_RECEIPTS_BATCH04", "time_utc": stamp,
        "entries": [{"path": str(path), "sha256": sha(path), "scope": scope, "chunk": chunk} for path, scope, chunk in reads],
        "compiler_invocations": 0, "mathematical_numeric_invocations": 0,
        "numeric_bank_required": False, "all_import_mathematical_FULL_claim": False})
    info = {"module": MODULE, "source": str(own_source), "source_sha256": SOURCE_SHA, "author_source": str(source),
        "author_receipt": str(author_receipt), "author_log": str(actual / (MODULE + ".log")), "author_row": row,
        "author_batch_status": receipt["status"], "declarations": [{"kind": kind, "qualified_name": "GoldbachContinuous22." + name} for kind, name in declarations],
        "qualified_prints": qualified, "theorem_count": 15, "definition_count": 4, "source_forbidden_tokens": forbidden,
        "compiler_options": ["-DmaxHeartbeats=1000000"], "dependencies": [], "scope": "ACTUAL_GAMMA_PSI_BETA_RATIO_AUXILIARY_ONLY"}
    write_new(OWN / "catalog.json", {"schema": "ROUND22_JUDGE5_MODULE_CATALOG_BATCH04", "time_utc": stamp, "modules": [info],
        "module_count": 1, "total_declarations": 19, "theorem_count": 15, "definition_count": 4,
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
    for name in ("write_metadata_sources.py", "prepare_metadata.py", "run_once.py", "preparation.md", "read_receipts.json", "catalog.json",
                 "import_bindings.json", "closed_judge_bindings.json"):
        bindings[str(OWN / name)] = sha(OWN / name)
    for path in (archive_path, LEAN_ROOT / "bin/lean.exe", PYTHON):
        bindings[str(path)] = sha(path)
    manifest = {"schema": "ROUND22_JUDGE5_PREPARED_MANIFEST_BATCH04", "time_utc": stamp,
        "status": "PREPARED_SOURCE_ONLY_GATE_CLOSED" if not unresolved else "PREPARATION_IMPORT_OPEN", "role": "ROLE5", "modules": [MODULE],
        "compiler_invocations": 0, "mathematical_numeric_invocations": 0, "import_module_count": len(closure),
        "implicit_Init_closure_included": True, "unresolved_modules": unresolved,
        "immutable_inputs": [{"path": path, "sha256": digest} for path, digest in sorted(bindings.items())],
        "source_catalog_sha256": sha(OWN / "catalog.json"), "launcher_sha256": sha(OWN / "run_once.py"),
        "numeric_banks": [], "closed_judge_files": len(old_rows), "protected_archive_count": 3089,
        "readonly_local_dependencies": [], "author_olean_used": False, "numeric_PASS_required": False,
        "official_baseline_requires_ROOT_observation": True, "previous_independent_pass_modules": 63,
        "previous_independent_pass_auxiliaries": 1057, "H1_paid": False, "C3_paid": False, "C5_paid": False, "D_N_paid": False, "win": False}
    write_new(OWN / "prepared_manifest.json", manifest)
    print(json.dumps({"status": manifest["status"], "module": MODULE, "declarations": 19, "theorems": 15, "definitions": 4,
        "imports": len(closure), "inputs": len(bindings), "old_judge_files": len(old_rows), "archives": 3089, "unresolved": unresolved,
        "manifest_sha256": sha(OWN / "prepared_manifest.json"), "launcher_sha256": manifest["launcher_sha256"],
        "catalog_sha256": manifest["source_catalog_sha256"], "compiler_invocations": 0, "mathematical_numeric_invocations": 0}))


if __name__ == "__main__":
    main()
'''
with (OWN / "prepare_metadata.py").open("x", encoding="utf-8", newline="\n") as stream:
    stream.write(header + helpers + main_text)

launcher = (PRIOR / "run_once.py").read_text(encoding="utf-8")
launcher = launcher.replace("batch03", "batch04").replace("BATCH03", "BATCH04").replace("GammaDerivative22", "GammaPsiCore22")
launcher = launcher.replace('DEPENDENCY_DIR = JUDGE / "batch02_attempt01"\n', "")
launcher = launcher.replace('len(rows) == 8', 'len(rows) == 19')
launcher = launcher.replace('"readonly_batch02_dependency_directory": str(DEPENDENCY_DIR)', '"readonly_local_dependencies": []')
launcher = launcher.replace('catalog["total_declarations"] != 8', 'catalog["total_declarations"] != 19')
launcher = launcher.replace('exactly eight auxiliary declarations', 'exactly nineteen auxiliary declarations')
start = launcher.index('    previous = json.loads(')
end = launcher.index('    gate_sha = sha(gate_path)', start)
launcher = launcher[:start] + launcher[end:]
start = launcher.index('    capture_paths = [OWN / name')
end = launcher.index('    copied = []', start)
launcher = launcher[:start] + '''    capture_paths = [OWN / name for name in ("sources/GammaPsiCore22.lean", "write_metadata_sources.py", "prepare_metadata.py", "run_once.py",
        "preparation.md", "catalog.json", "prepared_manifest.json", "prepared_receipt.json", "read_receipts.json",
        "import_bindings.json", "closed_judge_bindings.json")]
    author_actual = Path(info["author_receipt"]).parent
    capture_paths += [gate_path, Path(info["author_receipt"]), Path(info["author_log"]),
        author_actual / (MODULE + "_START.json"), author_actual / (MODULE + "_FIN.json"),
        BASE / ".arbor/sessions/parity/.coordinator/messages/round22_psi03_author_observation.json"]
''' + launcher[end:]
launcher = launcher.replace('paths = [out, DEPENDENCY_DIR]', 'paths = [out]')
launcher = launcher.replace('"readonly_local_dependencies": ["GammaPrerequisites22"]', '"readonly_local_dependencies": []')
launcher = launcher.replace('"declarations_passed": 8 if passed else 0', '"declarations_passed": 19 if passed else 0')
assert "DEPENDENCY_DIR" not in launcher and "GammaPrerequisites22" not in launcher
with (OWN / "run_once.py").open("x", encoding="utf-8", newline="\n") as stream:
    stream.write(launcher)
print("WROTE_FRESH_BATCH04_METADATA_SOURCE_ONLY_NO_COMPILER")
