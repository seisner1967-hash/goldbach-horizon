"""Core/Beta/Integral byte/import preparation only; no Lean or maths."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
OWN = Path(__file__).resolve().parent
JUDGE = OWN.parents[1]
BASE = JUDGE.parents[1]
CACHE = Path(r"D:\Users\Utilisateur\Desktop\Maths\q356-canonical-binding-replay\.lake\packages")
PACKAGES = ("aesop", "batteries", "importGraph", "LeanSearchClient", "mathlib", "plausible", "proofwidgets", "Qq")
LEAN_ROOT = Path(r"C:\Users\Utilisateur\.elan\toolchains\leanprover--lean4---v4.15.0")
PYTHON = Path(r"C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe")
SPECS = (
 ("GammaPsiCore22", "revision03", "psi_batch03_attempt01", "450962be9526866fa0ffebc39ef29a819d94b57a90000291337550e9f4dc7284", "350be4276efe5013e9530037cc3ad22aeee6ce17231d45ffb1ed1883a9b5a1bf", 15, 4, []),
 ("GammaPsiBetaLimit22", "revision04", "psi_batch04_attempt01", "b4adf3ac71dd7c9d0e6e78f83ce805ddc7eaf5e8f5978aa4c1d6b87bc8caceb8", "73580f763b089606dbe488720d86920658dacad1b100657c26b9c8cc2cf4209b", 20, 3, ["GammaPsiCore22"]),
 ("GammaPsiIntegral22", "revision04", "psi_batch04_attempt01", "3f254cdfeee333aa66eba719b944f64a693fa2e15f0265f340ace9c2a99f6aaf", "73580f763b089606dbe488720d86920658dacad1b100657c26b9c8cc2cf4209b", 9, 1, ["GammaPsiBetaLimit22"]),
)

def sha(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1048576), b""):
            digest.update(block)
    return digest.hexdigest()


def write_new(path, value):
    with Path(path).open("x", encoding="utf-8", newline="\n") as stream:
        json.dump(value, stream, ensure_ascii=False, indent=2)
        stream.write("\n")


def lean_code(path):
    """Metadata lexer, including nested comments; not an elaboration or evaluation."""
    text = Path(path).read_text(encoding="utf-8-sig")
    clean, i, depth, quoted = [], 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                clean.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif quoted:
            if text[i] == "\\":
                i += 2
            elif text[i] == '"':
                quoted = False
                i += 1
            else:
                clean.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif text.startswith("/-", i):
            depth = 1
            clean.append("  ")
            i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        elif text.startswith("r#", i) and (raw := re.match(r'r(#+)"', text[i:])):
            delimiter = '"' + raw.group(1)
            start = i + len(raw.group(0))
            end = text.find(delimiter, start)
            if end < 0:
                raise RuntimeError("Unterminated raw string")
            clean.append("\n" * text[start:end].count("\n"))
            i = end + len(delimiter)
        elif text[i] == "'" and (character := re.match(r"'(?:\\[^\n]|[^\\'\n])'", text[i:])):
            clean.append(" " * len(character.group(0)))
            i += len(character.group(0))
        elif text[i] == '"':
            quoted = True
            clean.append(" ")
            i += 1
        else:
            clean.append(text[i])
            i += 1
    if depth or quoted:
        raise RuntimeError("Unterminated Lean comment/string")
    return "".join(clean)


def imports(path):
    module = r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*"
    pattern = rf"^import[ \t]+({module}(?:[ \t]+{module})*)[ \t]*$"
    return [name for match in re.finditer(pattern, lean_code(path), re.MULTILINE)
            for name in match.group(1).split()]


def resolve(module):
    rel = Path(*module.split("."))
    candidates = [(CACHE / package / rel.with_suffix(".lean"),
                   CACHE / package / ".lake/build/lib" / rel.with_suffix(".olean")) for package in PACKAGES]
    candidates += [(root / rel.with_suffix(".lean"), LEAN_ROOT / "lib/lean" / rel.with_suffix(".olean"))
                   for root in (LEAN_ROOT / "src/lean", LEAN_ROOT / "src/lean/lake")]
    for source, olean in candidates:
        if source.exists() or olean.exists():
            return source, olean
    return None, None


def main():
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
        declarations = re.findall(r"^(theorem|def)\s+(\w+)", code, re.MULTILINE)
        prints = re.findall(r"^#print axioms GoldbachContinuous22\.(\w+)$", code, re.MULTILINE)
        qualified = ["GoldbachContinuous22." + name for name in prints]
        forbidden = re.findall(r"\b(?:sorry|admit|axiom|native_decide|unsafe)\b", code)
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
