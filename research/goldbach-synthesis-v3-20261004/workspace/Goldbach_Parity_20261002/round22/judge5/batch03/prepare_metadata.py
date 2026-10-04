"""Freeze one-source independent Judge metadata; never invokes Lean or mathematics."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re

OWN = Path(__file__).resolve().parent
JUDGE = OWN.parent
BASE = JUDGE.parents[1]
CACHE = Path(r"D:\Users\Utilisateur\Desktop\Maths\q356-canonical-binding-replay\.lake\packages")
PACKAGES = ("aesop", "batteries", "importGraph", "LeanSearchClient", "mathlib", "plausible", "proofwidgets", "Qq")
LEAN_ROOT = Path(r"C:\Users\Utilisateur\.elan\toolchains\leanprover--lean4---v4.15.0")
PYTHON = Path(r"C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe")
AUTHOR = BASE / "round22/role4/h1_contour/analytic_batch01"
SOURCE_SHA = "026ced6097c7d658b41501254bfbcdefe86ff2e68fb9fbe3fab01023a4cb0975"
RECEIPT_SHA = "939122be1e498225f47b15d79bb3357a68573bf306dffad37e31ba54a01ba613"
DEPENDENCY_SHA = "9f5e5fe14d18e2b7c3ab364e461bfcc01d29ee4ef4af6d627d6ad9fcd102fbe7"
DEPENDENCY_OLEAN_SHA = "fc0dad0b550f13a5c3a5b1e7cf1cfa22fc3a233822fc548cce155ab7a7274477"
MODULE = "GammaDerivative22"


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
        raise RuntimeError("No repeat preparation of a frozen batch")
    sources = OWN / "sources"
    sources.mkdir(exist_ok=False)
    source = AUTHOR / "sources" / (MODULE + ".lean")
    actual = AUTHOR / "actual_attempt01"
    author_receipt = actual / "receipt.json"
    receipt = json.loads(author_receipt.read_text(encoding="utf-8"))
    if sha(source) != SOURCE_SHA or sha(author_receipt) != RECEIPT_SHA:
        raise RuntimeError("Author bytes differ from authorized source/receipt")
    row = receipt["rows"][0]
    if (row["module"] != MODULE or row["source_sha256"] != SOURCE_SHA or row["exit_code"] != 0
            or row["status"] != "AUTHOR_ANALYTIC_AUX_PASS_PENDING_JUDGE"
            or not row["exact_standard_axiom_coverage"]):
        raise RuntimeError("The specific author module is not PASS")
    for key, suffix in (("stdout_sha256", ".stdout.log"), ("stderr_sha256", ".stderr.log"), ("olean_sha256", ".olean")):
        if sha(actual / (MODULE + suffix)) != row[key]:
            raise RuntimeError("Author artifact mismatch: " + key)
    own_source = sources / source.name
    own_source.write_bytes(source.read_bytes())
    code = lean_code(own_source)
    declarations = re.findall(r"^(theorem|def)\s+(\w+)", code, re.MULTILINE)
    prints = re.findall(r"^#print axioms GoldbachContinuous22\.(\w+)$", code, re.MULTILINE)
    qualified = ["GoldbachContinuous22." + name for name in prints]
    forbidden = re.findall(r"\b(?:sorry|admit|axiom|native_decide|unsafe)\b", code)
    if (len(declarations) != 8 or any(kind != "theorem" for kind, _ in declarations)
            or [name for _, name in declarations] != prints or forbidden
            or [item["declaration"] for item in row["qualified_axiom_rows"]] != qualified):
        raise RuntimeError("Declaration/print coverage or forbidden-token mismatch")
    dependency_source = JUDGE / "batch02_sources/GammaPrerequisites22.lean"
    dependency_dir = JUDGE / "batch02_attempt01"
    if sha(dependency_source) != DEPENDENCY_SHA or sha(dependency_dir / "GammaPrerequisites22.olean") != DEPENDENCY_OLEAN_SHA:
        raise RuntimeError("Own readonly Gamma dependency changed")
    dependency_receipt = json.loads((dependency_dir / "receipt.json").read_text(encoding="utf-8"))
    if (dependency_receipt["status"] != "INDEPENDENT_BATCH02_AUX_PASS"
            or dependency_receipt["rows"][2]["module"] != "GammaPrerequisites22"
            or dependency_receipt["rows"][2]["status"] != "INDEPENDENT_LEAN_AUX_PASS"):
        raise RuntimeError("Readonly dependency lacks independent PASS")
    bindings = {}
    closed = set()
    for path in JUDGE.iterdir():
        if (path.name.startswith(("batch01_", "batch02_"))
                or re.match(r"(?:prepare|run|adjudicate)_judge22_batch0[12]", path.name)
                or path.name == "write_batch02_metadata_sources.py"):
            closed.update(item for item in path.rglob("*") if item.is_file()) if path.is_dir() else closed.add(path)
    old_rows = [{"path": str(path), "sha256": sha(path)} for path in sorted(closed)]
    for item in old_rows:
        bindings[item["path"]] = item["sha256"]
    write_new(OWN / "closed_judge_bindings.json", {"schema": "ROUND22_JUDGE5_CLOSED_BATCHES_BINDINGS", "inputs": old_rows,
        "batch01_recompiled": False, "batch02_recompiled": False, "compiler_invocations": 0})
    provenance = [source, own_source, author_receipt, actual / (MODULE + ".stdout.log"), actual / (MODULE + ".stderr.log"),
        actual / (MODULE + "_START.json"), actual / (MODULE + "_FIN.json"), actual / (MODULE + ".olean"),
        actual / "START.json", actual / "PREEXEC.json", actual / "POSTEXEC.json",
        BASE / ".arbor/sessions/parity/.coordinator/messages/round22_analytic_author01_observation.json"]
    for path in provenance:
        bindings[str(path)] = sha(path)
    queue = imports(own_source) + imports(dependency_source) + ["Init"]
    closure, seen, unresolved = [], set(), []
    while queue:
        module = queue.pop()
        if module in seen or module in (MODULE, "GammaPrerequisites22"):
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
    write_new(OWN / "import_bindings.json", {"schema": "ROUND22_JUDGE5_IMPORT_BINDINGS_BATCH03", "module_count": len(closure),
        "explicit_implicit_prelude_seed": "Init", "unresolved": unresolved,
        "entries": sorted(closure, key=lambda item: item["module"]), "compiler_invocations": 0})
    bank_dir = BASE / "round22/role6/thermal_h1/revision01"
    bank_path = bank_dir / "actual_r01/result_r01.json"
    bank = json.loads(bank_path.read_text(encoding="utf-8"))
    bank_closure = json.loads((bank_dir / "closure_receipt_r01.json").read_text(encoding="utf-8-sig"))
    if (sha(bank_path) != "c43622616022e65991aee5a12d189d3bae142db1f2d347cb131e8abd685c7a6c"
            or bank["status"] != "THERMAL_COMPONENT_R01_AUX_PASS"
            or bank_closure["status"] != "CLOSED_AUX_PASS_NO_REPLAY"
            or bank_closure["case_count"] != 46 or bank_closure["mutation_count"] != 19):
        raise RuntimeError("Closed component R01 provenance changed")
    banks = [{"path": str(bank_path), "sha256": sha(bank_path), "status": bank["status"],
        "scope": bank_closure["scope"], "case_count": 46, "mutation_count": 19,
        "read_scope": "STATUS_PROJECTION_AND_FULL_CLOSURE_REPORT_NOT_FULL_RAW_RESULT", "replayed": False}]
    bank_artifacts = [bank_dir / "contract_r01.json", bank_dir / "closure_report_r01.md", bank_dir / "closure_receipt_r01.json"]
    bank_artifacts += [Path(item["path"]) for item in bank_closure["actual_bindings"]]
    for path in bank_artifacts:
        bindings[str(path)] = sha(path)
    reads = [
        (source, "FULL", "a8c01d"), (author_receipt, "FULL", "d272e7"),
        (actual / (MODULE + ".stdout.log"), "FULL", "1e78c7"),
        (actual / (MODULE + "_START.json"), "FULL", "1e78c7"),
        (provenance[-1], "FULL", "e53193"),
        (dependency_source, "FULL_IN_PREVIOUS_JUDGE_TURN", "21d3da"),
        (dependency_dir / "receipt.json", "FULL_IN_PREVIOUS_JUDGE_TURN", "feeb00"),
        (bank_dir / "closure_receipt_r01.json", "FULL", "4d371e"),
        (bank_dir / "closure_report_r01.md", "FULL", "4d371e"),
        (bank_dir / "contract_r01.json", "FULL", "4d371e"),
        (bank_dir / "actual_r01/actual_receipt.json", "FULL", "cd59b9"),
        (CACHE / "mathlib/Mathlib/Analysis/Complex/Liouville.lean", "TARGETED_DECLARATION_AND_CONTEXT", "f08e4d"),
        (BASE / "round22/USER_DIRECTIVE.md", "FULL_IN_PREVIOUS_JUDGE_TURN", "0cc8d5"),
        (BASE / "round22/PROBE_BLOCK.md", "FULL_IN_PREVIOUS_JUDGE_TURN", "0cc8d5"),
        (Path(r"C:\Users\Utilisateur\.codex\skills\arbor-agent-executor\SKILL.md"), "FULL_IN_PREVIOUS_JUDGE_TURN", "89d58e"),
        (Path(r"C:\Users\Utilisateur\.codex\skills\arbor-agent-merge-eval\SKILL.md"), "FULL_IN_PREVIOUS_JUDGE_TURN", "147a36"),
    ]
    write_new(OWN / "read_receipts.json", {"schema": "ROUND22_JUDGE5_READ_RECEIPTS_BATCH03", "time_utc": stamp,
        "entries": [{"path": str(path), "sha256": sha(path), "scope": scope, "chunk": chunk} for path, scope, chunk in reads],
        "numeric_results": banks, "numeric_projection_chunk": "cd59b9",
        "metadata_read_incidents": ["cd59b9 selected absent result keys returned null; counts/scope use FULL closure receipt, not these nulls"],
        "compiler_invocations": 0, "mathematical_numeric_invocations": 0})
    info = {"module": MODULE, "source": str(own_source), "source_sha256": SOURCE_SHA,
        "author_source": str(source), "author_receipt": str(author_receipt), "author_row": row,
        "author_batch_status": receipt["status"], "author_log": str(actual / (MODULE + ".stdout.log")),
        "declarations": [{"kind": kind, "qualified_name": "GoldbachContinuous22." + name} for kind, name in declarations],
        "qualified_prints": qualified, "theorem_count": 8, "definition_count": 0,
        "source_forbidden_tokens": forbidden, "compiler_options": ["-DmaxHeartbeats=1000000"],
        "dependencies": ["GammaPrerequisites22"], "scope": "AUXILIARY_CONTINUOUS_GAMMA_DERIVATIVE_ONLY"}
    write_new(OWN / "catalog.json", {"schema": "ROUND22_JUDGE5_MODULE_CATALOG_BATCH03", "time_utc": stamp,
        "modules": [info], "module_count": 1, "total_declarations": 8, "theorem_count": 8, "definition_count": 0,
        "readonly_local_dependencies": ["GammaPrerequisites22"], "compiler_invocations": 0, "win": False})
    archive_path = BASE / "round22/previous_artifacts_sha256.json"
    archives = json.loads(archive_path.read_text(encoding="utf-8"))
    for relative, expected in archives["sha256"].items():
        if sha(BASE / relative) != expected:
            raise RuntimeError("Old protected archive changed: " + relative)
    if len(archives["sha256"]) != archives["file_count"] or archives["file_count"] != 3089:
        raise RuntimeError("Protected archive registry count mismatch")
    for path, _, _ in reads:
        bindings[str(path)] = sha(path)
    for name in ("prepare_metadata.py", "run_once.py", "preparation.md", "read_receipts.json", "catalog.json",
                 "import_bindings.json", "closed_judge_bindings.json"):
        bindings[str(OWN / name)] = sha(OWN / name)
    for path in (archive_path, LEAN_ROOT / "bin/lean.exe", PYTHON):
        bindings[str(path)] = sha(path)
    manifest = {"schema": "ROUND22_JUDGE5_PREPARED_MANIFEST_BATCH03", "time_utc": stamp,
        "status": "PREPARED_SOURCE_ONLY_GATE_CLOSED" if not unresolved else "PREPARATION_IMPORT_OPEN",
        "role": "ROLE5", "modules": [MODULE], "compiler_invocations": 0, "mathematical_numeric_invocations": 0,
        "import_module_count": len(closure), "implicit_Init_closure_included": True, "unresolved_modules": unresolved,
        "immutable_inputs": [{"path": path, "sha256": digest} for path, digest in sorted(bindings.items())],
        "source_catalog_sha256": sha(OWN / "catalog.json"), "launcher_sha256": sha(OWN / "run_once.py"),
        "numeric_banks": banks, "closed_judge_files": len(old_rows), "protected_archive_count": 3089,
        "readonly_batch02_dependency_directory": str(dependency_dir), "author_olean_used": False,
        "official_baseline_modules": 62, "official_baseline_auxiliaries": 1049,
        "global_trace_certified": False, "H1_paid": False, "C3_paid": False, "C5_paid": False, "D_N_paid": False, "win": False}
    write_new(OWN / "prepared_manifest.json", manifest)
    print(json.dumps({"status": manifest["status"], "modules": [MODULE], "declarations": 8,
        "imports": len(closure), "inputs": len(bindings), "closed_judge_files": len(old_rows), "archives": 3089,
        "unresolved": unresolved, "manifest_sha256": sha(OWN / "prepared_manifest.json"),
        "catalog_sha256": manifest["source_catalog_sha256"], "launcher_sha256": manifest["launcher_sha256"],
        "compiler_invocations": 0, "mathematical_numeric_invocations": 0}))


if __name__ == "__main__":
    main()
