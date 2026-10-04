"""New batch05 metadata preparation only. No subprocess, Lean, or numeric maths."""
from datetime import datetime, timezone
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

OWN = Path(__file__).resolve().parent
JUDGE = OWN.parent
BASE = JUDGE.parents[1]
CACHE = Path(r"D:\Users\Utilisateur\Desktop\Maths\q356-canonical-binding-replay\.lake\packages")
PACKAGES = ("aesop", "batteries", "importGraph", "LeanSearchClient", "mathlib", "plausible", "proofwidgets", "Qq")
LEAN_ROOT = Path(r"C:\Users\Utilisateur\.elan\toolchains\leanprover--lean4---v4.15.0")
PYTHON = Path(r"C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe")
PYTHON_SHA = "4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c"
LEAN_SHA = "8a1ef18583d74d917194bba4743ce9765bad64b00c52bada002ee44796fb9e08"
MODULES = ("GammaBoxBounds22", "GammaContourComponent22")
LOCAL_DEPENDENCIES = ("GammaPrerequisites22", "GammaDerivative22")
AUTHOR = BASE / "round22/role4/h1_contour/analytic_batch02"
REPAIR = BASE / "round22/role3/contour_dependency_source22"
SPECS = (
    (MODULES[0], AUTHOR / "source-final/GammaBoxBounds22.lean",
     "4874192b1c2ca9edc7262d8a46f9d4a1e339c565e5bb48fefbf4d6d100071edf", 9, 3, "AUTHOR_PASS_PENDING_INDEPENDENT_JUDGE", "6f671a"),
    (MODULES[1], REPAIR / "GammaContourComponent22.lean",
     "891454d4714e68039a0976e7eb9347e10653237f4608993b52b481cc95b0a3fe", 8, 3, "CORRECTED_SOURCE_NOT_COMPILED", "c9134c"),
)
DEPS = (
    (LOCAL_DEPENDENCIES[0], JUDGE / "batch02_sources/GammaPrerequisites22.lean",
     JUDGE / "batch02_attempt01/GammaPrerequisites22.olean", JUDGE / "batch02_attempt01/receipt.json",
     "9f5e5fe14d18e2b7c3ab364e461bfcc01d29ee4ef4af6d627d6ad9fcd102fbe7",
     "fc0dad0b550f13a5c3a5b1e7cf1cfa22fc3a233822fc548cce155ab7a7274477", "63b5ef", "d0859a"),
    (LOCAL_DEPENDENCIES[1], JUDGE / "batch03/sources/GammaDerivative22.lean",
     JUDGE / "batch03/batch03_attempt01/GammaDerivative22.olean", JUDGE / "batch03/batch03_attempt01/receipt.json",
     "026ced6097c7d658b41501254bfbcdefe86ff2e68fb9fbe3fab01023a4cb0975",
     "0618f801c5feec7b760ba18ab3dddc960519b398dd1d1b719acc809132518125", "49e477", "e762e6"),
)


def sha(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1048576), b""):
            digest.update(block)
    return digest.hexdigest()


def write_new(path, data):
    with Path(path).open("x", encoding="utf-8", newline="\n") as stream:
        json.dump(data, stream, ensure_ascii=False, indent=2)
        stream.write("\n")


def lean_code(path):
    """Metadata lexer for import/declaration names; does not elaborate Lean."""
    content = Path(path).read_text(encoding="utf-8-sig")
    clean, i, depth, quoted = [], 0, 0, False
    while i < len(content):
        if depth:
            if content.startswith("/-", i):
                depth += 1
                i += 2
            elif content.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                clean.append("\n" if content[i] == "\n" else " ")
                i += 1
        elif quoted:
            if content[i] == "\\":
                i += 2
            elif content[i] == '"':
                quoted = False
                i += 1
            else:
                clean.append("\n" if content[i] == "\n" else " ")
                i += 1
        elif content.startswith("/-", i):
            depth = 1
            clean.append("  ")
            i += 2
        elif content.startswith("--", i):
            end = content.find("\n", i)
            i = len(content) if end < 0 else end
        elif content.startswith("r#", i) and (raw := re.match(r'r(#+)"', content[i:])):
            delimiter = '"' + raw.group(1)
            start = i + len(raw.group(0))
            end = content.find(delimiter, start)
            if end < 0:
                raise RuntimeError("Unterminated raw string")
            clean.append("\n" * content[start:end].count("\n"))
            i = end + len(delimiter)
        elif content[i] == "'" and (character := re.match(r"'(?:\\[^\n]|[^\\'\n])'", content[i:])):
            clean.append(" " * len(character.group(0)))
            i += len(character.group(0))
        elif content[i] == '"':
            quoted = True
            clean.append(" ")
            i += 1
        else:
            clean.append(content[i])
            i += 1
    if depth or quoted:
        raise RuntimeError("Unterminated Lean comment/string")
    return "".join(clean)


def imports(path):
    name = r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*"
    pattern = rf"^import[ \t]+({name}(?:[ \t]+{name})*)[ \t]*$"
    return [item for match in re.finditer(pattern, lean_code(path), re.MULTILINE)
            for item in match.group(1).split()]


def resolve(module):
    rel = Path(*module.split("."))
    candidates = [(CACHE / package / rel.with_suffix(".lean"),
                   CACHE / package / ".lake/build/lib" / rel.with_suffix(".olean")) for package in PACKAGES]
    candidates += [(root / rel.with_suffix(".lean"), LEAN_ROOT / "lib/lean" / rel.with_suffix(".olean"))
                   for root in (LEAN_ROOT / "src/lean", LEAN_ROOT / "src/lean/lake")]
    for source, obj in candidates:
        if source.exists() or obj.exists():
            return source, obj
    return None, None


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--builder-read", required=True)
    parser.add_argument("--launcher-read", required=True)
    parser.add_argument("--audit-read", required=True)
    args = parser.parse_args()
    if (OWN / "prepared_manifest.json").exists():
        raise RuntimeError("No repeat freeze")
    if Path(sys.executable).resolve() != PYTHON.resolve() or sha(PYTHON) != PYTHON_SHA or sha(LEAN_ROOT / "bin/lean.exe") != LEAN_SHA:
        raise RuntimeError("Pinned runtime mismatch")
    stamp = datetime.now(timezone.utc).isoformat()
    bindings, reads, rows, dependencies, queue = {}, [], [], [], ["Init"]
    author_receipt = AUTHOR / "actual_attempt01/receipt.json"
    if sha(author_receipt) != "d0bb6fda4cbdb187bea72c72423764a888c6a9cbd8ba87112e9d2519184dcbab":
        raise RuntimeError("Author receipt binding changed")
    author = json.loads(author_receipt.read_text(encoding="utf-8"))
    boxrow = next(row for row in author["rows"] if row["module"] == MODULES[0])
    if boxrow["exit_code"] != 0 or not boxrow["exact_standard_axiom_coverage"] or author["changed_inputs"]:
        raise RuntimeError("GammaBox author PASS not bound")
    for module, original, digest, nthm, ndef, status, chunk in SPECS:
        own_source = OWN / "sources" / (module + ".lean")
        if sha(original) != digest or sha(own_source) != digest:
            raise RuntimeError("Exact immutable source copy mismatch")
        code = lean_code(own_source)
        decls = re.findall(r"^(theorem|def)\s+(\w+)", code, re.MULTILINE)
        printed = re.findall(r"^#print axioms GoldbachContinuous22\.(\w+)$", code, re.MULTILINE)
        if ([name for _, name in decls] != printed or len(set(printed)) != len(printed)
                or sum(kind == "theorem" for kind, _ in decls) != nthm
                or sum(kind == "def" for kind, _ in decls) != ndef
                or re.search(r"\b(?:sorry|admit|axiom|native_decide|unsafe)\b", code)):
            raise RuntimeError("Declaration/print/forbidden-token mismatch")
        qualified = ["GoldbachContinuous22." + name for name in printed]
        if module == MODULES[0] and [item["declaration"] for item in boxrow["qualified_axiom_rows"]] != qualified:
            raise RuntimeError("GammaBox author print coverage changed")
        rows.append({"module": module, "source": str(own_source), "source_sha256": digest,
            "original_source": str(original), "source_status": status,
            "declarations": [{"kind": kind, "qualified_name": "GoldbachContinuous22." + name} for kind, name in decls],
            "qualified_prints": qualified, "theorem_count": nthm, "definition_count": ndef,
            "compiler_options": ["-DmaxHeartbeats=1000000"], "author_olean_allowed": False,
            "scope": "TRUE_WEIGHTED_GAMMA_BOX_AND_FACTOR_TAIL_AUX_ONLY"})
        for path in (original, own_source):
            bindings[str(path)] = sha(path)
        reads.append((original, "FULL", chunk))
        queue.extend(imports(own_source))
    actual = AUTHOR / "actual_attempt01"
    for suffix, key in ((".stdout.log", "stdout_sha256"), (".stderr.log", "stderr_sha256"), (".olean", "olean_sha256")):
        path = actual / (MODULES[0] + suffix)
        if sha(path) != boxrow[key]:
            raise RuntimeError("Author Box artifact changed")
        bindings[str(path)] = sha(path)
    for path in (author_receipt, actual / "GammaBoxBounds22_FIN.json", actual / "GammaBoxBounds22_START.json",
                 actual / "GammaContourComponent22_FIN.json", actual / "GammaContourComponent22.stdout.log",
                 actual / "PREEXEC.json", actual / "POSTEXEC.json"):
        bindings[str(path)] = sha(path)
    depdir = OWN / "readonly_oleans"
    depdir.mkdir(exist_ok=False)
    for module, source, obj, receipt_path, source_sha, obj_sha, rchunk, schunk in DEPS:
        receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
        row = next(item for item in receipt["rows"] if item["module"] == module)
        if (row["status"] != "INDEPENDENT_LEAN_AUX_PASS" or row["exit_code"] != 0
                or not row["exact_axiom_coverage_standard_only"] or not receipt["all_inputs_unchanged"]
                or row["source_sha256"] != source_sha or row["olean_sha256"] != obj_sha
                or sha(source) != source_sha or sha(obj) != obj_sha):
            raise RuntimeError("Readonly independent dependency mismatch")
        copy = depdir / (module + ".olean")
        copy.write_bytes(obj.read_bytes())
        if sha(copy) != obj_sha:
            raise RuntimeError("Readonly dependency copy mismatch")
        dependencies.append({"module": module, "source": str(source), "source_sha256": source_sha,
            "independent_olean": str(obj), "olean_copy": str(copy), "olean_sha256": obj_sha,
            "independent_receipt": str(receipt_path), "recompiled": False})
        for path in (source, obj, copy, receipt_path):
            bindings[str(path)] = sha(path)
        reads += [(source, "FULL", schunk), (receipt_path, "FULL", rchunk)]
        queue.extend(imports(source))
    if set(path.name for path in depdir.iterdir()) != {module + ".olean" for module in LOCAL_DEPENDENCIES}:
        raise RuntimeError("Unexpected readonly local dependency")
    closed = [path for path in JUDGE.rglob("*") if path.is_file() and OWN not in path.parents]
    old_rows = [{"path": str(path), "sha256": sha(path)} for path in sorted(closed)]
    bindings.update({row["path"]: row["sha256"] for row in old_rows})
    if json.loads((JUDGE / "batch04/three_modules/batch04_attempt01/receipt.json").read_text(encoding="utf-8"))["status"] != "INDEPENDENT_BATCH04_AUX_PASS":
        raise RuntimeError("Closed batch04 receipt missing")
    write_new(OWN / "closed_judge_bindings.json", {"schema": "ROUND22_JUDGE5_CLOSED_BINDINGS_BATCH05",
        "inputs": old_rows, "old_batches_recompiled": False, "compiler_invocations": 0})
    closure, unresolved, seen = [], [], set()
    while queue:
        module = queue.pop()
        if module in seen or module in MODULES or module in LOCAL_DEPENDENCIES:
            continue
        seen.add(module)
        source, obj = resolve(module)
        if source is None or not source.is_file() or not obj.is_file():
            unresolved.append({"module": module, "source": str(source), "olean": str(obj)})
            continue
        item = {"module": module, "source": str(source), "source_sha256": sha(source),
                "olean": str(obj), "olean_sha256": sha(obj), "read_scope": "HASH_AND_IMPORT_METADATA_ONLY"}
        closure.append(item)
        bindings[str(source)], bindings[str(obj)] = item["source_sha256"], item["olean_sha256"]
        queue.extend(imports(source))
    write_new(OWN / "import_bindings.json", {"schema": "ROUND22_JUDGE5_IMPORT_BINDINGS_BATCH05",
        "module_count": len(closure), "explicit_implicit_prelude_seed": "Init", "unresolved": unresolved,
        "entries": sorted(closure, key=lambda row: row["module"]), "readonly_local_entries": dependencies,
        "compiler_invocations": 0})
    reads += [(author_receipt, "FULL", "48bb9f"), (actual / "GammaBoxBounds22_FIN.json", "FULL", "942dcf"),
        (actual / "GammaBoxBounds22.stdout.log", "FULL", "f78466"),
        (REPAIR / "source_review22.md", "FULL", "0a8cba"),
        (REPAIR / "checkpoint_for_numeric_handoff22.md", "FULL", "97d7c1"),
        (CACHE / "mathlib/Mathlib/Topology/Basic.lean", "TARGETED_LINES_1438_1454", "0a7ea3"),
        (CACHE / "mathlib/Mathlib/Analysis/SpecialFunctions/ImproperIntegrals.lean", "TARGETED_LINES_1_53", "0a7ea3"),
        (OWN / "prepare_metadata.py", "FULL_BEFORE_METADATA_RUN", args.builder_read),
        (OWN / "run_once.py", "FULL_SOURCE_ONLY_NEVER_EXECUTED", args.launcher_read),
        (OWN / "preparation.md", "FULL_SOURCE_AUDIT", args.audit_read)]
    for path, _, _ in reads:
        bindings[str(path)] = sha(path)
    write_new(OWN / "read_receipts.json", {"schema": "ROUND22_JUDGE5_READ_RECEIPTS_BATCH05", "time_utc": stamp,
        "entries": [{"path": str(path), "sha256": sha(path), "scope": scope, "chunk": chunk} for path, scope, chunk in reads],
        "truncated_reads_excluded": ["1aaa00/255a2f combined", "45d119", "83c20c"],
        "all_import_mathematical_FULL_claim": False, "compiler_invocations": 0, "numeric_invocations": 0})
    write_new(OWN / "catalog.json", {"schema": "ROUND22_JUDGE5_CATALOG_BATCH05", "time_utc": stamp,
        "modules": rows, "module_count": 2, "total_declarations": 23, "theorem_count": 17, "definition_count": 6,
        "readonly_local_dependencies": list(LOCAL_DEPENDENCIES), "dependency_bindings": dependencies,
        "corrected_contour_author_PASS_claimed": False, "compiler_invocations": 0, "win": False})
    archive_path = BASE / "round22/previous_artifacts_sha256.json"
    archives = json.loads(archive_path.read_text(encoding="utf-8"))
    if len(archives["sha256"]) != 3089 or archives["file_count"] != 3089:
        raise RuntimeError("Protected archive count changed")
    for relative, digest in archives["sha256"].items():
        if sha(BASE / relative) != digest:
            raise RuntimeError("Protected archive changed")
    for path in (archive_path, PYTHON, LEAN_ROOT / "bin/lean.exe"):
        bindings[str(path)] = sha(path)
    for name in ("prepare_metadata.py", "run_once.py", "preparation.md", "catalog.json", "read_receipts.json",
                 "import_bindings.json", "closed_judge_bindings.json"):
        bindings[str(OWN / name)] = sha(OWN / name)
    manifest = {"schema": "ROUND22_JUDGE5_PREPARED_MANIFEST_BATCH05", "time_utc": stamp,
        "status": "PREPARED_SOURCE_ONLY_GATE_CLOSED" if not unresolved else "PREPARATION_IMPORT_OPEN",
        "role": "ROLE5", "modules": list(MODULES), "compiler_invocations": 0, "numeric_invocations": 0,
        "immutable_inputs": [{"path": path, "sha256": digest} for path, digest in sorted(bindings.items())],
        "import_module_count": len(closure), "implicit_Init_closure_included": True, "unresolved_modules": unresolved,
        "source_catalog_sha256": sha(OWN / "catalog.json"), "launcher_sha256": sha(OWN / "run_once.py"),
        "readonly_local_dependencies": list(LOCAL_DEPENDENCIES), "closed_judge_files": len(old_rows),
        "protected_archive_count": 3089, "author_olean_used": False, "numeric_banks": [],
        "previous_official_modules": 66, "previous_official_declarations": 1109,
        "hypothetical_after_two_PASS_modules": 68, "hypothetical_after_two_PASS_declarations": 1132,
        "official_count_requires_ROOT_observation": True,
        "H1_paid": False, "C3_paid": False, "C5_paid": False, "D_N_paid": False, "win": False}
    write_new(OWN / "prepared_manifest.json", manifest)
    receipt = {"schema": "ROUND22_JUDGE5_PREPARATION_RECEIPT_BATCH05", "time_utc": datetime.now(timezone.utc).isoformat(),
        "status": manifest["status"], "compiler_invocations": 0, "numeric_invocations": 0,
        "manifest_sha256": sha(OWN / "prepared_manifest.json"), "launcher_sha256": manifest["launcher_sha256"],
        "catalog_sha256": manifest["source_catalog_sha256"], "read_receipts_sha256": sha(OWN / "read_receipts.json"),
        "import_bindings_sha256": sha(OWN / "import_bindings.json"), "closed_judge_bindings_sha256": sha(OWN / "closed_judge_bindings.json"),
        "imports": len(closure), "inputs": len(bindings), "closed_judge_files": len(old_rows), "archives": 3089,
        "declarations": 23, "theorems": 17, "definitions": 6, "unresolved": unresolved,
        "corrected_contour_not_compiled": True, "no_author_olean_on_lean_path": True,
        "old_batches_recompiled": False, "numeric_bank_replayed": False, "no_win": True}
    write_new(OWN / "prepared_receipt.json", receipt)
    print(json.dumps(receipt, sort_keys=True))


if __name__ == "__main__":
    main()
