"""Freeze source and dependency metadata only. Never invokes Lean or evaluates maths."""
from __future__ import annotations

from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re

BASE = Path(r"D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002")
OWN = BASE / "round22" / "judge5"
SOURCES = OWN / "batch01_sources"
CACHE = Path(r"D:\Users\Utilisateur\Desktop\Maths\q356-canonical-binding-replay\.lake\packages")
PACKAGES = ("aesop", "batteries", "importGraph", "LeanSearchClient", "mathlib", "plausible", "proofwidgets", "Qq")
LEAN_ROOT = Path(r"C:\Users\Utilisateur\.elan\toolchains\leanprover--lean4---v4.15.0")
PYTHON = Path(r"C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe")
AUTHORS = (
    ("EpsteinKernel22", BASE / "round22" / "role3" / "revision02", "stage01_attempt02",
     "b465bf53b124fa158eed1b5f01171d18ce7f8d7252bf27cf30db1ed7575a773c", []),
    ("EpsteinFinite22", BASE / "round22" / "role3" / "stage02" / "revision03", "stage02_attempt03",
     "fb6205d1d88bbe864fd6c45f6ae60c5296812c966d9b2ce8bd2cccfc2128cc2d", ["EpsteinKernel22"]),
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
    """Lexical metadata scan, preserving line boundaries; no Lean execution."""
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
                raise RuntimeError("Unterminated raw string in metadata import scan")
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
        raise RuntimeError("Unterminated Lean comment/string during metadata scan")
    return "".join(clean)


def imports(path):
    module = r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*"
    pattern = rf"^import[ \t]+({module}(?:[ \t]+{module})*)[ \t]*$"
    return [name for match in re.finditer(pattern, lean_code(path), re.MULTILINE)
            for name in match.group(1).split()]


def resolve(module):
    rel = Path(*module.split("."))
    candidates = [(CACHE / package / rel.with_suffix(".lean"),
                   CACHE / package / ".lake" / "build" / "lib" / rel.with_suffix(".olean"))
                  for package in PACKAGES]
    candidates += [(root / rel.with_suffix(".lean"), LEAN_ROOT / "lib" / "lean" / rel.with_suffix(".olean"))
                   for root in (LEAN_ROOT / "src" / "lean", LEAN_ROOT / "src" / "lean" / "lake")]
    for source, olean in candidates:
        if source.exists() or olean.exists():
            return source, olean
    return None, None


def main():
    stamp = datetime.now(timezone.utc).isoformat()
    SOURCES.mkdir(exist_ok=False)
    bindings, catalog, queue = {}, [], []
    for module, folder, attempt, expected_sha, dependencies in AUTHORS:
        source = folder / (module + ".lean")
        actual = folder / attempt
        receipt_path = actual / "receipt.json"
        receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
        row = receipt["rows"][0]
        if (sha(source) != expected_sha or receipt["status"] != "AUTHOR_STAGE_AUX_PASS"
                or receipt["actual_child_invocations"] != 1 or not receipt["all_source_inputs_unchanged"]
                or row["module"] != module or row["exit_code"] != 0
                or row["source_sha256"] != expected_sha
                or sha(actual / (module + ".log")) != row["log_sha256"]):
            raise RuntimeError("Author PASS provenance mismatch: " + module)
        target = SOURCES / source.name
        target.write_bytes(source.read_bytes())
        if sha(target) != expected_sha:
            raise RuntimeError("Exact source copy mismatch")
        code = lean_code(target)
        declarations = re.findall(r"^(theorem|def)\s+(\w+)", code, re.MULTILINE)
        names = [name for _, name in declarations]
        prints = re.findall(r"^#print axioms Epstein22\.(\w+)$", code, re.MULTILINE)
        forbidden = re.findall(r"\b(?:sorry|admit|axiom|native_decide|unsafe)\b", code)
        if names != prints or forbidden:
            raise RuntimeError("Missing exact axiom coverage or forbidden source token")
        catalog.append({"module": module, "source": str(target), "source_sha256": expected_sha,
                        "author_source": str(source), "author_receipt": str(receipt_path),
                        "author_status": receipt["status"], "dependencies": dependencies,
                        "declarations": [{"kind": kind, "qualified_name": "Epstein22." + name}
                                         for kind, name in declarations],
                        "qualified_prints": ["Epstein22." + name for name in prints],
                        "theorem_count": sum(kind == "theorem" for kind, _ in declarations),
                        "definition_count": sum(kind == "def" for kind, _ in declarations),
                        "source_forbidden_tokens": forbidden,
                        "proof_scope": "AUXILIARY_GEOMETRIC_KERNEL_AND_FINITE_UNFOLDING_ONLY"})
        queue.extend(imports(target))
        for path in (source, target, receipt_path, actual / (module + ".log"),
                     actual / "START.json", actual / "PREEXEC.json", actual / "POSTEXEC.json"):
            bindings[str(path)] = sha(path)
    local = {row["module"] for row in catalog}
    closure, seen, unresolved = [], set(), []
    while queue:
        module = queue.pop()
        if module in seen or module in local:
            continue
        seen.add(module)
        source, olean = resolve(module)
        if source is None or not source.is_file() or not olean.is_file():
            unresolved.append({"module": module, "source": str(source), "olean": str(olean)})
            continue
        row = {"module": module, "source": str(source), "source_sha256": sha(source),
               "olean": str(olean), "olean_sha256": sha(olean), "read_scope": "HASH_AND_IMPORT_METADATA_ONLY"}
        closure.append(row)
        bindings[str(source)] = row["source_sha256"]
        bindings[str(olean)] = row["olean_sha256"]
        queue.extend(imports(source))
    closure.sort(key=lambda row: row["module"])
    read_rows = [
        (BASE / "round22" / "USER_DIRECTIVE.md", "FULL", "0cc8d5"),
        (BASE / "round22" / "PROBE_BLOCK.md", "FULL", "0cc8d5"),
        (AUTHORS[0][1] / "EpsteinKernel22.lean", "FULL", "c705ad"),
        (AUTHORS[1][1] / "EpsteinFinite22.lean", "FULL", "62d976"),
        (AUTHORS[0][1] / AUTHORS[0][2] / "receipt.json", "FULL", "fa2ea5"),
        (AUTHORS[1][1] / AUTHORS[1][2] / "receipt.json", "FULL", "bd3df5"),
        (BASE / "round22" / "role3" / "stage03" / "EpsteinUnfold22.lean", "FULL SOURCE ONLY NOT PASS", "b3bea2"),
        (BASE / "round22" / "role3" / "stage03" / "stage03_attempt01" / "receipt.json", "FULL FAIL RECEIPT", "f3fd38"),
        (BASE / "round22" / "role3" / "stage04" / "EpsteinTail22.lean", "FULL SOURCE ONLY NOT PASS", "9a0a7f"),
        (BASE / "round22" / "role4" / "prepare_gamma_metadata2.py", "FULL METADATA SCANNER REFERENCE", "c83654"),
        (BASE / "round22" / "role6" / "weil_gamma_interface22.md", "FULL SOURCE ONLY INTERFACE", "091f71; prior9f1dba truncated not FULL"),
        (Path(r"C:\Users\Utilisateur\.codex\skills\arbor-agent-executor\SKILL.md"), "FULL", "89d58e"),
        (Path(r"C:\Users\Utilisateur\.codex\skills\arbor-agent-merge-eval\SKILL.md"), "FULL", "147a36"),
    ]
    write_new(OWN / "batch01_read_receipts.json", {"schema": "ROUND22_JUDGE5_READ_RECEIPTS_BATCH01",
        "time_utc": stamp, "entries": [{"path": str(path), "sha256": sha(path), "scope": scope,
                                         "output_chunk": chunk} for path, scope, chunk in read_rows],
        "io_incidents_only": ["Initially looked for author actual_receipt.json; actual names receipt.json",
                              "judge5 absent before creation; no existing judge artifact overwritten",
                              "Broad initial rg encountered three inaccessible old fresh directories; no replay"],
        "compiler_invocations": 0, "mathematical_numeric_invocations": 0})
    write_new(OWN / "batch01_catalog.json", {"schema": "ROUND22_JUDGE5_MODULE_CATALOG_BATCH01",
        "time_utc": stamp, "module_count": len(catalog), "modules": catalog,
        "total_declarations": sum(len(row["declarations"]) for row in catalog),
        "compiler_invocations": 0, "win": False})
    write_new(OWN / "batch01_import_bindings.json", {"schema": "ROUND22_JUDGE5_IMPORT_BINDINGS_BATCH01",
        "time_utc": stamp, "module_count": len(closure), "unresolved": unresolved,
        "entries": closure, "compiler_invocations": 0})
    for path, _, _ in read_rows:
        # Draft failed Unfold/Tail are read receipts only, not executable audit dependencies.
        if "stage03" not in path.parts and "stage04" not in path.parts:
            bindings[str(path)] = sha(path)
    for name in ("batch01_read_receipts.json", "batch01_catalog.json", "batch01_import_bindings.json",
                 "prepare_judge22_batch01.py", "run_judge22_batch01_once.py", "batch01_source_audit.md"):
        path = OWN / name
        bindings[str(path)] = sha(path)
    for path in (BASE / "round22" / "previous_artifacts_sha256.json", LEAN_ROOT / "bin" / "lean.exe", PYTHON,
                 BASE / "round22" / "role6" / "actual_epstein22" / "epstein_result22.json"):
        bindings[str(path)] = sha(path)
    manifest = {"schema": "ROUND22_JUDGE5_PREPARED_MANIFEST_BATCH01", "time_utc": stamp,
        "status": "PREPARED_SOURCE_ONLY_GATE_CLOSED" if not unresolved else "PREPARATION_IMPORT_OPEN",
        "role": "ROLE5", "modules": [row["module"] for row in catalog],
        "source_catalog_sha256": sha(OWN / "batch01_catalog.json"),
        "launcher_sha256": sha(OWN / "run_judge22_batch01_once.py"),
        "immutable_inputs": [{"path": path, "sha256": digest} for path, digest in sorted(bindings.items())],
        "import_module_count": len(closure), "unresolved_modules": unresolved,
        "author_olean_used_by_judge": False, "compiler_invocations": 0,
        "mathematical_numeric_invocations": 0, "official_baseline_modules": 57,
        "official_baseline_auxiliaries": 942, "global_contract_certified": False,
        "D_N_paid": False, "win": False}
    write_new(OWN / "batch01_prepared_manifest.json", manifest)
    print(json.dumps({"status": manifest["status"], "modules": manifest["modules"],
                      "declarations": sum(len(row["declarations"]) for row in catalog),
                      "import_module_count": len(closure), "input_count": len(bindings),
                      "unresolved": unresolved,
                      "manifest_sha256": sha(OWN / "batch01_prepared_manifest.json"),
                      "catalog_sha256": sha(OWN / "batch01_catalog.json"),
                      "launcher_sha256": manifest["launcher_sha256"],
                      "compiler_invocations": 0, "mathematical_numeric_invocations": 0}))


if __name__ == "__main__":
    main()
