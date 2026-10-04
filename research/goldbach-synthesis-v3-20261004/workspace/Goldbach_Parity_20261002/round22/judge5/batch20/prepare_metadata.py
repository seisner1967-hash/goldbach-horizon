"""New batch20 SOURCE freeze only: hashing and lexical imports; no subprocess."""
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
CACHE = BASE.parent / "q356-canonical-binding-replay/.lake/packages"
PACKAGES = ("aesop", "batteries", "importGraph", "LeanSearchClient", "mathlib", "plausible", "proofwidgets", "Qq")
LEAN_ROOT = Path(r"C:\Users\Utilisateur\.elan\toolchains\leanprover--lean4---v4.15.0")
PYTHON = Path(r"C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe")
PYTHON_SHA = "4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c"
LEAN_SHA = "8a1ef18583d74d917194bba4743ce9765bad64b00c52bada002ee44796fb9e08"
SPECS = (
    ("ThermalGammaMellinInverse22", "role3/thermal_gamma_mellin_revision02", "daad8b5d5fb1181bfc714e1b470edd7d9a6ae07e9a1b76c384481964a42caf91", 9, 2, "SOURCE_ONLY_NOT_COMPILED", "e7807e", "GoldbachThermalMellin22"),)
MODULES = tuple(row[0] for row in SPECS)
LOCAL_DEPENDENCIES = ("GammaPrerequisites22",)
DEP_SOURCE = JUDGE / "batch02_sources/GammaPrerequisites22.lean"
DEP_OLEAN = JUDGE / "batch02_attempt01/GammaPrerequisites22.olean"
DEP_RECEIPT = JUDGE / "batch02_attempt01/receipt.json"
DEP_SOURCE_SHA = "9f5e5fe14d18e2b7c3ab364e461bfcc01d29ee4ef4af6d627d6ad9fcd102fbe7"
DEP_OLEAN_SHA = "fc0dad0b550f13a5c3a5b1e7cf1cfa22fc3a233822fc548cce155ab7a7274477"
DEP_RECEIPT_SHA = "a159b22e7ac4e8718f0572fdbf3e6d424294571eab01d5ed1ff979a821af48f9"


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
    """Discard comments and strings for lexical metadata, never elaborate."""
    content = Path(path).read_text(encoding="utf-8-sig")
    clean, i, depth, quoted = [], 0, 0, False
    while i < len(content):
        if depth:
            if content.startswith("/-", i):
                depth += 1; i += 2
            elif content.startswith("-/", i):
                depth -= 1; i += 2
            else:
                clean.append("\n" if content[i] == "\n" else " "); i += 1
        elif quoted:
            if content[i] == "\\":
                i += 2
            elif content[i] == '"':
                quoted = False; i += 1
            else:
                clean.append("\n" if content[i] == "\n" else " "); i += 1
        elif content.startswith("/-", i):
            depth = 1; clean.append("  "); i += 2
        elif content.startswith("--", i):
            end = content.find("\n", i); i = len(content) if end < 0 else end
        elif content.startswith("r#", i) and (raw := re.match(r'r(#+)"', content[i:])):
            start = i + len(raw.group(0)); delimiter = '"' + raw.group(1)
            end = content.find(delimiter, start)
            if end < 0: raise RuntimeError("Unterminated raw string")
            clean.append("\n" * content[start:end].count("\n")); i = end + len(delimiter)
        elif content[i] == "'" and (character := re.match(r"'(?:\\[^\n]|[^\\'\n])'", content[i:])):
            clean.append(" " * len(character.group(0))); i += len(character.group(0))
        elif content[i] == '"':
            quoted = True; clean.append(" "); i += 1
        else:
            clean.append(content[i]); i += 1
    if depth or quoted: raise RuntimeError("Unterminated comment/string")
    return "".join(clean)


def imports(path):
    name = r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*"
    return [word for match in re.finditer(rf"^import[ \t]+({name}(?:[ \t]+{name})*)[ \t]*$", lean_code(path), re.M) for word in match.group(1).split()]


def resolve(module):
    if module == "GammaPrerequisites22":
        return DEP_SOURCE, OWN / "readonly_oleans/GammaPrerequisites22.olean"
    rel = Path(*module.split("."))
    candidates = [(CACHE / package / rel.with_suffix(".lean"), CACHE / package / ".lake/build/lib" / rel.with_suffix(".olean")) for package in PACKAGES]
    candidates += [(root / rel.with_suffix(".lean"), LEAN_ROOT / "lib/lean" / rel.with_suffix(".olean")) for root in (LEAN_ROOT / "src/lean", LEAN_ROOT / "src/lean/lake")]
    for source, obj in candidates:
        if source.exists() or obj.exists(): return source, obj
    return None, None


def main():
    parser = argparse.ArgumentParser()
    for option in ("builder-read", "launcher-read", "audit-read", "source-read", "generator-read"):
        parser.add_argument("--" + option, required=True)
    args = parser.parse_args()
    if (OWN / "prepared_manifest.json").exists(): raise RuntimeError("No repeat freeze")
    if Path(sys.executable).resolve() != PYTHON.resolve() or sha(PYTHON) != PYTHON_SHA or sha(LEAN_ROOT / "bin/lean.exe") != LEAN_SHA: raise RuntimeError("Pinned runtime mismatch")
    stamp = datetime.now(timezone.utc).isoformat()
    bindings, rows, reads, queue = {}, [], [], ["Init"]
    for module, folder, digest, nthm, ndef, status, chunk, namespace in SPECS:
        original = BASE / "round22" / folder / (module + ".lean")
        own_source = OWN / "sources" / (module + ".lean")
        if own_source.resolve().parent != (OWN / "sources").resolve(): raise RuntimeError("Common source root required")
        if sha(original) != digest or sha(own_source) != digest: raise RuntimeError("Exact source copy mismatch")
        code = lean_code(own_source)
        decls = re.findall(r"^(theorem|def)\s+(\w+)", code, re.M)
        printed = re.findall(r"^#print axioms " + re.escape(namespace) + r"\.(\w+)$", code, re.M)
        if ([name for _, name in decls] != printed or len(set(printed)) != len(printed)
                or sum(kind == "theorem" for kind, _ in decls) != nthm
                or sum(kind == "def" for kind, _ in decls) != ndef
                or re.search(r"\b(?:sorry|admit|axiom|native_decide|unsafe)\b", code)):
            raise RuntimeError("Catalogue/forbidden tokens")
        rows.append({"module": module, "source": str(own_source), "source_sha256": digest,
            "original_source": str(original), "source_status": status, "theorem_count": nthm, "definition_count": ndef,
            "declarations": [{"kind": kind, "qualified_name": namespace + "." + name} for kind, name in decls],
            "qualified_prints": [namespace + "." + name for name in printed],
            "compiler_options": ["-DmaxHeartbeats=1000000"],
            "scope": "REAL_GAMMA_SCALAR_MELLIN_INVERSION_X_POSITIVE_AUX_ONLY",
            "author_olean_allowed": False})
        bindings[str(original)] = digest; bindings[str(own_source)] = digest
        reads += [(original, "FULL", chunk), (own_source, "FULL_OWN_COPY", args.source_read)]
        queue.extend(imports(own_source))
    depdir = OWN / "readonly_oleans"; depdir.mkdir(exist_ok=False)
    if any(sha(path) != expected for path, expected in ((DEP_SOURCE, DEP_SOURCE_SHA),
            (DEP_OLEAN, DEP_OLEAN_SHA), (DEP_RECEIPT, DEP_RECEIPT_SHA))):
        raise RuntimeError("Readonly independent Gamma binding changed")
    dep_receipt = json.loads(DEP_RECEIPT.read_text(encoding="utf-8"))
    dep_row = next(row for row in dep_receipt["rows"] if row["module"] == "GammaPrerequisites22")
    if (dep_receipt["status"] != "INDEPENDENT_BATCH02_AUX_PASS" or not dep_receipt["all_inputs_unchanged"]
            or dep_row["status"] != "INDEPENDENT_LEAN_AUX_PASS" or dep_row["exit_code"] != 0
            or not dep_row["exact_axiom_coverage_standard_only"] or len(dep_row["axiom_rows"]) != 23
            or dep_row["source_sha256"] != DEP_SOURCE_SHA or dep_row["olean_sha256"] != DEP_OLEAN_SHA
            or sha(DEP_RECEIPT.parent / "GammaPrerequisites22.log") != dep_row["log_sha256"]):
        raise RuntimeError("Independent Gamma PASS provenance invalid")
    dep_copy = depdir / "GammaPrerequisites22.olean"
    with dep_copy.open("xb") as stream: stream.write(DEP_OLEAN.read_bytes())
    if sha(dep_copy) != DEP_OLEAN_SHA: raise RuntimeError("Readonly olean copy mismatch")
    deps = [{"module": "GammaPrerequisites22", "source": str(DEP_SOURCE), "source_sha256": DEP_SOURCE_SHA,
        "olean_original": str(DEP_OLEAN), "olean_copy": str(dep_copy), "olean_sha256": DEP_OLEAN_SHA,
        "independent_receipt": str(DEP_RECEIPT), "independent_receipt_sha256": DEP_RECEIPT_SHA,
        "status": "INDEPENDENT_LEAN_AUX_PASS", "recompile_authorized": False}]
    for path in (DEP_SOURCE, DEP_OLEAN, dep_copy, DEP_RECEIPT,
            DEP_RECEIPT.parent / "GammaPrerequisites22_FIN.json", DEP_RECEIPT.parent / "GammaPrerequisites22.log"):
        bindings[str(path)] = sha(path)
    reads += [(DEP_SOURCE, "FULL_READONLY_INDEPENDENT_SOURCE", "5ae4ae"),
        (DEP_RECEIPT, "FULL_READONLY_INDEPENDENT_RECEIPT", "1d8c6e"),
        (DEP_RECEIPT.parent / "GammaPrerequisites22_FIN.json", "FULL", "e54fa9"),
        (DEP_RECEIPT.parent / "GammaPrerequisites22.log", "FULL", "e54fa9")]
    support = [
        (JUDGE / "mellin_inverse_source_review_revision02.md", "8beb643b7f86fd8a70906f335468f4d9aed2eaf13748425a3eb79955a5a753b8", "d3100b"),
        (JUDGE / "mellin_inverse_source_review22.md", "ea23cf317cebdfaf4328f53f691fc9f22412550eabdff273cab94f373ed8d0a8", "2092de"),
        (BASE / "round22/role3/thermal_gamma_mellin_revision02/revision_contract22.txt", "ad20abd8b3ac65ad37d8c25f82e9891ac32fa9afa525b4493ac758d69e7bacd6", "618d04"),
        (BASE / "round22/role3/thermal_gamma_mellin_revision02/source_read_receipts22.json", "8aeabccdc49f835e1c6656f7fa0b02ac6d03be0f8c9b66a3e8ce8802e1a064bc", "618d04"),
        (JUDGE / "batch18/adjudication.md", "e00bfdcb0b871103c295b73104a4e0feef770cedbb4e6d64758ff97f7417339a", "f84a7b"),
        (JUDGE / "batch18/completion_receipt.json", "28896f689441f63c3cf3d8bd8c683ecb3d989d5650ce8aa49d2e858b5d072b10", "f84a7b"),
        (JUDGE / "batch18/batch18_attempt01/receipt.json", "5cafbee7186adfbc6a9459b26dfc077999a68bd5eef3758a391f805a49f4c84f", "d5301a"),
        (JUDGE / "batch19/adjudication.md", "af4bb865b233d921d895ca44b4dbfe265b3d6eac918ae311830c833ad860c5a1", "a318ab"),
        (JUDGE / "batch19/completion_receipt.json", "a9fc7f95a8115b9187c16e20a145a372c9a5bd80e07901ba4463ed505fa7da70", "a318ab"),
        (JUDGE / "batch19/batch19_attempt01/receipt.json", "1a645174f44f5545e6069139cd3d452f9eb6100f7946152c5cf50c56c8252d57", "0d4e79")]
    for path, digest, chunk in support:
        if sha(path) != digest: raise RuntimeError("Support provenance changed")
        bindings[str(path)] = digest; reads.append((path, "FULL_CURRENT_OR_PREVIOUS_CLOSED", chunk))
    api_reads = [
        ("Mathlib/Analysis/MellinInversion.lean", "a13eb7", "FULL_PREVIOUS_UNCHANGED_API"),
        ("Mathlib/Analysis/MellinTransform.lean", "2867e9_HISTORICAL", "TARGETED_35_96"),
        ("Mathlib/Analysis/SpecialFunctions/Gamma/Deriv.lean", "59a6a9_HISTORICAL", "TARGETED_35_44_75_85"),
        ("Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean", "59a6a9_HISTORICAL", "TARGETED_83_112_305_322"),
        ("Mathlib/MeasureTheory/Integral/IntegrableOn.lean", "59a6a9_HISTORICAL", "TARGETED_220_231_695_707"),
        ("Mathlib/Topology/Basic.lean", "dd195e", "TARGETED_1425_1459"),
        ("Mathlib/Order/Interval/Set/Defs.lean", "dd195e", "TARGETED_67_79"),
        ("Mathlib/MeasureTheory/Function/L1Space.lean", "dd195e", "TARGETED_427_446")]
    for relative, chunk, scope in api_reads:
        path = CACHE / "mathlib" / relative
        bindings[str(path)] = sha(path); reads.append((path, scope, chunk))
    old_rows = [{"path": str(path), "sha256": sha(path)} for path in sorted(JUDGE.rglob("*")) if path.is_file() and OWN not in path.parents]
    bindings.update({item["path"]: item["sha256"] for item in old_rows})
    write_new(OWN / "closed_judge_bindings.json", {"schema": "ROUND22_JUDGE5_CLOSED_BINDINGS_BATCH20", "inputs": old_rows,
        "old_batches_recompiled": False, "compiler_invocations": 0})
    closure, unresolved, seen = [], [], set()
    while queue:
        module = queue.pop()
        if module in seen or module in MODULES: continue
        seen.add(module); source, obj = resolve(module)
        if source is None or not source.is_file() or not obj.is_file():
            unresolved.append({"module": module, "source": str(source), "olean": str(obj)}); continue
        item = {"module": module, "source": str(source), "source_sha256": sha(source),
            "olean": str(obj), "olean_sha256": sha(obj), "read_scope": "HASH_AND_IMPORT_METADATA_ONLY"}
        closure.append(item); bindings[str(source)] = item["source_sha256"]; bindings[str(obj)] = item["olean_sha256"]
        queue.extend(imports(source))
    write_new(OWN / "import_bindings.json", {"schema": "ROUND22_JUDGE5_IMPORT_BINDINGS_BATCH20", "module_count": len(closure),
        "explicit_implicit_prelude_seed": "Init", "unresolved": unresolved,
        "entries": sorted(closure, key=lambda item: item["module"]), "readonly_local_entries": deps, "compiler_invocations": 0})
    reads += [(OWN / "create_tools_source.py", "FULL_METADATA_TEXT_GENERATOR_ONLY", args.generator_read),
        (OWN / "prepare_metadata.py", "FULL_BEFORE_METADATA_RUN", args.builder_read),
        (OWN / "run_once.py", "FULL_SOURCE_ONLY_NEVER_EXECUTED", args.launcher_read),
        (OWN / "preparation.md", "FULL_SOURCE_AUDIT", args.audit_read)]
    for path, _, _ in reads: bindings[str(path)] = sha(path)
    write_new(OWN / "read_receipts.json", {"schema": "ROUND22_JUDGE5_READ_RECEIPTS_BATCH20", "time_utc": stamp,
        "entries": [{"path": str(path), "sha256": sha(path), "scope": scope, "chunk": chunk} for path, scope, chunk in reads],
        "truncated_reads_excluded": ["f01eb1", "a732a6", "56545d", "2d8015", "3b6479", "196191_combined_overall_truncated"],
        "common_source_root_prepared": str(OWN / "sources"), "all_import_mathematical_FULL_claim": False,
        "compiler_invocations": 0, "numeric_invocations": 0})
    write_new(OWN / "catalog.json", {"schema": "ROUND22_JUDGE5_CATALOG_BATCH20", "time_utc": stamp,
        "modules": rows, "module_count": 1, "total_declarations": 11, "theorem_count": 9, "definition_count": 2,
        "common_source_root": str(OWN / "sources"), "readonly_local_dependencies": list(LOCAL_DEPENDENCIES), "dependency_bindings": deps,
        "support_capture_paths": [str(item[0]) for item in support], "author_provenance_capture_paths": [],
        "modules_author_PASS_claimed": False, "compiler_invocations": 0, "win": False})
    archive_path = BASE / "round22/previous_artifacts_sha256.json"
    archives = json.loads(archive_path.read_text(encoding="utf-8"))
    if len(archives["sha256"]) != 3089 or archives["file_count"] != 3089: raise RuntimeError("Archive count changed")
    for relative, digest in archives["sha256"].items():
        if sha(BASE / relative) != digest: raise RuntimeError("Protected archive changed")
    for path in (archive_path, PYTHON, LEAN_ROOT / "bin/lean.exe"): bindings[str(path)] = sha(path)
    for name in ("prepare_metadata.py", "run_once.py", "preparation.md", "catalog.json", "read_receipts.json", "import_bindings.json", "closed_judge_bindings.json"):
        bindings[str(OWN / name)] = sha(OWN / name)
    manifest = {"schema": "ROUND22_JUDGE5_PREPARED_MANIFEST_BATCH20", "time_utc": stamp,
        "status": "PREPARED_SOURCE_ONLY_GATE_CLOSED" if not unresolved else "PREPARATION_IMPORT_OPEN", "role": "ROLE5",
        "modules": list(MODULES), "compiler_invocations": 0, "numeric_invocations": 0,
        "immutable_inputs": [{"path": path, "sha256": digest} for path, digest in sorted(bindings.items())],
        "import_module_count": len(closure), "implicit_Init_closure_included": True, "unresolved_modules": unresolved,
        "common_source_root": str(OWN / "sources"), "source_catalog_sha256": sha(OWN / "catalog.json"),
        "launcher_sha256": sha(OWN / "run_once.py"), "readonly_local_dependencies": list(LOCAL_DEPENDENCIES), "closed_judge_files": len(old_rows),
        "protected_archive_count": 3089, "author_olean_used": False, "numeric_banks": [],
        "previous_official_modules": 79, "previous_official_declarations": 1328,
        "hypothetical_after_all_PASS_modules": 80, "hypothetical_after_all_PASS_declarations": 1339,
        "official_count_requires_ROOT_observation": True, "H1_paid": False, "C3_paid": False,
        "C5_global_Arch_paid": False, "D_N_paid": False, "win": False}
    write_new(OWN / "prepared_manifest.json", manifest)
    receipt = {"schema": "ROUND22_JUDGE5_PREPARATION_RECEIPT_BATCH20", "time_utc": datetime.now(timezone.utc).isoformat(),
        "status": manifest["status"], "compiler_invocations": 0, "numeric_invocations": 0,
        "manifest_sha256": sha(OWN / "prepared_manifest.json"), "launcher_sha256": manifest["launcher_sha256"],
        "catalog_sha256": manifest["source_catalog_sha256"], "read_receipts_sha256": sha(OWN / "read_receipts.json"),
        "import_bindings_sha256": sha(OWN / "import_bindings.json"), "closed_judge_bindings_sha256": sha(OWN / "closed_judge_bindings.json"),
        "imports": len(closure), "inputs": len(bindings), "closed_judge_files": len(old_rows), "archives": 3089,
        "modules": 1, "declarations": 11, "theorems": 9, "definitions": 2, "unresolved": unresolved,
        "one_module_SOURCE_not_elaborated": True, "readonly_independent_dependency_count": 1,
        "common_source_root": str(OWN / "sources"), "no_author_olean_on_lean_path": True,
        "old_batches_recompiled": False, "numeric_bank_replayed": False, "no_win": True}
    write_new(OWN / "prepared_receipt.json", receipt)
    print(json.dumps(receipt, sort_keys=True))

if __name__ == "__main__":
    main()
