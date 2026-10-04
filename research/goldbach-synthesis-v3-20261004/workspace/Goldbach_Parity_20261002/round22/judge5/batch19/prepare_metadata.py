"""New batch19 SOURCE freeze only: hashing and lexical imports; no subprocess."""
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
    ("FiniteFieldProjection22", "role3/finite_field_projection_source22", "2b1cc267ce780a6a45c039f4b4b82d5a4ad4541fa224d76413dec5432658a48a", 20, 4, "SOURCE_ONLY_NOT_COMPILED", "8a0959", "GoldbachFiniteFieldProjection22"),)
MODULES = tuple(row[0] for row in SPECS)
LOCAL_DEPENDENCIES = ("QuantizedLambdaEnvelope22", "RationalLogQuantization22")
DEP_RECEIPT = JUDGE / "batch17/batch17_attempt01/receipt.json"
DEP_RECEIPT_SHA = "9449666ee8bdbbae74ea849e5a9ce2eb5c0c5bd7dd24c14a2d28065068178298"
DEP_SPECS = (
    ("QuantizedLambdaEnvelope22", "526354f4b96006eb2b297477fb6f09dd8a683e88cc95feb816a31357df0a2331", "e821070b97b3fa4b71a3e279ecb9bc6c0de6cafdfe9dc8712b5d5a22858a6485", 14, "0445ad"),
    ("RationalLogQuantization22", "dfabcabf39ecc1ba7769eb99ea73e0483dc6925f0bb3d11c05891d22c0a787a7", "20db07cdfb5717d7f9ab0b3e75d3c15b9e16c6820ad5285bd7debb62b0a31434", 38, "f4d314_HISTORICAL_FULL"),)



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
    if module in LOCAL_DEPENDENCIES:
        return JUDGE / "batch17/sources" / (module + ".lean"), OWN / "readonly_oleans" / (module + ".olean")
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
            "scope": "FINITE_FIELD_EXACT_SIGNED_CHARACTER_PROJECTION_CANONICAL_A32_AUX_ONLY",
            "author_olean_allowed": False})
        bindings[str(original)] = digest; bindings[str(own_source)] = digest
        reads += [(original, "FULL", chunk), (own_source, "FULL_OWN_COPY", args.source_read)]
        queue.extend(imports(own_source))
    depdir = OWN / "readonly_oleans"; depdir.mkdir(exist_ok=False)
    if sha(DEP_RECEIPT) != DEP_RECEIPT_SHA:
        raise RuntimeError("Independent batch17 receipt changed")
    dep_receipt = json.loads(DEP_RECEIPT.read_text(encoding="utf-8"))
    if (dep_receipt["status"] != "INDEPENDENT_BATCH17_AUX_PASS"
            or not dep_receipt["all_inputs_unchanged"]
            or dep_receipt["modules_passed"] != 2 or dep_receipt["declarations_passed"] != 52):
        raise RuntimeError("Independent batch17 provenance invalid")
    deps = []
    for module, source_digest, olean_digest, count, chunk in DEP_SPECS:
        source = JUDGE / "batch17/sources" / (module + ".lean")
        obj = DEP_RECEIPT.parent / (module + ".olean")
        log = DEP_RECEIPT.parent / (module + ".log")
        fin = DEP_RECEIPT.parent / (module + "_FIN.json")
        row = next(row for row in dep_receipt["rows"] if row["module"] == module)
        if (sha(source) != source_digest or sha(obj) != olean_digest
                or row["source_sha256"] != source_digest or row["olean_sha256"] != olean_digest
                or row["status"] != "INDEPENDENT_LEAN_AUX_PASS" or row["exit_code"] != 0
                or not row["exact_axiom_coverage_standard_only"] or len(row["axiom_rows"]) != count
                or sha(log) != row["log_sha256"] or json.loads(fin.read_text(encoding="utf-8")) != row):
            raise RuntimeError("Independent dependency PASS invalid: " + module)
        copy = depdir / (module + ".olean")
        with copy.open("xb") as stream: stream.write(obj.read_bytes())
        if sha(copy) != olean_digest: raise RuntimeError("Readonly dependency copy mismatch")
        deps.append({"module": module, "source": str(source), "source_sha256": source_digest,
            "olean_original": str(obj), "olean_copy": str(copy), "olean_sha256": olean_digest,
            "independent_receipt": str(DEP_RECEIPT), "independent_receipt_sha256": DEP_RECEIPT_SHA,
            "status": "INDEPENDENT_LEAN_AUX_PASS", "recompile_authorized": False})
        for path in (source, obj, copy, DEP_RECEIPT, fin, log): bindings[str(path)] = sha(path)
        reads.append((source, "FULL_READONLY_INDEPENDENT_SOURCE", chunk))
    reads.append((DEP_RECEIPT, "FULL_PREVIOUS_CLOSED_INDEPENDENT_RECEIPT", "ee2407_HISTORICAL_FULL"))
    support = [
        (JUDGE / "finite_field_projection_source_review22.md", "336e7e5a727d42a8de650186619ba2995dad23e63d0edcace73cd33ae8170917", "785fae"),
        (BASE / "round22/role3/finite_field_projection_source22/source_contract22.txt", "8e9797c1628762c82de4e333c326034f893d839e320f779b4576e7910ea4ca0d", "229926"),
        (BASE / "round22/role3/finite_field_projection_source22/source_read_receipts22.json", "71d97c57c71de01226e0d251fd60b7ecdeefe3a5b65f543b61f3102e2aa6a4d8", "229926"),
        (JUDGE / "batch17/adjudication.md", "ffab547e870266510c64ebe011b89998fe1d218ec27f347f8ca8a3ce38a331e3", "602acc_HISTORICAL_FULL"),
        (JUDGE / "batch17/completion_receipt.json", "150b360cfb3fabbcc3a1a42456c2a1ebd338683af9863c68134310c06775cdaa", "602acc_HISTORICAL_FULL"),
        (DEP_RECEIPT, DEP_RECEIPT_SHA, "ee2407_HISTORICAL_FULL"),
        (JUDGE / "batch18/adjudication.md", "e00bfdcb0b871103c295b73104a4e0feef770cedbb4e6d64758ff97f7417339a", "f84a7b"),
        (JUDGE / "batch18/completion_receipt.json", "28896f689441f63c3cf3d8bd8c683ecb3d989d5650ce8aa49d2e858b5d072b10", "f84a7b")]
    for path, digest, chunk in support:
        if sha(path) != digest: raise RuntimeError("Support provenance changed")
        bindings[str(path)] = digest; reads.append((path, "FULL_CURRENT_OR_PREVIOUS_CLOSED", chunk))
    api_reads = [
        ("Mathlib/RingTheory/RootsOfUnity/PrimitiveRoots.lean", "990f82", "TARGETED_45_79_278_329_386_440"),
        ("Mathlib/Algebra/GeomSum.lean", "990f82", "TARGETED_225_247"),
        ("Mathlib/Algebra/BigOperators/Ring.lean", "990f82", "TARGETED_31_66"),
        ("Mathlib/Data/Finset/NatAntidiagonal.lean", "990f82", "TARGETED_1_60"),
        ("Mathlib/Algebra/GroupWithZero/Basic.lean", "990f82", "TARGETED_399_439"),
        ("Mathlib/Data/ZMod/Basic.lean", "0445ad", "TARGETED_451_482_564_588_1315_1346")]
    for relative, chunk, scope in api_reads:
        path = CACHE / "mathlib" / relative
        bindings[str(path)] = sha(path); reads.append((path, scope, chunk))
    old_rows = [{"path": str(path), "sha256": sha(path)} for path in sorted(JUDGE.rglob("*")) if path.is_file() and OWN not in path.parents]
    bindings.update({item["path"]: item["sha256"] for item in old_rows})
    write_new(OWN / "closed_judge_bindings.json", {"schema": "ROUND22_JUDGE5_CLOSED_BINDINGS_BATCH19", "inputs": old_rows,
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
    write_new(OWN / "import_bindings.json", {"schema": "ROUND22_JUDGE5_IMPORT_BINDINGS_BATCH19", "module_count": len(closure),
        "explicit_implicit_prelude_seed": "Init", "unresolved": unresolved,
        "entries": sorted(closure, key=lambda item: item["module"]), "readonly_local_entries": deps, "compiler_invocations": 0})
    reads += [(OWN / "create_tools_source.py", "FULL_METADATA_TEXT_GENERATOR_ONLY", args.generator_read),
        (OWN / "prepare_metadata.py", "FULL_BEFORE_METADATA_RUN", args.builder_read),
        (OWN / "run_once.py", "FULL_SOURCE_ONLY_NEVER_EXECUTED", args.launcher_read),
        (OWN / "preparation.md", "FULL_SOURCE_AUDIT", args.audit_read)]
    for path, _, _ in reads: bindings[str(path)] = sha(path)
    write_new(OWN / "read_receipts.json", {"schema": "ROUND22_JUDGE5_READ_RECEIPTS_BATCH19", "time_utc": stamp,
        "entries": [{"path": str(path), "sha256": sha(path), "scope": scope, "chunk": chunk} for path, scope, chunk in reads],
        "truncated_reads_excluded": ["f01eb1", "a732a6", "56545d", "2d8015", "3b6479", "196191_combined_overall_truncated"],
        "common_source_root_prepared": str(OWN / "sources"), "all_import_mathematical_FULL_claim": False,
        "compiler_invocations": 0, "numeric_invocations": 0})
    write_new(OWN / "catalog.json", {"schema": "ROUND22_JUDGE5_CATALOG_BATCH19", "time_utc": stamp,
        "modules": rows, "module_count": 1, "total_declarations": 24, "theorem_count": 20, "definition_count": 4,
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
    manifest = {"schema": "ROUND22_JUDGE5_PREPARED_MANIFEST_BATCH19", "time_utc": stamp,
        "status": "PREPARED_SOURCE_ONLY_GATE_CLOSED" if not unresolved else "PREPARATION_IMPORT_OPEN", "role": "ROLE5",
        "modules": list(MODULES), "compiler_invocations": 0, "numeric_invocations": 0,
        "immutable_inputs": [{"path": path, "sha256": digest} for path, digest in sorted(bindings.items())],
        "import_module_count": len(closure), "implicit_Init_closure_included": True, "unresolved_modules": unresolved,
        "common_source_root": str(OWN / "sources"), "source_catalog_sha256": sha(OWN / "catalog.json"),
        "launcher_sha256": sha(OWN / "run_once.py"), "readonly_local_dependencies": list(LOCAL_DEPENDENCIES), "closed_judge_files": len(old_rows),
        "protected_archive_count": 3089, "author_olean_used": False, "numeric_banks": [],
        "previous_official_modules": 78, "previous_official_declarations": 1304,
        "hypothetical_after_all_PASS_modules": 79, "hypothetical_after_all_PASS_declarations": 1328,
        "official_count_requires_ROOT_observation": True, "H1_paid": False, "C3_paid": False,
        "C5_global_Arch_paid": False, "D_N_paid": False, "win": False}
    write_new(OWN / "prepared_manifest.json", manifest)
    receipt = {"schema": "ROUND22_JUDGE5_PREPARATION_RECEIPT_BATCH19", "time_utc": datetime.now(timezone.utc).isoformat(),
        "status": manifest["status"], "compiler_invocations": 0, "numeric_invocations": 0,
        "manifest_sha256": sha(OWN / "prepared_manifest.json"), "launcher_sha256": manifest["launcher_sha256"],
        "catalog_sha256": manifest["source_catalog_sha256"], "read_receipts_sha256": sha(OWN / "read_receipts.json"),
        "import_bindings_sha256": sha(OWN / "import_bindings.json"), "closed_judge_bindings_sha256": sha(OWN / "closed_judge_bindings.json"),
        "imports": len(closure), "inputs": len(bindings), "closed_judge_files": len(old_rows), "archives": 3089,
        "modules": 1, "declarations": 24, "theorems": 20, "definitions": 4, "unresolved": unresolved,
        "one_module_SOURCE_not_elaborated": True, "readonly_independent_dependency_count": 2,
        "common_source_root": str(OWN / "sources"), "no_author_olean_on_lean_path": True,
        "old_batches_recompiled": False, "numeric_bank_replayed": False, "no_win": True}
    write_new(OWN / "prepared_receipt.json", receipt)
    print(json.dumps(receipt, sort_keys=True))

if __name__ == "__main__":
    main()
