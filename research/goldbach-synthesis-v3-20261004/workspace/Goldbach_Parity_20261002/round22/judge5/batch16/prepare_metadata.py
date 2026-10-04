"""New batch16 SOURCE freeze only: hashing and lexical imports; no subprocess."""
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
    ("RationalLogQuantization22", "role3/log_quantization_source22/revision02", "9e59eb6b8aa4efcb5cc6cdc27d7d7a7d24517986fcd1ad2b4413b97c0efc1fb0", 23, 15, "SOURCE_ONLY_NOT_COMPILED", "87a11a", "GoldbachLogQuantization22"),
    ("QuantizedLambdaEnvelope22", "role3/log_quantization_source22/revision02", "526354f4b96006eb2b297477fb6f09dd8a683e88cc95feb816a31357df0a2331", 9, 5, "SOURCE_ONLY_NOT_COMPILED", "a87644", "GoldbachQuantizedCoefficient22"))
MODULES = tuple(row[0] for row in SPECS)
LOCAL_DEPENDENCIES = ()


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
            "scope": "CANONICAL_LOG32_TRUE_PRECISION_LAMBDA_PP_CONTINUOUS_COEFFICIENT_ENVELOPE_AUX_ONLY",
            "author_olean_allowed": False})
        bindings[str(original)] = digest; bindings[str(own_source)] = digest
        reads += [(original, "FULL", chunk), (own_source, "FULL_OWN_COPY", args.source_read)]
        queue.extend(imports(own_source))
    depdir = OWN / "readonly_oleans"; depdir.mkdir(exist_ok=False)
    if list(depdir.iterdir()): raise RuntimeError("No local dependency authorized")
    support = [
        (JUDGE / "log_quantization_source_review_revision02.md", "a8b74e2d2132ad40f0caa44e49ebd14cca234993bd0fd26f30ad83f15c5fcb65", "2bccd7"),
        (BASE / "round22/role3/log_quantization_source22/revision02/dependency_contract22.md", "cdb1b8510c13fe6ff69b6ed510df90335a831cef0181182c050c1781965fe91f", "587fd9"),
        (BASE / "round22/role3/log_quantization_source22/revision02/source_manifest22.json", "3d0af8eefbb29fd902bf3b1b86b4b15bce7280cbb262b1159486165ae2fd6a74", "587fd9"),
        (BASE / "round22/role3/log_quantization_source22/revision02/read_receipts22.json", "de4b33633a9e66471ed7a3d00c63dab2e522af6d356bc0968115076c3b29bcf9", "c127c0"),
        (JUDGE / "batch15/adjudication.md", "e2fda965a5cc1060a42920e5e889dc41f1867a2a6f091fb75ba132b7baaf1f49", "1b4643"),
        (JUDGE / "batch15/completion_receipt.json", "221d5c034dc90424deca0b566b1003e104b32453294ff8a305a7578b9eb71d3d", "1b4643"),
        (JUDGE / "batch15/batch15_attempt01/receipt.json", "ee18a68ce36db7757a139a803a7c555fb33dc9f99820cc1e3cf7b15222049845", "652cc7"),
        (JUDGE / "batch15/batch15_attempt01/DiscreteThermalProjection22.log", "5a99f3e74a991301a707747540267ab38d0ea673b9ac5a53aed5f38359a1f0da", "652cc7")]
    for path, digest, chunk in support:
        if sha(path) != digest: raise RuntimeError("Support provenance changed")
        bindings[str(path)] = digest; reads.append((path, "FULL_CURRENT_OR_PREVIOUS_CLOSED", chunk))
    api_reads = [
        ("Mathlib/Analysis/SpecialFunctions/Log/Deriv.lean", "054dec", "TARGETED_272_299"),
        ("Mathlib/Topology/Algebra/InfiniteSum/NatInt.lean", "054dec", "TARGETED_197_234"),
        ("Mathlib/Topology/Algebra/InfiniteSum/Order.lean", "054dec", "TARGETED_30_61"),
        ("Mathlib/Data/Nat/Log.lean", "054dec/b3b8e6", "TARGETED_208_234_106_150"),
        ("Mathlib/Analysis/SpecificLimits/Basic.lean", "b3b8e6", "TARGETED_278_300"),
        ("Mathlib/NumberTheory/VonMangoldt.lean", "b3b8e6", "TARGETED_58_86"),
        ("Mathlib/Data/Nat/Prime/Defs.lean", "b3b8e6", "TARGETED_254_284"),
        ("Mathlib/Algebra/Order/Floor.lean", "b3b8e6", "TARGETED_642_680")]
    for relative, chunk, scope in api_reads:
        path = CACHE / "mathlib" / relative
        bindings[str(path)] = sha(path); reads.append((path, scope, chunk))
    old_sources = (("RationalLogQuantization22", "d7ea4d46f0c595c05ccb140ee310996e3c257a240bde29a58c6a7c7811bce396"),
        ("QuantizedLambdaEnvelope22", "428836508d2edfe22c4639101f0b7a99ff34dbf57ea9375b72ab509e410ec1a3"))
    def headers(path):
        text = lean_code(path)
        return [" ".join(text[hit.start():text.index(":=", hit.end())].split())
            for hit in re.finditer(r"^(?:def|theorem)\s+\w+", text, re.M)]
    for module, expected in old_sources:
        original_old = BASE / "round22/role3/log_quantization_source22" / (module + ".lean")
        if sha(original_old) != expected: raise RuntimeError("Old source changed")
        if headers(original_old) != headers(OWN / "sources" / (module + ".lean")):
            raise RuntimeError("Source contract headers changed")
        bindings[str(original_old)] = expected
        reads.append((original_old, "BYTE_HASH_AND_LEXICAL_HEADERS_ONLY_NOT_FULL", "CURRENT_METADATA"))
    old_rows = [{"path": str(path), "sha256": sha(path)} for path in sorted(JUDGE.rglob("*")) if path.is_file() and OWN not in path.parents]
    bindings.update({item["path"]: item["sha256"] for item in old_rows})
    write_new(OWN / "closed_judge_bindings.json", {"schema": "ROUND22_JUDGE5_CLOSED_BINDINGS_BATCH16", "inputs": old_rows,
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
    write_new(OWN / "import_bindings.json", {"schema": "ROUND22_JUDGE5_IMPORT_BINDINGS_BATCH16", "module_count": len(closure),
        "explicit_implicit_prelude_seed": "Init", "unresolved": unresolved,
        "entries": sorted(closure, key=lambda item: item["module"]), "readonly_local_entries": [], "compiler_invocations": 0})
    reads += [(OWN / "create_tools_source.py", "FULL_METADATA_TEXT_GENERATOR_ONLY", args.generator_read),
        (OWN / "prepare_metadata.py", "FULL_BEFORE_METADATA_RUN", args.builder_read),
        (OWN / "run_once.py", "FULL_SOURCE_ONLY_NEVER_EXECUTED", args.launcher_read),
        (OWN / "preparation.md", "FULL_SOURCE_AUDIT", args.audit_read)]
    for path, _, _ in reads: bindings[str(path)] = sha(path)
    write_new(OWN / "read_receipts.json", {"schema": "ROUND22_JUDGE5_READ_RECEIPTS_BATCH16", "time_utc": stamp,
        "entries": [{"path": str(path), "sha256": sha(path), "scope": scope, "chunk": chunk} for path, scope, chunk in reads],
        "truncated_reads_excluded": ["ae4a74"], "empty_API_output_not_counted_as_read": "e7369c corrected054dec",
        "common_source_root_prepared": str(OWN / "sources"), "all_import_mathematical_FULL_claim": False,
        "compiler_invocations": 0, "numeric_invocations": 0})
    write_new(OWN / "catalog.json", {"schema": "ROUND22_JUDGE5_CATALOG_BATCH16", "time_utc": stamp,
        "modules": rows, "module_count": 2, "total_declarations": 52, "theorem_count": 32, "definition_count": 20,
        "common_source_root": str(OWN / "sources"), "readonly_local_dependencies": [], "dependency_bindings": [],
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
    manifest = {"schema": "ROUND22_JUDGE5_PREPARED_MANIFEST_BATCH16", "time_utc": stamp,
        "status": "PREPARED_SOURCE_ONLY_GATE_CLOSED" if not unresolved else "PREPARATION_IMPORT_OPEN", "role": "ROLE5",
        "modules": list(MODULES), "compiler_invocations": 0, "numeric_invocations": 0,
        "immutable_inputs": [{"path": path, "sha256": digest} for path, digest in sorted(bindings.items())],
        "import_module_count": len(closure), "implicit_Init_closure_included": True, "unresolved_modules": unresolved,
        "common_source_root": str(OWN / "sources"), "source_catalog_sha256": sha(OWN / "catalog.json"),
        "launcher_sha256": sha(OWN / "run_once.py"), "readonly_local_dependencies": [], "closed_judge_files": len(old_rows),
        "protected_archive_count": 3089, "author_olean_used": False, "numeric_banks": [],
        "previous_official_modules": 76, "previous_official_declarations": 1252,
        "hypothetical_after_all_PASS_modules": 78, "hypothetical_after_all_PASS_declarations": 1304,
        "official_count_requires_ROOT_observation": True, "H1_paid": False, "C3_paid": False,
        "C5_global_Arch_paid": False, "D_N_paid": False, "win": False}
    write_new(OWN / "prepared_manifest.json", manifest)
    receipt = {"schema": "ROUND22_JUDGE5_PREPARATION_RECEIPT_BATCH16", "time_utc": datetime.now(timezone.utc).isoformat(),
        "status": manifest["status"], "compiler_invocations": 0, "numeric_invocations": 0,
        "manifest_sha256": sha(OWN / "prepared_manifest.json"), "launcher_sha256": manifest["launcher_sha256"],
        "catalog_sha256": manifest["source_catalog_sha256"], "read_receipts_sha256": sha(OWN / "read_receipts.json"),
        "import_bindings_sha256": sha(OWN / "import_bindings.json"), "closed_judge_bindings_sha256": sha(OWN / "closed_judge_bindings.json"),
        "imports": len(closure), "inputs": len(bindings), "closed_judge_files": len(old_rows), "archives": 3089,
        "modules": 2, "declarations": 52, "theorems": 32, "definitions": 20, "unresolved": unresolved,
        "two_modules_SOURCE_not_elaborated": True, "readonly_independent_dependency_count": 0,
        "common_source_root": str(OWN / "sources"), "no_author_olean_on_lean_path": True,
        "old_batches_recompiled": False, "numeric_bank_replayed": False, "no_win": True}
    write_new(OWN / "prepared_receipt.json", receipt)
    print(json.dumps(receipt, sort_keys=True))

if __name__ == "__main__":
    main()
