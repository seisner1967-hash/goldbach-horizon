"""New batch11 SOURCE freeze only: hashing and lexical imports; no subprocess."""
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
    ("ThermalProjectionEnvelope22", "role4/projection_envelope_revision02", "77cdab8bed77a3580767bf20dfa8069860ea888490d673daf5144f1aba050ed5", 29, 13, "SOURCE_REVISION_NOT_COMPILED", "53a68d"),
    ("ThermalProjectionIdentity22", "role4/projection_identity_source01", "5b6da908dce97e0ad1ba08a893bd545a4a4c908f969d958102cf9e3509c5e99c", 18, 2, "SOURCE_NOT_COMPILED", "eecf65"),
)
MODULES = tuple(row[0] for row in SPECS)
DEPS = ()
LOCAL_DEPENDENCIES = ()
OWN_SOURCE_FULL = ("e8359e", "1ea418")


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
    for option in ("builder-read", "launcher-read", "audit-read"):
        parser.add_argument("--" + option, required=True)
    args = parser.parse_args()
    if (OWN / "prepared_manifest.json").exists(): raise RuntimeError("No repeat freeze")
    if Path(sys.executable).resolve() != PYTHON.resolve() or sha(PYTHON) != PYTHON_SHA or sha(LEAN_ROOT / "bin/lean.exe") != LEAN_SHA: raise RuntimeError("Pinned runtime mismatch")
    stamp = datetime.now(timezone.utc).isoformat()
    bindings, rows, reads, dependencies, queue = {}, [], [], [], ["Init"]
    for module, folder, digest, nthm, ndef, status, chunk in SPECS:
        original = BASE / "round22" / folder / (module + ".lean")
        own_source = OWN / "sources" / (module + ".lean")
        if own_source.resolve().parent != (OWN / "sources").resolve(): raise RuntimeError("Common source root required")
        if sha(original) != digest or sha(own_source) != digest: raise RuntimeError("Exact source copy mismatch " + module)
        code = lean_code(own_source)
        decls = re.findall(r"^(theorem|def)\s+(\w+)", code, re.M)
        printed = re.findall(r"^#print axioms GoldbachContinuous22\.(\w+)$", code, re.M)
        if ([name for _, name in decls] != printed or len(set(printed)) != len(printed) or sum(kind == "theorem" for kind, _ in decls) != nthm or sum(kind == "def" for kind, _ in decls) != ndef or re.search(r"\b(?:sorry|admit|axiom|native_decide|unsafe)\b", code)): raise RuntimeError("Catalogue/forbidden tokens " + module)
        rows.append({"module": module, "source": str(own_source), "source_sha256": digest, "original_source": str(original), "source_status": status, "theorem_count": nthm, "definition_count": ndef,
            "declarations": [{"kind": kind, "qualified_name": "GoldbachContinuous22." + name} for kind, name in decls], "qualified_prints": ["GoldbachContinuous22." + name for name in printed],
            "compiler_options": ["-DmaxHeartbeats=1000000"], "scope": "TRUE_LAMBDA_GEOMETRIC_ENVELOPE_AND_EXACT_CONTINUOUS_PROJECTION_AUX_ONLY", "author_olean_allowed": False})
        bindings[str(original)] = digest; bindings[str(own_source)] = digest
        reads.append((original, "FULL", chunk))
        reads.append((own_source, "FULL_EXACT_OWN_COPY", OWN_SOURCE_FULL[MODULES.index(module)]))
        queue.extend(imports(own_source))
    depdir = OWN / "readonly_oleans"; depdir.mkdir(exist_ok=False)
    for module, folder, actual, source_sha, obj_sha, schunk, rchunk, receipt_sha in DEPS:
        source = JUDGE / folder / (module + ".lean")
        obj = JUDGE / actual / (module + ".olean")
        receipt_path = JUDGE / actual / "receipt.json"
        if sha(receipt_path) != receipt_sha: raise RuntimeError("Independent receipt changed " + module)
        receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
        row = next(item for item in receipt["rows"] if item["module"] == module)
        if (row["status"] != "INDEPENDENT_LEAN_AUX_PASS" or row["exit_code"] != 0 or not row["exact_axiom_coverage_standard_only"] or not receipt["all_inputs_unchanged"] or row["source_sha256"] != source_sha or row["olean_sha256"] != obj_sha or sha(source) != source_sha or sha(obj) != obj_sha): raise RuntimeError("Readonly dependency mismatch " + module)
        copy = depdir / (module + ".olean"); copy.write_bytes(obj.read_bytes())
        if sha(copy) != obj_sha: raise RuntimeError("Readonly copy mismatch")
        dependencies.append({"module": module, "source": str(source), "source_sha256": source_sha, "independent_olean": str(obj), "olean_copy": str(copy), "olean_sha256": obj_sha, "independent_receipt": str(receipt_path), "recompiled": False})
        for path in (source, obj, copy, receipt_path): bindings[str(path)] = sha(path)
        reads += [(source, "FULL_PREVIOUS_CLOSED_OR_CURRENT_SOURCE", schunk), (receipt_path, "FULL_PREVIOUS_CLOSED_RECEIPT", rchunk)]
        queue.extend(imports(source))
    if set(path.name for path in depdir.iterdir()) != {name + ".olean" for name in LOCAL_DEPENDENCIES}: raise RuntimeError("Unexpected local dependency")
    support = [
        (JUDGE / "projection_source_review22.md", "c25aee9a13a3b010d214de2607d18f9add2cafbb3a47aefd03e28d5f79d81ba2", "b5b503"),
        (BASE / "round22/role4/projection_envelope_source01/source_contract22.md", "be06960786d9a8639f8b030de08fa6f71bdc382e6ce6759b89c0967f6ac35f5e", "17e103"),
        (BASE / "round22/role4/projection_envelope_source01/source_handoff_receipt22.json", "5efb0d8c953480a3ac6d6d938183717919e86838700a5eb0526ed28365c71f82", "17e103"),
        (BASE / "round22/role4/projection_identity_source01/source_contract22.md", "2c02229bce2b2e063479692b0488883791cbeaf52b69190733fb519d3a83d117", "7357be"),
        (BASE / "round22/role4/projection_identity_source01/source_handoff_receipt22.json", "3b97cebebaf965c5423dc2796df8a0b3c28b21ddda1604efb3b622764715bf10", "7357be"),
        (JUDGE / "batch10/adjudication.md", "defc47dd47ed3421e754478718650ab483c2c7ef623fbe363bc9401a9948e282", "25f877"),
        (JUDGE / "batch10/completion_receipt.json", "243ddccd2d1b11d6ee8c56f0fa9a1a863c7e07538936261f39179d8c2b268164", "25f877"),
        (BASE / "round22/role4/projection_envelope_revision02/repair_diagnostic22.md", "3739a5d6655eb48d1224c3e1396f9cc89ee098f53a9b8c45aae05f013e5c9208", "b0ec5a"),
        (BASE / "round22/role4/projection_envelope_revision02/source_handoff22.json", "57ad99a152f7a1f73d36e7b83ce1e7700147b4de13bd94264b0c34ee0e35d240", "b0ec5a")]
    supplement = []
    for path, digest, chunk in support:
        if sha(path) != digest: raise RuntimeError("Support provenance changed")
        bindings[str(path)] = digest; reads.append((path, "FULL_CURRENT_OR_PREVIOUS_CLOSED", chunk))
    api_reads = [
        ("Mathlib/MeasureTheory/Integral/IntervalIntegral.lean", "e45823", "TARGETED_325_350_EXPLICIT_MEASURE_SIGNATURE"),
        ("Mathlib/NumberTheory/VonMangoldt.lean", "1e9749", "FULL"),
        ("Mathlib/Analysis/SpecificLimits/Normed.lean", "1e9749", "TARGETED_184_199_AND_489_497"),
        ("Mathlib/Analysis/NormedSpace/FunctionSeries.lean", "1e9749", "TARGETED_107_117"),
        ("Mathlib/Analysis/SpecialFunctions/Integrals.lean", "ef0cf3", "TARGETED_425_457"),
        ("Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean", "ef0cf3", "TARGETED_1187_1205"),
        ("Mathlib/MeasureTheory/Integral/IntervalIntegral.lean", "ef0cf3", "TARGETED_338_349_519_528_547_549_564_567"),
        ("Mathlib/MeasureTheory/Integral/IntervalIntegral.lean", "ddf77c", "TARGETED_536_540"),
        ("Mathlib/Analysis/Normed/Group/Basic.lean", "ef0cf3", "TARGETED_834_849"),
        ("Mathlib/Topology/Algebra/InfiniteSum/Order.lean", "ef0cf3", "TARGETED_83_94"),
        ("Mathlib/Data/Finset/NatAntidiagonal.lean", "4091c2", "TARGETED_21_40"),
        ("Mathlib/Order/Filter/Tendsto.lean", "4091c2", "TARGETED_86_109"),
        ("Mathlib/Topology/Separation/Basic.lean", "4091c2", "TARGETED_700_708"),
        ("Mathlib/Topology/Algebra/InfiniteSum/NatInt.lean", "ddf77c", "TARGETED_220_235"),
        ("Mathlib/Data/Nat/Prime/Defs.lean", "8ffd6e", "TARGETED_273_287"),
        ("Mathlib/Analysis/SpecialFunctions/Log/Basic.lean", "8ffd6e", "TARGETED_269_284")]
    for relative, chunk, scope in api_reads:
        api = CACHE / "mathlib" / relative
        bindings[str(api)] = sha(api); reads.append((api, scope, chunk))
    author_capture_paths = []
    old_rows = [{"path": str(path), "sha256": sha(path)} for path in sorted(JUDGE.rglob("*")) if path.is_file() and OWN not in path.parents]
    bindings.update({item["path"]: item["sha256"] for item in old_rows})
    write_new(OWN / "closed_judge_bindings.json", {"schema": "ROUND22_JUDGE5_CLOSED_BINDINGS_BATCH11", "inputs": old_rows, "old_batches_recompiled": False, "compiler_invocations": 0})
    closure, unresolved, seen = [], [], set()
    while queue:
        module = queue.pop()
        if module in seen or module in MODULES or module in LOCAL_DEPENDENCIES: continue
        seen.add(module); source, obj = resolve(module)
        if source is None or not source.is_file() or not obj.is_file():
            unresolved.append({"module": module, "source": str(source), "olean": str(obj)}); continue
        item = {"module": module, "source": str(source), "source_sha256": sha(source), "olean": str(obj), "olean_sha256": sha(obj), "read_scope": "HASH_AND_IMPORT_METADATA_ONLY"}
        closure.append(item); bindings[str(source)] = item["source_sha256"]; bindings[str(obj)] = item["olean_sha256"]
        queue.extend(imports(source))
    write_new(OWN / "import_bindings.json", {"schema": "ROUND22_JUDGE5_IMPORT_BINDINGS_BATCH11", "module_count": len(closure), "explicit_implicit_prelude_seed": "Init", "unresolved": unresolved, "entries": sorted(closure, key=lambda item: item["module"]), "readonly_local_entries": dependencies, "compiler_invocations": 0})
    reads += [(OWN / "prepare_metadata.py", "FULL_BEFORE_METADATA_RUN", args.builder_read), (OWN / "run_once.py", "FULL_SOURCE_ONLY_NEVER_EXECUTED", args.launcher_read), (OWN / "preparation.md", "FULL_SOURCE_AUDIT", args.audit_read)]
    for path, _, _ in reads: bindings[str(path)] = sha(path)
    write_new(OWN / "read_receipts.json", {"schema": "ROUND22_JUDGE5_READ_RECEIPTS_BATCH11", "time_utc": stamp, "entries": [{"path": str(path), "sha256": sha(path), "scope": scope, "chunk": chunk} for path, scope, chunk in reads], "truncated_reads_excluded": ["e1533d", "afb905"], "common_source_root_prepared": str(OWN / "sources"), "all_import_mathematical_FULL_claim": False, "compiler_invocations": 0, "numeric_invocations": 0})
    write_new(OWN / "catalog.json", {"schema": "ROUND22_JUDGE5_CATALOG_BATCH11", "time_utc": stamp, "modules": rows, "module_count": 2, "total_declarations": 62, "theorem_count": 47, "definition_count": 15, "common_source_root": str(OWN / "sources"), "readonly_local_dependencies": list(LOCAL_DEPENDENCIES), "dependency_bindings": dependencies,
        "support_capture_paths": [str(item[0]) for item in support] + [str(item[0]) for item in supplement], "author_provenance_capture_paths": list(map(str, author_capture_paths)), "modules_author_PASS_claimed": False, "compiler_invocations": 0, "win": False})
    archive_path = BASE / "round22/previous_artifacts_sha256.json"
    archives = json.loads(archive_path.read_text(encoding="utf-8"))
    if len(archives["sha256"]) != 3089 or archives["file_count"] != 3089: raise RuntimeError("Archive count changed")
    for relative, digest in archives["sha256"].items():
        if sha(BASE / relative) != digest: raise RuntimeError("Protected archive changed")
    for path in (archive_path, PYTHON, LEAN_ROOT / "bin/lean.exe"): bindings[str(path)] = sha(path)
    for name in ("prepare_metadata.py", "run_once.py", "preparation.md", "catalog.json", "read_receipts.json", "import_bindings.json", "closed_judge_bindings.json"): bindings[str(OWN / name)] = sha(OWN / name)
    manifest = {"schema": "ROUND22_JUDGE5_PREPARED_MANIFEST_BATCH11", "time_utc": stamp, "status": "PREPARED_SOURCE_ONLY_GATE_CLOSED" if not unresolved else "PREPARATION_IMPORT_OPEN", "role": "ROLE5", "modules": list(MODULES), "compiler_invocations": 0, "numeric_invocations": 0,
        "immutable_inputs": [{"path": path, "sha256": digest} for path, digest in sorted(bindings.items())], "import_module_count": len(closure), "implicit_Init_closure_included": True, "unresolved_modules": unresolved, "common_source_root": str(OWN / "sources"), "source_catalog_sha256": sha(OWN / "catalog.json"), "launcher_sha256": sha(OWN / "run_once.py"), "readonly_local_dependencies": list(LOCAL_DEPENDENCIES), "closed_judge_files": len(old_rows), "protected_archive_count": 3089, "author_olean_used": False, "numeric_banks": [],
        "previous_official_modules": 73, "previous_official_declarations": 1161, "hypothetical_after_all_PASS_modules": 75, "hypothetical_after_all_PASS_declarations": 1223, "official_count_requires_ROOT_observation": True, "H1_paid": False, "C3_paid": False, "C5_global_Arch_paid": False, "D_N_paid": False, "win": False}
    write_new(OWN / "prepared_manifest.json", manifest)
    receipt = {"schema": "ROUND22_JUDGE5_PREPARATION_RECEIPT_BATCH11", "time_utc": datetime.now(timezone.utc).isoformat(), "status": manifest["status"], "compiler_invocations": 0, "numeric_invocations": 0, "manifest_sha256": sha(OWN / "prepared_manifest.json"), "launcher_sha256": manifest["launcher_sha256"], "catalog_sha256": manifest["source_catalog_sha256"], "read_receipts_sha256": sha(OWN / "read_receipts.json"), "import_bindings_sha256": sha(OWN / "import_bindings.json"), "closed_judge_bindings_sha256": sha(OWN / "closed_judge_bindings.json"), "imports": len(closure), "inputs": len(bindings), "closed_judge_files": len(old_rows), "archives": 3089, "modules": 2, "declarations": 62, "theorems": 47, "definitions": 15, "unresolved": unresolved, "two_modules_SOURCE_not_elaborated": True, "readonly_independent_dependency_count": 0, "common_source_root": str(OWN / "sources"), "no_author_olean_on_lean_path": True, "old_batches_recompiled": False, "numeric_bank_replayed": False, "no_win": True}
    write_new(OWN / "prepared_receipt.json", receipt)
    print(json.dumps(receipt, sort_keys=True))


if __name__ == "__main__":
    main()
