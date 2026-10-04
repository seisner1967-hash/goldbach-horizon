"""New batch13 SOURCE freeze only: hashing and lexical imports; no subprocess."""
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
    ("ThermalProjectionIdentity22", "role4/projection_identity_revision03", "8bb1eb5ec6ab4bf5e0c8cc053dcbe743049641dab5a3a3858205ad8ee2e2e9aa", 18, 2, "SOURCE_REVISION_NOT_COMPILED", "efa5cb"),
)
MODULES = tuple(row[0] for row in SPECS)
DEPS = (
    ("ThermalProjectionEnvelope22", "batch11/sources", "batch11/batch11_attempt01",
     "77cdab8bed77a3580767bf20dfa8069860ea888490d673daf5144f1aba050ed5",
     "9c2bb947ccd03436c8cb3c9e3e9f5ce95508ee719e506d9ca90c49623f6dac67",
     "664d8a", "e469d8", "0b25b00e57663172cacc25945ad232d807ff58cd3c34bae6f2e64bf2e852f62b"),
)
LOCAL_DEPENDENCIES = tuple(row[0] for row in DEPS)
OWN_SOURCE_FULL = ("5a2718",)


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
        reads.append((own_source, "FULL_OWN_COPY", OWN_SOURCE_FULL[MODULES.index(module)]))
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
        (JUDGE / "batch11/adjudication.md", "dd25619f5d0e8ab7f35b45a72527e55837da1743e240fc9170f46aeafa793018", "1020c8"),
        (JUDGE / "batch11/completion_receipt.json", "32f2894cc8d9e3fffa232c9acf58ce039373108194bb253590921caf38c53a99", "1020c8"),
        (BASE / "round22/role4/projection_identity_revision03/repair_diagnostic22.md", "a7ac080bdf03db01ef38904519ba615e647d45a241983c1ad2fe27f6876b43d2", "eee468"),
        (BASE / "round22/role4/projection_identity_revision03/source_handoff22.json", "342febedb322a5f76072e7f0ef5ce5358862609e9d0e287b6aa0ed25066eaf13", "80c2c5"),
        (BASE / "round22/role4/projection_identity_revision03/read_sources22.json", "70789a0896dbb07f738d61fab96fc9d91c50187296a1a975017947ce0f0be9a8", "eee468"),
        (JUDGE / "batch12/adjudication.md", "10577435fd3695e63cface9e3ba1533395e9593c7957e7869278294f44861f2f", "074112"),
        (JUDGE / "batch12/completion_receipt.json", "3ac2f583fb40adfc0e5dc52f7e022809833d8a4208dd98c5a100394fb8eaae37", "074112")]
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
    original_identity = BASE / "round22/role4/projection_identity_source01/ThermalProjectionIdentity22.lean"
    if sha(original_identity) != "5b6da908dce97e0ad1ba08a893bd545a4a4c908f969d958102cf9e3509c5e99c": raise RuntimeError("Prior failed source changed")
    def headers(path):
        text = lean_code(path)
        return [" ".join(text[hit.start():text.index(":=", hit.end())].split())
                for hit in re.finditer(r"^(?:def|theorem)\s+\w+", text, re.M)]
    if headers(original_identity) != headers(OWN / "sources/ThermalProjectionIdentity22.lean"):
        raise RuntimeError("Identity contract changed")
    bindings[str(original_identity)] = sha(original_identity)
    for relative, chunk, scope in (
        ("Mathlib/Analysis/SpecialFunctions/Integrals.lean", "804edf", "TARGETED_307_332_431_451_GLOBAL_NAMESPACE"),
        ("Mathlib/Algebra/Group/Hom/Defs.lean", "804edf", "TARGETED_417_429_TO_ADDITIVE_MAP_NEG"),
        ("Mathlib/Algebra/BigOperators/Group/Finset.lean", "804edf", "TARGETED_785_809_832_847_TO_ADDITIVE_SUM_COMM")):
        path = CACHE / "mathlib" / relative
        bindings[str(path)] = sha(path); reads.append((path, scope, chunk))
    cast_api = CACHE / "mathlib/Mathlib/Data/Complex/Basic.lean"
    bindings[str(cast_api)] = sha(cast_api)
    reads.append((cast_api, "TARGETED_217_223_423_429_HPERIOD_CASTS", "78b352"))
    old_rows = [{"path": str(path), "sha256": sha(path)} for path in sorted(JUDGE.rglob("*")) if path.is_file() and OWN not in path.parents]
    bindings.update({item["path"]: item["sha256"] for item in old_rows})
    write_new(OWN / "closed_judge_bindings.json", {"schema": "ROUND22_JUDGE5_CLOSED_BINDINGS_BATCH13", "inputs": old_rows, "old_batches_recompiled": False, "compiler_invocations": 0})
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
    write_new(OWN / "import_bindings.json", {"schema": "ROUND22_JUDGE5_IMPORT_BINDINGS_BATCH13", "module_count": len(closure), "explicit_implicit_prelude_seed": "Init", "unresolved": unresolved, "entries": sorted(closure, key=lambda item: item["module"]), "readonly_local_entries": dependencies, "compiler_invocations": 0})
    reads += [(OWN / "create_tools_source.py", "FULL_METADATA_TEXT_GENERATOR_ONLY", "c550da"), (OWN / "prepare_metadata.py", "FULL_BEFORE_METADATA_RUN", args.builder_read), (OWN / "run_once.py", "FULL_SOURCE_ONLY_NEVER_EXECUTED", args.launcher_read), (OWN / "preparation.md", "FULL_SOURCE_AUDIT", args.audit_read)]
    for path, _, _ in reads: bindings[str(path)] = sha(path)
    write_new(OWN / "read_receipts.json", {"schema": "ROUND22_JUDGE5_READ_RECEIPTS_BATCH13", "time_utc": stamp, "entries": [{"path": str(path), "sha256": sha(path), "scope": scope, "chunk": chunk} for path, scope, chunk in reads], "truncated_reads_excluded": [], "common_source_root_prepared": str(OWN / "sources"), "all_import_mathematical_FULL_claim": False, "compiler_invocations": 0, "numeric_invocations": 0})
    write_new(OWN / "catalog.json", {"schema": "ROUND22_JUDGE5_CATALOG_BATCH13", "time_utc": stamp, "modules": rows, "module_count": 1, "total_declarations": 20, "theorem_count": 18, "definition_count": 2, "common_source_root": str(OWN / "sources"), "readonly_local_dependencies": list(LOCAL_DEPENDENCIES), "dependency_bindings": dependencies,
        "support_capture_paths": [str(item[0]) for item in support] + [str(item[0]) for item in supplement], "author_provenance_capture_paths": list(map(str, author_capture_paths)), "modules_author_PASS_claimed": False, "compiler_invocations": 0, "win": False})
    archive_path = BASE / "round22/previous_artifacts_sha256.json"
    archives = json.loads(archive_path.read_text(encoding="utf-8"))
    if len(archives["sha256"]) != 3089 or archives["file_count"] != 3089: raise RuntimeError("Archive count changed")
    for relative, digest in archives["sha256"].items():
        if sha(BASE / relative) != digest: raise RuntimeError("Protected archive changed")
    for path in (archive_path, PYTHON, LEAN_ROOT / "bin/lean.exe"): bindings[str(path)] = sha(path)
    for name in ("prepare_metadata.py", "run_once.py", "preparation.md", "catalog.json", "read_receipts.json", "import_bindings.json", "closed_judge_bindings.json"): bindings[str(OWN / name)] = sha(OWN / name)
    manifest = {"schema": "ROUND22_JUDGE5_PREPARED_MANIFEST_BATCH13", "time_utc": stamp, "status": "PREPARED_SOURCE_ONLY_GATE_CLOSED" if not unresolved else "PREPARATION_IMPORT_OPEN", "role": "ROLE5", "modules": list(MODULES), "compiler_invocations": 0, "numeric_invocations": 0,
        "immutable_inputs": [{"path": path, "sha256": digest} for path, digest in sorted(bindings.items())], "import_module_count": len(closure), "implicit_Init_closure_included": True, "unresolved_modules": unresolved, "common_source_root": str(OWN / "sources"), "source_catalog_sha256": sha(OWN / "catalog.json"), "launcher_sha256": sha(OWN / "run_once.py"), "readonly_local_dependencies": list(LOCAL_DEPENDENCIES), "closed_judge_files": len(old_rows), "protected_archive_count": 3089, "author_olean_used": False, "numeric_banks": [],
        "previous_official_modules": 74, "previous_official_declarations": 1203, "hypothetical_after_all_PASS_modules": 75, "hypothetical_after_all_PASS_declarations": 1223, "official_count_requires_ROOT_observation": True, "H1_paid": False, "C3_paid": False, "C5_global_Arch_paid": False, "D_N_paid": False, "win": False}
    write_new(OWN / "prepared_manifest.json", manifest)
    receipt = {"schema": "ROUND22_JUDGE5_PREPARATION_RECEIPT_BATCH13", "time_utc": datetime.now(timezone.utc).isoformat(), "status": manifest["status"], "compiler_invocations": 0, "numeric_invocations": 0, "manifest_sha256": sha(OWN / "prepared_manifest.json"), "launcher_sha256": manifest["launcher_sha256"], "catalog_sha256": manifest["source_catalog_sha256"], "read_receipts_sha256": sha(OWN / "read_receipts.json"), "import_bindings_sha256": sha(OWN / "import_bindings.json"), "closed_judge_bindings_sha256": sha(OWN / "closed_judge_bindings.json"), "imports": len(closure), "inputs": len(bindings), "closed_judge_files": len(old_rows), "archives": 3089, "modules": 1, "declarations": 20, "theorems": 18, "definitions": 2, "unresolved": unresolved, "one_module_SOURCE_not_elaborated": True, "readonly_independent_dependency_count": 1, "common_source_root": str(OWN / "sources"), "no_author_olean_on_lean_path": True, "old_batches_recompiled": False, "numeric_bank_replayed": False, "no_win": True}
    write_new(OWN / "prepared_receipt.json", receipt)
    print(json.dumps(receipt, sort_keys=True))


if __name__ == "__main__":
    main()
