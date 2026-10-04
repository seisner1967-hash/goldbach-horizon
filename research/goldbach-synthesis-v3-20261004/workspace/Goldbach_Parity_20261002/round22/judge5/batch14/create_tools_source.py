"""Write fresh metadata tools by text construction, never execute a closed tool or candidate."""
from pathlib import Path

OWN = Path(__file__).resolve().parent
JUDGE = OWN.parent

def new(path, text):
    with path.open("x", encoding="utf-8", newline="\n") as stream:
        stream.write(text)

old_builder = (JUDGE / "batch13/prepare_metadata.py").read_text(encoding="utf-8")
prefix = old_builder[:old_builder.index("SPECS = (")]
prefix = prefix.replace("batch13", "batch14").replace("BATCH13", "BATCH14")
constants = '''SPECS = (("DiscreteThermalProjection22", "role3/discrete_circle_source22/revision02", "7ee2abb27d959f1511abb59e8425578b420d3e972a8d03eaff26635ac8fd581c", 20, 9, "SOURCE_REVISION_NOT_COMPILED", "391197"),)
MODULES = tuple(row[0] for row in SPECS)
LOCAL_DEPENDENCIES = ()
NAMESPACE = "GoldbachDiscreteCircle22"

'''
helpers = old_builder[old_builder.index("def sha(path):"):old_builder.index("def main():")]
main = r'''def main():
    parser = argparse.ArgumentParser()
    for option in ("builder-read", "launcher-read", "audit-read", "source-read", "generator-read"):
        parser.add_argument("--" + option, required=True)
    args = parser.parse_args()
    if (OWN / "prepared_manifest.json").exists(): raise RuntimeError("No repeat freeze")
    if Path(sys.executable).resolve() != PYTHON.resolve() or sha(PYTHON) != PYTHON_SHA or sha(LEAN_ROOT / "bin/lean.exe") != LEAN_SHA: raise RuntimeError("Pinned runtime mismatch")
    stamp = datetime.now(timezone.utc).isoformat()
    bindings, rows, reads, queue = {}, [], [], ["Init"]
    for module, folder, digest, nthm, ndef, status, chunk in SPECS:
        original = BASE / "round22" / folder / (module + ".lean")
        own_source = OWN / "sources" / (module + ".lean")
        if own_source.resolve().parent != (OWN / "sources").resolve(): raise RuntimeError("Common source root required")
        if sha(original) != digest or sha(own_source) != digest: raise RuntimeError("Exact source copy mismatch")
        code = lean_code(own_source)
        decls = re.findall(r"^(theorem|def)\s+(\w+)", code, re.M)
        printed = re.findall(r"^#print axioms " + re.escape(NAMESPACE) + r"\.(\w+)$", code, re.M)
        if ([name for _, name in decls] != printed or len(set(printed)) != len(printed)
                or sum(kind == "theorem" for kind, _ in decls) != nthm
                or sum(kind == "def" for kind, _ in decls) != ndef
                or re.search(r"\b(?:sorry|admit|axiom|native_decide|unsafe)\b", code)):
            raise RuntimeError("Catalogue/forbidden tokens")
        rows.append({"module": module, "source": str(own_source), "source_sha256": digest,
            "original_source": str(original), "source_status": status, "theorem_count": nthm, "definition_count": ndef,
            "declarations": [{"kind": kind, "qualified_name": NAMESPACE + "." + name} for kind, name in decls],
            "qualified_prints": [NAMESPACE + "." + name for name in printed],
            "compiler_options": ["-DmaxHeartbeats=1000000"],
            "scope": "CONCRETE_FINITE_CHARACTER_ORTHOGONALITY_A0_CIRCLE_TRUE_LAMBDA_PP_AUX_ONLY",
            "author_olean_allowed": False})
        bindings[str(original)] = digest; bindings[str(own_source)] = digest
        reads += [(original, "FULL", chunk), (own_source, "FULL_OWN_COPY", args.source_read)]
        queue.extend(imports(own_source))
    depdir = OWN / "readonly_oleans"; depdir.mkdir(exist_ok=False)
    if list(depdir.iterdir()): raise RuntimeError("No local dependency authorized")
    support = [
        (JUDGE / "discrete_source_review_revision02.md", "bee48a1fdb3347206ede5998f412e4aeebfe26cde334163d7220a887c364c459", "76fdfa"),
        (BASE / "round22/role3/discrete_circle_source22/revision02/source_review22.md", "ff8764229a61cb1cf4b9cf2f7d66a50dcacbf95e0e5bd2d88250419ac8190bd9", "f2bb01"),
        (BASE / "round22/role3/discrete_circle_source22/revision02/read_receipts22.json", "3fabab0aa54ea54ec3b875ef78710b277bd3f7dcde229c9c58257bf92f5843a4", "d2a0ba"),
        (BASE / "round22/role3/discrete_circle_source22/source_contract22.md", "f930ed4353729c73047a36d2ec68bab7387ee4ce2cdb2f4cf8ba1b13a941c49c", "09932d"),
        (BASE / "round22/role3/discrete_circle_source22/read_receipts22.json", "866035a817c15b6d094a6d491bb49093cab69dc1e0fe6bcd5e3664c148ac94d8", "3241a7"),
        (JUDGE / "batch13/adjudication.md", "170bbde5cba0e5d3040e5a6efe4c20946ba90acaf17c2e66ca125f727ee009c4", "8a4abb"),
        (JUDGE / "batch13/completion_receipt.json", "d805e32655b41b5ef152a30220d63401f4b9edda91ffafebd231a6d6cf2e5c5e", "878f46")]
    for path, digest, chunk in support:
        if sha(path) != digest: raise RuntimeError("Support provenance changed")
        bindings[str(path)] = digest; reads.append((path, "FULL_CURRENT_OR_PREVIOUS_CLOSED", chunk))
    api_reads = [
        ("Mathlib/Algebra/BigOperators/Ring.lean", "f4eb08", "TARGETED_9_74_SUM_MUL_SUM"),
        ("Mathlib/RingTheory/RootsOfUnity/Complex.lean", "85133f", "TARGETED_50_52_PRIMITIVE_EXP"),
        ("Mathlib/RingTheory/RootsOfUnity/PrimitiveRoots.lean", "e30279", "TARGETED_280_340_SIGNED_POW"),
        ("Mathlib/Data/Complex/Exponential.lean", "7d0bb6", "TARGETED_199_230_702_712"),
        ("Mathlib/Algebra/GeomSum.lean", "1dae51", "TARGETED_218_249"),
        ("Mathlib/Algebra/BigOperators/Group/Finset.lean", "1dae51", "TARGETED_789_817_TO_ADDITIVE_SUM_PRODUCT")]
    for relative, chunk, scope in api_reads:
        path = CACHE / "mathlib" / relative
        bindings[str(path)] = sha(path); reads.append((path, scope, chunk))
    original_old = BASE / "round22/role3/discrete_circle_source22/DiscreteThermalProjection22.lean"
    if sha(original_old) != "2a964deed343671d87b518b4da956cd36ad33fd6965f1feb69e5d3739ef0e696": raise RuntimeError("Old discrete source changed")
    def headers(path):
        text = lean_code(path)
        return [" ".join(text[hit.start():text.index(":=", hit.end())].split())
                for hit in re.finditer(r"^(?:def|theorem)\s+\w+", text, re.M)]
    if headers(original_old) != headers(OWN / "sources/DiscreteThermalProjection22.lean"):
        raise RuntimeError("Discrete contract changed")
    bindings[str(original_old)] = sha(original_old)
    old_rows = [{"path": str(path), "sha256": sha(path)} for path in sorted(JUDGE.rglob("*")) if path.is_file() and OWN not in path.parents]
    bindings.update({item["path"]: item["sha256"] for item in old_rows})
    write_new(OWN / "closed_judge_bindings.json", {"schema": "ROUND22_JUDGE5_CLOSED_BINDINGS_BATCH14", "inputs": old_rows,
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
    write_new(OWN / "import_bindings.json", {"schema": "ROUND22_JUDGE5_IMPORT_BINDINGS_BATCH14", "module_count": len(closure),
        "explicit_implicit_prelude_seed": "Init", "unresolved": unresolved,
        "entries": sorted(closure, key=lambda item: item["module"]), "readonly_local_entries": [], "compiler_invocations": 0})
    reads += [(OWN / "create_tools_source.py", "FULL_METADATA_TEXT_GENERATOR_ONLY", args.generator_read),
        (OWN / "prepare_metadata.py", "FULL_BEFORE_METADATA_RUN", args.builder_read),
        (OWN / "run_once.py", "FULL_SOURCE_ONLY_NEVER_EXECUTED", args.launcher_read),
        (OWN / "preparation.md", "FULL_SOURCE_AUDIT", args.audit_read)]
    for path, _, _ in reads: bindings[str(path)] = sha(path)
    write_new(OWN / "read_receipts.json", {"schema": "ROUND22_JUDGE5_READ_RECEIPTS_BATCH14", "time_utc": stamp,
        "entries": [{"path": str(path), "sha256": sha(path), "scope": scope, "chunk": chunk} for path, scope, chunk in reads],
        "truncated_reads_excluded": [], "corrected_read_path_error": "85133f Analysis/Complex/Exponential.lean missing; corrected745178/7d0bb6",
        "common_source_root_prepared": str(OWN / "sources"), "all_import_mathematical_FULL_claim": False,
        "compiler_invocations": 0, "numeric_invocations": 0})
    write_new(OWN / "catalog.json", {"schema": "ROUND22_JUDGE5_CATALOG_BATCH14", "time_utc": stamp,
        "modules": rows, "module_count": 1, "total_declarations": 29, "theorem_count": 20, "definition_count": 9,
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
    manifest = {"schema": "ROUND22_JUDGE5_PREPARED_MANIFEST_BATCH14", "time_utc": stamp,
        "status": "PREPARED_SOURCE_ONLY_GATE_CLOSED" if not unresolved else "PREPARATION_IMPORT_OPEN", "role": "ROLE5",
        "modules": list(MODULES), "compiler_invocations": 0, "numeric_invocations": 0,
        "immutable_inputs": [{"path": path, "sha256": digest} for path, digest in sorted(bindings.items())],
        "import_module_count": len(closure), "implicit_Init_closure_included": True, "unresolved_modules": unresolved,
        "common_source_root": str(OWN / "sources"), "source_catalog_sha256": sha(OWN / "catalog.json"),
        "launcher_sha256": sha(OWN / "run_once.py"), "readonly_local_dependencies": [], "closed_judge_files": len(old_rows),
        "protected_archive_count": 3089, "author_olean_used": False, "numeric_banks": [],
        "previous_official_modules": 75, "previous_official_declarations": 1223,
        "hypothetical_after_all_PASS_modules": 76, "hypothetical_after_all_PASS_declarations": 1252,
        "official_count_requires_ROOT_observation": True, "H1_paid": False, "C3_paid": False,
        "C5_global_Arch_paid": False, "D_N_paid": False, "win": False}
    write_new(OWN / "prepared_manifest.json", manifest)
    receipt = {"schema": "ROUND22_JUDGE5_PREPARATION_RECEIPT_BATCH14", "time_utc": datetime.now(timezone.utc).isoformat(),
        "status": manifest["status"], "compiler_invocations": 0, "numeric_invocations": 0,
        "manifest_sha256": sha(OWN / "prepared_manifest.json"), "launcher_sha256": manifest["launcher_sha256"],
        "catalog_sha256": manifest["source_catalog_sha256"], "read_receipts_sha256": sha(OWN / "read_receipts.json"),
        "import_bindings_sha256": sha(OWN / "import_bindings.json"), "closed_judge_bindings_sha256": sha(OWN / "closed_judge_bindings.json"),
        "imports": len(closure), "inputs": len(bindings), "closed_judge_files": len(old_rows), "archives": 3089,
        "modules": 1, "declarations": 29, "theorems": 20, "definitions": 9, "unresolved": unresolved,
        "one_module_SOURCE_not_elaborated": True, "readonly_independent_dependency_count": 0,
        "common_source_root": str(OWN / "sources"), "no_author_olean_on_lean_path": True,
        "old_batches_recompiled": False, "numeric_bank_replayed": False, "no_win": True}
    write_new(OWN / "prepared_receipt.json", receipt)
    print(json.dumps(receipt, sort_keys=True))

if __name__ == "__main__":
    main()
'''
new(OWN / "prepare_metadata.py", prefix + constants + helpers + main)
launcher = (JUDGE / "batch13/run_once.py").read_text(encoding="utf-8")
launcher = launcher.replace("batch13", "batch14").replace("BATCH13", "BATCH14")
launcher = launcher.replace("ThermalProjectionIdentity22", "DiscreteThermalProjection22")
launcher = launcher.replace('LOCAL_DEPENDENCIES = ("ThermalProjectionEnvelope22",)', 'LOCAL_DEPENDENCIES = ()')
launcher = launcher.replace("one projection identity auxiliary", "one finite discrete projection auxiliary")
new(OWN / "run_once.py", launcher)
(OWN / "sources").mkdir(exist_ok=False)
original = JUDGE.parent / "role3/discrete_circle_source22/revision02/DiscreteThermalProjection22.lean"
with (OWN / "sources" / original.name).open("xb") as stream:
    stream.write(original.read_bytes())
print("New SOURCE tools and Discret29 copy written. No freeze, candidate import, Lean or numeric invocation.")
