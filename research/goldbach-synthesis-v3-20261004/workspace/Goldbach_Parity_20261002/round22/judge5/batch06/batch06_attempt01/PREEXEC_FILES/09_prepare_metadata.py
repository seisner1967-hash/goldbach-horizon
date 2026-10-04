"""New batch06 SOURCE freeze only: hashing and lexical imports; no subprocess."""
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
    ("ZetaEulerDirect22", "role4/h1_contour", "0d790ed67706e2f3c3556d2c5e7fefd50664177f5fb54584beee1d137e430a71", 4, 1, "SOURCE_NOT_COMPILED", "1145d0"),
    ("ZetaReflection22", "role4/h1_contour", "54e32a95a62929c7251bf130156adbc7da7d66ceb1cb77609382e33c025f4a42", 6, 1, "SOURCE_NOT_COMPILED", "388201"),
    ("GammaPsiDuplication22", "role3/h1_psi/revision05/source_final", "0491177c6cfc1ef35b28796be404a3ca7975bac357cc6551b80d12333726812e", 2, 0, "AUTHOR_PASS_PENDING_INDEPENDENT_JUDGE", "1748b3"),
    ("GammaPsiReflection22", "role3/h1_psi", "8e070c18a483ac71703f66b80dbcf4129f0f16ada8f2a933497655b3a7cdaa30", 5, 0, "SOURCE_NOT_COMPILED", "a8d62a"),
    ("ContourChiPsi22", "role3/h1_psi", "a90d536187fe342d01cf913a56c80a34e6846eb273a533bcdd843289f7d83248", 9, 1, "SOURCE_NOT_COMPILED", "b7ddba"),
    ("ContourChiScaled22", "role3/h1_psi", "d0aa03290fe806f9c84c0311a7e07a2fe0737148c9c1de7c80876118fb7a64d7", 8, 2, "SOURCE_NOT_COMPILED", "56411a"),
    ("PsiKernelEnvelope22", "role3/h1_psi", "949c6fc0d895003b522518e18ae89bdf6b5062448d5273f146685645afb72ef8", 8, 1, "SOURCE_NOT_COMPILED", "1a045e"),
    ("PsiKernelDomination22", "role3/h1_psi", "80b85c14c7db79121f7c9cb003edf97a7d5e947f785ce8402f910ea93aad48bc", 19, 2, "SOURCE_NOT_COMPILED", "f4d66f"),
    ("PsiMixedFubini22", "role3/h1_psi", "d143b0fbdf795a1b400f737274a5eae5c8c5bba0c2e4ecaf145d86932df0b250", 17, 2, "SOURCE_NOT_COMPILED", "e4904c"),
)
MODULES = tuple(row[0] for row in SPECS)
DEPS = (
    ("GammaPrerequisites22", "batch02_sources", "batch02_attempt01", "9f5e5fe14d18e2b7c3ab364e461bfcc01d29ee4ef4af6d627d6ad9fcd102fbe7", "fc0dad0b550f13a5c3a5b1e7cf1cfa22fc3a233822fc548cce155ab7a7274477", "d0859a", "63b5ef", "a159b22e7ac4e8718f0572fdbf3e6d424294571eab01d5ed1ff979a821af48f9"),
    ("GammaDerivative22", "batch03/sources", "batch03/batch03_attempt01", "026ced6097c7d658b41501254bfbcdefe86ff2e68fb9fbe3fab01023a4cb0975", "0618f801c5feec7b760ba18ab3dddc960519b398dd1d1b719acc809132518125", "e762e6", "49e477", "74959436b372e6dc180b1f5b79e51e17bded56361ba70774695a906dc3f3d4ee"),
    ("GammaBoxBounds22", "batch05/sources", "batch05/batch05_attempt01", "4874192b1c2ca9edc7262d8a46f9d4a1e339c565e5bb48fefbf4d6d100071edf", "4cb4d50f6d7dd8087e9d227d7052cb445527f018249dc3ffe6493ea2a87bfce3", "9ca5d5", "dd3834", "090538a9240c53bf248f7c9dbfef3fc708f5de272313e2d4733cb216ad252607"),
    ("GammaContourComponent22", "batch05/sources", "batch05/batch05_attempt01", "891454d4714e68039a0976e7eb9347e10653237f4608993b52b481cc95b0a3fe", "f9b5a9b2f47dd0ee03a58e6cd666d702ff5fc6eba39d07e89566a254df44648b", "2e798b", "dd3834", "090538a9240c53bf248f7c9dbfef3fc708f5de272313e2d4733cb216ad252607"),
    ("GammaPsiCore22", "batch04/three_modules/sources", "batch04/three_modules/batch04_attempt01", "450962be9526866fa0ffebc39ef29a819d94b57a90000291337550e9f4dc7284", "15f66830eab0ee8e192d4fffee9518abd001b3167c28c527881bbdaabefb9a4b", "4a0681", "8657fd", "228b0958ecac8037e1776cf5cc32db340a8f52944c1e9cd398415dd9f0415c5d"),
    ("GammaPsiBetaLimit22", "batch04/three_modules/sources", "batch04/three_modules/batch04_attempt01", "b4adf3ac71dd7c9d0e6e78f83ce805ddc7eaf5e8f5978aa4c1d6b87bc8caceb8", "28e54d352bde19a6ab175dfa6dfa7667f41e2f644b81c90ac6256ead16b40cd0", "732f07", "8657fd", "228b0958ecac8037e1776cf5cc32db340a8f52944c1e9cd398415dd9f0415c5d"),
    ("GammaPsiIntegral22", "batch04/three_modules/sources", "batch04/three_modules/batch04_attempt01", "3f254cdfeee333aa66eba719b944f64a693fa2e15f0265f340ace9c2a99f6aaf", "5dd15ee927c32894e7cafb4f05c78fb65c48e1cca93d91eee7ae96518f43ee1e", "6060c8", "8657fd", "228b0958ecac8037e1776cf5cc32db340a8f52944c1e9cd398415dd9f0415c5d"),
)
LOCAL_DEPENDENCIES = tuple(row[0] for row in DEPS)
OWN_SOURCE_FULL = ("e37773", "7f2cb8", "ed619f", "624c6e", "fbcf86", "69fda6", "d24b1f", "844cbd", "c7b9c0")


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
        if sha(original) != digest or sha(own_source) != digest: raise RuntimeError("Exact source copy mismatch " + module)
        code = lean_code(own_source)
        decls = re.findall(r"^(theorem|def)\s+(\w+)", code, re.M)
        printed = re.findall(r"^#print axioms GoldbachContinuous22\.(\w+)$", code, re.M)
        if ([name for _, name in decls] != printed or len(set(printed)) != len(printed) or sum(kind == "theorem" for kind, _ in decls) != nthm or sum(kind == "def" for kind, _ in decls) != ndef or re.search(r"\b(?:sorry|admit|axiom|native_decide|unsafe)\b", code)): raise RuntimeError("Catalogue/forbidden tokens " + module)
        rows.append({"module": module, "source": str(own_source), "source_sha256": digest, "original_source": str(original), "source_status": status, "theorem_count": nthm, "definition_count": ndef,
            "declarations": [{"kind": kind, "qualified_name": "GoldbachContinuous22." + name} for kind, name in decls], "qualified_prints": ["GoldbachContinuous22." + name for name in printed],
            "compiler_options": ["-DmaxHeartbeats=1000000"], "scope": "TRUE_CHI_PSI_PAIRED_KERNEL_AND_MIXED_FUBINI_AUX_ONLY", "author_olean_allowed": False})
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
    support = [(BASE / "round22/role3/h1_psi/C5_checkpoint_after_psi05.md", "9119650574a298e229f620623d50c14d7e749d915305ffe0fa459a9dc6c889f7", "68ae01"),
        (JUDGE / "C5_source_review22.md", "b2458e4edfd3a8b21de91a09d2d3ea4a0134ae764dc64d7c1d617cdd3b0a66e8", "53f668"),
        (JUDGE / "error_contract_source_review22.md", "6ac1af9df6b555aa34dcb9714c6c43f8dd6345d804577409688ca7ef3557cccc", "dcdccb"),
        (BASE / "round22/role3/h1_psi/revision05/psi_batch05_attempt01/receipt.json", "74b5dfe2fd4f1b470714fd2d27aee62e678e77ab33f64b36e04eab92fc3ea531", "90775a")]
    for path, digest, chunk in support:
        if sha(path) != digest: raise RuntimeError("Support provenance changed")
        bindings[str(path)] = digest; reads.append((path, "FULL_CURRENT_OR_PREVIOUS_CLOSED", chunk))
    duplication = json.loads(support[-1][0].read_text(encoding="utf-8"))
    drow = next(item for item in duplication["rows"] if item["module"] == "GammaPsiDuplication22")
    if drow["exit_code"] != 0 or not drow["exact_axiom_coverage_standard_only"] or not duplication["all_inputs_unchanged"] or drow["source_sha256"] != SPECS[2][2]: raise RuntimeError("Dup05 author provenance not PASS")
    author_log = support[-1][0].parent / "GammaPsiDuplication22.log"
    author_obj = support[-1][0].parent / "GammaPsiDuplication22.olean"
    if sha(author_log) != drow["log_sha256"] or sha(author_obj) != drow["olean_sha256"]: raise RuntimeError("Dup05 author artifact changed")
    bindings[str(author_obj)] = sha(author_obj)
    author_capture_paths = [support[-1][0]]
    for name in ("GammaPsiDuplication22_START.json", "GammaPsiDuplication22_FIN.json", "GammaPsiDuplication22.log"):
        path = support[-1][0].parent / name
        if not path.exists(): raise RuntimeError("Author provenance artifact missing " + name)
        bindings[str(path)] = sha(path); author_capture_paths.append(path)
    reads += [(support[-1][0].parent / "GammaPsiDuplication22_FIN.json", "FULL", "1a9e6f"), (author_log, "FULL", "1a9e6f")]
    old_rows = [{"path": str(path), "sha256": sha(path)} for path in sorted(JUDGE.rglob("*")) if path.is_file() and OWN not in path.parents]
    bindings.update({item["path"]: item["sha256"] for item in old_rows})
    write_new(OWN / "closed_judge_bindings.json", {"schema": "ROUND22_JUDGE5_CLOSED_BINDINGS_BATCH06", "inputs": old_rows, "old_batches_recompiled": False, "compiler_invocations": 0})
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
    write_new(OWN / "import_bindings.json", {"schema": "ROUND22_JUDGE5_IMPORT_BINDINGS_BATCH06", "module_count": len(closure), "explicit_implicit_prelude_seed": "Init", "unresolved": unresolved, "entries": sorted(closure, key=lambda item: item["module"]), "readonly_local_entries": dependencies, "compiler_invocations": 0})
    reads += [(OWN / "prepare_metadata.py", "FULL_BEFORE_METADATA_RUN", args.builder_read), (OWN / "run_once.py", "FULL_SOURCE_ONLY_NEVER_EXECUTED", args.launcher_read), (OWN / "preparation.md", "FULL_SOURCE_AUDIT", args.audit_read)]
    for path, _, _ in reads: bindings[str(path)] = sha(path)
    write_new(OWN / "read_receipts.json", {"schema": "ROUND22_JUDGE5_READ_RECEIPTS_BATCH06", "time_utc": stamp, "entries": [{"path": str(path), "sha256": sha(path), "scope": scope, "chunk": chunk} for path, scope, chunk in reads], "truncated_reads_excluded": ["f3c2c8 own MixedFubini aggregate read; replaced FULL c7b9c0"], "all_import_mathematical_FULL_claim": False, "compiler_invocations": 0, "numeric_invocations": 0})
    write_new(OWN / "catalog.json", {"schema": "ROUND22_JUDGE5_CATALOG_BATCH06", "time_utc": stamp, "modules": rows, "module_count": 9, "total_declarations": 88, "theorem_count": 78, "definition_count": 10, "readonly_local_dependencies": list(LOCAL_DEPENDENCIES), "dependency_bindings": dependencies,
        "support_capture_paths": [str(item[0]) for item in support[:3]], "author_provenance_capture_paths": list(map(str, author_capture_paths)), "non_DUP_modules_author_PASS_claimed": False, "compiler_invocations": 0, "win": False})
    archive_path = BASE / "round22/previous_artifacts_sha256.json"
    archives = json.loads(archive_path.read_text(encoding="utf-8"))
    if len(archives["sha256"]) != 3089 or archives["file_count"] != 3089: raise RuntimeError("Archive count changed")
    for relative, digest in archives["sha256"].items():
        if sha(BASE / relative) != digest: raise RuntimeError("Protected archive changed")
    for path in (archive_path, PYTHON, LEAN_ROOT / "bin/lean.exe"): bindings[str(path)] = sha(path)
    for name in ("prepare_metadata.py", "run_once.py", "preparation.md", "catalog.json", "read_receipts.json", "import_bindings.json", "closed_judge_bindings.json"): bindings[str(OWN / name)] = sha(OWN / name)
    manifest = {"schema": "ROUND22_JUDGE5_PREPARED_MANIFEST_BATCH06", "time_utc": stamp, "status": "PREPARED_SOURCE_ONLY_GATE_CLOSED" if not unresolved else "PREPARATION_IMPORT_OPEN", "role": "ROLE5", "modules": list(MODULES), "compiler_invocations": 0, "numeric_invocations": 0,
        "immutable_inputs": [{"path": path, "sha256": digest} for path, digest in sorted(bindings.items())], "import_module_count": len(closure), "implicit_Init_closure_included": True, "unresolved_modules": unresolved, "source_catalog_sha256": sha(OWN / "catalog.json"), "launcher_sha256": sha(OWN / "run_once.py"), "readonly_local_dependencies": list(LOCAL_DEPENDENCIES), "closed_judge_files": len(old_rows), "protected_archive_count": 3089, "author_olean_used": False, "numeric_banks": [],
        "previous_official_modules": 68, "previous_official_declarations": 1132, "hypothetical_after_all_PASS_modules": 77, "hypothetical_after_all_PASS_declarations": 1220, "official_count_requires_ROOT_observation": True, "H1_paid": False, "C3_paid": False, "C5_global_Arch_paid": False, "D_N_paid": False, "win": False}
    write_new(OWN / "prepared_manifest.json", manifest)
    receipt = {"schema": "ROUND22_JUDGE5_PREPARATION_RECEIPT_BATCH06", "time_utc": datetime.now(timezone.utc).isoformat(), "status": manifest["status"], "compiler_invocations": 0, "numeric_invocations": 0, "manifest_sha256": sha(OWN / "prepared_manifest.json"), "launcher_sha256": manifest["launcher_sha256"], "catalog_sha256": manifest["source_catalog_sha256"], "read_receipts_sha256": sha(OWN / "read_receipts.json"), "import_bindings_sha256": sha(OWN / "import_bindings.json"), "closed_judge_bindings_sha256": sha(OWN / "closed_judge_bindings.json"), "imports": len(closure), "inputs": len(bindings), "closed_judge_files": len(old_rows), "archives": 3089, "modules": 9, "declarations": 88, "theorems": 78, "definitions": 10, "unresolved": unresolved, "eight_modules_SOURCE_not_compiled": True, "Dup05_author_PASS_only": True, "no_author_olean_on_lean_path": True, "old_batches_recompiled": False, "numeric_bank_replayed": False, "no_win": True}
    write_new(OWN / "prepared_receipt.json", receipt)
    print(json.dumps(receipt, sort_keys=True))


if __name__ == "__main__":
    main()
