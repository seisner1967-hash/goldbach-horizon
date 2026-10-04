"""Batch21 metadata only: exact hashes, copies and lexical import/print headers.
No Lean, tactic, candidate import, modular arithmetic or subprocess invocation.
Run once only after this entire helper and launcher have been read as SOURCE.
"""
from datetime import datetime, timezone
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

OWN = Path(__file__).resolve().parent
BASE = OWN.parents[2]
JUDGE = BASE / "round22/judge5"
CACHE = BASE.parent / "q356-canonical-binding-replay/.lake/packages"
PACKAGES = ("aesop", "batteries", "importGraph", "LeanSearchClient", "mathlib", "plausible", "proofwidgets", "Qq")
LEAN_ROOT = Path(r"C:\Users\Utilisateur\.elan\toolchains\leanprover--lean4---v4.15.0")
PYTHON = Path(r"C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe")
PYTHON_SHA = "4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c"
LEAN_SHA = "8a1ef18583d74d917194bba4743ce9765bad64b00c52bada002ee44796fb9e08"
REG_SHA = "875cebdd8e510fe3341b05009a76991801777b2a060a07229c5323033226ba99"
SOURCE_DIR = BASE / "round22/role3/concrete_ntt_roots_source22"
REVIEW_DIR = BASE / "round22/role4/concrete_ntt_roots_review_source01"
SPECS = (
    ("ConcreteNTTRoots22", "433903d458f6ccd43f366e92265d0778250484f4721fcd885ca0a01a771e8e6a", 17, 1, "GoldbachConcreteNTTRoots22", "9a1c58"),
    ("ConcreteNTTA32Projection22", "cefc07197945f1e9710895d4a01455861ae6db21365cc44dec206178e76af4c3", 5, 5, "GoldbachConcreteNTTA32Projection22", "958225"))
MODULES = tuple(row[0] for row in SPECS)
DEP_SPECS = (
    ("FiniteFieldProjection22", 19, "2b1cc267ce780a6a45c039f4b4b82d5a4ad4541fa224d76413dec5432658a48a", "0304400125a93cfddace45bcc4428d835c8ee204817f88f156e9fd44ee856f4f", "1a645174f44f5545e6069139cd3d452f9eb6100f7946152c5cf50c56c8252d57", 24),
    ("QuantizedLambdaEnvelope22", 17, "526354f4b96006eb2b297477fb6f09dd8a683e88cc95feb816a31357df0a2331", "e821070b97b3fa4b71a3e279ecb9bc6c0de6cafdfe9dc8712b5d5a22858a6485", "9449666ee8bdbbae74ea849e5a9ce2eb5c0c5bd7dd24c14a2d28065068178298", 14),
    ("RationalLogQuantization22", 17, "dfabcabf39ecc1ba7769eb99ea73e0483dc6925f0bb3d11c05891d22c0a787a7", "20db07cdfb5717d7f9ab0b3e75d3c15b9e16c6820ad5285bd7debb62b0a31434", "9449666ee8bdbbae74ea849e5a9ce2eb5c0c5bd7dd24c14a2d28065068178298", 38))
LOCAL_DEPENDENCIES = tuple(row[0] for row in DEP_SPECS)
SUPPORT = (
    (SOURCE_DIR / "source_contract22.txt", "01ff6b0e86bd86882708ef9230e741abbb854ac837851139db312cbde00c07f5", "FULL", "b76221"),
    (SOURCE_DIR / "source_read_receipts22.json", "ddd215014eb76c6a37dac5ea924acf6bbc7819e981ae0e6365f9f1521864bc7f", "FULL", "b76221"),
    (SOURCE_DIR / "source_handoff22.json", "a8aebfae0848840f24abe94f97227db9860f9e7d4d1632cee5bb661ec9bc93e8", "FULL", "b76221"),
    (REVIEW_DIR / "review22.md", "690dd65701892780da9647adc29557df902ada9889f080399d03c12bed38d0d5", "FULL", "48ee50"),
    (REVIEW_DIR / "review_receipts22.json", "70b446f514c42b67d4878c9a02b1bcd29f55c91dd36ff42d81f15595d9476109", "FULL", "857e1e"),
    (JUDGE / "batch20/completion_receipt.json", "ae094e8b630468029d9546fad96ac12bad81e82dcb3df488069440c4a893a885", "FULL", "d7e7be"),
    (JUDGE / "batch20/batch20_attempt01/receipt.json", "28a07d17e88dbb09157c5958306efd557cd9d4727dd4948b336aaad4ee48d68c", "FULL", "d7e7be"),
    (BASE / ".arbor/sessions/parity/.coordinator/messages/round22_judge_batch20_closed_observation.json", "247ee3f969b70fb04894db0c474d21d8fe5407461945fcb02d305661d8609ef5", "FULL", "60f1d5"))


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
    """Lexical HEADER metadata only; no parser/elaborator/tactic execution."""
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
            if end < 0:
                raise RuntimeError("Unterminated raw string")
            clean.append("\n" * content[start:end].count("\n")); i = end + len(delimiter)
        elif content[i] == "'" and (character := re.match(r"'(?:\\[^\n]|[^\\'\n])'", content[i:])):
            clean.append(" " * len(character.group(0))); i += len(character.group(0))
        elif content[i] == '"':
            quoted = True; clean.append(" "); i += 1
        else:
            clean.append(content[i]); i += 1
    if depth or quoted:
        raise RuntimeError("Unterminated comment/string")
    return "".join(clean)


def imports(path):
    code = lean_code(path)
    name = r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*"
    result = [word for match in re.finditer(rf"^import[ \t]+({name}(?:[ \t]+{name})*)[ \t]*$", code, re.M)
              for word in match.group(1).split()]
    if not re.search(r"^prelude[ \t]*$", code, re.M):
        result.append("Init")
    return result


def resolve(module):
    if module in LOCAL_DEPENDENCIES:
        dep = next(row for row in DEP_SPECS if row[0] == module)
        return JUDGE / (f"batch{dep[1]:02d}/sources/{module}.lean"), OWN / "readonly_oleans" / (module + ".olean")
    rel = Path(*module.split("."))
    candidates = [(CACHE / package / rel.with_suffix(".lean"), CACHE / package / ".lake/build/lib" / rel.with_suffix(".olean"))
                  for package in PACKAGES]
    candidates += [(root / rel.with_suffix(".lean"), LEAN_ROOT / "lib/lean" / rel.with_suffix(".olean"))
                   for root in (LEAN_ROOT / "src/lean", LEAN_ROOT / "src/lean/lake")]
    for source, obj in candidates:
        if source.exists() or obj.exists():
            return source, obj
    return None, None


def main():
    parser = argparse.ArgumentParser()
    for option in ("builder-read", "launcher-read", "audit-read", "source-read"):
        parser.add_argument("--" + option, required=True)
    args = parser.parse_args()
    if any((OWN / name).exists() for name in ("prepared_manifest.json", "prepared_receipt.json", "readonly_oleans", "catalog.json")):
        raise RuntimeError("Exclusive one-time metadata preparation only")
    if Path(sys.executable).resolve() != PYTHON.resolve() or sha(PYTHON) != PYTHON_SHA or sha(LEAN_ROOT / "bin/lean.exe") != LEAN_SHA:
        raise RuntimeError("Pinned metadata runtime bytes mismatch")
    stamp = datetime.now(timezone.utc).isoformat()
    bindings, rows, reads, queue = {}, [], [], ["Init"]

    def bind(path, expected=None):
        path = Path(path).resolve()
        digest = sha(path)
        if expected is not None and digest != expected:
            raise RuntimeError("Frozen binding changed: " + str(path))
        entry = {"path": str(path), "sha256": digest, "bytes": path.stat().st_size}
        k = str(path).casefold()
        if k in bindings and bindings[k] != entry:
            raise RuntimeError("Binding conflict: " + str(path))
        bindings[k] = entry
        return digest

    for module, digest, nthm, ndef, namespace, original_read in SPECS:
        original = SOURCE_DIR / (module + ".lean")
        own_source = OWN / "sources" / (module + ".lean")
        bind(original, digest); bind(own_source, digest)
        code = lean_code(own_source)
        decls = re.findall(r"^(theorem|def)\s+(\w+)", code, re.M)
        printed = re.findall(r"^#print axioms " + re.escape(namespace) + r"\.(\w+)$", code, re.M)
        if ([name for _, name in decls] != printed or len(set(printed)) != len(printed)
                or sum(kind == "theorem" for kind, _ in decls) != nthm
                or sum(kind == "def" for kind, _ in decls) != ndef
                or re.search(r"\b(?:sorry|admit|axiom|native_decide|unsafe)\b", code)):
            raise RuntimeError("Catalogue or forbidden candidate tokens mismatch")
        rows.append({"module": module, "source": str(own_source), "source_sha256": digest,
            "original_source": str(original), "source_status": "SOURCE_ONLY_NOT_ELABORATED",
            "theorem_count": nthm, "definition_count": ndef,
            "declarations": [{"kind": kind, "qualified_name": namespace + "." + name} for kind, name in decls],
            "qualified_prints": [namespace + "." + name for name in printed],
            "compiler_options": ["-DmaxHeartbeats=1000000"],
            "scope": "CONCRETE_LUCAS_DYADIC_ROOT_AND_CANONICAL_A32_FINITE_PROJECTION_AUX_ONLY",
            "author_olean_allowed": False})
        reads.extend([(original, "FULL", original_read), (own_source, "FULL_EXACT_COPY", args.source_read)])
        queue.extend(imports(own_source))

    depdir = OWN / "readonly_oleans"
    depdir.mkdir(exist_ok=False)
    deps = []
    for module, batch, source_sha, olean_sha, receipt_sha, nprints in DEP_SPECS:
        source = JUDGE / f"batch{batch:02d}/sources/{module}.lean"
        actual = JUDGE / f"batch{batch:02d}/batch{batch:02d}_attempt01"
        olean, receipt_path = actual / (module + ".olean"), actual / "receipt.json"
        for path, digest in ((source, source_sha), (olean, olean_sha), (receipt_path, receipt_sha)):
            bind(path, digest)
        receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
        row = next(row for row in receipt["rows"] if row["module"] == module)
        if (receipt["status"] != f"INDEPENDENT_BATCH{batch:02d}_AUX_PASS" or not receipt["all_inputs_unchanged"]
                or row["status"] != "INDEPENDENT_LEAN_AUX_PASS" or row["exit_code"] != 0
                or not row["exact_axiom_coverage_standard_only"] or len(row["axiom_rows"]) != nprints
                or row["source_sha256"] != source_sha or row["olean_sha256"] != olean_sha):
            raise RuntimeError("Real independent readonly provenance mismatch: " + module)
        bind(actual / (module + ".log"), row["log_sha256"])
        bind(actual / (module + "_FIN.json"))
        dep_copy = depdir / (module + ".olean")
        with dep_copy.open("xb") as stream:
            stream.write(olean.read_bytes())
        bind(dep_copy, olean_sha)
        deps.append({"module": module, "source": str(source), "source_sha256": source_sha,
            "olean_original": str(olean), "olean_copy": str(dep_copy), "olean_sha256": olean_sha,
            "independent_receipt": str(receipt_path), "independent_receipt_sha256": receipt_sha,
            "status": "INDEPENDENT_LEAN_AUX_PASS", "recompile_authorized": False})
        reads.extend([(source, "HASH_ONLY_READONLY_SOURCE", "200439_or_metadata"),
            (receipt_path, "HASH_PLUS_CONTROL_JSON_PROVENANCE_CHECK_NOT_RAW_FULL", "45cceb"),
            (actual / (module + "_FIN.json"), "FULL", "8a43d6" if batch == 19 else "60f1d5"),
            (actual / (module + ".log"), "FULL", "8a43d6")])

    for path, digest, scope, chunk in SUPPORT:
        bind(path, digest); reads.append((path, scope, chunk))
    observation = json.loads(SUPPORT[-1][0].read_text(encoding="utf-8"))
    if observation["official_modules"] != 80 or observation["official_declarations"] != 1339 or observation["status"] != "INDEPENDENT_BATCH20_AUX_PASS":
        raise RuntimeError("Actual ROOT baseline20 observation mismatch")
    review = json.loads((REVIEW_DIR / "review_receipts22.json").read_text(encoding="utf-8"))
    for item in review["bindings"]:
        bind(item["path"], item["sha256"])
        reads.append((Path(item["path"]), item["scope"], item["receipt"]))

    old_rows = [{"path": str(path), "sha256": sha(path), "bytes": path.stat().st_size}
                for path in sorted(JUDGE.rglob("*")) if path.is_file()]
    for item in old_rows:
        bind(item["path"], item["sha256"])
    write_new(OWN / "closed_judge_bindings.json", {"schema": "ROUND22_JUDGE5_CLOSED_BINDINGS_BATCH21",
        "inputs": old_rows, "scope": "BYTE_HASH_ALL_CLOSED_JUDGE_FILES_PRESENT_THROUGH_BATCH20",
        "raw_FULL_text_claim": False, "old_batches_recompiled": False, "compiler_invocations": 0})
    closure, unresolved, seen = [], [], set()
    while queue:
        module = queue.pop()
        if module in seen or module in MODULES:
            continue
        seen.add(module); source, obj = resolve(module)
        if source is None or not source.is_file() or not obj.is_file():
            unresolved.append({"module": module, "source": str(source), "olean": str(obj)})
            continue
        closure.append({"module": module, "source": str(source), "source_sha256": bind(source),
            "olean": str(obj), "olean_sha256": bind(obj), "read_scope": "HASH_AND_LEXICAL_IMPORT_HEADER_ONLY"})
        queue.extend(imports(source))
    write_new(OWN / "import_bindings.json", {"schema": "ROUND22_JUDGE5_IMPORT_BINDINGS_BATCH21",
        "module_count": len(closure), "implicit_Init_for_each_nonprelude_module": True,
        "explicit_prelude_seed": "Init", "unresolved": unresolved,
        "entries": sorted(closure, key=lambda item: item["module"]), "readonly_local_entries": deps,
        "metadata_only": True, "compiler_invocations": 0})

    reads.extend([(OWN / "prepare_metadata.py", "FULL_BEFORE_METADATA_EXECUTION", args.builder_read),
        (OWN / "run_once.py", "FULL_SOURCE_ONLY_NEVER_EXECUTED", args.launcher_read),
        (OWN / "preparation.md", "FULL", args.audit_read)])
    for path, _, _ in reads:
        bind(path)
    write_new(OWN / "read_receipts.json", {"schema": "ROUND22_JUDGE5_READ_RECEIPTS_BATCH21", "time_utc": stamp,
        "entries": [{"path": str(path), "sha256": sha(path), "scope": scope, "chunk": chunk} for path, scope, chunk in reads],
        "truncated_reads_excluded": ["358bb1 recursive inventory truncated", "0c6104 broad API search truncated"],
        "all_import_mathematical_FULL_claim": False, "candidate_sources_not_elaborated": True,
        "compiler_invocations": 0, "candidate_numeric_invocations": 0})
    write_new(OWN / "catalog.json", {"schema": "ROUND22_JUDGE5_CATALOG_BATCH21", "time_utc": stamp,
        "modules": rows, "module_count": 2, "total_declarations": 28, "theorem_count": 22, "definition_count": 6,
        "common_source_root": str(OWN / "sources"), "readonly_local_dependencies": list(LOCAL_DEPENDENCIES),
        "dependency_bindings": deps, "support_capture_paths": [str(item[0]) for item in SUPPORT],
        "author_provenance_capture_paths": [], "modules_author_PASS_claimed": False,
        "child_wall_seconds": 300, "max_heartbeats": 1000000, "compiler_invocations": 0, "win": False})
    archive_path = BASE / "round22/previous_artifacts_sha256.json"
    bind(archive_path, REG_SHA)
    archives = json.loads(archive_path.read_text(encoding="utf-8"))
    if len(archives["sha256"]) != 3089 or archives["file_count"] != 3089:
        raise RuntimeError("Protected archive count mismatch")
    for relative, digest in archives["sha256"].items():
        path = (BASE / relative).resolve()
        if not path.is_relative_to(BASE.resolve()) or sha(path) != digest:
            raise RuntimeError("Protected archive changed")
    for path in (PYTHON, LEAN_ROOT / "bin/lean.exe"):
        bind(path)
    for name in ("prepare_metadata.py", "run_once.py", "preparation.md", "catalog.json", "read_receipts.json", "import_bindings.json", "closed_judge_bindings.json"):
        bind(OWN / name)
    manifest = {"schema": "ROUND22_JUDGE5_PREPARED_MANIFEST_BATCH21", "time_utc": stamp,
        "status": "PREPARED_SOURCE_ONLY_GATE_CLOSED" if not unresolved else "PREPARATION_IMPORT_OPEN", "role": "ROLE5",
        "modules": list(MODULES), "compiler_invocations": 0, "candidate_numeric_invocations": 0,
        "immutable_inputs": sorted(bindings.values(), key=lambda item: item["path"].casefold()),
        "import_module_count": len(closure), "implicit_Init_closure_included": True, "unresolved_modules": unresolved,
        "common_source_root": str(OWN / "sources"), "source_catalog_sha256": sha(OWN / "catalog.json"),
        "launcher_sha256": sha(OWN / "run_once.py"), "readonly_local_dependencies": list(LOCAL_DEPENDENCIES),
        "closed_judge_files": len(old_rows), "protected_archive_count": 3089,
        "author_olean_used": False, "numeric_banks": [], "previous_official_modules": 80,
        "previous_official_declarations": 1339, "hypothetical_after_all_PASS_modules": 82,
        "hypothetical_after_all_PASS_declarations": 1367, "official_count_requires_ROOT_observation": True,
        "H1_paid": False, "native_refinement_paid": False, "coefficient_N_computed": False, "D_N_paid": False, "win": False}
    write_new(OWN / "prepared_manifest.json", manifest)
    receipt = {"schema": "ROUND22_JUDGE5_PREPARATION_RECEIPT_BATCH21", "time_utc": datetime.now(timezone.utc).isoformat(),
        "status": manifest["status"], "compiler_invocations": 0, "candidate_numeric_invocations": 0,
        "manifest_sha256": sha(OWN / "prepared_manifest.json"), "launcher_sha256": manifest["launcher_sha256"],
        "catalog_sha256": manifest["source_catalog_sha256"], "read_receipts_sha256": sha(OWN / "read_receipts.json"),
        "import_bindings_sha256": sha(OWN / "import_bindings.json"), "closed_judge_bindings_sha256": sha(OWN / "closed_judge_bindings.json"),
        "builder_sha256": sha(OWN / "prepare_metadata.py"), "preparation_doc_sha256": sha(OWN / "preparation.md"),
        "imports": len(closure), "inputs": len(bindings), "closed_judge_files": len(old_rows), "archives": 3089,
        "modules": 2, "declarations": 28, "theorems": 22, "definitions": 6, "unresolved": unresolved,
        "two_sources_not_elaborated": True, "readonly_independent_dependency_count": 3,
        "common_source_root": str(OWN / "sources"), "no_author_olean_on_lean_path": True,
        "old_batches_recompiled": False, "numeric_bank_replayed": False, "no_win": True}
    write_new(OWN / "prepared_receipt.json", receipt)
    print(json.dumps(receipt, sort_keys=True))


if __name__ == "__main__":
    main()
