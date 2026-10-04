"""Batch32 metadata only: exact hashes, copies and lexical import/print headers.
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
SOURCE_DIR = BASE / "round22/role4/complex_gamma_mellin_lambda_source01"
REVIEW_DIR = BASE / "round22/role3/gamma_exp_tail_bridge_source_review01"
OLD21 = BASE / "round22/role4/concrete_ntt_roots_prepare21"
BASELINE_OBSERVATION = (
    BASE / ".arbor/sessions/parity/.coordinator/messages/round22_judge_batch31_closed_observation.json",
    "cc2d85ccc2704cec69650e958c27327e64a4389f25f218faf6a315514307ee95")
SPECS = (
    ("ComplexGammaMellinExpTailBridge22", "4e804a6c678274c01848d290845c1a76b6820d790bfd14a34a80abb59feda38c", 2, 0, "GoldbachComplexGammaMellin22", "70a859"),)
MODULES = tuple(row[0] for row in SPECS)
DEP_SPECS = (
    ("GammaPrerequisites22", "batch02_sources/GammaPrerequisites22.lean", "batch02_attempt01",
     "9f5e5fe14d18e2b7c3ab364e461bfcc01d29ee4ef4af6d627d6ad9fcd102fbe7",
     "fc0dad0b550f13a5c3a5b1e7cf1cfa22fc3a233822fc548cce155ab7a7274477",
     "a159b22e7ac4e8718f0572fdbf3e6d424294571eab01d5ed1ff979a821af48f9", 23, 2),
    ("ThermalGammaMellinInverse22", "batch20/sources/ThermalGammaMellinInverse22.lean", "batch20/batch20_attempt01",
     "daad8b5d5fb1181bfc714e1b470edd7d9a6ae07e9a1b76c384481964a42caf91",
     "e9442776bb512a4f83391b63402a1dc86bce61070dfc386bc8b6873af521ce24",
     "28a07d17e88dbb09157c5958306efd557cd9d4727dd4948b336aaad4ee48d68c", 11, 20),
    ("ComplexGammaMellinLocal22", "batch26/sources/ComplexGammaMellinLocal22.lean", "batch26/batch26_attempt01",
     "e54cac5b2ab3996eb7bb86165448e0eff4c837b2fbda0af923e454962e526e08",
     "364ac79a2fb46546da4ffdb94993479ce90bbb861c5c5cd27e253cbc5f1968b5",
     "53201e46ee6a6418915358d37a61655a286bd2d814930d0fe68520fec4c92cdb", 22, 26),
    ("ComplexGammaMellinHolomorphy22", "batch27/sources/ComplexGammaMellinHolomorphy22.lean", "batch27/batch27_attempt01",
     "b8b69c16cdbe1afc6e0cbccf28b4a64903d91266bb4eae68652f8ebe5640b7f2",
     "f831358e15e1a088988b8bc102a3f7ca23df4a32c3210cfb072273ae4abcccbf",
     "63bc0f7463b2c5e42841b30846cda0a44f17bd40c3256e2952248c5e64a86f11", 15, 27),
    ("ComplexGammaMellinTail22", "batch30/sources/ComplexGammaMellinTail22.lean", "batch30/batch30_attempt01",
     "e5ba99611a069111292c9057a2a70b5cd936f24d244c9e23d966dfb12bb884a0",
     "168112f8064e3355b387c53dc50b82fac024309acdbd68bbbd0d1ed4060d2ad5",
     "aabb463dcbbb3736ecd0396454dc31f3dd69c08031a6a996ee3e1477b9a2cd50", 22, 30))
LOCAL_DEPENDENCIES = tuple(row[0] for row in DEP_SPECS)
SUPPORT = (
    (SOURCE_DIR / "pending_bridge_catalog22.json", "86164d7575b79c3ace42ebb1f56d2b88be0078873f76c0998175c1c0ae6604cb", "FULL", "6c920a"),
    (OWN / "source_catalog_author22.json", "86164d7575b79c3ace42ebb1f56d2b88be0078873f76c0998175c1c0ae6604cb", "EXACT_COPY_OF_FULL_HISTORICAL_AUTHOR_CATALOG", "6c920a"),
    (REVIEW_DIR / "review22.txt", "8d7eaef4972475be3c4edc884d03613e9c6480cae807218d101dae3369d5c0fb", "FULL_INDEPENDENT_ROLE3_SOURCE_REVIEW", "d31b7a"),
    (REVIEW_DIR / "read_receipts22.json", "597ed1b2f81124d3b01fef0901d3b975761c2553c38d52b2c2fa27d3140553e1", "FULL", "1da034"),
    (REVIEW_DIR / "source_handoff22.json", "4526d82976e7099ed06928dcb72bc477887a7a23b31a844436e6c8816d36686b", "FULL", "97dd00"),
    (BASE / ".arbor/sessions/parity/.coordinator/messages/round22_exp_tail_bridge_source32_selection.json", "9f9361f2eb2ab188ef307ebcd23a00d38e9931e2df7906f94c828150b72de0b5", "FULL", "707dc2"),
    (BASELINE_OBSERVATION[0], BASELINE_OBSERVATION[1], "FULL", "18aeb7"),
    (JUDGE / "batch31/adjudication.md", "1b13c5c07f416553cc8a1921998701ad267c9a16b04d09c4c7cce0ec31157eb8", "FULL", "290a00"),
    (JUDGE / "batch31/completion_receipt.json", "8a2237ddb9e4e20b5b046b60a9d92ed73e8ce26d6867b7c0495903195f4fb3ef", "FULL", "03d79f"),
    (JUDGE / "batch31/batch31_attempt01/receipt.json", "470f798110abde794b6742605c5dc66e4c7aabe7bc6a9e81e502e3c41aab9d1c", "FULL", "1a8b93"),
    (JUDGE / "batch31/batch31_attempt01/ComplexGammaMellinLambda22.log", "baf6fe9d6f7ba57c9259eaec5481de08f993228748891793a9234626737bc367", "FULL", "f8ec56"),
    (JUDGE / "batch26/completion_receipt.json", "6681b27ff6b8be03f471e59e753d7461aa52d6a205bfb872b27b52d77b85678a", "FULL", "dffaf8"),
    (JUDGE / "batch27/completion_receipt.json", "68e368bcd1f666bc1e282c2c66ea8d3d1e96d3f9a804426e37b9960a7ec3e8d0", "FULL", "4a8be4"),
    (BASE / ".arbor/sessions/parity/.coordinator/messages/round22_judge_batch27_closed_observation.json", "7ae697adeb55bd7aa124c19ed69e7ef1d0b2cb05b10fc386f4cd55a312478f2f", "FULL", "63fd59"),
    (JUDGE / "batch30/completion_receipt.json", "32a7ba50b7954486fb68fc09266254a602a3ecfe9fcea06f76423428a677954c", "FULL", "ad806e"),
    (BASE / ".arbor/sessions/parity/.coordinator/messages/round22_judge_batch30_closed_observation.json", "7fd118336cfc1b1106c166282f88030c79e49014efa55bc6a4ce0e463357e292", "FULL", "63fd59"),
    (BASE / ".arbor/sessions/parity/.coordinator/messages/round22_judge_batch26_closed_observation.json", "9b7697d2d35d12903e436403e77fb44e8ea76c6f586940e28d168ab851340e9b", "FULL", "402373"))
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
        return JUDGE / dep[1], OWN / "readonly_oleans" / (module + ".olean")
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
            "scope": "COMPLEX_GAMMA_EXP_TAIL_BRIDGE_AUX_ONLY",
            "author_olean_allowed": False})
        reads.extend([(original, "FULL", original_read), (own_source, "FULL_EXACT_COPY", args.source_read)])
        queue.extend(imports(own_source))

    depdir = OWN / "readonly_oleans"
    depdir.mkdir(exist_ok=False)
    deps = []
    for module, source_relative, actual_relative, source_sha, olean_sha, receipt_sha, nprints, batch in DEP_SPECS:
        source = JUDGE / source_relative
        actual = JUDGE / actual_relative
        olean, receipt_path = actual / (module + ".olean"), actual / "receipt.json"
        for path, digest in ((source, source_sha), (olean, olean_sha), (receipt_path, receipt_sha)):
            bind(path, digest)
        receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
        row = next(row for row in receipt["rows"] if row["module"] == module)
        expected_global = "INDEPENDENT_BATCH26_FAILED" if batch == 26 else f"INDEPENDENT_BATCH{batch:02d}_AUX_PASS"
        expected_prints = re.findall(r"^#print axioms ([A-Za-z_][A-Za-z_0-9.]*)$", lean_code(source), re.M)
        if (receipt["status"] != expected_global or not receipt["all_inputs_unchanged"] or not receipt.get("all_current_bytes_preserved", receipt["all_inputs_unchanged"])
                or row["status"] != "INDEPENDENT_LEAN_AUX_PASS" or row["exit_code"] != 0
                or not row["exact_axiom_coverage_standard_only"] or len(row["axiom_rows"]) != nprints
                or [item["declaration"] for item in row["axiom_rows"]] != expected_prints
                or any(set(item["axioms"]) - {"propext", "Classical.choice", "Quot.sound"} for item in row["axiom_rows"])
                or row["source_sha256"] != source_sha or row["olean_sha256"] != olean_sha):
            raise RuntimeError("Real independent readonly provenance mismatch: " + module)
        bind(actual / (module + ".log"), row["log_sha256"])
        bind(actual / (module + "_FIN.json"))
        if json.loads((actual / (module + "_FIN.json")).read_text(encoding="utf-8")) != row:
            raise RuntimeError("Independent module FIN does not match its receipt row")
        if batch == 26:
            closed_path = JUDGE / "batch26/completion_receipt.json"
            obs_path = SUPPORT[-1][0]
            bind(closed_path, "6681b27ff6b8be03f471e59e753d7461aa52d6a205bfb872b27b52d77b85678a")
            bind(obs_path, SUPPORT[-1][1])
            closed = json.loads(closed_path.read_text(encoding="utf-8"))
            obs = json.loads(obs_path.read_text(encoding="utf-8"))
            ev = next(item for item in closed["module_evidence"] if item["module"] == module)
            if (closed["status"] != expected_global or closed["actual_receipt_sha256"] != receipt_sha
                    or not closed["all_current_bytes_preserved"] or closed["modules_passed"] != 1 or closed["declarations_passed"] != 22
                    or ev["status"] != row["status"] or ev["exit_code"] != 0 or ev["declarations_passed"] != 22
                    or ev["olean_sha256"] != olean_sha or ev["log_sha256"] != row["log_sha256"]
                    or obs["status"] != expected_global or obs["receipt_sha256"] != receipt_sha
                    or obs["completion_sha256"] != sha(closed_path) or obs["new_modules"] != 1 or obs["new_declarations"] != 22
                    or obs["official_modules"] != 84 or obs["official_declarations"] != 1419):
                raise RuntimeError("Local26 real row PASS and ROOT partial closure not verified")
        if batch in (27, 30):
            pins = {
                27: ("68e368bcd1f666bc1e282c2c66ea8d3d1e96d3f9a804426e37b9960a7ec3e8d0", "7ae697adeb55bd7aa124c19ed69e7ef1d0b2cb05b10fc386f4cd55a312478f2f", 85, 1434),
                30: ("32a7ba50b7954486fb68fc09266254a602a3ecfe9fcea06f76423428a677954c", "7fd118336cfc1b1106c166282f88030c79e49014efa55bc6a4ce0e463357e292", 86, 1456)}
            closed_sha, obs_sha, official_modules, official_declarations = pins[batch]
            closed_path = JUDGE / f"batch{batch}/completion_receipt.json"
            obs_path = BASE / f".arbor/sessions/parity/.coordinator/messages/round22_judge_batch{batch}_closed_observation.json"
            bind(closed_path, closed_sha); bind(obs_path, obs_sha)
            closed, obs = (json.loads(path.read_text(encoding="utf-8")) for path in (closed_path, obs_path))
            ev = next(item for item in closed["module_evidence"] if item["module"] == module)
            if (closed["status"] != expected_global or closed["actual_receipt_sha256"] != receipt_sha
                    or not closed["all_current_bytes_preserved"] or closed["modules_passed"] != 1
                    or closed["declarations_passed"] != nprints or ev["status"] != row["status"]
                    or ev["exit_code"] != 0 or ev["declarations_passed"] != nprints
                    or ev["olean_sha256"] != olean_sha or ev["log_sha256"] != row["log_sha256"]
                    or obs["status"] != expected_global or obs["receipt_sha256"] != receipt_sha
                    or obs["completion_sha256"] != closed_sha or obs["new_modules"] != 1
                    or obs["new_declarations"] != nprints or obs["official_modules"] != official_modules
                    or obs["official_declarations"] != official_declarations):
                raise RuntimeError("Actual independent PASS and ROOT closure not verified")
        dep_copy = depdir / (module + ".olean")
        with dep_copy.open("xb") as stream:
            stream.write(olean.read_bytes())
        bind(dep_copy, olean_sha)
        deps.append({"module": module, "source": str(source), "source_sha256": source_sha,
            "olean_original": str(olean), "olean_copy": str(dep_copy), "olean_sha256": olean_sha,
            "independent_receipt": str(receipt_path), "independent_receipt_sha256": receipt_sha,
            "status": "INDEPENDENT_LEAN_AUX_PASS", "independent_receipt_global_status": expected_global,
            "module_row_and_exact_axioms_verified": True, "ROOT_partial_observation_required_and_verified": batch == 26,
            "ROOT_closed_observation_required_and_verified": batch in (27, 30),
            "recompile_authorized": False})
        reads.extend([(source, "HASH_ONLY_READONLY_SOURCE", "CURRENT_METADATA_HASH"),
            (receipt_path, "HASH_PLUS_CONTROL_JSON_PROVENANCE_CHECK_NOT_RAW_FULL", "CURRENT_METADATA_PROVENANCE"),
            (actual / (module + "_FIN.json"), "HASH_ONLY_FROZEN_INDEPENDENT_FIN", "CURRENT_METADATA_HASH"),
            (actual / (module + ".log"), "HASH_ONLY_FROZEN_INDEPENDENT_LOG", "CURRENT_METADATA_HASH")])

    for path, digest, scope, chunk in SUPPORT:
        bind(path, digest); reads.append((path, scope, chunk))
    observation = json.loads(BASELINE_OBSERVATION[0].read_text(encoding="utf-8"))
    if (observation["official_modules"] != 86 or observation["official_declarations"] != 1456
            or observation["status"] != "INDEPENDENT_BATCH31_FAILED"
            or observation["new_modules"] != 0 or observation["new_declarations"] != 0
            or observation["receipt_sha256"] != "470f798110abde794b6742605c5dc66e4c7aabe7bc6a9e81e502e3c41aab9d1c"
            or observation["completion_sha256"] != "8a2237ddb9e4e20b5b046b60a9d92ed73e8ce26d6867b7c0495903195f4fb3ef"):
        raise RuntimeError("Actual ROOT baseline after failed closed31 mismatch")
    review = json.loads((REVIEW_DIR / "read_receipts22.json").read_text(encoding="utf-8-sig"))
    handoff = json.loads((REVIEW_DIR / "source_handoff22.json").read_text(encoding="utf-8-sig"))
    if (handoff["source"]["sha256"] != SPECS[0][1]
            or handoff["catalog"]["sha256"] != SUPPORT[0][1]
            or handoff["review_report"]["sha256"] != SUPPORT[2][1]
            or handoff["read_receipts"]["sha256"] != SUPPORT[3][1]
            or handoff["status"] != "SOURCE_BRIDGE_COHERENT_WITH_ACTUAL_PAID_DEPENDENCIES_NOT_COMPILED"
            or handoff["precise_mathematical_objections"]
            or handoff["direct_imports"] != ["ComplexGammaMellinHolomorphy22", "ComplexGammaMellinTail22"]
            or handoff["compiler_calls"] != 0 or handoff["numeric_calls"] != 0
            or handoff["mainLambda_paid_assumed"] or handoff["new_theorems_paid"]
            or review["written_bridge_theorems"] != 2 or review["written_bridge_axiom_prints"] != 2
            or review["observed_bridge_axiom_prints"] != 0 or len(review["reads"]) != 6
            or len(review["paid_readonly_oleans_metadata"]) != 2):
        raise RuntimeError("Independent ROLE3 bridge review or paid import provenance mismatch")
    for item in review["reads"] + review["paid_readonly_oleans_metadata"]:
        path = Path(item["path"]).resolve()
        bind(path, item["sha256"])
        if path.stat().st_size != item["bytes"]:
            raise RuntimeError("Independent review binding byte count mismatch")
        reads.append((path, "HASH_PLUS_ROLE3_RECORDED_" + item.get("scope", "BYTE_HASH_OLEAN"),
                      item.get("evidence_tool_chunk", "CURRENT_METADATA_BYTE_HASH")))
    selected = json.loads(SUPPORT[5][0].read_text(encoding="utf-8"))
    if (selected["source_sha256"] != SPECS[0][1] or selected["author_catalog_sha256"] != SUPPORT[0][1]
            or selected["module_count"] != 1 or selected["declaration_count"] != 2
            or selected["theorem_count"] != 2 or selected["definition_count"] != 0
            or selected["paid_readonly_local_dependencies"] != list(LOCAL_DEPENDENCIES)
            or selected["mainLambda_dependency"] or selected["numeric_authorized"]):
        raise RuntimeError("ROOT SOURCE32 selected scope mismatch")
    historical = json.loads((SOURCE_DIR / "pending_bridge_catalog22.json").read_text(encoding="utf-8"))
    if (historical["module"] != MODULES[0] or historical["declarations"] != 2
            or historical["theorem_count"] != 2 or historical["definition_count"] != 0
            or historical["direct_imports"] != ["ComplexGammaMellinHolomorphy22", "ComplexGammaMellinTail22"]):
        raise RuntimeError("Exact historical frozen bridge catalogue mismatch")
    # Historical pending comments/catalogue remain byte-identical.
    # Real independent Holo27/Tail30, not failed31 main Lambda, supply the imports.
    old_paths = {path for path in JUDGE.rglob("*") if path.is_file() and not path.resolve().is_relative_to(OWN.resolve())}
    old_paths.update(path for path in OLD21.rglob("*") if path.is_file())
    old_rows = [{"path": str(path), "sha256": sha(path), "bytes": path.stat().st_size}
                for path in sorted(old_paths)]
    for item in old_rows:
        bind(item["path"], item["sha256"])
    write_new(OWN / "closed_judge_bindings.json", {"schema": "ROUND22_JUDGE5_CLOSED_BINDINGS_BATCH32",
        "inputs": old_rows, "scope": "BYTE_HASH_ALL_PRIOR_JUDGE_FILES_AND_EXPLICIT_ROLE4_CLOSED_BATCH21",
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
    write_new(OWN / "import_bindings.json", {"schema": "ROUND22_JUDGE5_IMPORT_BINDINGS_BATCH32",
        "module_count": len(closure), "implicit_Init_for_each_nonprelude_module": True,
        "explicit_prelude_seed": "Init", "unresolved": unresolved,
        "entries": sorted(closure, key=lambda item: item["module"]), "readonly_local_entries": deps,
        "metadata_only": True, "compiler_invocations": 0})

    reads.extend([(OWN / "prepare_metadata.py", "FULL_BEFORE_METADATA_EXECUTION", args.builder_read),
        (OWN / "run_once.py", "FULL_SOURCE_ONLY_NEVER_EXECUTED", args.launcher_read),
        (OWN / "preparation.md", "FULL", args.audit_read)])
    for filename in ("source_tools_handoff32.json", "source_tool_reads32.json"):
        reads.append((OWN / filename, "HASH_PLUS_SOURCE_TOOL_HANDOFF_JSON_NOT_IMPORT_CLOSURE", "SOURCE_FREEZE32"))
    for path, _, _ in reads:
        bind(path)
    write_new(OWN / "read_receipts.json", {"schema": "ROUND22_JUDGE5_READ_RECEIPTS_BATCH32", "time_utc": stamp,
        "entries": [{"path": str(path), "sha256": sha(path), "scope": scope, "chunk": chunk} for path, scope, chunk in reads],
        "truncated_reads_excluded": ["Long SOURCE32 writer CreateProcessAsUserW5 before SpawnChild: no process, files or PREP. Main Lambda proofs/APIs excluded. Template builder31 FULL9cd4d4 and launcher31 FULLa567e5; no own FULL cache claim."],
        "all_import_mathematical_FULL_claim": False, "candidate_sources_not_elaborated": True,
        "compiler_invocations": 0, "candidate_numeric_invocations": 0, "numeric_invocations": 0})
    write_new(OWN / "catalog.json", {"schema": "ROUND22_JUDGE5_CATALOG_BATCH32", "time_utc": stamp,
        "modules": rows, "module_count": 1, "total_declarations": 2, "theorem_count": 2, "definition_count": 0,
        "common_source_root": str(OWN / "sources"), "readonly_local_dependencies": list(LOCAL_DEPENDENCIES),
        "dependency_bindings": deps, "support_capture_paths": [str(item[0]) for item in SUPPORT],
        "author_provenance_capture_paths": [str(path) for path in sorted(OLD21.rglob("*")) if path.is_file()], "modules_author_PASS_claimed": False,
        "child_wall_seconds": 300, "max_heartbeats": 1000000, "compiler_invocations": 0, "numeric_invocations": 0, "win": False})
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
    manifest = {"schema": "ROUND22_JUDGE5_PREPARED_MANIFEST_BATCH32", "time_utc": stamp,
        "status": "PREPARED_SOURCE_ONLY_GATE_CLOSED" if not unresolved else "PREPARATION_IMPORT_OPEN", "role": "ROLE5",
        "modules": list(MODULES), "compiler_invocations": 0, "candidate_numeric_invocations": 0, "numeric_invocations": 0,
        "immutable_inputs": sorted(bindings.values(), key=lambda item: item["path"].casefold()),
        "import_module_count": len(closure), "implicit_Init_closure_included": True, "unresolved_modules": unresolved,
        "common_source_root": str(OWN / "sources"), "source_catalog_sha256": sha(OWN / "catalog.json"),
        "launcher_sha256": sha(OWN / "run_once.py"), "readonly_local_dependencies": list(LOCAL_DEPENDENCIES),
        "closed_judge_files": len(old_rows), "protected_archive_count": 3089,
        "author_olean_used": False, "numeric_banks": [], "previous_official_modules": 86,
        "previous_official_declarations": 1456, "hypothetical_after_all_PASS_modules": 87,
        "hypothetical_after_all_PASS_declarations": 1458, "official_count_requires_ROOT_observation": True,
        "H1_paid": False, "native_refinement_paid": False, "coefficient_N_computed": False, "D_N_paid": False, "win": False}
    write_new(OWN / "prepared_manifest.json", manifest)
    receipt = {"schema": "ROUND22_JUDGE5_PREPARATION_RECEIPT_BATCH32", "time_utc": datetime.now(timezone.utc).isoformat(),
        "status": manifest["status"], "compiler_invocations": 0, "candidate_numeric_invocations": 0, "numeric_invocations": 0,
        "manifest_sha256": sha(OWN / "prepared_manifest.json"), "launcher_sha256": manifest["launcher_sha256"],
        "catalog_sha256": manifest["source_catalog_sha256"], "read_receipts_sha256": sha(OWN / "read_receipts.json"),
        "import_bindings_sha256": sha(OWN / "import_bindings.json"), "closed_judge_bindings_sha256": sha(OWN / "closed_judge_bindings.json"),
        "builder_sha256": sha(OWN / "prepare_metadata.py"), "preparation_doc_sha256": sha(OWN / "preparation.md"),
        "imports": len(closure), "inputs": len(bindings), "closed_judge_files": len(old_rows), "archives": 3089,
        "modules": 1, "declarations": 2, "theorems": 2, "definitions": 0, "unresolved": unresolved,
        "candidate_source_not_elaborated": True, "readonly_independent_dependency_count": 5,
        "common_source_root": str(OWN / "sources"), "no_author_olean_on_lean_path": True,
        "old_batches_recompiled": False, "numeric_bank_replayed": False, "no_win": True}
    write_new(OWN / "prepared_receipt.json", receipt)
    print(json.dumps(receipt, sort_keys=True))


if __name__ == "__main__":
    main()
