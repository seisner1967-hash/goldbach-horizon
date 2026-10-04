"""SOURCE ONLY batch36 metadata builder, never a Lean or numerical executor.
Real ROOT35 whole-module PASS is pinned; future invocation still needs PREP authority.
The lexical metadata layer is adapted from frozen FULL-read STOPPED batch34 text only.
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
OLD21 = BASE / "round22/role4/concrete_ntt_roots_prepare21"
BASELINE_OBSERVATION_PATH = BASE / ".arbor/sessions/parity/.coordinator/messages/round22_judge_batch35_closed_observation.json"
# Real independently compiled main35 and its physical ROOT closure are pinned.
BASELINE_EXPECTED_SHA = "dc598597605146946c2deb26bba7db1542e2b4d328821c102d89bf0d8ffcb1c7"
NAMESPACE = "GoldbachComplexGammaMellin22"
MODULES = ("ComplexGammaMellinLambdaTail22", "ComplexGammaCircleGeometry22")
SOURCE_DIRS = {
    MODULES[0]: BASE / "round22/role4/complex_gamma_mellin_lambda_tail_source01",
    MODULES[1]: BASE / "round22/role4/complex_gamma_circle_geometry_source01"}
SPECS = (
    (MODULES[0], "68a008f55e1dcff723dfcbf398061a69e3c3495fee739965f3cfdc884232b01e", 12, 4),
    (MODULES[1], "2322915060c608e58c499af0c9303d3032f488e12980bc240aa7eca0807c44c5", 22, 3))
MANUAL_NAMES = {
    MODULES[0]: (
        "signedLambdaMellinTail", "lambdaMellinTail", "lambdaMellinTailRadius", "lambdaMellinTruncated",
        "lambdaMellinProduct_bound", "signedLambdaMellinTail_integrable", "signedLambdaMellinTail_norm_le",
        "lambdaMellinTail_norm_le", "signedLambdaMellinTail_true_eq_Iio",
        "lambdaMellinThermal_sub_truncated_eq_tail", "lambdaMellinThermal_truncation_error_le",
        "lambdaMellinTailRadius_eq_closed", "lambdaMellinTailRadius_continuousAt",
        "lambdaMellinTailRadius_pos", "lambdaMellinTailRadius_antitone", "exists_local_uniform_Lambda_tail"),
    MODULES[1]: (
        "circleMellinPoint", "circleMellinRadius", "circleDecayFloor", "circleMellinPoint_re",
        "circleMellinPoint_im", "circleMellinPoint_ne_zero", "circleMellinPoint_mem_slitPlane",
        "circleMellinPoint_norm_eq_radius", "circleMellinPoint_norm_sq", "circleMellinPoint_norm_pos",
        "circleMellinPoint_abs_theta_le_norm", "circleMellinRadius_pos", "circleMellinPoint_arg",
        "circleMellinPoint_abs_arg", "circleMellinPoint_sin_abs_arg", "circleMellinPoint_rotation_cos_sq",
        "kernelCoefficient_circle_eq_norm", "kernelCoefficient_circle_eq_radius", "kernelCoefficient_circle_le_four",
        "circleDecayFloor_pos", "decayGap_circle_eq", "decayGap_circle_ge_floor",
        "circleMellinRadius_continuous", "circleDecayFloor_continuous", "circleCoefficientClosed_continuousAt")}
AUTHOR_SUPPORT = {
    MODULES[0]: (
        ("source_contract22.md", "17e038d03f977e026853905eb3b7cb88f2d7fd574b71cbc73e9de774392c90bc"),
        ("source_catalog22.json", "f094c54a6a10aa0ad026dce78233f98e53d972341e2f2ce08d86306492e330ea"),
        ("source_read_receipts22.json", "d535fcfec37e6cd003a732fb3f0c33c0a7e2bcb1e4c3c19b0f80bb81fd936a37"),
        ("source_handoff22.json", "31bbd5ddef991c58a9c58bdb0f1aca2d90f3a71a0dcffdbb751871c7434c4298")),
    MODULES[1]: (
        ("source_contract22.md", "002993384eb6d114ea33b429a9c410729588efc700e881b970ed215e15f80e1a"),
        ("source_catalog22.json", "6f85beb2fd6eaf111a2ef453614938081385456a7d567bfb3e0f39b61e371312"),
        ("source_read_receipts22.json", "4a0c0e52c40fbe6243389da59d25e6feab8e939fbb9eff485750851b43ff4822"),
        ("source_handoff22.json", "a9e2f04e5a2244b1f017aeb2b998ea569f964464bc7a99db4297cfa4f0d8bfd6"))}
AUTHOR_COPIES = {
    MODULES[0]: "source_catalog_elambda_author22.json",
    MODULES[1]: "source_catalog_geometry_author22.json"}
REVIEW_SPECS = (
    ("round22/role3/elambda16_source_review01", "source_handoff22_revision02.json",
     "f2b93e0fa76f3b82a4a389355a70736847d5064fc9c59c1940b6ed2a343b62a6",
     "review22.txt", "0497ba1f300dd5916fbac27835a04c1968822ef707182dc6e94c10d1bce8d252",
     "read_receipts22_revision02.json", "b0ef828f7df8e5eef01c93515f016b47ea80bb433f21f137d3ebc8728f0b395f",
     "SOURCE_ANALYTIC_CHAIN_COHERENT_PENDING_DEPENDENCIES_AND_ELABORATION"),
    ("round22/role3/circle_gamma_geometry_source_review01", "source_handoff22.json",
     "16fe9a2936376c19e36a5561c1e129e00f680515441178cea2399aeb03617708",
     "review22.txt", "992e109a51a906a6b2e3d9010addcd967f6ac918bb94c91a69207d378cd2c85b",
     "read_receipts22.json", "863accf7c91d9c8381b593acab3a75661e37f741ca83052a3dd6bb4d1a793f12",
     "SOURCE_GEOMETRY_CHAIN_COHERENT_NOT_ELABORATED"))
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
     "aabb463dcbbb3736ecd0396454dc31f3dd69c08031a6a996ee3e1477b9a2cd50", 22, 30),
    ("ComplexGammaMellinLambda22", "batch35/sources/ComplexGammaMellinLambda22.lean", "batch35/batch35_attempt01",
     "4a94415678e4c3295b989dccbcda9e049483e131c17efce68099d05686e1c72d",
     "8b557d2ccc8f8f6efbf5a33147aca94e12a3d7b2fcdd095af9024ffb492777c5",
     "3cffa331b39283808678dbfa5dc36081f4e5a2698c8a9f278d6b8b6a63ec6832", 30, 35))
LOCAL_DEPENDENCIES = tuple(row[0] for row in DEP_SPECS)
SCIENCE_REVIEW_DIR = JUDGE / "lambda_tail_geometry_source_review36"
SCIENCE_REVIEW_STATUS = "SOURCE_SCIENTIFIC_CHAIN_COHERENT_NOT_ELABORATED"
SUPPORT = (
    (BASE / ".arbor/sessions/parity/.coordinator/messages/round22_lambda_tail_geometry_source36_selection.json",
     "dbbea57ff1b555ebd9093b577b95d40b0dbb40d9ea5ce5ae4d62413a104b7576", "FULL_SELECTION_ONLY", "2634ba"),
    (JUDGE / "batch34/prepare_metadata.py", "f3d8a404abdc11bd852e711e966c1df80b289bbbcef0f0854f6e909d69fcd94e", "FULL_STOPPED_TEXT_TEMPLATE_NOT_INVOKED", "11cdae+868f50"),
    (JUDGE / "batch34/run_once.py", "dd64c49467b7969c052d7e70fa59f78139372f7a81147c72a0ef67bbb7484bb3", "FULL_STOPPED_TEXT_TEMPLATE_NOT_INVOKED", "87baa0"),
    (JUDGE / "batch35/preparation.md", "758ffc8410307f7b2b7ae6836e7cee9685833520dae4e09965a7aa6221612f2c", "FULL_HISTORICAL_DOCUMENT_NOT_CURRENT_STATUS", "87baa0"),
    (SCIENCE_REVIEW_DIR / "review22.md", "f3e4972113fe07af80d63aa175e8e344b530e920b7a7c273f42dcf7e4451c5a3", "FULL_ROLE5_INDEPENDENT_SCIENTIFIC_SOURCE_REVIEW_NOT_ELABORATED", "c95c9b"),
    (SCIENCE_REVIEW_DIR / "read_receipts22.json", "b0ee226a6074a4dbbdffa399e5177cb28598e7e2dd0f633f7ecf5d7949d5e0b7", "FULL_ROLE5_SCIENTIFIC_READ_SCOPE_METADATA", "c95c9b"),
    (SCIENCE_REVIEW_DIR / "source_handoff22.json", "3a496634927a1b50be3aac10a17fa46ac990312fd64201d736324b8658e3c7ae", "FULL_ROLE5_SCIENTIFIC_REVIEW_HANDOFF_METADATA", "c95c9b"))

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
    parser.add_argument("--baseline-observation", required=True)
    parser.add_argument("--baseline-observation-sha256", required=True)
    parser.add_argument("--official-modules", required=True, type=int)
    parser.add_argument("--official-declarations", required=True, type=int)
    args = parser.parse_args()
    if any((OWN / name).exists() for name in ("prepared_manifest.json", "prepared_receipt.json", "readonly_oleans", "catalog.json")):
        raise RuntimeError("Exclusive metadata preparation only; no implicit retry")
    if Path(sys.executable).resolve() != PYTHON.resolve() or sha(PYTHON) != PYTHON_SHA or sha(LEAN_ROOT / "bin/lean.exe") != LEAN_SHA:
        raise RuntimeError("Pinned metadata runtime mismatch")
    stamp = datetime.now(timezone.utc).isoformat()
    bindings, rows, reads, queue = {}, [], [], ["Init"]

    def bind(path, expected=None):
        path = Path(path).resolve()
        digest = sha(path)
        if expected is not None and digest != expected:
            raise RuntimeError("Frozen binding changed: " + str(path))
        entry = {"path": str(path), "sha256": digest, "bytes": path.stat().st_size}
        key = str(path).casefold()
        if key in bindings and bindings[key] != entry:
            raise RuntimeError("Binding conflict: " + str(path))
        bindings[key] = entry
        return digest

    # No material PREP output is created before verifying the genuine PASS35
    # and physical ROOT closure. Both exist; separate PREP authority is required.
    baseline_path = Path(args.baseline_observation).resolve()
    if (baseline_path != BASELINE_OBSERVATION_PATH.resolve()
            or args.baseline_observation_sha256 != BASELINE_EXPECTED_SHA
            or (args.official_modules, args.official_declarations) != (88, 1488)):
        raise RuntimeError("Canonical ROOT35 observation required")
    bind(baseline_path, args.baseline_observation_sha256)
    observation = json.loads(baseline_path.read_text(encoding="utf-8"))
    baseline_receipt_path = JUDGE / "batch35/batch35_attempt01/receipt.json"
    baseline_completion_path = JUDGE / "batch35/completion_receipt.json"
    bind(baseline_receipt_path, observation["receipt_sha256"])
    bind(baseline_completion_path, observation["completion_sha256"])
    baseline_receipt = json.loads(baseline_receipt_path.read_text(encoding="utf-8"))
    baseline_completion = json.loads(baseline_completion_path.read_text(encoding="utf-8"))
    if (observation["schema"] != "ROUND22_ROOT_JUDGE_STAGE_CLOSED_OBSERVATION"
            or observation["batch"] != "batch35" or observation["status"] != "INDEPENDENT_BATCH35_AUX_PASS"
            or observation["new_modules"] != 1 or observation["new_declarations"] != 30
            or observation["modules_failed"] != 0 or observation["modules_not_invoked"] != 0
            or observation["official_modules"] != args.official_modules
            or observation["official_declarations"] != args.official_declarations
            or args.official_modules != 87 + observation["new_modules"]
            or args.official_declarations != 1458 + observation["new_declarations"]
            or baseline_receipt["status"] != observation["status"]
            or not baseline_receipt["all_current_bytes_preserved"]
            or not baseline_receipt["all_inputs_unchanged"]
            or baseline_receipt["modules_passed"] != 1 or baseline_receipt["declarations_passed"] != 30
            or baseline_receipt["actual_child_invocations"] != 1 or baseline_receipt["hidden_retries"]
            or len(baseline_receipt["rows"]) != 1
            or baseline_completion["status"] != observation["status"]
            or not baseline_completion["all_current_bytes_preserved"]
            or baseline_completion["actual_receipt_sha256"] != observation["receipt_sha256"]
            or baseline_completion["modules_passed"] != 1 or baseline_completion["declarations_passed"] != 30):
        raise RuntimeError("Whole-module PASS35 and physical closure are mandatory")
    baseline_main_row = baseline_receipt["rows"][0]
    if (baseline_main_row["module"] != "ComplexGammaMellinLambda22"
            or baseline_main_row["source_sha256"] != DEP_SPECS[-1][3]
            or baseline_main_row["status"] != "INDEPENDENT_LEAN_AUX_PASS"
            or baseline_main_row["exit_code"] != 0
            or not baseline_main_row["exact_axiom_coverage_standard_only"]
            or len(baseline_main_row["axiom_rows"]) != 30
            or baseline_main_row["olean_sha256"] != DEP_SPECS[-1][4]
            or not isinstance(baseline_main_row["olean_sha256"], str)
            or not re.fullmatch(r"[0-9a-f]{64}", baseline_main_row["olean_sha256"])):
        raise RuntimeError("Only repaired SOURCE03 4a944 main35 actual PASS is admissible")
    baseline_capture_paths = [baseline_path, baseline_receipt_path, baseline_completion_path]
    support_paths = []
    author_capture_paths = []
    reads.extend((path, "PARSED_CONTROL_JSON_AND_SHA_AFTER_REAL_ROOT35_CLOSURE_NOT_RAW_FULL", "FUTURE_METADATA_PREP36")
                 for path in baseline_capture_paths)

    for module, digest, nthm, ndef in SPECS:
        directory = SOURCE_DIRS[module]
        original = directory / (module + ".lean")
        own_source = OWN / "sources" / (module + ".lean")
        bind(original, digest); bind(own_source, digest)
        code = lean_code(own_source)
        decls = re.findall(r"^(theorem|def)\s+(\w+)", code, re.M)
        printed = re.findall(r"^#print axioms " + re.escape(NAMESPACE) + r"\.(\w+)$", code, re.M)
        if ([name for _, name in decls] != list(MANUAL_NAMES[module]) or printed != list(MANUAL_NAMES[module])
                or len(set(printed)) != len(printed)
                or sum(kind == "theorem" for kind, _ in decls) != nthm
                or sum(kind == "def" for kind, _ in decls) != ndef
                or re.search(r"\b(?:sorry|admit|axiom|native_decide|unsafe)\b", code)):
            raise RuntimeError("Manual catalogue or forbidden source command mismatch: " + module)
        rows.append({"module": module, "source": str(own_source), "source_sha256": digest,
            "original_source": str(original), "source_status": "SOURCE_ONLY_NOT_ELABORATED",
            "theorem_count": nthm, "definition_count": ndef,
            "declarations": [{"kind": kind, "qualified_name": NAMESPACE + "." + name} for kind, name in decls],
            "qualified_prints": [NAMESPACE + "." + name for name in printed],
            "compiler_options": ["-DmaxHeartbeats=1000000"],
            "scope": "WEIGHTED_LAMBDA_TAIL_THEN_LINKED_CIRCLE_GEOMETRY_AUX_ONLY",
            "author_olean_allowed": False})
        science_chunk = "7ed586" if module == MODULES[0] else "2bb8d9"
        author_chunk = "2aecf0" if module == MODULES[0] else "c60118"
        reads.extend([(original, "FULL", science_chunk), (own_source, "FULL_EXACT_COPY", args.source_read)])
        queue.extend(imports(own_source))
        for name, expected_sha in AUTHOR_SUPPORT[module]:
            path = directory / name
            bind(path, expected_sha); support_paths.append(path)
            chunk = science_chunk if name in ("source_catalog22.json", "source_contract22.md") else author_chunk
            reads.append((path, "FULL_FROZEN_AUTHOR_DOCUMENT_HISTORICAL_STATUS_PRESERVED", chunk))
        catalog_path = OWN / AUTHOR_COPIES[module]
        bind(catalog_path, dict(AUTHOR_SUPPORT[module])["source_catalog22.json"])
        support_paths.append(catalog_path)
        author_catalog = json.loads(catalog_path.read_text(encoding="utf-8"))
        author_handoff = json.loads((directory / "source_handoff22.json").read_text(encoding="utf-8"))
        expected_count = 32 if module == MODULES[0] else 22
        if author_handoff["bindings_count"] != expected_count or len(author_handoff["bindings"]) != expected_count:
            raise RuntimeError("Frozen author binding count mismatch")
        author_keys = set()
        for item in author_handoff["bindings"]:
            path = Path(item["path"]).resolve()
            key = str(path).casefold()
            if key in author_keys:
                raise RuntimeError("Duplicate author byte binding")
            author_keys.add(key)
            bind(path, item["sha256"])
            if path.stat().st_size != item["bytes"]:
                raise RuntimeError("Frozen author byte size mismatch")
            author_capture_paths.append(path)
            reads.append((path, "HASH_ONLY_HISTORICAL_AUTHOR_BINDING_" + item["scope"], "CURRENT_METADATA_SHA"))
        if module == MODULES[0]:
            names = author_catalog["definition_names"] + author_catalog["theorem_names"]
            counts = (author_catalog["declarations"], author_catalog["theorems"], author_catalog["definitions"],
                      author_catalog["qualified_print_axioms"])
            local_imports = author_catalog["local_imports"]
            expected_imports = ["ComplexGammaMellinLambda22", "ComplexGammaMellinTail22"]
        else:
            names = [item["name"].removeprefix(NAMESPACE + ".") for item in author_catalog["declarations"]]
            count_object = author_catalog["counts"]
            counts = tuple(count_object[key] for key in ("declarations", "theorems", "definitions", "qualified_print_axioms"))
            local_imports = [author_catalog["only_local_import"]]
            expected_imports = ["ComplexGammaMellinLocal22"]
        if (author_catalog["source_sha256"] != digest or names != list(MANUAL_NAMES[module])
                or counts != (nthm + ndef, nthm, ndef, nthm + ndef) or local_imports != expected_imports):
            raise RuntimeError("Exact frozen manual author catalogue mismatch")

    for index, spec in enumerate(REVIEW_SPECS):
        relative, handname, handsha, reportname, reportsha, readname, readsha, status = spec
        directory = BASE / relative
        for name, digest in ((handname, handsha), (reportname, reportsha), (readname, readsha)):
            path = directory / name
            bind(path, digest); support_paths.append(path)
            chunk = "4154da" if index == 0 else "cd8b61"
            reads.append((path, "ROLE3_HISTORICAL_FULL_INDEPENDENT_SOURCE_REVIEW_NOT_A_COMPILER_VERDICT", chunk))
        handoff = json.loads((directory / handname).read_text(encoding="utf-8"))
        source_sha = handoff["source"]["sha256"] if index == 0 else handoff["source_sha256"]
        objection_key = "precise_mathematical_objections" if index == 0 else "precise_objections"
        if handoff["status"] != status or source_sha != SPECS[index][1] or handoff[objection_key] != []:
            raise RuntimeError("Selected independent SOURCE review mismatch")

    for path, digest, scope, chunk in SUPPORT:
        bind(path, digest); support_paths.append(path); reads.append((path, scope, chunk))
    scientific_review = json.loads((SCIENCE_REVIEW_DIR / "source_handoff22.json").read_text(encoding="utf-8"))
    science_reads = json.loads((SCIENCE_REVIEW_DIR / "read_receipts22.json").read_text(encoding="utf-8"))
    if (scientific_review["status"] != SCIENCE_REVIEW_STATUS
            or scientific_review["reviewer"] != "ROLE5" or scientific_review["source_author"] != "ROLE4"
            or scientific_review["precise_scientific_objections"] != []
            or scientific_review["baseline"]["modules"] != 88
            or scientific_review["baseline"]["declarations"] != 1488
            or scientific_review["baseline"]["root35_observation_sha256"] != BASELINE_EXPECTED_SHA
            or [(item["module"], item["sha256"], item["declarations"], item["theorems"], item["definitions"])
                for item in scientific_review["selected_sources"]]
                != [(module, digest, nthm + ndef, nthm, ndef) for module, digest, nthm, ndef in SPECS]
            or scientific_review["catalogue"]["observed_candidate_prints"] != 0
            or scientific_review["formal_elaboration"] != "OPEN"
            or any(scientific_review[key] != 0 for key in
                ("PREP_invocations", "Lean_invocations", "numeric_invocations", "new_auxiliary_credit"))
            or science_reads["status"] != SCIENCE_REVIEW_STATUS
            or science_reads["scientific_objections"] != []
            or not science_reads["all_declared_historical_bindings_match"]):
        raise RuntimeError("Independent ROLE5 scientific SOURCE review mismatch")

    depdir = OWN / "readonly_oleans"
    depdir.mkdir(exist_ok=False)
    deps = []
    for module, source_relative, actual_relative, source_sha, olean_sha, receipt_sha, nprints, batch in DEP_SPECS:
        if batch == 35:
            olean_sha = baseline_main_row["olean_sha256"]
            receipt_sha = observation["receipt_sha256"]
        source, actual = JUDGE / source_relative, JUDGE / actual_relative
        olean, receipt_path = actual / (module + ".olean"), actual / "receipt.json"
        for path, digest in ((source, source_sha), (olean, olean_sha), (receipt_path, receipt_sha)):
            bind(path, digest)
        receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
        row = next(row for row in receipt["rows"] if row["module"] == module)
        expected_global = "INDEPENDENT_BATCH26_FAILED" if batch == 26 else f"INDEPENDENT_BATCH{batch:02d}_AUX_PASS"
        expected_prints = re.findall(r"^#print axioms ([A-Za-z_][A-Za-z_0-9.]*)$", lean_code(source), re.M)
        if (receipt["status"] != expected_global or not receipt["all_inputs_unchanged"]
                or not receipt.get("all_current_bytes_preserved", receipt["all_inputs_unchanged"])
                or row["status"] != "INDEPENDENT_LEAN_AUX_PASS" or row["exit_code"] != 0
                or not row["exact_axiom_coverage_standard_only"] or len(row["axiom_rows"]) != nprints
                or [item["declaration"] for item in row["axiom_rows"]] != expected_prints
                or any(set(item["axioms"]) - {"propext", "Classical.choice", "Quot.sound"} for item in row["axiom_rows"])
                or any(len(item["axioms"]) != len(set(item["axioms"])) for item in row["axiom_rows"])
                or row["source_sha256"] != source_sha or row["olean_sha256"] != olean_sha):
            raise RuntimeError("Actual independent readonly module-row provenance mismatch: " + module)
        bind(actual / (module + ".log"), row["log_sha256"])
        fin_path = actual / (module + "_FIN.json")
        bind(fin_path)
        if json.loads(fin_path.read_text(encoding="utf-8")) != row:
            raise RuntimeError("Actual independent FIN differs from module row")
        if batch in (26, 27, 30, 35):
            obs_path = BASE / f".arbor/sessions/parity/.coordinator/messages/round22_judge_batch{batch}_closed_observation.json"
            closed_path = JUDGE / f"batch{batch}/completion_receipt.json"
            obs_sha = {
                26: "9b7697d2d35d12903e436403e77fb44e8ea76c6f586940e28d168ab851340e9b",
                27: "7ae697adeb55bd7aa124c19ed69e7ef1d0b2cb05b10fc386f4cd55a312478f2f",
                30: "7fd118336cfc1b1106c166282f88030c79e49014efa55bc6a4ce0e463357e292",
                35: args.baseline_observation_sha256}[batch]
            bind(obs_path, obs_sha)
            obs = json.loads(obs_path.read_text(encoding="utf-8"))
            bind(closed_path, obs["completion_sha256"])
            closed = json.loads(closed_path.read_text(encoding="utf-8"))
            evidence = next(item for item in closed["module_evidence"] if item["module"] == module)
            if (obs["status"] != expected_global or obs["receipt_sha256"] != receipt_sha
                    or obs["new_modules"] != 1 or obs["new_declarations"] != nprints
                    or closed["status"] != expected_global or closed["actual_receipt_sha256"] != receipt_sha
                    or not closed["all_current_bytes_preserved"] or closed["modules_passed"] != 1
                    or closed["declarations_passed"] != nprints or evidence["status"] != row["status"]
                    or evidence["exit_code"] != 0 or evidence["declarations_passed"] != nprints
                    or evidence["olean_sha256"] != olean_sha or evidence["log_sha256"] != row["log_sha256"]):
                raise RuntimeError("Whole-module independent ROOT closure mismatch: " + module)
            support_paths.extend((obs_path, closed_path))
        dep_copy = depdir / (module + ".olean")
        with dep_copy.open("xb") as stream:
            stream.write(olean.read_bytes())
        bind(dep_copy, olean_sha)
        deps.append({"module": module, "source": str(source), "source_sha256": source_sha,
            "olean_original": str(olean), "olean_copy": str(dep_copy), "olean_sha256": olean_sha,
            "independent_receipt": str(receipt_path), "independent_receipt_sha256": receipt_sha,
            "status": "INDEPENDENT_LEAN_AUX_PASS", "independent_receipt_global_status": expected_global,
            "module_row_and_exact_axioms_verified": True, "ROOT_closed_observation_verified": batch in (26, 27, 30, 35),
            "recompile_authorized": False})
        reads.extend((path, "HASH_AND_SELECTED_CONTROL_JSON_ONLY_NOT_RAW_FULL", "CURRENT_METADATA_PROVENANCE")
                     for path in (source, receipt_path, fin_path, actual / (module + ".log")))

    old_paths = {path for path in JUDGE.rglob("*") if path.is_file() and not path.resolve().is_relative_to(OWN.resolve())}
    old_paths.update(path for path in OLD21.rglob("*") if path.is_file())
    old_rows = [{"path": str(path), "sha256": sha(path), "bytes": path.stat().st_size} for path in sorted(old_paths)]
    for item in old_rows:
        bind(item["path"], item["sha256"])
    write_new(OWN / "closed_judge_bindings.json", {"schema": "ROUND22_JUDGE5_CLOSED_BINDINGS_BATCH36",
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
    for prelude in ("Init", "Init.Prelude"):
        if prelude not in {item["module"] for item in closure}:
            unresolved.append({"module": prelude, "reason": "Explicit Init/Prelude byte closure required"})
    write_new(OWN / "import_bindings.json", {"schema": "ROUND22_JUDGE5_IMPORT_BINDINGS_BATCH36",
        "module_count": len(closure), "implicit_Init_for_each_nonprelude_module": True,
        "explicit_prelude_seed": "Init", "unresolved": unresolved,
        "entries": sorted(closure, key=lambda item: item["module"]), "readonly_local_entries": deps,
        "metadata_only": True, "compiler_invocations": 0})
    reads.extend([(OWN / "prepare_metadata.py", "FULL_BEFORE_METADATA_EXECUTION", args.builder_read),
        (OWN / "run_once.py", "FULL_SOURCE_ONLY_NEVER_EXECUTED", args.launcher_read),
        (OWN / "preparation.md", "FULL", args.audit_read)])
    for filename in ("source_tools_handoff36.json", "source_tool_reads36.json"):
        path = OWN / filename
        support_paths.append(path)
        reads.append((path, "HASH_PLUS_SOURCE_TOOL_CONTROL_JSON_NOT_IMPORT_CLOSURE", "SOURCE_FREEZE36"))
    for path, _, _ in reads:
        bind(path)
    write_new(OWN / "read_receipts.json", {"schema": "ROUND22_JUDGE5_READ_RECEIPTS_BATCH36", "time_utc": stamp,
        "entries": [{"path": str(path), "sha256": sha(path), "scope": scope, "chunk": chunk} for path, scope, chunk in reads],
        "read_scope_note": "Science/contracts/catalogues FULL7ed586 and2bb8d9; author reads/handoffs FULL2aecf0 andc60118. Historical ROLE3 reviews FULL4154da andcd8b61 retain their original unpaid provenance. New independent ROLE5 science review/report/reads/handoff FULLc95c9b, SOURCE coherent not elaborated. STOPPED34 templates FULL11cdae+868f50/87baa0 are text only, never adapted in place or invoked. Genuine main35 receipt/completion/log FULL949fa6 and ROOT observation FULL2634ba; current preparation verifies paid source03/olean and all readonly receipt rows. No import mathematics FULL claim.",
        "all_import_mathematical_FULL_claim": False, "candidate_sources_not_elaborated": True,
        "compiler_invocations": 0, "numeric_invocations": 0})
    write_new(OWN / "catalog.json", {"schema": "ROUND22_JUDGE5_CATALOG_BATCH36", "time_utc": stamp,
        "modules": rows, "module_count": 2, "total_declarations": 41, "theorem_count": 34, "definition_count": 7,
        "common_source_root": str(OWN / "sources"), "readonly_local_dependencies": list(LOCAL_DEPENDENCIES),
        "dependency_bindings": deps, "support_capture_paths": [str(path) for path in support_paths + baseline_capture_paths],
        "author_provenance_capture_paths": [str(path) for path in dict.fromkeys(author_capture_paths)],
        "modules_author_PASS_claimed": False, "child_wall_seconds": 300, "max_heartbeats": 1000000,
        "compiler_invocations": 0, "numeric_invocations": 0, "win": False})
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
    manifest = {"schema": "ROUND22_JUDGE5_PREPARED_MANIFEST_BATCH36", "time_utc": stamp,
        "status": "PREPARED_SOURCE_ONLY_GATE_CLOSED" if not unresolved else "PREPARATION_IMPORT_OPEN", "role": "ROLE5",
        "modules": list(MODULES), "compiler_invocations": 0, "candidate_numeric_invocations": 0, "numeric_invocations": 0,
        "immutable_inputs": sorted(bindings.values(), key=lambda item: item["path"].casefold()),
        "import_module_count": len(closure), "implicit_Init_closure_included": True, "unresolved_modules": unresolved,
        "common_source_root": str(OWN / "sources"), "source_catalog_sha256": sha(OWN / "catalog.json"),
        "launcher_sha256": sha(OWN / "run_once.py"), "readonly_local_dependencies": list(LOCAL_DEPENDENCIES),
        "closed_judge_files": len(old_rows), "protected_archive_count": 3089,
        "author_olean_used": False, "numeric_banks": [], "previous_official_modules": args.official_modules,
        "previous_official_declarations": args.official_declarations,
        "baseline_observation_path": str(baseline_path), "baseline_observation_sha256": args.baseline_observation_sha256,
        "baseline_observation_status": observation["status"],
        "baseline_actual_receipt_path": str(baseline_receipt_path), "baseline_actual_receipt_sha256": observation["receipt_sha256"],
        "baseline_completion_path": str(baseline_completion_path), "baseline_completion_sha256": observation["completion_sha256"],
        "hypothetical_after_all_PASS_modules": args.official_modules + 2,
        "hypothetical_after_all_PASS_declarations": args.official_declarations + 41,
        "official_count_requires_ROOT_observation": True, "whole_module_credit_only": True,
        "historical_author_pending_references_preserved": True,
        "current_paid_main_module": "ComplexGammaMellinLambda22",
        "current_paid_main_source_sha256": DEP_SPECS[-1][3],
        "current_paid_main_olean_sha256": DEP_SPECS[-1][4],
        "scientific_interfaces_resolved_to_paid_main35_and_tail30": True,
        "independent_scientific_review_status": SCIENCE_REVIEW_STATUS,
        "independent_scientific_review_handoff_sha256": sha(SCIENCE_REVIEW_DIR / "source_handoff22.json"),
        "H1_paid": False, "native_refinement_paid": False, "coefficient_N_computed": False, "D_N_paid": False, "win": False}
    write_new(OWN / "prepared_manifest.json", manifest)
    receipt = {"schema": "ROUND22_JUDGE5_PREPARATION_RECEIPT_BATCH36", "time_utc": datetime.now(timezone.utc).isoformat(),
        "status": manifest["status"], "compiler_invocations": 0, "candidate_numeric_invocations": 0, "numeric_invocations": 0,
        "manifest_sha256": sha(OWN / "prepared_manifest.json"), "launcher_sha256": manifest["launcher_sha256"],
        "catalog_sha256": manifest["source_catalog_sha256"], "read_receipts_sha256": sha(OWN / "read_receipts.json"),
        "import_bindings_sha256": sha(OWN / "import_bindings.json"), "closed_judge_bindings_sha256": sha(OWN / "closed_judge_bindings.json"),
        "builder_sha256": sha(OWN / "prepare_metadata.py"), "preparation_doc_sha256": sha(OWN / "preparation.md"),
        "imports": len(closure), "inputs": len(bindings), "closed_judge_files": len(old_rows), "archives": 3089,
        "modules": 2, "declarations": 41, "theorems": 34, "definitions": 7, "unresolved": unresolved,
        "candidate_source_not_elaborated": True, "readonly_independent_dependency_count": 6,
        "baseline_observation_path": str(baseline_path), "baseline_observation_sha256": args.baseline_observation_sha256,
        "previous_official_modules": args.official_modules, "previous_official_declarations": args.official_declarations,
        "common_source_root": str(OWN / "sources"), "no_author_olean_on_lean_path": True,
        "old_batches_recompiled": False, "numeric_bank_replayed": False, "no_win": True}
    write_new(OWN / "prepared_receipt.json", receipt)
    print(json.dumps(receipt, sort_keys=True))


if __name__ == "__main__":
    main()
