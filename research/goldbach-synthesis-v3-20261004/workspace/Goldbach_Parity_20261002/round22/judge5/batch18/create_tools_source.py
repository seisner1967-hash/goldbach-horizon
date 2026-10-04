"""Metadata text generation for batch18; no candidate imports, compiler or calculation."""
from pathlib import Path
import hashlib

OWN = Path(__file__).resolve().parent
JUDGE = OWN.parent
BASE = JUDGE.parents[1]
PRIOR = JUDGE / "batch17"


def replace_once(text, old, new):
    if text.count(old) != 1:
        raise RuntimeError("Template block not unique: " + old[:80])
    return text.replace(old, new, 1)


def write_new(path, text):
    with path.open("x", encoding="utf-8", newline="\n") as stream:
        stream.write(text)


builder = (PRIOR / "prepare_metadata.py").read_text(encoding="utf-8")
builder = builder.replace("batch17", "batch18").replace("BATCH17", "BATCH18")
start, end = builder.index("SPECS = ("), builder.index("\n\n\ndef sha")
builder = builder[:start] + '''SPECS = (
    ("ThermalGammaMellinInverse22", "role3/phase_mellin_inversion_source22", "5271bbf9a9917a3ab61c6c7e0e747af4014e214b0867a9c81b43b5aa08fccec1", 9, 2, "SOURCE_ONLY_NOT_COMPILED", "2092de/a13eb7", "GoldbachThermalMellin22"),)
MODULES = tuple(row[0] for row in SPECS)
LOCAL_DEPENDENCIES = ("GammaPrerequisites22",)
DEP_SOURCE = JUDGE / "batch02_sources/GammaPrerequisites22.lean"
DEP_OLEAN = JUDGE / "batch02_attempt01/GammaPrerequisites22.olean"
DEP_RECEIPT = JUDGE / "batch02_attempt01/receipt.json"
DEP_SOURCE_SHA = "9f5e5fe14d18e2b7c3ab364e461bfcc01d29ee4ef4af6d627d6ad9fcd102fbe7"
DEP_OLEAN_SHA = "fc0dad0b550f13a5c3a5b1e7cf1cfa22fc3a233822fc548cce155ab7a7274477"
DEP_RECEIPT_SHA = "a159b22e7ac4e8718f0572fdbf3e6d424294571eab01d5ed1ff979a821af48f9"''' + builder[end:]
builder = replace_once(builder, '    rel = Path(*module.split("."))', '''    if module == "GammaPrerequisites22":
        return DEP_SOURCE, OWN / "readonly_oleans/GammaPrerequisites22.olean"
    rel = Path(*module.split("."))''')
builder = builder.replace("CANONICAL_LOG32_TRUE_PRECISION_LAMBDA_PP_CONTINUOUS_COEFFICIENT_ENVELOPE_AUX_ONLY", "REAL_GAMMA_SCALAR_MELLIN_INVERSION_X_POSITIVE_AUX_ONLY")
start, end = builder.index('    depdir = OWN / "readonly_oleans"'), builder.index('    old_rows = ')
builder = builder[:start] + '''    depdir = OWN / "readonly_oleans"; depdir.mkdir(exist_ok=False)
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
        (JUDGE / "mellin_inverse_source_review22.md", "ea23cf317cebdfaf4328f53f691fc9f22412550eabdff273cab94f373ed8d0a8", "2092de"),
        (BASE / "round22/role3/phase_mellin_inversion_source22/source_contract22.md", "984f3e16d927b8d373b3c81af2848e18f77ffa7eb89efb7ab7c6ddf33accde01", "5ae4ae"),
        (BASE / "round22/role3/phase_mellin_inversion_source22/read_receipts22.json", "a77e878bfc84be170ba4f8c52f743887d9afbcc57fd5cc82370f208ab51a6a0a", "5ae4ae"),
        (JUDGE / "batch17/adjudication.md", "ffab547e870266510c64ebe011b89998fe1d218ec27f347f8ca8a3ce38a331e3", "602acc_HISTORICAL_FULL"),
        (JUDGE / "batch17/completion_receipt.json", "150b360cfb3fabbcc3a1a42456c2a1ebd338683af9863c68134310c06775cdaa", "602acc_HISTORICAL_FULL"),
        (JUDGE / "batch17/batch17_attempt01/receipt.json", "9449666ee8bdbbae74ea849e5a9ce2eb5c0c5bd7dd24c14a2d28065068178298", "ee2407_HISTORICAL_FULL")]
    for path, digest, chunk in support:
        if sha(path) != digest: raise RuntimeError("Support provenance changed")
        bindings[str(path)] = digest; reads.append((path, "FULL_CURRENT_OR_PREVIOUS_CLOSED", chunk))
    api_reads = [
        ("Mathlib/Analysis/MellinInversion.lean", "a13eb7", "FULL"),
        ("Mathlib/Analysis/MellinTransform.lean", "2867e9_HISTORICAL", "TARGETED_35_96"),
        ("Mathlib/Analysis/SpecialFunctions/Gamma/Deriv.lean", "59a6a9_HISTORICAL", "TARGETED_35_44_75_85"),
        ("Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean", "59a6a9_HISTORICAL", "TARGETED_83_112_305_322"),
        ("Mathlib/MeasureTheory/Integral/IntegrableOn.lean", "59a6a9_HISTORICAL", "TARGETED_220_231_695_707"),
        ("Mathlib/MeasureTheory/Function/L1Space.lean", "e0f4d5", "TARGETED_432_444")]
    for relative, chunk, scope in api_reads:
        path = CACHE / "mathlib" / relative
        bindings[str(path)] = sha(path); reads.append((path, scope, chunk))
''' + builder[end:]
builder = builder.replace('"readonly_local_entries": []', '"readonly_local_entries": deps')
builder = builder.replace('"truncated_reads_excluded": ["ae4a74"], "empty_API_output_not_counted_as_read": "e7369c corrected054dec",', '"truncated_reads_excluded": ["f01eb1", "a732a6", "56545d", "2d8015", "3b6479"],')
builder = builder.replace('"module_count": 2, "total_declarations": 52, "theorem_count": 32, "definition_count": 20', '"module_count": 1, "total_declarations": 11, "theorem_count": 9, "definition_count": 2')
builder = builder.replace('"readonly_local_dependencies": [], "dependency_bindings": []', '"readonly_local_dependencies": list(LOCAL_DEPENDENCIES), "dependency_bindings": deps')
builder = builder.replace('"readonly_local_dependencies": [], "closed_judge_files"', '"readonly_local_dependencies": list(LOCAL_DEPENDENCIES), "closed_judge_files"')
builder = builder.replace('"previous_official_modules": 76, "previous_official_declarations": 1252', '"previous_official_modules": 78, "previous_official_declarations": 1304')
builder = builder.replace('"hypothetical_after_all_PASS_modules": 78, "hypothetical_after_all_PASS_declarations": 1304', '"hypothetical_after_all_PASS_modules": 79, "hypothetical_after_all_PASS_declarations": 1315')
builder = builder.replace('"modules": 2, "declarations": 52, "theorems": 32, "definitions": 20', '"modules": 1, "declarations": 11, "theorems": 9, "definitions": 2')
builder = builder.replace('"two_modules_SOURCE_not_elaborated": True, "readonly_independent_dependency_count": 0', '"one_module_SOURCE_not_elaborated": True, "readonly_independent_dependency_count": 1')

launcher = (PRIOR / "run_once.py").read_text(encoding="utf-8")
launcher = launcher.replace("batch17", "batch18").replace("BATCH17", "BATCH18")
launcher = launcher.replace("two canonical-log and coefficient auxiliaries", "one genuine Gamma scalar Mellin inversion auxiliary")
launcher = replace_once(launcher, 'MODULES = ("RationalLogQuantization22", "QuantizedLambdaEnvelope22")', 'MODULES = ("ThermalGammaMellinInverse22",)')
launcher = replace_once(launcher, 'LOCAL_DEPENDENCIES = ()', 'LOCAL_DEPENDENCIES = ("GammaPrerequisites22",)')
launcher = launcher.replace('"compiler_invocations_maximum": 2', '"compiler_invocations_maximum": 1').replace('"child_invocations_maximum": 2', '"child_invocations_maximum": 1')
write_new(OWN / "prepare_metadata.py", builder)
write_new(OWN / "run_once.py", launcher)
(OWN / "sources").mkdir(exist_ok=False)
original = BASE / "round22/role3/phase_mellin_inversion_source22/ThermalGammaMellinInverse22.lean"
data = original.read_bytes()
if hashlib.sha256(data).hexdigest() != "5271bbf9a9917a3ab61c6c7e0e747af4014e214b0867a9c81b43b5aa08fccec1":
    raise RuntimeError("Frozen author source changed")
with (OWN / "sources/ThermalGammaMellinInverse22.lean").open("xb") as stream:
    stream.write(data)
print("Batch18 tools and exact source copy created; no metadata freeze, candidate import or compiler invoked.")
