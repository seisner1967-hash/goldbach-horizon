"""Fresh SOURCE tools only: transform readonly batch11 text, never import or execute it."""
from pathlib import Path

OWN = Path(__file__).resolve().parent
JUDGE = OWN.parent
previous = JUDGE / "batch11"

def new(path, value):
    with path.open("x", encoding="utf-8", newline="\n") as stream:
        stream.write(value)

builder = (previous / "prepare_metadata.py").read_text(encoding="utf-8-sig")
builder = builder.replace("batch11", "batch12").replace("BATCH11", "BATCH12")
begin = builder.index("SPECS = (")
end = builder.index("\n\ndef sha", begin)
builder = builder[:begin] + '''SPECS = (
    ("ThermalProjectionIdentity22", "role4/projection_identity_revision02", "533f81f523f465240ebf7f129d32c9d6c0119e0e0d7936a42bc65e75823880d0", 18, 2, "SOURCE_REVISION_NOT_COMPILED", "7a5ec6"),
)
MODULES = tuple(row[0] for row in SPECS)
DEPS = (
    ("ThermalProjectionEnvelope22", "batch11/sources", "batch11/batch11_attempt01",
     "77cdab8bed77a3580767bf20dfa8069860ea888490d673daf5144f1aba050ed5",
     "9c2bb947ccd03436c8cb3c9e3e9f5ce95508ee719e506d9ca90c49623f6dac67",
     "664d8a", "e469d8", "0b25b00e57663172cacc25945ad232d807ff58cd3c34bae6f2e64bf2e852f62b"),
)
LOCAL_DEPENDENCIES = tuple(row[0] for row in DEPS)
OWN_SOURCE_FULL = ("7a5ec6_EXACT_COPY_HASH_VERIFIED_FULL_COPY_PENDING",)
''' + builder[end:]
begin = builder.index("    support = [")
end = builder.index("    supplement = []", begin)
builder = builder[:begin] + '''    support = [
        (JUDGE / "projection_source_review22.md", "c25aee9a13a3b010d214de2607d18f9add2cafbb3a47aefd03e28d5f79d81ba2", "b5b503"),
        (JUDGE / "batch11/adjudication.md", "dd25619f5d0e8ab7f35b45a72527e55837da1743e240fc9170f46aeafa793018", "1020c8"),
        (JUDGE / "batch11/completion_receipt.json", "32f2894cc8d9e3fffa232c9acf58ce039373108194bb253590921caf38c53a99", "1020c8"),
        (BASE / "round22/role4/projection_identity_revision02/repair_diagnostic22.md", "489f676365f07bad59c2c89cf6d3aca36814786a0ef8a478a8f98c54fcdb3e12", "253e91"),
        (BASE / "round22/role4/projection_identity_revision02/source_handoff22.json", "820143dd819a18fba371233cb90ad52ec9393563b7383b230798ee848062ffda", "605fa1"),
        (BASE / "round22/role4/projection_identity_revision02/read_sources22.json", "7c2a31d71c99e55425d73e592c2294c296c7dc771705194da760b9376eb13d5f", "605fa1")]
''' + builder[end:]
builder = builder.replace('"FULL_EXACT_OWN_COPY"', '"FULL_OWN_COPY"')
builder = builder.replace('"module_count": 2, "total_declarations": 62, "theorem_count": 47, "definition_count": 15', '"module_count": 1, "total_declarations": 20, "theorem_count": 18, "definition_count": 2')
builder = builder.replace('"previous_official_modules": 73, "previous_official_declarations": 1161', '"previous_official_modules": 74, "previous_official_declarations": 1203')
builder = builder.replace('"modules": 2, "declarations": 62, "theorems": 47, "definitions": 15', '"modules": 1, "declarations": 20, "theorems": 18, "definitions": 2')
builder = builder.replace('"two_modules_SOURCE_not_elaborated": True, "readonly_independent_dependency_count": 0', '"one_module_SOURCE_not_elaborated": True, "readonly_independent_dependency_count": 1')
builder = builder.replace('"truncated_reads_excluded": ["e1533d", "afb905"]', '"truncated_reads_excluded": []')
builder = builder.replace('    author_capture_paths = []', '''    author_capture_paths = []
    original_identity = BASE / "round22/role4/projection_identity_source01/ThermalProjectionIdentity22.lean"
    if sha(original_identity) != "5b6da908dce97e0ad1ba08a893bd545a4a4c908f969d958102cf9e3509c5e99c": raise RuntimeError("Prior failed source changed")
    def headers(path):
        text = lean_code(path)
        return [" ".join(text[hit.start():text.index(":=", hit.end())].split())
                for hit in re.finditer(r"^(?:def|theorem)\\s+\\w+", text, re.M)]
    if headers(original_identity) != headers(OWN / "sources/ThermalProjectionIdentity22.lean"):
        raise RuntimeError("Identity contract changed")
    bindings[str(original_identity)] = sha(original_identity)
    for relative, chunk, scope in (
        ("Mathlib/Analysis/SpecialFunctions/Integrals.lean", "804edf", "TARGETED_307_332_431_451_GLOBAL_NAMESPACE"),
        ("Mathlib/Algebra/Group/Hom/Defs.lean", "804edf", "TARGETED_417_429_TO_ADDITIVE_MAP_NEG"),
        ("Mathlib/Algebra/BigOperators/Group/Finset.lean", "804edf", "TARGETED_785_809_832_847_TO_ADDITIVE_SUM_COMM")):
        path = CACHE / "mathlib" / relative
        bindings[str(path)] = sha(path); reads.append((path, scope, chunk))''')
new(OWN / "prepare_metadata.py", builder)

launcher = (previous / "run_once.py").read_text(encoding="utf-8-sig")
launcher = launcher.replace("batch11", "batch12").replace("BATCH11", "BATCH12")
launcher = launcher.replace('of two projection auxiliaries', 'of one projection identity auxiliary')
launcher = launcher.replace('MODULES = ("ThermalProjectionEnvelope22", "ThermalProjectionIdentity22")', 'MODULES = ("ThermalProjectionIdentity22",)')
launcher = launcher.replace('LOCAL_DEPENDENCIES = ()', 'LOCAL_DEPENDENCIES = ("ThermalProjectionEnvelope22",)')
launcher = launcher.replace('"compiler_invocations_maximum": 2', '"compiler_invocations_maximum": 1')
launcher = launcher.replace('"child_invocations_maximum": 2', '"child_invocations_maximum": 1')
new(OWN / "run_once.py", launcher)
source = OWN / "sources"
source.mkdir(exist_ok=False)
new_source = source / "ThermalProjectionIdentity22.lean"
original = JUDGE.parent / "role4/projection_identity_revision02/ThermalProjectionIdentity22.lean"
with new_source.open("xb") as stream:
    stream.write(original.read_bytes())
print("Fresh SOURCE tools and one exact Identity copy created. No freeze, import, Lean or numeric invocation.")
