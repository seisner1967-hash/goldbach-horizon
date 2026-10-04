"""Create new batch13 text tools without importing/executing closed batch12 tools."""
from pathlib import Path

OWN = Path(__file__).resolve().parent
JUDGE = OWN.parent

def new(path, value):
    with path.open("x", encoding="utf-8", newline="\n") as stream:
        stream.write(value)

builder = (JUDGE / "batch12/prepare_metadata.py").read_text(encoding="utf-8")
builder = builder.replace("batch12", "batch13").replace("BATCH12", "BATCH13")
builder = builder.replace("projection_identity_revision02", "projection_identity_revision03")
builder = builder.replace("533f81f523f465240ebf7f129d32c9d6c0119e0e0d7936a42bc65e75823880d0", "8bb1eb5ec6ab4bf5e0c8cc053dcbe743049641dab5a3a3858205ad8ee2e2e9aa")
builder = builder.replace('"7a5ec6"', '"efa5cb"')
builder = builder.replace('"6e5cf8"', '"OWN_COPY_FULL_PENDING"')
builder = builder.replace("489f676365f07bad59c2c89cf6d3aca36814786a0ef8a478a8f98c54fcdb3e12", "a7ac080bdf03db01ef38904519ba615e647d45a241983c1ad2fe27f6876b43d2")
builder = builder.replace("820143dd819a18fba371233cb90ad52ec9393563b7383b230798ee848062ffda", "342febedb322a5f76072e7f0ef5ce5358862609e9d0e287b6aa0ed25066eaf13")
builder = builder.replace("7c2a31d71c99e55425d73e592c2294c296c7dc771705194da760b9376eb13d5f", "70789a0896dbb07f738d61fab96fc9d91c50187296a1a975017947ce0f0be9a8")
builder = builder.replace('"253e91"', '"eee468"')
builder = builder.replace('"605fa1")', '"80c2c5")', 1)
builder = builder.replace('"605fa1")]', '"eee468"),\n        (JUDGE / "batch12/adjudication.md", "10577435fd3695e63cface9e3ba1533395e9593c7957e7869278294f44861f2f", "074112"),\n        (JUDGE / "batch12/completion_receipt.json", "3ac2f583fb40adfc0e5dc52f7e022809833d8a4208dd98c5a100394fb8eaae37", "074112")]')
builder = builder.replace('(OWN / "create_tools_source.py", "FULL_METADATA_TEXT_GENERATOR_ONLY", "a2dcc3")', '(OWN / "create_tools_source.py", "FULL_METADATA_TEXT_GENERATOR_ONLY", "CREATE_TOOL_FULL_PENDING")')
marker = '    old_rows = [{"path": str(path), "sha256": sha(path)}'
addition = '''    cast_api = CACHE / "mathlib/Mathlib/Data/Complex/Basic.lean"
    bindings[str(cast_api)] = sha(cast_api)
    reads.append((cast_api, "TARGETED_217_223_423_429_HPERIOD_CASTS", "78b352"))
'''
assert marker in builder
builder = builder.replace(marker, addition + marker)
new(OWN / "prepare_metadata.py", builder)

launcher = (JUDGE / "batch12/run_once.py").read_text(encoding="utf-8")
launcher = launcher.replace("batch12", "batch13").replace("BATCH12", "BATCH13")
new(OWN / "run_once.py", launcher)
sources = OWN / "sources"
sources.mkdir(exist_ok=False)
original = JUDGE.parent / "role4/projection_identity_revision03/ThermalProjectionIdentity22.lean"
with (sources / original.name).open("xb") as stream:
    stream.write(original.read_bytes())
print("New SOURCE tools and Identity03 copy written. No freeze, candidate import, Lean or numeric invocation.")
