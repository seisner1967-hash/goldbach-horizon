"""Only the new round-9 contract: exact isolated replay and source-page link."""
import contextlib
import hashlib
import importlib.util
import json
from pathlib import Path
import runpy
import shutil
import sys

sys.dont_write_bytecode = True
OUTPUT = Path(__file__).resolve().parent
JUDGE = OUTPUT.parent
ROUND = JUDGE.parent
BASE = ROUND.parent

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

inputs_path = JUDGE / "input_sha256.json"
inputs = json.loads(inputs_path.read_text(encoding="utf-8"))
assert inputs["role_reports"] == 5 and inputs["numerical_sources"] == 1
assert inputs["role3_completion_sha256"] == inputs["sha256"]["agent3_contract_audit.md"]
for relative, expected in inputs["sha256"].items():
    assert digest(ROUND / relative) == expected, relative
for absolute, expected in inputs["external_sha256"].items():
    assert digest(Path(absolute)) == expected, absolute
manifest_path = ROUND / "previous_artifacts_sha256.json"
manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
assert manifest["file_count"] == len(manifest["sha256"]) == 307
spec = importlib.util.spec_from_file_location("goldbach_round9_conservation", ROUND / "conservation.py")
preservation = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = preservation
spec.loader.exec_module(preservation)
assert preservation.verify()["files"] == 307

def snapshot():
    paths = [BASE / relative for relative in manifest["sha256"]]
    paths += [ROUND / relative for relative in inputs["sha256"]]
    paths += [Path(absolute) for absolute in inputs["external_sha256"]]
    paths += [inputs_path, manifest_path]
    return {str(p): digest(p) for p in paths}

before = snapshot()
source = ROUND / "new_contract_checks.py"
shutil.copyfile(source, OUTPUT / source.name)
saved_argv = sys.argv
sys.argv = [str(source), "--output-dir", str(OUTPUT)]
try:
    with (OUTPUT / "new_contracts_replay.log").open("w", encoding="utf-8") as log:
        with contextlib.redirect_stdout(log):
            runpy.run_path(str(source), run_name="__main__")
finally:
    sys.argv = saved_argv
original_path = ROUND / "new_contracts.json"
replay_path = OUTPUT / "new_contracts.json"
original = json.loads(original_path.read_text(encoding="utf-8"))
replay = json.loads(replay_path.read_text(encoding="utf-8"))
assert original == replay
assert original_path.read_bytes() == replay_path.read_bytes()
assert replay["N"] == 100000000 and replay["status"] == "FINITE_NEW_CONTRACT_CHECKS_ONLY"
assert replay["script_sha256"] == digest(source)
assert not replay["victory"] and not replay["Lean_called"]
assert replay["face"]["status"] == "PASS_IDENTITY_ONLY_CORRECTED_V2"
assert replay["face"]["rejected_V1"]["status"] == "ERROR_FALSIFIER"
assert replay["weighted_operator"]["status"] == "PASS_IDENTITY_ONLY_WEIGHTED_ENERGY"
assert replay["weighted_operator"]["rejected_prime_claim_m311"]["status"] == "ERROR_FALSIFIER"
assert replay["weighted_operator"]["properpower_analytic_payment_tested"] is False
assert replay["weighted_operator"]["analytic_gain"] is False
assert replay["weighted_operator"]["rank_one_assumed"] is False
for relative, expected in replay["imports"].items():
    assert digest(BASE / relative) == expected, relative
assert replay["conservation_before"]["files"] == replay["conservation_after"]["files"] == 307

# Reproduce the pixels and text of physical page 27, from the original PDF.
import pypdfium2 as pdfium
from pypdf import PdfReader
source_receipt_path = ROUND / "source54_render_receipt.json"
source_receipt = json.loads(source_receipt_path.read_text(encoding="utf-8"))
pdf_path = Path(source_receipt["source"])
assert digest(pdf_path) == source_receipt["source_sha256"]
assert [entry["physical_page"] for entry in source_receipt["pages"]] == [27]
source_output = JUDGE / "source_pages"
source_output.mkdir(parents=True, exist_ok=True)
reader = PdfReader(pdf_path)
pdf = pdfium.PdfDocument(str(pdf_path))
source_replay = dict(source=str(pdf_path), source_sha256=digest(pdf_path), page_count=len(reader.pages), pages=[])
try:
    for entry in source_receipt["pages"]:
        index = entry["physical_page"] - 1
        png, txt = source_output / entry["png"], source_output / entry["text"]
        page = pdf[index]
        bitmap = page.render(scale=1.7)
        try:
            bitmap.to_pil().save(png)
            txt.write_text(reader.pages[index].extract_text() or "", encoding="utf-8")
        finally:
            bitmap.close()
            page.close()
        assert digest(png) == entry["png_sha256"] == digest(ROUND / entry["png"])
        assert digest(txt) == entry["text_sha256"] == digest(ROUND / entry["text"])
        source_replay["pages"].append(dict(
            physical_page=index+1, png=png.name, png_sha256=digest(png),
            text=txt.name, text_sha256=digest(txt)))
finally:
    pdf.close()
assert source_replay == source_receipt
reproduced_source_receipt = source_output / "source54_render_receipt.json"
reproduced_source_receipt.write_text(json.dumps(source_replay, indent=2) + "\n", encoding="utf-8")
assert reproduced_source_receipt.read_bytes() == source_receipt_path.read_bytes()

after = snapshot()
assert before == after, "An original or frozen artifact changed"
preserved = preservation.verify()
assert preserved["files"] == 307 and preserved["status"] == "PRESERVED"
receipt = dict(
    status="PASS_EXACT_REPLAY", round=9, N=100000000,
    outputs_isolated=True, original_artifacts_preserved=True,
    all_json_fields_equal=True, all_json_bytes_equal=True,
    production_json_sha256=digest(original_path), replay_json_sha256=digest(replay_path),
    production_script_sha256=digest(source),
    contract_statuses=dict(
        face=replay["face"]["status"], weighted=replay["weighted_operator"]["status"],
        V1=replay["face"]["rejected_V1"]["status"],
        m311=replay["weighted_operator"]["rejected_prime_claim_m311"]["status"]),
    properpower_analytic_payment_tested=False,
    preserved_previous_artifacts=preserved,
    source54=dict(physical_page=27, original_pdf_sha256=digest(pdf_path),
        pixels_text_and_receipt_bytes_equal=True, receipt=str(reproduced_source_receipt),
        receipt_sha256=digest(source_receipt_path),
        literal_exponent="-sqrt(u/60)", weaker_round9_majorant="-sqrt(u)/60"),
    production_sha256_before=before, production_sha256_after=after,
    wrapper_sha256=digest(Path(__file__)), input_manifest_sha256=digest(inputs_path),
    lean_invoked=False, new_lean_modules=0, new_lean_conclusions=0,
    limitations="One new finite contract only; no analytical budget or global signed moment tested",
)
(OUTPUT / "replay_receipt.json").write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
print(json.dumps({key:receipt[key] for key in (
    "status", "all_json_fields_equal", "all_json_bytes_equal", "contract_statuses",
    "properpower_analytic_payment_tested", "preserved_previous_artifacts", "source54", "lean_invoked")}, indent=2))
