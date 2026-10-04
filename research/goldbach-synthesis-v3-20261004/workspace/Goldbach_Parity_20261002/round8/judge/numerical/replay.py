"""Frozen-path round-8 numerical and source-page replay; isolated outputs."""
import contextlib
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import sys

sys.dont_write_bytecode = True
OUTPUT = Path(__file__).resolve().parent
ROUND = OUTPUT.parents[1]
BASE = ROUND.parent
sys.path.insert(0, str(ROUND))
STATUS = {
    "compensation": "PASS_EXACT_IDENTITIES_ONLY",
    "native_gram": "PASS_ALGEBRA_ONLY",
    "head_regrouping": "PASS_HEAD_IDENTITY_ONLY",
}

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def load_source(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    assert Path(module.__file__).resolve() == path.resolve()
    return module

manifest_path = ROUND / "previous_artifacts_sha256.json"
manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
assert manifest["file_count"] == len(manifest["sha256"]) == 227
inputs_path = ROUND / "judge" / "input_sha256.json"
inputs = json.loads(inputs_path.read_text(encoding="utf-8"))
assert inputs["role_reports"] == 5 and inputs["numerical_sources"] == 3
for relative, expected in inputs["sha256"].items():
    assert digest(ROUND / relative) == expected, relative
for absolute, expected in inputs["external_sha256"].items():
    assert digest(Path(absolute)) == expected, absolute
preservation = load_source("conservation", ROUND / "conservation.py")
assert preservation.verify()["files"] == 227
# This name is shared with earlier scripts; bind the current helper first.
load_source("shared", ROUND / "shared.py")

def snapshot():
    paths = [BASE / relative for relative in manifest["sha256"]]
    paths += [ROUND / relative for relative in inputs["sha256"]]
    paths += [Path(absolute) for absolute in inputs["external_sha256"]]
    paths += [inputs_path, manifest_path]
    return {str(p): digest(p) for p in paths}

before = snapshot()
comparisons = []
for stem, expected_status in STATUS.items():
    filename = stem + "_checks.py"
    source = ROUND / filename
    shutil.copyfile(source, OUTPUT / filename)
    module = load_source(stem + "_checks", source)
    assert module.verify.__globals__["BASELINE"] == manifest_path
    saved_argv = sys.argv
    sys.argv = [str(source), "--output-dir", str(OUTPUT)]
    try:
        with (OUTPUT / (stem + "_replay.log")).open("w", encoding="utf-8") as log:
            with contextlib.redirect_stdout(log):
                module.run()
    finally:
        sys.argv = saved_argv
    original = json.loads((ROUND / (stem + ".json")).read_text(encoding="utf-8"))
    replay = json.loads((OUTPUT / (stem + ".json")).read_text(encoding="utf-8"))
    assert original == replay, stem
    assert replay["status"] == expected_status and replay["N"] == 100000000
    assert replay["script_sha256"] == digest(source)
    assert digest(ROUND / (stem + ".json")) == digest(OUTPUT / (stem + ".json"))
    comparisons.append(dict(
        file=stem + ".json", status=replay["status"], all_fields_equal=True,
        original_sha256=digest(ROUND / (stem + ".json")),
        replay_sha256=digest(OUTPUT / (stem + ".json")), original_script_sha256=digest(source),
    ))

# Independently reproduce the already inspected physical source pages.
# This binds their pixels and extracted text to the unchanged original PDF.
import pypdfium2 as pdfium
from pypdf import PdfReader
source_receipt_path = ROUND / "source_onset_render_receipt.json"
original_source_receipt = json.loads(source_receipt_path.read_text(encoding="utf-8"))
pdf_path = Path(original_source_receipt["source"])
assert digest(pdf_path) == original_source_receipt["source_sha256"]
assert [v["physical_page"] for v in original_source_receipt["pages"]] == [32, 33, 36]
source_output = OUTPUT.parent / "source_pages"
source_output.mkdir(parents=True, exist_ok=True)
reader = PdfReader(pdf_path)
pdf = pdfium.PdfDocument(str(pdf_path))
source_replay = dict(source=str(pdf_path), source_sha256=digest(pdf_path), page_count=len(reader.pages), pages=[])
try:
    for entry in original_source_receipt["pages"]:
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
        assert digest(png) == entry["png_sha256"]
        assert digest(txt) == entry["text_sha256"]
        assert digest(ROUND / entry["png"]) == digest(png)
        assert digest(ROUND / entry["text"]) == digest(txt)
        source_replay["pages"].append(dict(
            physical_page=index+1, png=png.name, png_sha256=digest(png),
            text=txt.name, text_sha256=digest(txt)))
finally:
    pdf.close()
assert source_replay == original_source_receipt
(source_output / "source_onset_render_receipt.json").write_text(
    json.dumps(source_replay, indent=2) + "\n", encoding="utf-8")
assert digest(source_output / "source_onset_render_receipt.json") == digest(source_receipt_path)

after = snapshot()
assert before == after, "An original or frozen artifact changed"
preserved = preservation.verify()
assert preserved["status"] == "PRESERVED" and preserved["files"] == 227
receipt = dict(
    status="PASS_EXACT_REPLAY", N=100000000, round=8,
    outputs_isolated=True, original_artifacts_preserved=True,
    preserved_previous_artifacts=preserved, checks=comparisons,
    source_onset=dict(
        original_pdf_sha256=digest(pdf_path), physical_pages=[32,33,36],
        all_pixels_text_and_receipt_hashes_equal=True,
        reproduced_receipt=str(source_output / "source_onset_render_receipt.json"),
        receipt_sha256=digest(source_receipt_path),
        onset="u >= 10^24, visually inspected source; budget constants 1024 remain distinct"),
    production_sha256_before=before, production_sha256_after=after,
    wrapper_sha256=digest(Path(__file__)), input_manifest_sha256=digest(inputs_path),
    lean_invoked=False, new_lean_modules=0, new_lean_conclusions=0,
    limitations="Declared finite identities only; no complete head, analytical gain or global D_N computation",
)
(OUTPUT / "replay_receipt.json").write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
print(json.dumps({k: receipt[k] for k in (
    "status", "N", "outputs_isolated", "preserved_previous_artifacts", "checks", "source_onset", "lean_invoked")}, indent=2))
