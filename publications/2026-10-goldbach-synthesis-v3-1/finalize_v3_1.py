"""Bind verified document artifacts and assemble a documentary handoff."""
import difflib
import hashlib
import json
import shutil
import zipfile
from datetime import datetime, timezone
from pathlib import Path

root = Path(__file__).resolve().parent
workspace = root.parent
repo = workspace / 'goldbach-v3-publication-20261004'
historical = workspace / 'Goldbach_Parity_20261002/synthesis_v3'
archive = repo / 'research/goldbach-numerical-20261004'
publication = repo / 'publications/2026-10-goldbach-synthesis-v3-1'


def binding(path):
    return {'bytes': path.stat().st_size,
            'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n',
                    encoding='utf-8')


def make_zip(path, names):
    with zipfile.ZipFile(path, 'w', compression=zipfile.ZIP_DEFLATED,
                         compresslevel=9) as package:
        for name in sorted(names):
            info = zipfile.ZipInfo(name, (2026, 10, 4, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            package.writestr(info, (root / name).read_bytes())
    with zipfile.ZipFile(path) as package:
        assert package.testzip() is None
        for name in names:
            assert package.read(name) == (root / name).read_bytes()


build = json.loads((root / 'output/pdf/build_receipt_v3_1.json').read_text())
qa = json.loads((root / 'output/pdf/pdf_qa_v3_1.json').read_text())
assert build['exit_code'] == 0 and build['PDF_valid_for_this_source_build']
assert build['source_sha256'] == binding(root / 'goldbach_synthesis_v3_1.tex')['sha256']
assert qa['PDF_sha256'] == build['PDF_sha256']
assert qa['A4'] and qa['all_pages_have_text'] and qa['render_exit_code'] == 0
assert not any(qa[k] for k in ['chars_outside_page', 'missing_character_log',
                              'overfull_boxes_log', 'unresolved_references_log'])
for name in ['goldbach_synthesis_v3_1.pdf', 'build_receipt_v3_1.json',
             'pdf_qa_v3_1.json', 'tectonic_stdout.log', 'tectonic_stderr.log']:
    shutil.copyfile(root / 'output/pdf' / name, root / name)
for name in ['goldbach_synthesis_v3.pdf', 'evidence_v3.json', 'HANDOFF_THEORY_V3.txt']:
    shutil.copyfile(historical / name, root / name)
supplied_pdf = Path(r'D:\Users\Utilisateur\Downloads\goldbach_synthesis_v3.pdf')
assert binding(supplied_pdf) == binding(root / 'goldbach_synthesis_v3.pdf')

diff = difflib.unified_diff(
    (historical / 'goldbach_synthesis_v3.tex').read_text().splitlines(True),
    (root / 'goldbach_synthesis_v3_1.tex').read_text().splitlines(True),
    fromfile='goldbach_synthesis_v3.tex', tofile='goldbach_synthesis_v3_1.tex')
(root / 'V3_TO_V3_1.patch').write_text(''.join(diff), encoding='utf-8')
make_zip(root / 'goldbach_arxiv_source_v3_1.zip',
         ['goldbach_synthesis_v3_1.tex', 'README_SOURCE_V3_1.txt'])

verdict = json.loads((root / 'numerical_verdict.json').read_text())
manifest = json.loads((archive / 'ARCHIVE_MANIFEST.json').read_text())
assert manifest['file_count'] == 47 and not manifest['omitted_files']
assert verdict['CRT_equals_producer_equals_direct_A32']
assert verdict['fresh_producer_matches_entire_checked_payload']
assert verdict['actual_difference_numerator'] == '0'
entries = {f['path']: f for f in manifest['files']}
assert binding(root / 'numerical_verdict.json') == {
    k: entries['numerical_verdict.json'][k] for k in ['bytes', 'sha256']}

deliver = ['.gitattributes', 'README.md', 'goldbach_synthesis_v3_1.pdf', 'goldbach_synthesis_v3_1.tex',
           'goldbach_arxiv_source_v3_1.zip', 'goldbach_synthesis_v3.pdf',
           'evidence_v3.json', 'HANDOFF_THEORY_V3.txt', 'HANDOFF_FEJER_V3_1.txt',
           'README_SOURCE_V3_1.txt', 'numerical_addendum.txt', 'numerical_verdict.json',
           'build_receipt_v3_1.json', 'pdf_qa_v3_1.json', 'native_editor_diagnostics.json',
           'scientific_review_v3_1.txt', 'V3_TO_V3_1.patch', 'build_pdf_v3_1.py',
           'pdf_qa_v3_1.py', 'finalize_v3_1.py', 'fontconfig.xml',
           'tectonic_stdout.log', 'tectonic_stderr.log']
registry = {
    'schema': 'GOLDBACH_SYNTHESIS_V3_1_DOCUMENTARY_EVIDENCE',
    'created_at_utc': datetime.now(timezone.utc).isoformat(),
    'revision': '3.1', 'author': 'Durand Serge',
    'scope': 'Complete V3 revision plus numerical addendum, no new theory or Lean proof.',
    'page_count': qa['page_count'],
    'historical_V3_unchanged': True,
    'supplied_V3_PDF_matches_historical': True,
    'formal_inventory': {'credited_modules': 88, 'auxiliary_declarations': 1488,
                         'definitions_included': True, 'unchanged': True},
    'observed_numerical_verdict': verdict,
    'proof_boundaries': {k: False for k in [
        'native_Lean_refinement', 'B40_real_log_refinement_Lean',
        'Mellin_coefficient_truncation_chain_compiled', 'spectral_H1', 'D_N', 'WIN']},
    'new_numerical_archive': {
        'repository_path': 'research/goldbach-numerical-20261004',
        'manifest': binding(archive / 'ARCHIVE_MANIFEST.json'),
        'verification_receipt': binding(archive / 'ARCHIVE_VERIFICATION.json'),
        'file_count': manifest['file_count'], 'original_bytes': manifest['original_bytes'],
        'omitted_files': manifest['omitted_files'], 'original_file_bindings': manifest['files']},
    'document_files': {name: binding(root / name) for name in deliver},
    'documentary_review_scope': 'Entire revised TeX, numerical verdict and archive receipts; internal review only.',
    'PDF_export_validated': True, 'all_pages_rendered': True,
    'builtin_compiler_initialization_failed': True,
    'independent_full_catalogue_replay_in_document_revision': False,
    'new_scientific_executions_in_document_revision': 0,
    'source_diff': 'V3_TO_V3_1.patch',
    'resume_entry_point': 'HANDOFF_FEJER_V3_1.txt',
}
write_json(root / 'evidence_v3_1.json', registry)
deliver.append('evidence_v3_1.json')
make_zip(root / 'goldbach_session_handoff_v3_1.zip', deliver)
deliver.append('goldbach_session_handoff_v3_1.zip')
delivery = {'schema': 'GOLDBACH_V3_1_DELIVERY',
            'repository_path': 'publications/2026-10-goldbach-synthesis-v3-1',
            'files': {name: binding(root / name) for name in deliver},
            'scope': 'All listed documentary files; full native payloads in separate verified archive.'}
write_json(root / 'DELIVERY_V3_1.json', delivery)
deliver.append('DELIVERY_V3_1.json')
publication.mkdir(parents=True, exist_ok=True)
for name in deliver:
    shutil.copyfile(root / name, publication / name)
    assert binding(root / name) == binding(publication / name)
print(json.dumps({'publication': str(publication), 'files': len(deliver),
                  'PDF': binding(root / 'goldbach_synthesis_v3_1.pdf'),
                  'handoff_zip': binding(root / 'goldbach_session_handoff_v3_1.zip'),
                  'page_count': qa['page_count'], 'status': 'DOCUMENTARY_DELIVERY_VERIFIED'}, indent=2))
