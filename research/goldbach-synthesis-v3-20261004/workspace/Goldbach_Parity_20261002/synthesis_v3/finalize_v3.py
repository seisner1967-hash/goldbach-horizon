"""Seal the documentary delivery and engineering checkpoint, without research."""
import hashlib
import json
import zipfile
from datetime import datetime, timezone
from pathlib import Path

root = Path(__file__).resolve().parent
B = root.parent
C = B / '.arbor/sessions/parity/.coordinator'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


source = root / 'goldbach_synthesis_v3.tex'
pdf = root / 'output/pdf/goldbach_synthesis_v3.pdf'
evidence_path = root / 'evidence_v3.json'
handoff = root / 'HANDOFF_THEORY_V3.txt'
review = root / 'scientific_review_v3.txt'
build = json.loads((root / 'output/pdf/build_receipt_v3.json').read_text(encoding='utf-8'))
qa = json.loads((root / 'output/pdf/pdf_qa_v3.json').read_text(encoding='utf-8'))
evidence = json.loads(evidence_path.read_text(encoding='utf-8'))
assert build['exit_code'] == 0 and build['PDF_valid_for_this_source_build']
assert evidence['language'] == 'en'
source_binding = next(row for row in evidence['documents'] if row['id'] == 'tex_v3')
assert build['source_sha256'] == sha(source) == source_binding['sha256']
assert build['PDF_sha256'] == qa['PDF_sha256'] == sha(pdf)
assert sha(root / 'goldbach_synthesis_v3.pdf') == sha(pdf)
assert qa['page_count'] > 0 and qa['A4'] and qa['all_pages_have_text']
assert not any(qa[k] for k in ['encrypted', 'chars_outside_page', 'missing_character_log',
                              'overfull_boxes_log', 'unresolved_references_log'])
assert evidence['official_inventory'] == {'modules': 88, 'auxiliary_declarations': 1488,
                                          'includes_definitions': True, 'baseline_observation_id': 'root35'}
assert evidence['research_frozen'] and not evidence['coefficient_N_computed']
assert not evidence['D_N_proved'] and not evidence['WIN']
bindings = evidence['documents'] + evidence['evidence_files']
assert len(bindings) == 47
for row in bindings:
    path = (B / row['path']).resolve(strict=True)
    assert path.stat().st_size == row['bytes'] and sha(path) == row['sha256'], row['id']
assert sha(source) in review.read_text(encoding='utf-8'), 'Final source must be in independent review addendum'
french_snapshot = root / 'fr_archive/goldbach_synthesis_v3.tex'
assert sha(french_snapshot) == '222f187546550d9f03589e219e008d11e07e6c0e1a85f39834c3e1e8319c02f1'
assert sha(root / 'fr_archive/goldbach_synthesis_v3.pdf') == '0edf084715dbaec2fdb2766c51756e0259b7787dc7ecde5b81a34987c50f82cd'

archive = root / 'goldbach_arxiv_source_v3.zip'
with zipfile.ZipFile(archive, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as bundle:
    for path in [source, root / 'README_SOURCE_V3.txt']:
        bundle.write(path, arcname=path.name)
with zipfile.ZipFile(archive) as bundle:
    assert bundle.testzip() is None
    assert bundle.read(source.name) == source.read_bytes()

now = datetime.now(timezone.utc).isoformat()
files = [source, pdf, root / 'goldbach_synthesis_v3.pdf', evidence_path, handoff, review, archive,
         root / 'output/pdf/build_receipt_v3.json', root / 'output/pdf/pdf_qa_v3.json']
delivery = {'schema': 'GOLDBACH_SYNTHESIS_V3_DOCUMENT_DELIVERY', 'sealed_at_utc': now,
            'status': 'DOCUMENT_COMPLETE_ENGINEERING_FROZEN_THEORY_OPEN',
            'language': 'en', 'page_count': qa['page_count'], 'standalone_arxiv_source': True,
            'french_snapshot_preserved': {'path': french_snapshot.relative_to(B).as_posix(),
                                          'sha256': sha(french_snapshot)},
            'official_modules': 88, 'auxiliary_declarations_including_definitions': 1488,
            'evidence_bindings_rehashed': len(bindings),
            'visual_review': 'All final page contact sheets inspected; key equation and provenance pages inspected at full size.',
            'coefficient_N_computed': False, 'D_N_proved': False, 'WIN': False,
            'scientific_executions_in_document_closure': 0,
            'files': [{'path': p.relative_to(B).as_posix(), 'bytes': p.stat().st_size,
                       'sha256': sha(p)} for p in files]}
with (root / 'DELIVERY_V3.json').open('w', encoding='utf-8') as stream:
    json.dump(delivery, stream, ensure_ascii=False, indent=2)
    stream.write('\n')
cp_path = C / 'checkpoint.json'
cp = json.loads(cp_path.read_text(encoding='utf-8'))
cp['status'] = 'engineering_session_frozen_by_user'
cp['phase'] = 'SYNTHESIS_V3_ENGLISH_SEALED_FOR_PUBLICATION_THEORY_OPEN'
cp['document_delivery'] = {'path': 'synthesis_v3/DELIVERY_V3.json',
                           'sha256': sha(root / 'DELIVERY_V3.json'), 'sealed_at_utc': now,
                           'language': 'en'}
for actor in cp.get('in_flight_executors', []):
    actor['status'] = 'FROZEN_NO_SCIENTIFIC_EXECUTOR_RUNNING'
cp_path.write_text(json.dumps(cp, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
stats_path = B / '.arbor/sessions/parity/run_stats.json'
old_stats = json.loads(stats_path.read_text(encoding='utf-8'))
historical_stats = old_stats.get('historical_stats_snapshot_20261002_preserved', old_stats)
stats = {'status': 'engineering_session_frozen_by_user', 'reported_at_utc': now,
         'research_objective_complete': False, 'victory': False,
         'metric_name': 'semantic_parity_breakthrough', 'baseline_score': 0, 'trunk_score': 0,
         'B_test': 'not_applicable_to_exact_proof', 'official_modules': 88,
         'official_auxiliary_declarations_including_definitions': 1488,
         'last_lean_batch': 36, 'last_lean_status': 'FAILED_TECHNICAL_ZERO_CREDIT',
         'document_language': 'en', 'document_pages': qa['page_count'],
         'new_scientific_executions_in_closure': 0,
         'historical_stats_snapshot_20261002_preserved': historical_stats}
stats_path.write_text(json.dumps(stats, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
with (B / 'REPORT.md').open('a', encoding='utf-8') as stream:
    stream.write(f"\nEnglish Synthesis V3 finalized: {qa['page_count']} pages, standalone source and arXiv archive; ")
    stream.write('compilation documentaire exit0, rendu contrôlé, 47 liens de preuve rehashés. ')
    stream.write('Aucun nouveau test scientifique ; empreintes dans synthesis_v3/DELIVERY_V3.json. ')
    stream.write('La publication GitHub conserve tous les fichiers du corpus gelé et les payloads trop volumineux sous forme reconstructible.\n')
print(json.dumps(delivery, ensure_ascii=False, indent=2))
