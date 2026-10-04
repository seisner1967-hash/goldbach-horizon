"""One fresh read-only exact-inventory preflight for round18: 799+198=997."""
import sys
sys.dont_write_bytecode = True
from hashlib import sha256
from pathlib import Path
import argparse
import json
import os
import re

ROOT = Path(__file__).resolve().parent
BASE = ROOT.parent
BASELINE = ROOT / 'previous_artifacts_sha256.json'
PREVIOUS_BASELINE = BASE / 'round17' / 'previous_artifacts_sha256.json'
CONTROLLER = BASE / 'round17' / 'controller_manifest.json'
PROBE = ROOT / 'PROBE_BLOCK.md'
EXPECTED_BASELINE = '05212665afffecade91134e1533f93d11eba8058179198e4420eef1fe252f2bc'
EXPECTED_PREVIOUS_BASELINE = '1c21af8d00924e126bf541c03f13277fa699c6f8e9d3a9edbbda337b9cead420'
EXPECTED_CONTROLLER = '5d20d749aa30bcf939e33cd0f1d1efc1049c85634f6054ae79c81890e6d628a4'
EXPECTED_PROBE = '83046b133bceda4f73e9e31ec08fd61f80c4b72c95d88e054bc223f32f2e8d24'
EXPECTED_PREVIOUS, EXPECTED_ADDED, EXPECTED_FILES = 799, 198, 997
SKIP = {'.lake', '.git', '.arbor', '__pycache__', '.pytest_cache', '.mypy_cache', '.ruff_cache'}


def digest(path):
    h = sha256()
    with Path(path).open('rb') as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()


def read_json(path):
    return json.loads(Path(path).read_text(encoding='utf-8'))


def check(condition, detail):
    if not condition:
        raise AssertionError(detail)


def safe_relative(value):
    p = Path(value)
    check(not p.is_absolute() and '..' not in p.parts, ('unsafe_manifest_path', value))
    return p


def skip_directory(name):
    if name in SKIP:
        return True
    match = re.fullmatch(r'round([0-9]+)', name)
    return bool(match and int(match.group(1)) >= 18)


def actual_inventory():
    result = {}
    for directory, children, files in os.walk(BASE, followlinks=False):
        children[:] = sorted(name for name in children if not skip_directory(name))
        for name in sorted(files):
            path = Path(directory) / name
            if path == BASE / 'REPORT.md':
                continue
            result[path.relative_to(BASE).as_posix()] = digest(path)
    return dict(sorted(result.items()))


def original_sources():
    expected = read_json(BASE / 'INPUT_HASHES.json')
    check(len(expected) == 2, 'exactly_two_original_documents_required')
    fixed = {
        r'D:\Users\Utilisateur\Downloads\goldbach_synthesis.pdf':
            'bbcbe5849e2b169f01a2d64457ccf7d1f3b25edcf2b5ca911bcf01343586eb24',
        r'D:\Users\Utilisateur\Downloads\Goldbach_Continuation_Cofacteur_Court_2026-10-01.zip':
            '32b12b8d6823ed71323bb76ed1ba1ed7bc2d1ffad38fa973f043f4ae933e49cd',
    }
    check(expected == fixed, 'original_hash_registry_changed')
    result = {}
    for path, wanted in sorted(fixed.items()):
        actual = digest(path)
        check(actual == wanted, ('original_document_changed', path, wanted, actual))
        result[path] = {'expected_sha256': wanted, 'actual_sha256': actual, 'status': 'PRESERVED'}
    return result


def verify():
    for path, wanted in [(BASELINE, EXPECTED_BASELINE),
                         (PREVIOUS_BASELINE, EXPECTED_PREVIOUS_BASELINE),
                         (CONTROLLER, EXPECTED_CONTROLLER), (PROBE, EXPECTED_PROBE)]:
        check(digest(path) == wanted, ('fixed_input_hash_mismatch', str(path)))
    baseline = read_json(BASELINE)
    previous = read_json(PREVIOUS_BASELINE)['sha256']
    controller = read_json(CONTROLLER)
    bindings = controller['bindings_sha256']
    check(len(previous) == EXPECTED_PREVIOUS, 'previous_registry_count_not799')
    check(len(bindings) == EXPECTED_ADDED - 1, 'controller_bindings_count_not197')
    check(controller['round'] == 17 and controller['victory'] is False and controller['score'] == 0,
          'controller_round_or_nonvictory_metadata_mismatch')
    check(controller['previous_artifacts_preserved'] == EXPECTED_PREVIOUS,
          'controller_previous_preservation_count_mismatch')
    check(controller['next_protected_artifacts_expected'] == EXPECTED_FILES,
          'controller_next_registry_count_mismatch')
    expected = dict(previous)
    for relative, wanted in bindings.items():
        safe_relative(relative)
        key = 'round17/' + Path(relative).as_posix()
        check(key not in expected, ('overlapping_union_key', key))
        expected[key] = wanted
    check('round17/controller_manifest.json' not in expected, 'controller_self_overlap')
    expected['round17/controller_manifest.json'] = EXPECTED_CONTROLLER
    expected = dict(sorted(expected.items()))
    check(len(expected) == EXPECTED_FILES, 'union_count_not997')
    check(baseline['file_count'] == EXPECTED_FILES and baseline['previous799'] == EXPECTED_PREVIOUS
          and baseline['round17_with_controller198'] == EXPECTED_ADDED, 'baseline_count_metadata_mismatch')
    check(baseline['sha256'] == expected, 'baseline_is_not_exact799_plus198_union')
    check(baseline['controller17_sha256'] == EXPECTED_CONTROLLER and
          baseline['source_previous_registry_sha256'] == EXPECTED_PREVIOUS_BASELINE,
          'baseline_provenance_metadata_mismatch')
    records = actual_inventory()
    changed = {key: {'expected': wanted, 'actual': records.get(key, 'MISSING')}
               for key, wanted in expected.items() if records.get(key) != wanted}
    added = sorted(set(records) - set(expected))
    removed = sorted(set(expected) - set(records))
    diagnostic = {'changed': changed, 'added': added, 'removed': removed,
                  'expected_files': EXPECTED_FILES, 'actual_files': len(records)}
    check(not changed and not added and not removed and len(records) == EXPECTED_FILES, diagnostic)
    originals = original_sources()
    check(controller['original_sources_sha256'] == read_json(BASE / 'INPUT_HASHES.json'),
          'controller_original_sources_binding_mismatch')
    for field, key in [('judge_report_sha256', 'agent5.md'),
                       ('judge_final_receipt_sha256', 'judge/final_receipt.json'),
                       ('judge_manifest_sha256', 'judge/manifest.json'),
                       ('audit_receipt_sha256', 'judge/audit_receipt.json'),
                       ('input_manifest_sha256', 'judge/input_sha256.json')]:
        # All paths are the literal controller schema, not inferred substitutes.
        check(key in bindings and controller[field] == bindings[key],
              ('controller_declared_final_binding_mismatch', field, key))
    return {
        'status': 'PRESERVED', 'scope': 'READ_ONLY_CONSERVATION_VERIFICATION',
        'round': 18, 'files': len(records), 'previous_protected_files': EXPECTED_PREVIOUS,
        'round17_files_including_controller': EXPECTED_ADDED, 'controller197_bindings_verified': True,
        'exact_union_799_plus_198_verified': True, 'exact_inventory_additions_and_removals_checked': True,
        'changed': changed, 'added': added, 'removed': removed,
        'baseline_sha256': EXPECTED_BASELINE, 'previous_baseline_sha256': EXPECTED_PREVIOUS_BASELINE,
        'controller17_sha256': EXPECTED_CONTROLLER, 'probe_sha256': EXPECTED_PROBE,
        'registry': str(BASELINE), 'original_sources': originals,
        'old_producer_executed_by_this_verification': False, 'old_PASS_replayed': False,
        'old_Lean_recompiled': False, 'old_dependency_recompiled': False, 'old_PDF_rerendered': False,
        'old_W_or_D_recomputed': False, 'old_sign_recomputed': False,
        'numeric_contract_launched_by_this_verification': False,
        'mathematical_identity_certified_by_conservation': False,
        'flags_describe_this_readonly_verification_not_global_execution': True,
        'source_onset': 'log N >= 10^24', 'finite_N_source_onset_claim': False,
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--output-dir', type=Path, default=ROOT)
    directory = parser.parse_args().output_dir.resolve()
    check(directory == ROOT or ROOT in directory.parents, 'outputs_must_stay_in_round18')
    directory.mkdir(parents=True, exist_ok=True)
    try:
        result = verify()
    except Exception as error:
        (directory / 'conservation_failure.json').write_text(
            json.dumps({'status': 'FAILED', 'error_type': type(error).__name__,
                        'error': repr(error)}, indent=2) + '\n', encoding='utf-8')
        raise
    (directory / 'conservation.json').write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(result, indent=2))
