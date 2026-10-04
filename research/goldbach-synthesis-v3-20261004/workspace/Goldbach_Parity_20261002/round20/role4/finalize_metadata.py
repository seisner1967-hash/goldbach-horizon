"""Final ROLE4 hashes and execution provenance only; no Lean or mathematical producer."""
import hashlib
import json
import re
from datetime import datetime, timezone
from pathlib import Path

W = Path(__file__).resolve().parent
B = W.parents[1]
G = B / 'round20' / 'role4_geometry'
NOW = datetime.now(timezone.utc).isoformat()
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
CACHE = {}

def sha(path):
    p = Path(path)
    if str(p) not in CACHE:
        CACHE[str(p)] = hashlib.sha256(p.read_bytes()).hexdigest()
    return CACHE[str(p)]

def check(path, expected):
    actual = sha(path)
    assert actual == expected, (str(path), expected, actual)
    return actual

def item(path, scope=None):
    p = Path(path)
    result = {'path': str(p), 'sha256': sha(p)}
    if scope:
        result['scope'] = scope
    return result

def load(path):
    return json.loads(Path(path).read_text(encoding='utf-8'))

def lean_without_comments(text):
    result = []
    i = 0
    level = 0
    while i < len(text):
        if text.startswith('/-', i):
            level += 1
            i += 2
        elif level and text.startswith('-/', i):
            level -= 1
            i += 2
        elif level:
            i += 1
        elif text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        else:
            result.append(text[i])
            i += 1
    assert level == 0
    return ''.join(result)

owned_ledgers = [W / name for name in
    ['build_receipt.json', 'extension_build_receipt.json',
     'aggregation_build_receipt.json', 'source_budget_build_receipt.json']]
all_ledgers = owned_ledgers + [G / 'geometry_build_receipt.json']
modules = []
attempts = []
public_count = 0
for lp in all_ledgers:
    ledger = load(lp)
    assert ledger['historical_source_compiles'] == 0
    assert ledger['victory'] is False
    for entry in ledger['attempts']:
        for key, hk in [
            ('snapshot', 'snapshot_sha256'),
            ('source_snapshot', 'source_snapshot_sha256'),
            ('builder_snapshot', 'builder_snapshot_sha256'),
            ('launcher_snapshot', 'launcher_snapshot_sha256'),
            ('started_receipt', 'started_receipt_sha256'),
            ('log', 'log_sha256'),
            ('raw_finished_receipt', 'raw_finished_receipt_sha256')]:
            if entry.get(key) and entry.get(hk):
                check(entry[key], entry[hk])
        assert entry['exit_code'] in [0, 1]
        attempts.append({'ledger': str(lp), 'attempt': entry['attempt'],
            'source': entry['source'], 'source_sha256': entry['source_sha256'],
            'started_utc': entry['started_utc'], 'finished_utc': entry['finished_utc'],
            'exit_code': entry['exit_code'],
            'credited_pass': entry.get('credited_pass', entry['exit_code'] == 0),
            'log': item(entry['log']),
            'post_integrity_unchanged': entry.get('post_integrity', {}).get('all_unchanged'),
            'owner': 'ROLE4_geometry' if lp.parent == G else 'ROLE4'} )
    for name, success in ledger['successful_modules'].items():
        check(success['source'], success['source_sha256'])
        check(success['olean'], success['olean_sha256'])
        entry = next(e for e in ledger['attempts'] if e['attempt'] == success['attempt'])
        assert entry['exit_code'] == 0
        assert entry.get('credited_pass', True) is True
        if 'post_integrity' in entry:
            assert entry['post_integrity']['all_unchanged'] is True
        source = Path(success['source']).read_text(encoding='utf-8')
        code = lean_without_comments(source)
        assert not re.search(r'\b(sorry|admit|axiom|native_decide|trustMe)\b', code), name
        log = Path(entry['log']).read_text(encoding='utf-8')
        assert 'sorryAx' not in log and ': error:' not in log, name
        axiom_lists = re.findall(r'depends on axioms:\s*\[(.*?)\]', log, re.S)
        observed = set()
        for block in axiom_lists:
            used = {x.strip() for x in block.split(',') if x.strip()}
            assert used <= ALLOWED, (name, used)
            observed.update(used)
        printed = len(re.findall(r'^#print axioms\s+', source, re.M))
        recorded = len(axiom_lists) + log.count('does not depend on any axioms')
        assert printed == recorded, (name, printed, recorded)
        public_count += printed
        modules.append(dict(success, module=name, ledger=str(lp),
            log_sha256=sha(entry['log']), public_axiom_prints=printed,
            observed_axioms=sorted(observed), source_forbidden_tokens_absent=True,
            owner='ROLE4_geometry' if lp.parent == G else 'ROLE4'))

own_attempts = [a for a in attempts if a['owner'] == 'ROLE4']
own_modules = [m for m in modules if m['owner'] == 'ROLE4']
assert len(own_attempts) == 22 and len(own_modules) == 9
assert len(attempts) == 24 and len(modules) == 10
assert sum(a['exit_code'] == 0 for a in own_attempts) == 9
assert sum(a['exit_code'] != 0 for a in own_attempts) == 13
assert sum(a['exit_code'] == 0 for a in attempts) == 10

latest = load(W / 'source_budget_build_receipt.json')['attempts'][-1]
assert latest['exit_code'] == 0 and latest['credited_pass'] is True
post_checks = latest['post_integrity']['checks']
assert latest['post_integrity']['all_unchanged'] is True
for value in post_checks.values():
    assert value['unchanged'] is True
    check(value['path'], value['expected_sha256'])

# Preserve the first read receipt byte-for-byte; add newly completed reading scopes.
old_reads = load(W / 'read_input_sha256.json')
for group in ['primary_inputs', 'skills', 'dependency_source_scopes', 'compile_gates']:
    for value in old_reads[group]:
        check(value['path'], value['sha256'])
reads2 = {'round': 20, 'role': 'logicalROLE4', 'node': '14.5', 'at_utc': NOW,
    'original_read_receipt': item(W / 'read_input_sha256.json'),
    'additional_compile_gates': [item(B / f'.arbor/sessions/parity/.coordinator/messages/round20_formal4_authorization_phase{phase}.json',
        'FULL_TEXT_READ') for phase in [4, 6]],
    'geometry_final_source': item(G / 'FriableSourceGeometry.lean', 'FULL_TEXT_READ_TOOL105473_AFTER_ACTUAL_PASS02'),
    'geometry_previous_read': 'Partial source excerpts only before the final FULL read; no retroactive FULL claim.',
    'own_final_sources': [item(m['source'], 'OWNED_PROOF_SOURCE_WRITTEN_AND_READ') for m in own_modules],
    'numerical_bindings': '38 hash bindings from the canonical new actual PASS; no bank reexecution or mathematical Python.',
    'historical_bindings': '18 readonly hash bindings; targeted source scopes remain as originally recorded.',
    'old_Lean_reexecution': False, 'PASS_replay': False, 'new_mathematical_python': 0,
    'victory': False}
with (W / 'read_input_sha256_v2.json').open('x', encoding='utf-8') as handle:
    handle.write(json.dumps(reads2, indent=2, ensure_ascii=False) + '\n')

report_path = B / 'round20' / 'agent4_formalisation.md'
report_path.write_text((W / 'FINAL4.md').read_text(encoding='utf-8'), encoding='utf-8')

external_files = {G / 'FriableSourceGeometry.lean', G / 'FriableSourceGeometry.olean',
    G / 'geometry_build_receipt.json', G / 'compile_once.py', G / 'preparation_v2.json'}
geometry_entry = load(G / 'geometry_build_receipt.json')['attempts'][-1]
for key in ['source_snapshot', 'launcher_snapshot', 'started_receipt', 'raw_finished_receipt', 'stdout', 'stderr', 'log']:
    external_files.add(Path(geometry_entry[key]))
owned_files = sorted(p for p in W.rglob('*') if p.is_file()
    and p.name not in ['output_manifest.json', 'final_receipt.json'])
manifest = {'round': 20, 'role': 'logicalROLE4', 'node': '14.5', 'at_utc': NOW,
    'owned_files': [item(p) for p in owned_files],
    'report': item(report_path),
    'external_geometry_readonly': [item(p) for p in sorted(external_files)],
    'successful_modules': modules, 'execution_attempts': attempts,
    'original_inputs_read_receipt': item(W / 'read_input_sha256.json'),
    'additional_inputs_read_receipt': item(W / 'read_input_sha256_v2.json'),
    'no_old_producer_or_Lean_reexecution': True, 'PASS_replay': False,
    'whole_ledger_paid': False, 'victory': False}
with (W / 'output_manifest.json').open('x', encoding='utf-8') as handle:
    handle.write(json.dumps(manifest, indent=2, ensure_ascii=False) + '\n')

receipt = {'round': 20, 'role': 'logicalROLE4', 'node': '14.5', 'at_utc': NOW,
    'status': 'FINAL_AUXILIARY_SOURCE_FRIABLE_BUDGET_PASS_NOT_GLOBAL_WIN',
    'report': item(report_path), 'final4': item(W / 'FINAL4.md'),
    'manifest': item(W / 'output_manifest.json'),
    'compiler_failures': item(W / 'compiler_failures.md'),
    'read_input_sha256': item(W / 'read_input_sha256.json'),
    'read_input_sha256_v2': item(W / 'read_input_sha256_v2.json'),
    'owned_Lean_invocations': 22, 'owned_PASS': 9, 'owned_FAIL': 13,
    'external_geometry_Lean_invocations': 2, 'external_geometry_PASS': 1, 'external_geometry_FAIL': 1,
    'logical_ROLE4_total_Lean_invocations': 24, 'logical_ROLE4_total_PASS': 10,
    'logical_ROLE4_total_FAIL': 14, 'historical_Lean_invocations': 0,
    'new_mathematical_python': 0, 'numeric_bank_executions_by_ROLE4': 0,
    'source_forbidden_tokens_absent': True, 'all_PASS_axioms_standard_only': True,
    'public_axiom_prints_checked': public_count, 'PASS_replay': False,
    'successful_modules': modules,
    'source_budget': {'theorem': 'GoldbachRound20.Friable.SourceGeometry.actual_source_friable_absolute_cost_budget',
        'premise': 'SourceOnset N only: log N >= 10^24',
        'cost': 'actual friableThetaDemand(F0 or F1 on H19) + actual uniqueReciprocalCost1(F1)',
        'bound': 'N / (8192 * log N * log(log N))',
        'axis': 'theta aggregation; actual raw ABS local bound also proved, not added as another payment',
        'TK_discharged': True, 'source_geometry_discharged': True,
        'freestanding_small_mass_or_payment_premise': False},
    'latest_budget_execution': {'ledger': item(W / 'source_budget_build_receipt.json'),
        'attempt': latest['attempt'], 'started_utc': latest['started_utc'], 'finished_utc': latest['finished_utc'],
        'exit_code': latest['exit_code'], 'credited_pass': latest['credited_pass'],
        'post_integrity_unchanged': True, 'post_integrity_bindings_checked': len(post_checks),
        'log': item(latest['log'])},
    'F0_minus_F1_nonfriable_reciprocal_paid': False, 'source_H_to_whole_support_bridge': False,
    'whole_ledger_paid': False, 'Gamma_TA_capacity_paid': False,
    'independent_Judge20_executed': False, 'global_DN_target_proved': False, 'victory': False}
with (W / 'final_receipt.json').open('x', encoding='utf-8') as handle:
    handle.write(json.dumps(receipt, indent=2, ensure_ascii=False) + '\n')
print(json.dumps({'metadata_only': True, 'owned_modules': len(own_modules), 'all_modules': len(modules),
    'owned_Lean_attempts': len(own_attempts), 'all_Lean_attempts': len(attempts),
    'public_axiom_prints': public_count, 'post_integrity_bindings': len(post_checks),
    'owned_manifest_files': len(owned_files), 'report_sha256': sha(report_path),
    'manifest_sha256': sha(W / 'output_manifest.json'), 'final_receipt_sha256': sha(W / 'final_receipt.json'),
    'reads_v2_sha256': sha(W / 'read_input_sha256_v2.json'), 'victory': False}, ensure_ascii=False))
