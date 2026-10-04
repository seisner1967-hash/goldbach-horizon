"""ROOT metadata-only observation of an incomplete, resource-limited bank."""
import argparse, hashlib, json, subprocess, sys
from datetime import datetime, timezone
from pathlib import Path

B = Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C = B / '.arbor/sessions/parity/.coordinator'
P = B / 'round22/role4/h1_global_numeric/launch_prepare02'
A = P / 'actual_attempt01'

def read(p):
    return json.loads(p.read_text(encoding='utf-8-sig'))

def sha(p):
    h = hashlib.sha256()
    with p.open('rb') as f:
        for block in iter(lambda: f.read(1048576), b''):
            h.update(block)
    return h.hexdigest()

ap = argparse.ArgumentParser()
ap.add_argument('--receipt-sha', required=True)
ap.add_argument('--ROOT-full-read-receipts', required=True)
args = ap.parse_args()
assert sha(A / 'receipt.json') == args.receipt_sha
r = read(A / 'receipt.json')
assert r == read(A / 'FIN.json')
assert r['status'] == 'GLOBAL_THERMAL_ATTEMPT_FAIL'
assert r['resource_failure'] == 'MAX_WALL_SECONDS' and r['control_error'] is None
assert r['mathematical_children_started'] == 1 and r['retries'] == r['old_bank_replays'] == r['Lean_invocations'] == 0
assert r['post_integrity'] and not r['output_errors']
assert r['formal_H1'] == 'OPEN' and r['coefficient_N'] == 'OPEN' and r['D_N'] == 'UNPAID' and not r['WIN']
assert not r['structural_PASS_is_enclosure_PASS'] and not r['structural_checker_alone_is_primitive_certificate']
assert r['resource_limits']['max_wall_seconds'] == 3600
prep = read(P / 'preparation22.json')
assert sha(P / 'preparation22.json') == r['preparation_sha256'] == '60f88dc205fd8f9c6a4953bf9bc5b5d0d38522329fde9399c9b75118e6b12cba'
gate = C / 'messages/round22_global_thermal_h1_authorization01.json'
assert sha(gate) == r['root_gate_sha256'] == 'e826200adca1e52b6362667a7c8e7ef7d80a1e75e4302d4c1163bf77dfe62b8d'
pre, post = read(A / 'PREEXEC.json'), read(A / 'POSTEXEC.json')
start, childstart = read(A / 'START.json'), read(A / 'child_START.json')
assert pre['token'] == start['token'] == childstart['token'] == r['token']
assert start['time_utc'] == r['actual_START'] and start['PREEXEC_complete'] and start['no_retry']
assert start['context_sha256'] == sha(A / 'child_context.json') == pre['context_sha256']
assert post['all_intact'] and post['preparation_intact'] and post['root_gate_intact'] and post['context_intact']
assert len(prep['bindings']) == len(pre['bindings']) == len(post['bindings']) == 1003
assert len(pre['captures']) == len(post['captures']) == 1005 and pre['all_captures_verified']
expected = {x['path']: x for x in prep['bindings']}
for rows in (pre['bindings'], post['bindings']):
    assert set(expected) == {x['path'] for x in rows}
    for x in rows:
        e = expected[x['path']]
        assert x['unchanged'] and x['actual_sha256'] == x['expected_sha256'] == e['sha256'] == sha(Path(x['path']))
        assert Path(x['path']).stat().st_size == x['bytes'] == e['bytes']
post_captures = {x['path']: x for x in post['captures']}
assert set(post_captures) == {x['copy'] for x in pre['captures']}
for x in pre['captures']:
    q = post_captures[x['copy']]
    assert q['unchanged'] and sha(Path(x['copy'])) == sha(Path(x['original'])) == x['sha256'] == q['expected_sha256'] == q['actual_sha256']
    assert Path(x['copy']).stat().st_size == x['bytes'] == q['bytes']
registry = B / 'round22/previous_artifacts_sha256.json'
assert sha(registry) == '875cebdd8e510fe3341b05009a76991801777b2a060a07229c5323033226ba99'
archive = read(registry)
assert archive['file_count'] == len(archive['sha256']) == 3089
for relative, digest in archive['sha256'].items():
    p = (B / relative).resolve()
    assert p.is_relative_to(B.resolve()) and sha(p) == digest
for inventory in (pre['archives'], post['archives']):
    assert inventory['unchanged'] and inventory['file_count'] == 3089 and inventory['registry_sha256'] == sha(registry)
for x in r['outputs']:
    p = Path(x['path']).resolve()
    assert p.is_relative_to(A.resolve()) and sha(p) == x['sha256'] and p.stat().st_size == x['bytes']
absent = ['child_FIN.json', 'numeric_data/global_thermal_result.json', 'numeric_data/structural_checker_result.json', 'numeric_data/new_arithmetic.ndjson']
assert all(not (A / name).exists() for name in absent)
progress_lines = (A / 'child.stdout.log').read_text(encoding='utf-8').splitlines()
progress = [json.loads(line) for line in progress_lines if line.strip()]
last = next(x for x in reversed(progress) if 'progress' in x)
assert last['progress']['volet'] == 'vertical'
assert last['progress']['nodes'] < 204800
cpp = C / 'checkpoint.json'
cp = read(cpp)
official = cp['official_auxiliary_validation']
o = dict(schema='ROUND22_GLOBAL_RESOURCE_CLOSURE_ROOT_METADATA_OBSERVATION', time_utc=datetime.now(timezone.utc).isoformat(),
    status='RESOURCE_LIMIT_CLOSED_INCOMPLETE_NOT_IDENTITY_FALSIFICATION', receipt_sha256=args.receipt_sha,
    actual_START=r['actual_START'], child_process_FINISH=r['child_process_FINISH'], actual_FINISH=r['actual_FINISH'],
    token=r['token'], mathematical_children_started=1, resource_failure=r['resource_failure'],
    inputs_verified=1003, captures_verified=1005, archives_verified=3089, all_bytes_preserved=True,
    outputs=r['outputs'], absent_final_outputs=absent, last_emitted_progress=last,
    ROOT_FULL_read_receipts=args.ROOT_full_read_receipts,
    inventory_read_scope='All JSON entries parsed and bytes hashed; raw FULL inventories and node catalogue text not claimed',
    identity_agreement='NOT_REACHED', effective_total_error='NOT_OBSERVED', mutant_comparison='NOT_REACHED',
    official_modules=official['modules'], official_declarations=official['declarations'],
    root_numeric_invocations=0, root_Lean_invocations=0, old_bank_replays=0, retries=0,
    H1_paid=False, coefficient_N_paid=False, D_N_paid=False, WIN=False)
op = C / 'messages/round22_global_resource_closure_observation.json'
with op.open('x', encoding='utf-8') as f:
    json.dump(o, f, ensure_ascii=False, indent=2); f.write('\n')
insight = ('Global thermal bank02 closed MAX_WALL_SECONDS3600s, one mathematical child/no retry; '
    + str(last['progress']['nodes']) + '/204800 vertical nodes emitted, no final agreement/checker/arithmetic/mutants. '
    '1003inputs/1005captures/3089archives and bound outputs intact. Resource failure is not an identity/parity counterexample. '
    'Optimized SOURCE version requires independent review and distinct gate; H1/coefficientN/D_N/WIN open.')
helper = r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py'
for command, extra in [('record', ['--node-id', '15.3', '--raw-report', insight, '--score', '0', '--insight', insight,
    '--result', 'RESOURCE_LIMIT_INCOMPLETE_NOT_MATHEMATICAL_FAIL', '--no-propagate']),
    ('update', ['--node-id', '15.3', '--status', 'running', '--insight', insight])]:
    result = subprocess.run([sys.executable, '-B', '-X', 'utf8', helper, command, '--cwd', str(B), '--run-name', 'parity', *extra],
        capture_output=True, text=True, encoding='utf-8')
    assert result.returncode == 0, (result.stdout, result.stderr)
cp['phase'] = 'ROUND22_GLOBAL_NUMERIC_RESOURCE_CLOSED_FRESH_SOURCE_REVIEW_PENDING'
cp['last_progress'] = insight
cp['previous_goal_turn_evidence'].append(str(op.relative_to(B)))
for actor in cp['in_flight_executors']:
    if actor['role'] == 3:
        actor['status'] = 'ROLE6_GLOBAL_NUMERIC_CLOSED_RESOURCE_SOURCE_OPTIMIZATION_DISTINCT'
cpp.write_text(json.dumps(cp, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
with (B / 'REPORT.md').open('a', encoding='utf-8') as f:
    f.write('\nBanque thermique globale02 : clôture effective MAX_WALL_SECONDS après3600s, un enfant et aucun retry ; '
        + str(last['progress']['nodes']) + '/204800 nœuds verticaux émis. Calcul incomplet : aucune comparaison globale, '
        'Etotal effectif, vérification finale ou mutants observés. Toutes1003liaisons/1005captures/3089archives conservées. '
        'Échec de ressources, sans falsification de l’identité ni conclusion sur la parité. '
        'Une version SOURCE optimisée distincte doit subir une revue indépendante avant tout nouveau contrat/gate. '
        'Officiel' + str(official['modules']) + '/' + str(official['declarations']) + ' auxiliaires ; H1/coefficientN/D_N/WIN ouverts.\n')
print(json.dumps(o, ensure_ascii=False, indent=2))
