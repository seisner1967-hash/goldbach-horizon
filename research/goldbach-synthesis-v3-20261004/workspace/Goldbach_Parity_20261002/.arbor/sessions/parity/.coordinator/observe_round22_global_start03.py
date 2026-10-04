"""ROOT observes launch metadata only; no interval values or proof evaluator."""
import hashlib
import json
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

B = Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C = B / '.arbor/sessions/parity/.coordinator'
T = B / 'round22/role3/performance_sourcepack02/launch_prepare03'
A = T / 'actual_attempt01'
G = C / 'messages/round22_global_thermal_h1_authorization02.json'

def read(path):
    return json.loads(path.read_text(encoding='utf-8-sig'))

def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1048576), b''):
            h.update(block)
    return h.hexdigest()

assert sha(G) == '6847fff85e007303594f3257f2a027a7a4ccfb31393674338ebae22307f7a5c9'
assert sha(T / 'preparation22.json') == '8d08bc4db8f702a53ae3340a2ba9102969caf7ea7995aa282638cd0e84919433'
assert sha(A / 'START.json') == '7e8bdc07bed4d5868bac50bad7c09fbd23cedd80f59babe732b99cc7423eeb6f'
assert sha(A / 'child_START.json') == 'd1dfab90daffff388138495a9f0a3070fa37969a4d0f079e9d8d16db61f56354'
start, childstart, pre, context = map(read, (A / 'START.json', A / 'child_START.json', A / 'PREEXEC.json', A / 'child_context.json'))
prep = read(T / 'preparation22.json')
assert start['token'] == childstart['token'] == pre['token'] == context['token'] == 'b104f84087a84a55a8ebfccdf5558a21'
assert sha(A / 'child_context.json') == start['context_sha256'] == childstart['context_sha256'] == pre['context_sha256']
assert start['PREEXEC_complete'] is start['no_retry'] is pre['all_captures_verified'] is True
assert start['max_children'] == 1 and childstart['source_imports_started'] == 0
assert start['command'][1:6] == ['-I', '-S', '-B', '-X', 'utf8']
assert pre['archives']['unchanged'] and pre['archives']['file_count'] == 3089
assert pre['closed_attempt']['unchanged'] and pre['closed_attempt']['numeric_values_reused'] is False
assert len(pre['bindings']) == len(prep['bindings']) == 1016
assert len(pre['captures']) == 1018
for row in pre['bindings']:
    assert row['unchanged'] and sha(Path(row['path'])) == row['expected_sha256'] == row['actual_sha256']
for row in pre['captures']:
    assert sha(Path(row['original'])) == sha(Path(row['copy'])) == row['sha256']
    assert Path(row['copy']).stat().st_size == row['bytes']
assert context['limits'] == prep['limits'] and context['limits']['max_wall_seconds'] == 10800
assert context['future_evaluation_level'] == 'PAPER_AUDITED_DIRECTED_INTERVAL_PRODUCER_WITH_INDEPENDENT_STRUCTURAL_CHECKER'
assert context['analytic_certification_level'] == 'PAPER_DERIVATIONS_WITH_EXACT_DOMAINS_NOT_LEAN_CERTIFICATION'
assert context['structural_PASS_is_enclosure_PASS'] is False
cp_path = C / 'checkpoint.json'
cp = read(cp_path)
assert cp['official_auxiliary_validation']['modules'] == 73
assert cp['official_auxiliary_validation']['declarations'] == 1161
observation = dict(schema='ROUND22_GLOBAL_START03_ROOT_METADATA_OBSERVATION',
    time_utc=datetime.now(timezone.utc).isoformat(), status='ACTUAL_STARTED_NO_NUMERICAL_VERDICT',
    gate_sha256=sha(G), preparation_sha256=sha(T / 'preparation22.json'),
    START_sha256=sha(A / 'START.json'), child_START_sha256=sha(A / 'child_START.json'),
    PREEXEC_sha256=sha(A / 'PREEXEC.json'), context_sha256=sha(A / 'child_context.json'),
    actual_START=start['time_utc'], child_START=childstart['time_utc'], token=start['token'],
    mathematical_children_started_by_ROLE6=1, maximum_children=1, retries=0,
    bindings_verified=1016, captures_verified=1018, protected_archives_PRE=3089,
    closed_bank_integrity_PRE=True, previous_numeric_values_reused=False,
    ROOT_FULL_read_receipts='START and childSTART ef9d2e FULL; stdout1b415a TARGETED last4lines only; all PRE metadata parsed and captures hashed, no RAWFULL inventory or interval audit claim',
    limits=prep['limits'], future_evaluation_level=context['future_evaluation_level'],
    analytic_certification_level=context['analytic_certification_level'],
    structural_PASS_is_enclosure_PASS=False, ROOT_numeric_invocations=0, ROOT_Lean_invocations=0,
    H1_FORMAL='OPEN', COEFFICIENT_N='OPEN', D_N='UNPAID', WIN=False)
out = C / 'messages/round22_global_start03_observation.json'
with out.open('x', encoding='utf-8') as stream:
    json.dump(observation, stream, ensure_ascii=False, indent=2)
    stream.write('\n')
insight = ('Global numeric03 actual START14:48:16UTC, one ROLE6 child10800s/2GiB/no retry; '
    '1016inputs/1018captures/3089archives and closed bank02 PRE intact. Independent SOURCE/PAPER review638b… '
    'binds21sources/9aliases972runtime and exact tools/resources. No final numerical agreement, Etotal or mutants yet. '
    'Official73modules1161aux; projection62SOURCE awaiting lot10, Scaled10 repairSOURCE awaiting lot11. '
    'Uniform-phase Mellin note PAPER only, no angular producer; H1/coefficientN/D_N/WIN open.')
helper = r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py'
for command, extra in (
    ('record', ['--node-id','15.3','--raw-report',insight,'--score','0','--insight',insight,
                '--result','GLOBAL_NUMERIC03_RUNNING_SOURCE_REVIEWED_NO_VERDICT','--no-propagate']),
    ('update', ['--node-id','15.3','--status','running','--insight',insight]),
):
    result = subprocess.run([sys.executable,'-B','-X','utf8',helper,command,'--cwd',str(B),'--run-name','parity',*extra],
        capture_output=True, text=True, encoding='utf-8')
    assert result.returncode == 0, (result.stdout, result.stderr)
cp['phase'] = 'ROUND22_GLOBAL_NUMERIC03_RUNNING_PROJECTION_SOURCE_PREPARATION'
cp['last_progress'] = insight
cp['previous_goal_turn_evidence'].append(str(out.relative_to(B)))
for actor in cp['in_flight_executors']:
    if actor['role'] == 3:
        actor['status'] = 'ROLE6_GLOBAL_NUMERIC03_RUNNING_ONE_CHILD_SOURCE_REPAIRS_DISTINCT'
    if actor['role'] == 5:
        actor['status'] = 'BATCH09_CLOSED_PROJECTION_BATCH10_SOURCE_PREPARATION'
cp_path.write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
with (B / 'REPORT.md').open('a',encoding='utf-8') as stream:
    stream.write('\nBanque globale03 réellement démarrée14:48:16UTC, un enfant ROLE6, plafond10800s/2GiB et zéro retry. '
        'Revue indépendante SOURCE/PAPIER des21sources et cinq outils close ;1016liaisons/1018captures et archives historiques '
        'vérifiées avant START, ancien calcul clos conservé. Aucun accord/Etotal/mutants encore acquis. '
        'Le banc reste en phase zéro ; la projection additive et son enveloppe62déclarations SOURCE attendent le lot10. '
        'La note Mellin uniforme est PAPER seulement et expose une dette de hauteur/quadrature àa=1/N. '
        'Officiel73modules/1161déclarations auxiliaires ; H1 formel, coefficientN, D_N et victoire ouverts.\n')
print(json.dumps(observation,ensure_ascii=False,indent=2))
