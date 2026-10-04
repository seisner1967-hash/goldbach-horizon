"""ROOT metadata only: retain source/paper handoffs without mathematical credit."""
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path

B = Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C = B / '.arbor/sessions/parity/.coordinator'

def sha(path):
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1048576), b''):
            digest.update(block)
    return digest.hexdigest()

def read(path):
    return json.loads(path.read_text(encoding='utf-8-sig'))

bindings = {
    'round22/role3/coefficient_projection_contract_source22/coefficient_circle_contract22_revision02.md': '9e6d349ff283b1914750c05473d50982795a641cf6b429369504fc7b9ef73ddf',
    'round22/role3/coefficient_projection_contract_source22/read_receipts22.json': 'fc75023d6cdd5e9333ad281f2b86276f5b3a210ba7c8d6fe8b7defb9ac4aa50e',
    'round22/judge5/coefficient_circle_paper_review22.md': 'bd4161cc33953e41c401631a3d92d8c9480f9cbdb035b86507ff7eb4bc01b6d9',
    'round22/role4/phase_mellin_re2_source01/source_handoff22.json': 'edb479ea2c17f428132ce82fd7f022eda743b44ada87dba319c45bb355da898e',
    'round22/role4/phase_mellin_re2_source01/source_contract22.md': '11bf1c0bcf25b274296844e77474a85944710f1e7e85e12b125fd066e34fb156',
    'round22/role4/phase_mellin_re2_source01/read_sources22.json': '28fb9cf840a2df5a79865cb3cc7e0820ff330dc72884de5923c6ef9c9270837f',
    'round22/judge5/batch11/completion_receipt.json': '32f2894cc8d9e3fffa232c9acf58ce039373108194bb253590921caf38c53a99',
    'round22/judge5/batch11/batch11_attempt01/receipt.json': '0b25b00e57663172cacc25945ad232d807ff58cd3c34bae6f2e64bf2e852f62b',
}
for relative, expected in bindings.items():
    assert sha(B / relative) == expected, relative
handoff = read(B / 'round22/role4/phase_mellin_re2_source01/source_handoff22.json')
assert handoff['status'] == 'SOURCE_ONLY_NOT_PREPARED_NOT_COMPILED'
assert handoff['new_declarations'] == 49
assert handoff['new_theorems'] == 39 and handoff['new_definitions'] == 10
assert handoff['official_credit_added'] == 0
for row in handoff['bindings']:
    assert sha(Path(row['path'])) == row['sha256'], row['path']
cp_path = C / 'checkpoint.json'
cp = read(cp_path)
assert cp['official_auxiliary_validation']['modules'] == 74
assert cp['official_auxiliary_validation']['declarations'] == 1203
observation = {
    'schema': 'ROUND22_ROOT_CONTINUOUS_SOURCE_HANDOFFS11',
    'time_utc': datetime.now(timezone.utc).isoformat(),
    'status': 'SOURCE_PAPER_PARTIAL_PROGRESS_NOT_TARGET_COMPLETION',
    'bound_files': bindings,
    'Re2_handoff_bindings_verified': len(handoff['bindings']),
    'ROOT_read_receipts': {
        'circle_contract': 'FULLc43cd0', 'circle_reads': 'FULLa33671',
        'independent_circle_review': 'FULL169b65', 'Re2_handoff': 'FULLaa3e19',
        'Re2_contract': 'FULL211c31', 'Re2_reads': 'FULLeca7e1',
        'actual_Lean_receipt11': 'FULL89181e', 'completion11': 'FULLcf04af',
    },
    'circle_status': 'PAPER_REVIEWED_PRODUCER_RESOURCES_DISCRETE_ORTHOGONALITY_OPEN',
    'circle_has_actual_N_1e8_evaluation': False,
    'Re2_status': '49_SOURCE_DECLARATIONS_NOT_COMPILED_INDEPENDENT_REVIEW_PENDING',
    'Lean11_status': '42_ENVELOPE_PASS_20_IDENTITY_FAIL_TECHNICAL',
    'next_Lean_scope': 'Identity revision02 only, 20 declarations, Envelope PASS11 readonly',
    'numeric03_status': 'ONE_ACTUAL_ROLE6_CHILD_RUNNING_NO_FINAL_RESULT_OBSERVED',
    'numeric03_is_coefficient_projection_test': False,
    'roles': 'Six roles timesliced, at most three collaborating actors plus ROOT',
    'ROOT_compiler_invocations': 0, 'ROOT_numerical_invocations': 0,
    'official_credit_added': 0, 'H1_paid': False, 'D_N_paid': False, 'WIN': False,
}
path = C / 'messages/round22_continuous_sources11_observation.json'
with path.open('x', encoding='utf-8') as stream:
    json.dump(observation, stream, ensure_ascii=False, indent=2)
    stream.write('\n')
for actor in cp['in_flight_executors']:
    if actor['role'] == 3:
        actor['status'] = 'ROLE6_NUMERIC03_RUNNING_AND_ROLE3_DISCRETE_CIRCLE_SOURCE'
    if actor['role'] == 4:
        actor['status'] = 'IDENTITY_REVISION02_SOURCE_REPAIR_PRIORITY_RE2_49_FROZEN'
    if actor['role'] == 5:
        actor['status'] = 'BATCH11_CLOSED_RE2_SOURCE_REVIEW_PENDING_IDENTITY12_HANDOFF'
cp['previous_goal_turn_evidence'].append(str(path.relative_to(B)))
cp_path.write_text(json.dumps(cp, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
with (B / 'REPORT.md').open('a', encoding='utf-8') as stream:
    stream.write('\nCercle coefficient N : contrat révision02 et revue indépendante PAPER conservés ; aucune évaluation du coefficient à N=1e8, aucun producteur préparé. Les coûts et gardes restent explicites. Re2 :49 déclarations SOURCE non compilées, revue indépendante en cours. Prochain lot Lean réservé à Identity révision02 avec Envelope PASS11 readonly. Banc03 phase zéro continue son unique enfant ; aucun résultat final observé. Officiel74/1203 inchangé ; H1/D_N/WIN ouverts.\n')
print(json.dumps({'observation': str(path), 'sha256': sha(path), 'metadata_only': True}))
