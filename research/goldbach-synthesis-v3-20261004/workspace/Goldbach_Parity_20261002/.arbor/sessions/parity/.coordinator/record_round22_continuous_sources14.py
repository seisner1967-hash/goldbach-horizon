"""ROOT metadata only; preserve source handoffs, with no mathematical evaluation."""
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
    'round22/role3/global_h1_execution03/closure22.md': '66db74f839b6a551504efc4dcae3831dd832bad4206bf31960c065885c88eba6',
    'round22/role3/global_h1_execution03/closure_receipt22.json': '0d7b483056f75dde372b0e5c21a6cc9edf608a37bebb8a1fcfec515e90b331fe',
    'round22/role3/global_h1_execution03/decision_projection22.json': 'd76f6f9c373b6289e4c5466dd32bc98b2a091595724c9087b7839261d60e5b54',
    'round22/role3/discrete_circle_source22/revision02/DiscreteThermalProjection22.lean': '7ee2abb27d959f1511abb59e8425578b420d3e972a8d03eaff26635ac8fd581c',
    'round22/role3/discrete_circle_source22/revision02/source_review22.md': 'ff8764229a61cb1cf4b9cf2f7d66a50dcacbf95e0e5bd2d88250419ac8190bd9',
    'round22/role3/discrete_circle_source22/revision02/read_receipts22.json': '3fabab0aa54ea54ec3b875ef78710b277bd3f7dcde229c9c58257bf92f5843a4',
    'round22/judge5/discrete_source_review_revision02.md': 'bee48a1fdb3347206ede5998f412e4aeebfe26cde334163d7220a887c364c459',
    'round22/role3/phase_mellin_inversion_source22/ThermalGammaMellinInverse22.lean': '5271bbf9a9917a3ab61c6c7e0e747af4014e214b0867a9c81b43b5aa08fccec1',
    'round22/role3/phase_mellin_inversion_source22/source_contract22.md': '984f3e16d927b8d373b3c81af2848e18f77ffa7eb89efb7ab7c6ddf33accde01',
    'round22/role3/phase_mellin_inversion_source22/read_receipts22.json': 'a77e878bfc84be170ba4f8c52f743887d9afbcc57fd5cc82370f208ab51a6a0a',
    'round22/role4/circle_ntt_paper01/source_handoff22.json': 'fbbf4bef50bae5fb9de72e2bb923a3fbc0cfc03982a26abf2bb6f889002a1eab',
    'round22/role4/circle_ntt_paper01/projection_contract22_final.md': 'dd86c92c15e05febad687c240eb58d9dae2f930b646356f1dfe99e3bb35a680f',
    'round22/role4/circle_ntt_paper01/native_spec22_final.md': '6bc24ecfe96437e5c437fe003788194548b379c0c7bbf0dfed81f118c0eb322b',
    'round22/role4/circle_ntt_paper01/fixed_parameter_log_model22.py': '80718ee9c1306a974554a70322ad36648897216890f6747ed2ddede840421d98',
    'round22/role4/circle_ntt_paper01/next_theorem_obligations22.md': '78e0fe0b58dfee998fa4095164e109a1806c5237939f29b8e4f2c97ca35ccf72',
    'round22/role4/circle_ntt_paper01/read_sources22.json': '9acbec104f4e8fabd4097ca0a1e566509e81d03a7330e4da7a4598271286d241',
}
for relative, expected in bindings.items():
    assert sha(B / relative) == expected, relative
ntt = read(B / 'round22/role4/circle_ntt_paper01/source_handoff22.json')
assert ntt['status'] == 'PAPER_ALGORITHM_SPECIFICATION_NOT_PREPARED'
assert ntt['binding_count'] == len(ntt['bindings']) == 19
assert ntt['model']['functions_executed'] == 0 and not ntt['PREPARED']
assert not ntt['NTT_PASS'] and not ntt['WIN']
for row in ntt['bindings']:
    assert sha(Path(row['path'])) == row['sha256'], row['path']
closure = read(B / 'round22/role3/global_h1_execution03/closure_receipt22.json')
assert closure['status'] == 'THERMAL_TRACE_NUMERICAL_AUX_PASS_SOURCE_AUDITED'
assert closure['new_math_evaluations_for_documentation'] == 0
assert not closure['WIN']
cp_path = C / 'checkpoint.json'
cp = read(cp_path)
assert cp['official_auxiliary_validation']['modules'] == 75
assert cp['official_auxiliary_validation']['declarations'] == 1223
observation = {
    'schema': 'ROUND22_ROOT_CONTINUOUS_SOURCE_HANDOFFS14',
    'time_utc': datetime.now(timezone.utc).isoformat(),
    'status': 'SOURCE_PAPER_PARTIAL_PROGRESS_NOT_TARGET_COMPLETION',
    'bound_files': bindings,
    'NTT_handoff_bindings_verified': 19,
    'ROOT_read_receipts': {
        'numeric03_closure': 'FULLb451f3',
        'numeric03_decision_non_catalogue_copy': 'FULL493a6a',
        'discrete29_revision02_docs': 'FULL529a64',
        'discrete29_revision02_independent_review': 'FULLe2b8f8',
        'NTT_final_contract': 'FULL41c53d',
        'NTT_native_and_next_lemma_specs': 'FULL29e446',
        'NTT_handoff_reads_and_model': 'FULLfa6e56',
        'scalar_Mellin11_contract': 'FULL5b50f4',
        'scalar_Mellin11_reads': 'FULL295727',
        'Identity13_actual_log_receipt': 'FULL5d53bf',
        'Identity13_adjudication_completion': 'FULLd948cf',
    },
    'numeric03_status': closure['status'],
    'numeric03_is_coefficient_projection_test': False,
    'numeric03_certification_level': closure['level'],
    'Identity13_status': 'ACTUAL_AUX_PASS20_OBSERVED_ROOT75_1223',
    'discrete29_revision02_status': 'SOURCE_ONLY_INDEPENDENT_REVIEWED_NOT_PREPARED',
    'next_Lean_scope': 'Discrete29 revision02 selected for metadata preparation; no gate or invocation',
    'scalar_Mellin11_status': 'SOURCE_ONLY_INDEPENDENT_REVIEW_PENDING',
    'NTT_status': ntt['status'],
    'NTT_new_Lean_or_numerical_runs': 0,
    'NTT_native_producer_checker_and_practical_resources': 'OPEN',
    'roles': 'Six research roles timesliced; at most three collaborating actors plus ROOT',
    'ROOT_compiler_invocations': 0, 'ROOT_numerical_invocations': 0,
    'official_credit_added': 0, 'H1_paid': False,
    'coefficient_N_numerically_paid': False, 'D_N_paid': False, 'WIN': False,
}
path = C / 'messages/round22_continuous_sources14_observation.json'
with path.open('x', encoding='utf-8') as stream:
    json.dump(observation, stream, ensure_ascii=False, indent=2)
    stream.write('\n')
for actor in cp['in_flight_executors']:
    if actor['role'] == 3:
        actor['status'] = 'NUMERIC03_CLOSED_SOURCE_LOG_QUANTIZATION_ACTIVE_DISCRETE29_REV02_FROZEN'
    if actor['role'] == 4:
        actor['status'] = 'NTT_PAPER_FROZEN_NATIVE_READONLY_INVENTORY_SOURCE_PREPARATION_ACTIVE'
    if actor['role'] == 5:
        actor['status'] = 'BATCH13_CLOSED_AUX_PASS_DISCRETE29_AND_NTT_SOURCE_REVIEW_ACTIVE'
cp['phase'] = 'ROUND22_CONTINUOUS_IDENTITY_PAID_NUMERIC_ZERO_CLOSED_COEFFICIENT_EVALUATOR_OPEN'
cp['previous_goal_turn_evidence'].append(str(path.relative_to(B)))
cp_path.write_text(json.dumps(cp, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
with (B / 'REPORT.md').open('a', encoding='utf-8') as stream:
    stream.write('\nBoucle22 : Identity13 effectivement AUX_PASS20 et Envelope11 AUX_PASS42 ; officiel75modules/1223aux. Banque03 phase zéro close, accord numérique SOURCE/PAPER avec contrôle structurel, E_total<1e-8<tau et3mutants disjoints selon les reçus du ROLE6 ; elle ne teste pas le coefficient de Goldbach. Discret29 révision02 et inversion Gamma-Mellin11 demeurent SOURCE sans compilation. Contrat CIRCLE NTT final lié par19bindings, N=M=1e8/K=2^27/S=2^58/a=0 fini, enveloppe et gardes définies ; producteur/checker natifs, précision formelle et contrôles effectifs encore ouverts. Six rôles sont répartis dans le temps ; H1 global/D_N/WIN restent ouverts.\n')
print(json.dumps({'observation': str(path), 'sha256': sha(path), 'metadata_only': True}))
