"""Read-only observation of the new typei result, followed by coordinator bookkeeping."""
import sys
sys.dont_write_bytecode = True
from pathlib import Path
import json, hashlib

root = Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
coord = root / '.arbor/sessions/parity/.coordinator'
out = coord / 'messages/round16_root_typei_observation.json'
assert not out.exists(), 'Observation already recorded; inspect it.'
expected = {
    'round16/agent1_bilinear_covariance.md': 'f60827e9e72e73cde93512448bd6acc289807d43180b844040326456a5e2d754',
    'round16/agent2_or_incidence.md': 'f6f12c39afc445ce82482850c34482fa2450b9df1df7dbeef2089574b308128b',
    'round16/typei_checks.py': 'e59caddb2a123374a70e85686cdbe5d00677317b48d9f8c6fc2b7bbd934f9a6e',
    'round16/typei.json': 'a1443ee83b346fc6a3cf330a09bf07a05a4e4a5d00230ed418aebeb8a9b65b1c',
    'round16/isolated_typei/typei.json': 'a1443ee83b346fc6a3cf330a09bf07a05a4e4a5d00230ed418aebeb8a9b65b1c',
    'round16/role6/typei_attempt01.log': '4b9eb9f6c550fbc09efe909c42ec56cae5f10a5cc1cb5c1235db3e14751a28b0',
    'round16/role6/typei_isolated_replay.log': '4b9eb9f6c550fbc09efe909c42ec56cae5f10a5cc1cb5c1235db3e14751a28b0',
}
for rel, digest in expected.items():
    assert hashlib.sha256((root / rel).read_bytes()).hexdigest() == digest, rel
canonical = json.loads((root / 'round16/typei.json').read_text(encoding='utf-8'))
replay = json.loads((root / 'round16/role6/typei_replay_receipt.json').read_text(encoding='utf-8'))
launch = json.loads((root / 'round16/role6/typei_canonical_success.json').read_text(encoding='utf-8'))
assert launch['attempt'] == 1 and launch['exit_code'] == replay['exit_code'] == 0
assert replay['bytes_identical'] and replay['all_fields_identical']
assert canonical['A_beta'] == 216 and canonical['A_classes_mod3'] == [0,106,110]
assert canonical['unit_counts']['J'] == 51948
assert canonical['TypeI3_exact']['uniform_drift_Af_minus_rho_Jf'] == '38'
assert canonical['TypeI3_exact']['corrected_drift_Af_minus_rho_star_Jf'] == '2'
assert canonical['theta_prime_counts_classes'] == [5067,5079,0]
assert all(canonical['sign_certificates'][x]['sign'] == 'NEGATIVE' for x in ['Gamma', 'Gamma_star', 'L3'])
assert len(canonical['raw_Lambda_N']['proper_power_records_complete']) == 9
assert not canonical['D_W_kernels_recomputed'] and not canonical['victory']
bindings = dict(expected)
for rel in ['round16/shared.py', 'round16/role6/typei_replay_receipt.json', 'round16/role6/typei_canonical_success.json', '.arbor/sessions/parity/.coordinator/messages/round16_primary_source_context.md']:
    bindings[rel] = hashlib.sha256((root / rel).read_bytes()).hexdigest()
receipt = {
    'status': 'ROOT_OBSERVED_NEW_TYPEI_CANONICAL_AND_ISOLATED_RESULTS_NO_REEXECUTION',
    'files_sha256': bindings,
    'full_sources_read_by_root': ['round16/typei_checks.py', 'round16/shared.py', 'round16/agent1_bilinear_covariance.md', 'round16/agent2_or_incidence.md'],
    'producer_invoked_by_root': False, 'Lean_invoked_by_root': False,
    'canonical_attempt': 1, 'canonical_exit_code': 0, 'isolated_exit_code': 0,
    'A':216, 'uniform_drift':38, 'corrected_drift':2, 'proper_powers':9,
    'Gamma_Gamma_star_L3': 'ALL_STRICTLY_NEGATIVE_FINITE_ONLY',
    'conservation_flag_scope': 'numeric_contract_round16_launched and mathematical_identity_round16_certified in conservation.verify are static preflight-scope flags, not global execution tracking. Actual new launches are bound by canonical/replay receipts.',
    'independent_Judge16_pending': True, 'anchor_Lean_final_pending': True,
    'global_D_N': False, 'victory':False,
}
out.write_text(json.dumps(receipt, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')
cp_path = coord / 'checkpoint.json'
cp = json.loads(cp_path.read_text(encoding='utf-8'))
cp['phase'] = 'ROUND16_ANCHOR_FORMALIZATION_AND_SECOND_NUMERICAL_CONTRACT'
cp['in_flight_executors'] = [
    'round13_formal3_switch:role6 second new complete small-core bank and frozen numerical reports',
    'round16_formal3_anchor:role3 actual Euler-tail/singularSeries anchor',
    'round16_formal4_margin:role4 harmonic/logarithmic margin and small cases'
]
cp['last_progress'] += ' FINAL2_16 frozen f6f12c39... Npairpositive realtprod anchor A7; both newbanks explicitly selected. Formalizers3/4 dispatchedsplit Euler-tail vsH-logmargin. RootFULLread typei/shared/FINAL1/2 andcanonical/replayreceipts, actualnewbank1attempt1exit0 anduniqueisolatedidentical. A216/J51948, classes0/106/110, uniformdrift38 corrected2 difference36, theta5067/5079/0, nine rawproperpowers, Gamma/Gammastar/L3 allNEGfinite. NoD/W/sourceboundcalledinbank1. Scope caveat staticconservation preflightflags recorded; actuallaunch receipts authoritative. No16 LeanFINALorindependentJudge yet; secondbankpending.'
for rel in ['round16/typei_checks.py','round16/typei.json','round16/role6/typei_replay_receipt.json', '.arbor/sessions/parity/.coordinator/messages/round16_primary_source_context.md', '.arbor/sessions/parity/.coordinator/messages/round16_root_typei_observation.json']:
    if rel not in cp['previous_goal_turn_evidence']:
        cp['previous_goal_turn_evidence'].append(rel)
cp_path.write_text(json.dumps(cp,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
report = root / 'REPORT.md'
text = report.read_text(encoding='utf-8')
marker = '### Sélection16 et premier résultat nouveau observé'
assert marker not in text
text += '''
### Sélection16 et premier résultat nouveau observé

Les deux mécanismes16 sont sélectionnés sous13.8 et14.1 après lecture entière des rapports et contraintes fraîches. FINAL1 est gelé SHA f60827e9e72e73cde93512448bd6acc289807d43180b844040326456a5e2d754 ; FINAL2 SHA f6f12c39afc445ce82482850c34482fa2450b9df1df7dbeef2089574b308128b. Le rôle1 dérive un défaut TypeI3 de taille principale pour sa référence uniforme, puis conserve la correction locale et la covariance résiduelle. Le rôle2 donne par écrit la marge S(N)-logp0≥1/144 pour le premier impair minimal absent d'un N pair positif ; son signe source reclassifie une sous-famille existante sans minorer ses incidences. Les formaliseurs3/4 sont lancés sur le vrai produit eulérien et la marge harmonique, sans postuler la marge.

Le banc1 neuf complet d77 passe à son premier essai puis dans son unique copie isolée, identique en octets et champs. Sur129870 entiers, J51948 et β216 avec classes0/106/110 ; le drift uniforme38 devient2 après correction, différence36. Les vrais premiers candidats ont les comptes5067/5079/0 ; neuf properpowers raw restent présents. Γ, Γ corrigée et L3 sont strictement négatifs dans cette fenêtre. Aucun kernel D/W ni estimateur source n'est appelé pour cette question locale. Root a lu les nouvelles sources, rapports, logs et reçus, et vérifié leurs empreintes sans lancer le producteur. L'audit indépendant16 reste à faire.

Le second banc sélectionné garde tous les petits cœurs physiques sous leur cap98 et tous qpremiers dans1000100..1000300, avec e1/e3 dépensés une fois. Il est en préparation/exécution par le rôle6, sans résultat présumé. Les champs de conservation issus du préflight sont statiques et ne suivent pas les nouveaux lancements ; les reçus d'exécution font foi pour ceux-ci. Aucun Lean final16 ni victoire n'est annoncé. Γ/TypeII, F6 et capacité globale restent ouverts ; la cible D_N≤N/(256u ell) reste non démontrée.
'''
report.write_text(text,encoding='utf-8')
print('ROOT16_TYPEI_OBSERVATION_RECORDED; no numerical producer or Lean invoked.')
