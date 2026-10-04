"""Record real selections and accepted role dispatches18; no math execution."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
from hashlib import sha256
import json
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C=B/'.arbor/sessions/parity/.coordinator'
def read(p):return json.loads(p.read_bytes())
files={'round18/agent1_calibrated_typeii.md':'228766a630e37e4cee7f92bc46cb862582da59379b15653f4c00abcbc37313f0',
 'round18/agent2_capacity_incidence.md':'48dbcc5875c140d6d4991fa7d6cd58749048e3cf151e35f476893c27f81ae595'}
for name,h in files.items():assert sha256((B/name).read_bytes()).hexdigest()==h
for name,node in [('round18_typeii_selection.json','13.10'),('round18_semiprime_selection.json','14.3')]:
 r=read(C/'messages'/name);assert r['node']==node and r['numerical_contract_authorized'] and not r['numerical_result_presumed']
tree=read(C/'idea_tree.json')
assert all(tree['nodes'][n]['status']=='running' for n in ['13.10','14.3'])
state=dict(status='ROUND18_TWO_FROZEN_CONCEPTS_SELECTED_REAL_DISPATCHES_ACCEPTED',frozen_inputs_sha256=files,
 nodes=['13.10','14.3'],selectors_actual_exit_codes=[0,0],
 role3='followup accepted; actual startup message confirms writing SeparatedTypeII.lean, no compile before numericPASS',
 role4='followup accepted; specific startup message pending',
 role6='both contracts accepted by actual message; TypeII preparation first then SS, no canonical execution reported yet',
 numeric_results_presumed=False,new_Lean_compiles_reported=False,protected_artifacts=997,victory=False)
(C/'messages/round18_selected_dispatch.json').write_text(json.dumps(state,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
p=C/'checkpoint.json';cp=read(p)
cp['in_flight_executors']=[{'role':3,'agent':'/root/round13_formal3_switch','node':'13.10','status':'writing_active_startup_confirmed_compile_waits_numericPASS'},
 {'role':4,'agent':'/root/round13_bilateral_ideation','node':'14.3','status':'followup_accepted_specific_startup_pending'},
 {'role':6,'agent':'/root/round18_numeric_conservation','nodes':['13.10','14.3'],'status':'both_contracts_actual_accepted_typeii_preparation_then_SS'}]
cp['last_progress']+=' Both frozen concepts selected by actual exit0 selectors, runtime4slots/root+formal3+formal4+numeric. Role3 startup actual; role4 followup accepted, specific startup pending; numeric both contracts actual accepted, no producer process or compile result reported.'
cp['previous_goal_turn_evidence']=list(dict.fromkeys(cp['previous_goal_turn_evidence']+['.arbor/sessions/parity/.coordinator/messages/round18_selected_dispatch.json']))
p.write_text(json.dumps(cp,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
p=B/'REPORT.md';txt=p.read_text(encoding='utf-8')
txt+='''
### Boucle18 : deux mécanismes neufs sélectionnés, contrôles en préparation

Les FINALs conceptuels sont gelés et lus intégralement. Node13.10 : séparation des lignes modulo d, coefficient périodique sur un premier omis et minorant CRT écrit du vrai TypeII ; une obstruction de fibre isolée, sans NoGo global. Le conducteur91 fixe concerne seulement le banc fini ; le source garde un conducteur croissant et le premier11 pour la contradiction annoncée. La dispersion mixte après agrégation reste ouverte. Node14.3 : extraction canonique double-semipremière de ressources nonrough, quatre formes divisées CRT et coût écrit de tous e/témoins. Le budget est obtenu seulement pouru>=10^36 ; le gap depuis10^24 et le complément à quotient composite/T_A restent impayés. Le réciproque m0 a axe p0q et raw nul ; aucun crédit fictif ni ressource doublée.

Deux nouveaux contratsN=10^8 sont autorisés :109890b surd91, tousv11..20 et les masques39/429 portées0/91 ; puis5001entiersq1400100..1405100 et touscœursSFunit>3jusqu'à70. Les références et prixθ/II/IIraw, les properpowers, les factorisations et vertices uniques restent visibles. Aucun résultat numérique n'est présumé. Formal3 écrit la séparation/coefficient/somme réelle ; formal4 reçoit le raccord CRT/division/racines. Les compilations de chaque candidat attendent son PASS numérique canonique inspecté ; Juge indépendant aprèsgel. Les22modules337conclusions vérifiées restent le cumul, aucune nouvelle compilation18 encore rapportée, aucun Win.
'''
p.write_text(txt,encoding='utf-8')
print('ROUND18_SELECTIONS_DISPATCH_OBSERVED; hashes confirmed; no mathematics/compiler/audit invoked')
