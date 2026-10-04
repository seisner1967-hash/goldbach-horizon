"""Root observation of produced files only; no math producer or compiler."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
from hashlib import sha256
from collections import Counter
import json
BASE=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C=BASE/'.arbor/sessions/parity/.coordinator'
def read(p): return json.loads(p.read_bytes())
def digest(p):
 h=sha256()
 with p.open('rb') as f:
  for chunk in iter(lambda:f.read(1048576),b''):h.update(chunk)
 return h.hexdigest()
r=read(BASE/'round17/role6/rough_canonical_success.json');assert r['exit_code']==0
for key,hkey in [('producer','producer_sha256'),('source_snapshot','source_snapshot_sha256'),('log','log_sha256'),('output','output_sha256')]:
 assert digest(Path(r[key]))==r[hkey],key
assert Path(r['producer']).read_bytes()==Path(r['source_snapshot']).read_bytes()
b=read(Path(r['output']));assert b['N']==100000000 and not b['victory'] and not b['Lean_called']
assert b['candidate_count']==b['unique_physical_m_count']==len(b['physical_candidates_catalog'])==252
assert b['kernel_count']==len(b['kernel_catalog'])==47 and b['literal_zero_axis_W_count']==205
assert b['q_window_complete']['integer_count']==len(b['q_window_complete']['all_q_tested'])==201
assert len(b['q_window_complete']['prime_unit_q'])==9
assert len(b['core_window_complete']['squarefree_unit_cores'])==28
counts={k:sum(len(v[k]) for v in b['partition_active_demands'].values()) for k in ['A','R','S']}
assert counts=={'A':11,'R':0,'S':18}
assert b['no_source_C6_C7_U4_applied_to_finite_N'] and b['whole_U_a_original_Q_strict_front_k1_preserved']
assert b['raw_Lambda_N']['proper_power_count']==0 and b['old_vertices_readonly_guard']['new_computed_m_disjoint']
witness=b['ERROR_FALSIFIER'][0]['witness'];witness_sign=b['physical_candidates_catalog'][str(witness['m'])]['B_theta_sign_certificate']['sign']
sign_positions=Counter();stack=[b]
while stack:
 item=stack.pop()
 if isinstance(item,dict):
  if item.get('sign') in ['POSITIVE','NEGATIVE','ZERO','UNRESOLVED']:sign_positions[item['sign']]+=1
  stack.extend(v for v in item.values() if isinstance(v,(dict,list)))
 elif isinstance(item,list):stack.extend(v for v in item if isinstance(v,(dict,list)))
assert not sign_positions['UNRESOLVED']
obs={'status':'ROOT_OBSERVED_CANONICAL_ONLY_AWAITING_FINAL_REPLAY_AND_JUDGE','protected_archives':799,
 'source_full_read':['round17/rough_checks.py','round17/shared.py','round17/run_new.py','round17/replay_new.py'],
 'bindings_checked':r,'counts':counts,'q':9,'cores':28,'candidates':252,'kernels':47,'literal_zero_axis_W':205,
 'sign_position_counts':dict(sign_positions),'absence_witness_sign':witness_sign,
 'finite_selberg_core_statuses':dict(Counter(v['status'] for v in b['finite_selberg_by_core'])),
 'falsifier_statuses':[v['status'] for v in b['ERROR_FALSIFIER']],
 'root_executed_math_producer':False,'root_executed_Lean':False,'source_asymptotic_bounds_applied':False,'victory':False}
(C/'messages/round17_root_rough_observation.json').write_text(json.dumps(obs,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
p=C/'checkpoint.json';j=read(p)
j.update(phase='ROUND17_TWO_NUMERIC_CONTRACTS_FORMALIZATION_AND_ROUGH_CANONICAL',in_flight_executors=[
 'round13_formal3_switch: role6 rough canonical PASS, unique replay underway, new TypeII preparation',
 'round17_formal3_selberg: role3 finite Selberg weights/inversion/counting, actual Lean attempts underway',
 'round13_bilateral_ideation: role4 actual four-form local roots/collisions/saturation, actual Lean attempts underway'],
 next_focus='Finish complete new TypeII bank and both actual Selberg/root modules, then independent Judge17; quantitative remaining A/S/Gamma/TypeII/global incidence obligations retained.',
 coordination_incident='Transient failed dispatches launched no work. Formal3 fresh spawn and formal4 current-slot followup now effective; no external blocker.',external_blocker=None)
j['last_progress']+=' Root fully read rough/shared/new launch/replay sources and actual canonical log/receipt; exact bindings and complete 201 integers/9q/28cores/252 candidates/47new kernels observed. Finite A11/R0/S18 and positive whole deficit do not pay source T_A/T_S. Formal3/4 both active; technical Lean errors archived, no full FINAL17 or independent Judge yet. Unique rough replay underway; second new TypeII bank preparation authorized. No math producer/compiler rerun by root.'
for n in ['round17/rough_checks.py','round17/rough.json','round17/role6/rough_canonical_success.json','.arbor/sessions/parity/.coordinator/messages/round17_root_rough_observation.json']:
 if n not in j['previous_goal_turn_evidence']:j['previous_goal_turn_evidence'].append(n)
p.write_text(json.dumps(j,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
p=BASE/'REPORT.md';txt=p.read_text(encoding='utf-8')
marker='### Sélections 17 et observation du premier banc canonique'
assert marker not in txt
p.write_text(txt+'\n'+marker+'\n\nLes deux FINAL conceptuels et l’addendum de masque sont figés et sélectionnés sous 14.2 et 13.9. Le masque réel ancien était gcd(b,N) ; la variante avec77 conserve son prix E77. Les deux nouveaux contrats numériques sont autorisés. Les formaliseurs3 et4 travaillent effectivement en parallèle sur les poids Selberg construits et les racines réelles des quatre formes ; chaque essai technique est conservé. Aucun nouveau module complet n’est encore certifié par le Juge.\n\nLe premier banc canonique neuf passe à son premier essai :201 entiers q,9 premiers unitaires,28 cœurs,252 candidats,47 noyaux D/W neufs et205 axes exactement nuls. Il vérifie les poids finis, principale=1/G, les carrés point à point et les vrais restes CRT avec +1. Les branches saturées ne forment pas G. La partition active contient11 cibles A,0 R et18 S ; le déficit après ressources uniques et la somme entière sont positifs. Trois promotions locales sont falsifiées ; aucun estimateur C6/C7/U4 source n’est appliqué à N=10^8. Root a lu les sources/logs/reçus et vérifié les empreintes sans lancer le producteur. Le rejeu isolé unique et l’audit indépendant restent à terminer, ainsi que le nouveau banc TypeII complet. Les bornes C4/C6 restent écrites ; T_A/T_S, les autres modes TypeII et D_N restent ouverts. Aucune victoire.\n',encoding='utf-8')
print(json.dumps({k:v for k,v in obs.items() if k not in ['bindings_checked','source_full_read']},ensure_ascii=False))
