"""Observe produced TypeII evidence, never execute a producer or compiler."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
from hashlib import sha256
from collections import Counter
import json
BASE=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002');C=BASE/'.arbor/sessions/parity/.coordinator'
def read(p):return json.loads(p.read_bytes())
def digest(p):
 h=sha256()
 with p.open('rb') as f:
  for chunk in iter(lambda:f.read(1048576),b''):h.update(chunk)
 return h.hexdigest()
r=read(BASE/'round17/role6/typeii_canonical_success.json');fail=read(BASE/'round17/role6/typeii_attempt01_failure.json')
assert r['attempt']==2 and r['exit_code']==0 and fail['exit_code']==1
for rec in [r,fail]:
 for k,hk in [('source_snapshot','source_snapshot_sha256'),('log','log_sha256')]:assert digest(Path(rec[k]))==rec[hk]
for k,hk in [('producer','producer_sha256'),('output','output_sha256')]:assert digest(Path(r[k]))==r[hk]
assert Path(r['producer']).read_bytes()==Path(r['source_snapshot']).read_bytes()
b=read(Path(r['output']));assert b['N']==100000000 and not b['victory'] and not b['Lean_called']
p=b['progression_complete'];assert p['integer_count']==162338 and p['length_X']==12499950 and p['X_minus77_integer_count']==-76
assert len(p['b_factorizations_complete_column'].split(';'))==len(p['j_factorizations_complete_column'].split(';'))==162338
assert b['beta_structural']['A']==len(b['beta_structural']['canonical_vertices'])==181
assert b['v_complete']['eligible']==[17,19] and p['theta_candidate_count']==12460
assert b['raw_Lambda_N']['unit_proper_power_count']==len(b['raw_Lambda_N']['unit_proper_power_vertices'])==8
assert b['new_mode_only_no_complete_TypeII_estimate'] and b['no_BV_onset_certified'] and b['Gamma39_unestimated']
assert b['strict_rational_only'] and b['raw_Lambda_N']['no_mu_n_squared_filter']
counts=Counter();stack=[b]
while stack:
 item=stack.pop()
 if isinstance(item,dict):
  if item.get('sign') in ['POSITIVE','NEGATIVE','ZERO','UNRESOLVED']:counts[item['sign']]+=1
  stack.extend(v for v in item.values() if isinstance(v,(dict,list)))
 elif isinstance(item,list):stack.extend(v for v in item if isinstance(v,(dict,list)))
assert not counts['UNRESOLVED']
obs={'status':'ROOT_OBSERVED_CANONICAL_TYPEII_AWAITING_REPLAY_FINAL_AND_JUDGE','bindings_checked':r,
 'real_numeric_failures':[fail],'failure_classification':'out_of_domain_auxiliary_radical_factorization; bounded-factor union correction only',
 'source_full_read_then_exact_diff_read':True,'integer_count':162338,'beta':181,'theta_candidates':12460,'properpowers':8,
 'unit_J':{k:v['J'] for k,v in b['unit_conventions'].items()},'sign_position_counts':dict(counts),
 'TypeII':{k:v['z_functional']['exact_rational'] for k,v in b['functionals_exact']['II']['by_mask'].items()},
 'L13_theta_signs':{k:v['sign_certificate']['sign'] for k,v in b['prices_by_weight']['theta']['L13'].items()},
 'AP_decomposition':b['AP_decomposition'],'multiplicity_counts':b['v_complete']['multiplicity_counts'],
 'x_over_A':b['normalization_x_over_A'],'root_reran_math_producer':False,'root_reran_Lean':False,'victory':False}
(C/'messages/round17_root_typeii_observation.json').write_text(json.dumps(obs,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
p=C/'checkpoint.json';j=read(p);j.update(phase='ROUND17_BOTH_NUMERIC_CANONICAL_PASS_FORMALIZATION',external_blocker=None)
j['in_flight_executors'][0]='round13_formal3_switch: role6 both canonical banks PASS, rough isolated replay PASS, unique TypeII replay underway'
j['last_progress']+=' TypeII canonical attempt2 exit0 after one real technical domain failure kept. Root fully read source and exact bounded-factor union correction, logs/receipts/hashbindings, complete162338 integer rows/caps/products/masks, A181/theta12460/eight rawproperpowers and nonzero theta calibration prices. No finite BV or global covariance claim. Formal3 reports first full producer PASS at attempt11, continuing actual-rho raccord; not yet independent Judge.'
for n in ['round17/typeii_checks.py','round17/typeii.json','round17/role6/typeii_canonical_success.json','round17/role6/typeii_attempt01_failure.json','.arbor/sessions/parity/.coordinator/messages/round17_root_typeii_observation.json']:
 if n not in j['previous_goal_turn_evidence']:j['previous_goal_turn_evidence'].append(n)
p.write_text(json.dumps(j,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
p=BASE/'REPORT.md';t=p.read_text(encoding='utf-8');marker='### Deuxième banc17 : vrai mode TypeII et prix distincts'
assert marker not in t
p.write_text(t+'\n'+marker+'\n\nLe banc TypeII complet passe à la tentative2 après une erreur technique de domaine dans la factorisation auxiliaire de rad(hN), conservée avec source et journal. La correction réunit les facteurs de composantes admissibles et garde le contrat. Sur162338 entiers, β181,12460 candidats premiers et8 properpowers raw sont conservés. Les six masques donnent J0=[64936,43291,39961] et J77=[50599,33732,31136]. Les couples v17/19 et leur intersection323 gardent la multiplicité analytique, sans créer de capacité physique. Les identités de calibration et leurs prix sont vérifiés séparément pour theta, II et II_raw ; les deux prix L13_theta sont strictement négatifs dans cette fenêtre. Aucun BV, D/W ou estimateur asymptotique n’est appliqué. Root a lu source, correction exacte, journaux et reçus puis vérifié les bindings sans lancer le producteur. Le rejeu unique TypeII et le Juge restent pendants.\n\nLe rôle3 annonce un premier PASS intégral à l’essai11 pour l’inversion Selberg, principale=1/G, le support nul, la formule des poids et |lambda|<=1, avec axiomes standards seuls. Il poursuit le raccord aux racines effectives du rôle4. Ce résultat producteur n’est pas encore audité ni ajouté au cumul acquis. Le contrôle strict d’arbre reste pendant pour les rapports et métriques des nodes13.9/14.2 encore running ; aucun score fictif n’est créé.\n',encoding='utf-8')
print(json.dumps({k:v for k,v in obs.items() if k not in ['bindings_checked','real_numeric_failures']},ensure_ascii=False))
