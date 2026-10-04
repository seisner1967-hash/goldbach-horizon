"""Inspect stored SS18 evidence only, with no producer, kernel, compiler or audit run."""
import sys
sys.dont_write_bytecode=True
sys.set_int_max_str_digits(0)
from pathlib import Path
from hashlib import sha256
from fractions import Fraction
from datetime import datetime
from collections import Counter
import json
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C=B/'.arbor/sessions/parity/.coordinator';R=B/'round18';V=R/'role6'
def read(p):return json.loads(p.read_bytes())
def digest(p):return sha256(p.read_bytes()).hexdigest()
expected={'semiprime_checks.py':'3c196ecbfe8d66a864bc421e0bf76bdfd95e9d7a2849a4c6c743133b5a04e23c',
 'role6/semiprime_helpers.py':'106ba674bca2c4f111f51c8c8497a4f87e40d432610f71a4722e272530be7fe7',
 'role6/strict.py':'20aada21669af3869b1ef1fee4b0e846cbc64b543e765fbf1943dcc8f2825a8a',
 'role6/run_semiprime_once.py':'c774bdf29c6fd33697326b2363b3c4612b0aa025a974f68a906fc53125810ac7',
 'semiprime.json':'c30c84e1a7d01cb6146caedb08e5addb81b8795d90c89875e878a6fc1e924f0c',
 'role6/semiprime_attempt02.log':'8ab8df1c047cfefa87c08c4361cdd82d14527846b68eb4c1068ab460d97cbdd1',
 'role6/semiprime_canonical_receipt.json':'5b0ef9f42846574090e8ba43fe20b53cb92021324bba238e6607c55521a1889f'}
for name,h in expected.items():assert digest(R/name)==h,name
r=read(V/'semiprime_canonical_receipt.json');p=read(V/'semiprime_attempt02_started.json');d=read(R/'semiprime.json')
assert r==read(V/'semiprime_attempt02_receipt.json')
assert r['exit_code']==0 and r['attempt']==2 and r['canonical_pass'] and r['bank']=='semiprime'
assert r['command']==p['command']
assert datetime.fromisoformat(p['started_at_utc'])<=datetime.fromisoformat(p['snapshot_completed_at_utc'])<datetime.fromisoformat(r['finished_at_utc'])
assert r['sources_before_sha256']==r['sources_after_sha256']==p['sources_sha256']
for name,h in r['sources_before_sha256'].items():assert digest(R/name)==h
assert r['snapshots_sha256']==p['snapshots_sha256']
for name,h in r['snapshots_sha256'].items():assert digest(R/name)==h
assert r['launcher_sha256']==p['launcher_sha256']==expected['role6/run_semiprime_once.py']
assert r['protected_registry_sha256']==digest(R/'previous_artifacts_sha256.json')=='05212665afffecade91134e1533f93d11eba8058179198e4420eef1fe252f2bc'
assert r['output_sha256']==expected['semiprime.json'] and r['output_status']==d['status']
assert len(list(V.glob('semiprime_attempt*_started.json')))==2
f=read(V/'semiprime_attempt01_receipt.json')
assert f['exit_code']==1 and not f['canonical_pass']
assert f['log_sha256']==digest(V/'semiprime_attempt01.log')=='e51d6cf583a5dd8139e9f5fb5bd5e09680f7f582655072454faa5dba06aeed84'
for name,h in f['snapshots_sha256'].items():assert digest(R/name)==h
old=(V/'semiprime_attempt01_semiprime_checks.py.txt').read_text(encoding='utf-8')
new=(R/'semiprime_checks.py').read_text(encoding='utf-8')
assert old.replace('s.bithex(s.prime(q) for q in range(QLOW, QHIGH + 1))','s.bithex([s.prime(q) for q in range(QLOW, QHIGH + 1)])')==new
assert 'TypeError: object of type' in (V/'semiprime_attempt01.log').read_text(encoding='utf-8')
assert d['strict_rational_only'] and not d['Lean_called'] and not d['global_D_N'] and not d['victory']
assert d['D5_D10_D11_source_bounds_not_applied'] and d['source_intermediate_segment_unpaid']
assert d['finite_N_is_not_either_source_onset_test'] and d['outside_selected_SS_W_D_kernels_literal_uncomputed']
assert d['complete_window']['integer_count']==5001 and d['complete_window']['prime_unit_q_count']==333
assert len(d['complete_window']['all_SF_unit_cores_gt3'])==22
assert d['partition_complete']['theta_demand_counts']==dict(A=258,R=32,S=674,SS=40,S_minus_SS=634)
assert d['partition_complete']['all_target_axis_rows']==7326 and d['partition_complete']['SS_resource_q_count']==14
assert d['switch_completeness']['triplet_count']==len(d['new_divided_switches'])==286
u=d['physical_union'];assert u['unique_vertex_count']==68 and u['unique_active_kernel_count']==54 and u['literal_zero_vertex_count']==14
assert u['existing_anchor_p0_count']==2 and u['no_capacity_credit_from_m0']
assert len(d['new_selected_kernel_profiles'])==54
certs=[]
def walk(x):
 assert not isinstance(x,float),'Float inside strict numerical gate'
 if isinstance(x,dict):
  if {'sign','lower','upper'}<=x.keys():
   lo,hi=Fraction(x['lower']),Fraction(x['upper']);assert lo<=hi
   assert (x['sign']=='POSITIVE' and lo>0) or (x['sign']=='NEGATIVE' and hi<0) or (x['sign']=='ZERO' and lo==hi==0)
   certs.append(x['sign'])
  for y in x.values():walk(y)
 elif isinstance(x,list):
  for y in x:walk(y)
walk(d)
assert len(d['local_falsifiers'])==4
assert all(x['no_global_impossibility'] and 'FALSIFIED' in x['status'] for x in d['local_falsifiers'])
result=dict(status='ROOT_INSPECTED_EXISTING_CANONICAL_SS18_PASS_COMPILE_GATE_OPEN',checked_inputs_sha256=expected,
 actual_attempts=2,actual_exit_codes=[1,0],first_failure='encoding generator has no len; captured one-line correction only',
 stored_strict_sign_positions=len(certs),stored_sign_distribution=dict(Counter(certs)),
 measure_signs={k:v['sign_certificate']['sign'] for k,v in d['selected_measures'].items()},
 complete_partition=d['partition_complete'],physical_counts={k:u[k] for k in ['unique_vertex_count','unique_active_kernel_count','literal_zero_vertex_count','existing_anchor_p0_count']},
 four_finite_local_falsifiers=True,actual_selected_identity_false=False,source_bounds_not_used_finitely=True,
 formal4_candidate_compilation_authorized=True,root_reran_producer_signs_Lean_or_audit=False,victory=False)
ob=C/'messages/round18_semiprime_root_observation.json'
with ob.open('x',encoding='utf-8') as handle:json.dump(result,handle,indent=2,ensure_ascii=False);handle.write('\n')
gate=dict(root_authorized=True,canonical_SS_PASS_inspected=True,
 root_observation=str(ob),root_observation_sha256=digest(ob),
 numeric_receipt='round18/role6/semiprime_canonical_receipt.json',numeric_receipt_sha256=expected['role6/semiprime_canonical_receipt.json'],
 numeric_output='round18/semiprime.json',numeric_output_sha256=expected['semiprime.json'],
 historical_rebuilds_authorized=False,victory=False)
with (R/'role4/compile_gate.json').open('x',encoding='utf-8') as handle:json.dump(gate,handle,indent=2);handle.write('\n')
cp=read(C/'checkpoint.json');cp.update(phase='ROUND18_BOTH_NUMERIC_PASS_BOTH_FORMAL_COMPILE_GATES_OPEN',objective_complete=False,victory=False)
cp['in_flight_executors']=[{'role':3,'agent':'/root/round13_formal3_switch','node':'13.10','status':'core_authorPASS03_extensions_active_independent_judge_pending'},
 {'role':4,'agent':'/root/round13_bilateral_ideation','node':'14.3','status':'writing_actual_compile_gate_open_after_root_inspected_SS_PASS'},
 {'role':6,'agent':'/root/round18_numeric_conservation','status':'both_canonical_PASS_frozen_unique_isolated_replays_not_yet_authorized'}]
cp['last_progress']+=' SS18 canonical attempt02 exit0 after preserved encoding failure01; root fully reads sources/helper/launcher/logs/receipts and validates stored certificates/hash captures without running kernels. 5001q/333prime/22cores/7326axes/A258R32S674=SS40+634,286dividedtriplets,68vertices54active14zero,2existinganchors. ActualSSidentity valid; four localpromotionfalsifiers/no globalproof. Formal4 compilegate opened, producers frozen, no replay authorized yet.'
cp['previous_goal_turn_evidence']=list(dict.fromkeys(cp['previous_goal_turn_evidence']+['round18/semiprime_checks.py','round18/semiprime.json','round18/role6/semiprime_canonical_receipt.json','.arbor/sessions/parity/.coordinator/messages/round18_semiprime_root_observation.json','round18/role4/compile_gate.json']))
(C/'checkpoint.json').write_text(json.dumps(cp,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
p=B/'REPORT.md';txt=p.read_text(encoding='utf-8')
txt+='\n### Double extraction18 : calcul canonique contrôlé\n\nSS attempt01 exit1 conserve une erreur d’encodage generator→len ; attempt02 exit0 corrige uniquement cet appel vers une liste. Sources/helpers/launcher/captures/logs/reçus intégralement lus et liés par empreintes par root, certificats rationnels stockés contrôlés sans recalcul des producteurs. Fenêtre5001entiers,333qpremiers,22cores,7326axes : A258/R32/S674, dontSS40 et634horsSS ;286triplets divisés,68sommetsphysiques/54kernelsactifs/14zéros,2ancresdéjàprésentes. Les quatre falsificateurs sont locaux, la borne source D5/D10/D11 n’est pas appliquée au N fini. Le gate de compilation rôle4 est ouvert ; le Juge indépendant et les rejeux isolés restent à effectuer. Aucune victoire ni borne globale D_N.\n'
p.write_text(txt,encoding='utf-8')
print(json.dumps(result,ensure_ascii=False))
