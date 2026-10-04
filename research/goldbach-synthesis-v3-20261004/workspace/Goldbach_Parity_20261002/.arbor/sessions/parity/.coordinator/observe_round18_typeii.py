"""Inspect existing new TypeII PASS; never import or run its producer."""
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
expected={'typeii_checks.py':'39dc54f832069e4171c666ab244123a371575f48d90cc6e2e0fe8ef97254aec8',
 'role6/strict.py':'20aada21669af3869b1ef1fee4b0e846cbc64b543e765fbf1943dcc8f2825a8a',
 'role6/run_once.py':'a5541c468c45a55b0cd66cb8ad6083983e24c7ae04a00568516da6b5620279f0',
 'typeii.json':'31e873ab0170b1d479c95fdbbe38d989e260cbdd30b5fbba5974f9fc51c63687',
 'role6/typeii_attempt01.log':'b4705e9e66599af582bc5fed8174a2d802f92b42bb3aacebd7380cb8454a3e2e',
 'role6/typeii_canonical_receipt.json':'623a5c64d7f60f4b8e390aa6b51ebeedb49a775bbaebc7c08b194fbfe9f4db22'}
for name,h in expected.items():assert digest(R/name)==h,name
r=read(V/'typeii_canonical_receipt.json');p=read(V/'typeii_attempt01_started.json');d=read(R/'typeii.json')
assert r==read(V/'typeii_attempt01_receipt.json')
assert r['exit_code']==0 and r['attempt']==1 and r['canonical_pass']
assert r['command']==p['command'] and r['bank']==p['bank']=='typeii'
assert datetime.fromisoformat(p['started_at_utc'])<=datetime.fromisoformat(p['snapshot_completed_at_utc'])<datetime.fromisoformat(r['finished_at_utc'])
for field,file in [('source','typeii_checks.py'),('helper','role6/strict.py')]:
 assert r[field+'_sha256']==r[field+'_after_sha256']==p[field+'_sha256']==expected[file]
 assert digest(V/('typeii_attempt01_'+('source' if field=='source' else 'strict')+'.py.txt'))==expected[file]
assert r['output_sha256']==expected['typeii.json'] and r['output_status']==d['status']
assert len(list(V.glob('typeii_attempt*_started.json')))==1
assert d['strict_rational_only'] and not d['Lean_called'] and not d['global_D_N'] and not d['victory']
assert not d['source_onset_applied_to_finite_N'] and d['source_R3_R4_R5_R6_not_claimed_by_finite_test']
assert d['progression_complete']['integer_count']==109890 and d['beta_structural']['A']==196
assert d['progression_complete']['theta_candidate_count']==8441 and d['raw_Lambda_N']['unit_proper_power_count']==9
assert d['candidate_products_complete']['all_pair_count']==d['candidate_products_complete']['column_count']==57189
assert d['coefficient_construction']['E']==[17,19] and d['coefficient_construction']['modulus']==1001
assert {k:v['J'] for k,v in d['unit_conventions'].items()}=={'0:39':27050,'0:429':24591,'91:39':23185,'91:429':21077}
certs=[]
def walk(x):
 assert not isinstance(x,float),'Float inside strict gate'
 if isinstance(x,dict):
  if {'sign','lower','upper'}<=x.keys():
   lo,hi=Fraction(x['lower']),Fraction(x['upper']);assert lo<=hi
   assert (x['sign']=='POSITIVE' and lo>0) or (x['sign']=='NEGATIVE' and hi<0) or (x['sign']=='ZERO' and lo==hi==0)
   certs.append(x['sign'])
  for y in x.values():walk(y)
 elif isinstance(x,list):
  for y in x:walk(y)
walk(d)
assert len(d['local_promotion_falsifiers'])==2
for scope,jr in [('0',273),('91',234)]:
 row=d['R2_R7_R8_by_scope'][scope]
 assert row['JR11']==jr and row['R2_R7_R8_verified'] and row['corrected_T_adversarial_exact']=='0'
 assert row['finite_budget_comparison']['status']=='LOCAL_PROMOTION_FALSIFIED'
 assert row['finite_budget_comparison']['source_R6_not_tested'] and row['finite_budget_comparison']['no_global_impossibility']
result=dict(status='ROOT_INSPECTED_EXISTING_CANONICAL_TYPEII18_PASS_COMPILE_GATE_OPEN',
 checked_inputs_sha256=expected,actual_attempts=1,actual_exit_code=0,stored_strict_sign_positions=len(certs),
 stored_sign_distribution=dict(Counter(certs)),two_local_promotion_falsifiers=True,actual_identity_false=False,
 source_bounds_not_used_finitely=True,formal3_candidate_compilation_authorized=True,
 semiprime_compile_gate_still_pending=True,root_reran_producer_signs_Lean_or_audit=False,victory=False)
(C/'messages/round18_typeii_root_observation.json').write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
cp=read(C/'checkpoint.json');cp.update(phase='ROUND18_TYPEII_NUMERIC_PASS_FORMAL3_COMPILE_GATE_OPEN_SS_PREPARATION',objective_complete=False,victory=False)
cp['in_flight_executors']=[{'role':3,'agent':'/root/round13_formal3_switch','node':'13.10','status':'writing_active_compile_gate_open_after_existing_numericPASS'},
 {'role':4,'agent':'/root/round13_bilateral_ideation','node':'14.3','status':'actual_startup_writing_DoubleExtractionArithmetic_DividedFourForms_compile_waits_SSPASS'},
 {'role':6,'agent':'/root/round18_numeric_conservation','status':'TypeIIcanonicalPASS_attempt1_no_replay_SS_preparation'}]
cp['last_progress']+=' ActualTypeIIattempt01 exit0; root fully read source/helper/launcher/log/receipt/started, verified captured hashes and stored strict signbounds without rerunning producer. 109890b/A196/theta8441/rawpp9/57189column pairs; JR273/234 and two localpromotionfalsifiers preserve identity/calibration prices, no globalNoGo. Formal3 compilation now authorized; formal4 writing actualstartup/SSgate pending.'
cp['previous_goal_turn_evidence']=list(dict.fromkeys(cp['previous_goal_turn_evidence']+['round18/typeii_checks.py','round18/typeii.json','round18/role6/typeii_canonical_receipt.json','.arbor/sessions/parity/.coordinator/messages/round18_typeii_root_observation.json']))
(C/'checkpoint.json').write_text(json.dumps(cp,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print(json.dumps(result,ensure_ascii=False))
