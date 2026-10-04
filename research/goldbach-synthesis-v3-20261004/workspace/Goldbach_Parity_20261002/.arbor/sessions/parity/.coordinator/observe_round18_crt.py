"""Inspect stored CRT annex captures and rational encodings; no producer rerun."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
from hashlib import sha256
from fractions import Fraction
from datetime import datetime,timezone
import json
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
R=B/'round18/role6_crt';C=B/'.arbor/sessions/parity/.coordinator'
def h(p):return sha256(Path(p).read_bytes()).hexdigest()
def load(p):return json.loads(Path(p).read_text(encoding='utf-8'))
a=load(R/'canonical_receipt.json');s=load(R/'canonical_attempt01_started.json')
assert h(R/'canonical_receipt.json')==h(R/'canonical_attempt01_receipt.json')=='13648681abf108c6bb0214968322dfe5652f2426bda3b4b66245cef273061d4a'
assert h(R/'canonical_attempt01_started.json')==a['started_sha256']=='daf958caee010e854a824f55e17937b0aeeedcc040b58bb696c565639835b164'
assert a['exit_code']==0 and a['canonical_pass'] and a['post_execution_validation_error'] is None
assert a['reviewed_sha256']==a['source_after_sha256']==s['reviewed_sha256']
for name,value in a['reviewed_sha256'].items(): assert h(R/name)==value
for name,item in a['input_bindings'].items(): assert h(item['path'])==item['sha256']==a['input_after_sha256'][name]
assert a['input_bindings']==s['input_bindings'] and len(a['input_bindings'])==11
assert a['capture_sha256']==s['capture_sha256']
for name,value in a['capture_sha256'].items(): assert h(name)==value
assert h(R/'canonical_authorization.json')==a['authorization_sha256']==s['authorization_sha256']
assert h(R/'canonical_attempt01.log')==a['log_sha256']=='920cc215d50e6d260beb8a7ae143ebea5ed8ceae91aace8cbed83147ec740d33'
assert h(a['output'])==a['output_sha256']=='56ac567743c306755fc49925e039272ba4c0f4e3517167c7848c0a6c57b09ac5'
d=load(a['output'])
assert d['status']==a['output_status']=='PASS_NEW_CRT_FULL_DIVISORS_IE_AND_GUARDED_FRONTS'
def q(value):
    x=Fraction(value['numerator'],value['denominator'])
    assert value['denominator']>0 and str(x)==value['text']
    return x
def encodings(obj):
    assert not isinstance(obj,float)
    if isinstance(obj,dict):
        if {'numerator','denominator','text'}<=obj.keys(): q(obj)
        for v in obj.values():encodings(v)
    elif isinstance(obj,list):
        for v in obj:encodings(v)
encodings(d)
assert [v['v'] for v in d['source_H_rows']]==d['E_all_integer_unit_rows']==[17,19]
assert [v['direct_unit_row_count'] for v in d['source_H_rows']]==[124,110]
assert d['all_k_all_E_CRT_checks']==1944
assert [len(v['all_divisor_CRT_checks']) for v in d['source_H_rows']]==[972,972]
for row in d['source_H_rows']:
    assert len(row['direct_b_values'])==row['direct_unit_row_count']==row['full_moebius_IE_row_count']
    for item in row['all_divisor_CRT_checks']:
        assert item['left_direct_count']==item['right_class_count']==item['floor_count']
        assert abs(q(item['signed_front']))<=1 and item['front_at_most_one'] and item['finite_interval_equivalence']
assert [d['R4_premises_only'][k]['satisfied'] for k in ['R4a','R4b','R4c']]==[False,True,False]
assert not d['R5']['premises_satisfied'] and not d['R5']['theorem_applied']
assert d['JR_direct_sum_of_rows']==234 and d['J_source_H']==23185 and d['structural_A_read_only']==196
assert d['corrected_H_times_ell']['J']==21077 and d['corrected_H_times_ell']['JR']==0
assert not d['corrected_H_times_ell']['ell_H_coprime_guard'] and not d['corrected_H_times_ell']['old_minorant_applied']
assert d['logarithmic_certificates_added']==0 and not d['victory'] and not d['global_D_N_controlled']
obs=dict(status='ROOT_INSPECTED_NEW_CRT_CANONICAL_PASS',utc=datetime.now(timezone.utc).isoformat(),
 actual_exit_code=0,input_bindings_verified=11,captures_verified=len(a['capture_sha256']),
 checked_count=1944,J=23185,JR=234,corrected_J=21077,corrected_JR=0,R4=[False,True,False],R5_applied=False,
 canonical_receipt_sha256=h(R/'canonical_receipt.json'),output_sha256=h(a['output']),
 independent_judge_pending=True,replay_required=False,replay_authorized=False,replays_executed=0,
 root_reran_producer_or_Lean_or_audit_or_kernel_or_sign=False,victory=False)
p=C/'messages/round18_crt_root_observation.json'
with p.open('x',encoding='utf-8') as f:json.dump(obs,f,indent=2);f.write('\n')
cpPath=C/'checkpoint.json';cp=load(cpPath)
cp['last_progress']+=' NewCRTcanon01 actualexit0 rootfullyreadsource/helper/launcher/contract/input/log/receipt/started and metadata verifies11inputs/allPREEXECcaptures/1944storedfronts/encodings; J23185JR234/corrected21077zero, R4false,true,false henceR5notapplied. No new logarithmic signs. IndependentJudge rational checks remaining, no unresolved repeat concern; zeroCRT replay required/authorized. FINAL6CRT and contentreport pending, no audit/Lean authorization yet.'
cp['previous_goal_turn_evidence']=list(dict.fromkeys(cp['previous_goal_turn_evidence']+['round18/role6_crt/canonical_receipt.json','round18/role6_crt/canonical_attempt01/crt.json',str(p.relative_to(B)).replace('\\','/')]))
cpPath.write_text(json.dumps(cp,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print(json.dumps(dict(status=obs['status'],captures_verified=obs['captures_verified'],checks=1944,observation_sha256=h(p))))
