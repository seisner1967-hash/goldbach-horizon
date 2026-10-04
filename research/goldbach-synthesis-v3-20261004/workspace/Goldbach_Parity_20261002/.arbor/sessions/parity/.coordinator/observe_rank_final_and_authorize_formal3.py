"""Read immutable rank19 evidence and create the root author gate, no producers."""
import hashlib, json, re, sys
from datetime import datetime, timezone
from pathlib import Path
sys.set_int_max_str_digits(0)
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
R=B/'round19'; C=B/'.arbor/sessions/parity/.coordinator'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p): return json.loads(p.read_text(encoding='utf-8'))
def save(p,d):
    with p.open('x',encoding='utf-8') as f: f.write(json.dumps(d,ensure_ascii=False,indent=2)+'\n')
finalp=R/'role6_rank/final_receipt.json'; final=read(finalp)
assert sha(finalp)=='a08fbf8e3e402713317c0a146ddddd79d654be0d3732d8d08db7c7d9c55005c9'
assert len(final['bindings'])==29 and final['actual_exit_code']==0
assert final['canonical_attempts']==1 and final['mathematical_failures']==final['replays']==0
assert final['victory'] is False and final['Gamma_rank_DN_or_capacity_bound'] is False
bindings={}
for rel,e in final['bindings'].items():
    p=R/rel; assert p.stat().st_size==e['bytes'] and sha(p)==e['sha256'],rel
    bindings['round19/'+rel]=e['sha256']
bindings['round19/role6_rank/final_receipt.json']=sha(finalp)
receipt=read(R/'role6_rank/canonical_attempt01/receipt.json')
assert receipt['exit_code']==0 and receipt['subprocess_launch_error'] is None
assert receipt['new_canonical_invocations']==1 and receipt['automatic_replay'] is False
assert receipt['W_D_kernel_parent_or_old_preflight_Lean_PDF_execution'] is False
assert receipt['captured_binding_hashes_unchanged_after_execution'] is True
assert receipt['prepared_original_binding_hashes_unchanged_after_execution'] is True
assert len(receipt['PREEXEC_captures'])==13
for k,e in receipt['PREEXEC_captures'].items():
    assert sha(Path(e['original']))==sha(Path(e['snapshot']))==e['sha256'], k
logtext=Path(receipt['log']).read_text(encoding='utf-8'); logobjects=[]; dec=json.JSONDecoder()
while logtext.strip():
    obj,end=dec.raw_decode(logtext.lstrip()); logobjects.append(obj)
    logtext=logtext.lstrip()[end:]
log=logobjects[-1]; result=read(Path(receipt['result']))
assert log['status']==result['status']=='PASS_NEW_ALL_RANK_FINITE_IDENTITIES_ONLY'
assert receipt['result_sha256']==sha(Path(receipt['result']))
certs={'stored_positions':0,'stored_sign_labels':{}}
def visit(x):
    if isinstance(x,dict):
        if {'lower_scaled','upper_scaled','sign','dyadic_bits'}<=x.keys():
            assert re.fullmatch(r'-?\d+',x['lower_scaled']) and re.fullmatch(r'-?\d+',x['upper_scaled'])
            assert x['dyadic_bits']==128
            assert x['sign'] in {'POSITIVE','NEGATIVE','ZERO','UNRESOLVED','PARAMETER_BOX_MAY_CHANGE_SIGN'}
            certs['stored_positions']+=1
            s=x['sign']; certs['stored_sign_labels'][s]=certs['stored_sign_labels'].get(s,0)+1
        for y in x.values(): visit(y)
    elif isinstance(x,list):
        for y in x: visit(y)
visit(result)
prep=read(R/'role3/preparation.json')
sources={e['module']+'.lean':e['sha256'] for e in prep['written_modules']}
for n,digest in sources.items(): assert sha(R/'role3'/n)==digest,n
assert sha(R/'role3/build_once.py')==prep['launcher_sha256']=='f7391bae3c2baad30f21bcc1798bf5417af2c7637644d1da5ada3336632ab588'
assert not (R/'role3/build_receipt.json').exists()
previous=read(C/'messages/round19_role3_source_root_observation.json')
gate={'compile_authorization_token':'ROOT19_FORMAL3_COMPILE',
 'formal3_candidate_compilation_authorized':True,'canonical_numeric_pass':True,
 'actual_identity_false':False,'actual_numeric_exit_code':0,
 'authorized_new_modules':[e['module'] for e in prep['written_modules']],
 'checked_inputs_sha256':bindings,'authorized_at_utc':datetime.now(timezone.utc).isoformat(),
 'initial_sources_already_FULL_root_read_and_now_hash_verified':sources,
 'full_root_read_builder_sha256':sha(R/'role3/build_once.py'),
 'repairs_after_actual_FAIL_authorized':True,'unchanged_PASS_replay_authorized':False,
 'historical_compile_or_mathematical_replay_authorized':False,
 'scope':'Six new rank19 author modules only; auxiliary noWin; independent Judge pending',
 'official_Judge_counts_modified':False,'victory':False}
gatep=C/'messages/round19_formal3_compile_authorization.json'; save(gatep,gate)
obs={'status':'ROOT_VERIFIED_ACTUAL_UNIQUE_NEW_RANK19_FINAL_PASS_AUXILIARY_ONLY',
 'observed_utc':gate['authorized_at_utc'],'numeric_bindings':bindings,
 'verified_final_bindings':29,'verified_PREEXEC_captures':13,'stored_log_JSON_objects':len(logobjects),
 'root_metadata_reader_failure_record':'round19_rank_root_reader_failed01.json',
 'actual_start':receipt['started_at_utc'],'actual_finish':receipt['finished_at_utc'],
 'actual_exit_code':0,'canonical_invocations':1,'replays':0,
 'stored_certificate_encodings_not_recomputed_signs':certs,
 'formal3_gate_path':str(gatep),'formal3_gate_sha256':sha(gatep),
 'root_math_producer_Lean_or_sign_recomputations':0,
 'official_Judge_counts_modified':False,'victory':False}
save(C/'messages/round19_rank_finish_root_observation.json',obs)
cp=read(C/'checkpoint.json'); cp['phase']='ROUND19_BOTH_NUMERIC_FINAL_VERIFIED_FORMAL3_GATE_ISSUED_FORMAL4_FINAL_JUDGE_PREPARING'
cp['in_flight_executors']=[{'role':3,'agent':None,'status':'numeric_PASS_verified_concrete_gate_ready_for_fresh_continuation'},
 {'role':4,'agent':None,'status':'FINAL_report_read_all5authorPASS_independent_Judge_pending'},
 {'role':6,'agent':None,'status':'two_FINAL_banks_root_verified_unique_each_no_replay'},
 {'role':5,'agent':'/root/round19_judge','status':'DRAFT_audit_rank_delta_read_pending_no_audit_gate'}]
cp['last_progress']+=' Newrank19 actualuniquePASS exit0 and29FINALbindings/13PREEXECverified; second compressedcatalogues bound. Root reads stored enclosures only, no signs/logs recalculated. Concrete sixmodule ROOT19_FORMAL3_COMPILE issued after fullsource review and currenthashcheck; author4 FINAL reports5PASS12attempts7technicalFAIL and1separatelauncherparsefail. IndependentJudge pending, official30/507 unchanged, noWin.'
for p in [gatep,C/'messages/round19_rank_finish_root_observation.json']:
    rel=p.relative_to(B).as_posix()
    if rel not in cp['previous_goal_turn_evidence']: cp['previous_goal_turn_evidence'].append(rel)
(C/'checkpoint.json').write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:obs[k] for k in ['status','verified_final_bindings','verified_PREEXEC_captures','stored_certificate_encodings_not_recomputed_signs','formal3_gate_sha256']},ensure_ascii=False,indent=2))
