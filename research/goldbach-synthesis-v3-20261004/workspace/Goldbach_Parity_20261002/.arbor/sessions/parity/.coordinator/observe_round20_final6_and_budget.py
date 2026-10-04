"""Root byte/receipt observation of FINAL6 and actual exceptional source budget."""
import json,hashlib
from pathlib import Path
from datetime import datetime,timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C=B/'.arbor/sessions/parity/.coordinator';W=B/'round20/role4'
def sha(p):
    h=hashlib.sha256()
    with Path(p).open('rb') as f:
        for x in iter(lambda:f.read(1024*1024),b''):h.update(x)
    return h.hexdigest()
def load(p):return json.loads(Path(p).read_text(encoding='utf-8-sig'))
def save(p,x):
    with p.open('x',encoding='utf-8',newline='\n') as f:
        json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
six=B/'round20/role6/final_receipt.json'
assert sha(six)=='5e74e0a1839c746fc828e0be09050d57f6f09ae33a115c5fa91dc13ea461a5e5'
f=load(six)
assert f['global_final'] and f['both_actual_exit_codes']==[0,0]
assert f['new_mathematical_subprocess_count']==2 and f['mathematical_execution_during_finalization']==0
assert f['routine_replays']==0 and not f['victory']
assert sha(f['report_path'])==f['report_sha256']=='8266fb4f5586e389f97c880b413a88d0d49bc972086b3049da8def553f23d898'
assert sha(f['manifest_path'])==f['manifest_sha256']=='25ddedcbf52dff612595770a671de3129d9e29e7da84212983094e6fe98baa5e'
fm=load(f['manifest_path'])
assert len(fm['sha256'])==f['binding_count']==677
for path,digest in fm['sha256'].items():assert sha(path)==digest,path
for folder,key in [('role6_friable','friable'),('role6_composite','composite')]:
    fp=B/'round20'/folder/'final_receipt.json'
    assert sha(fp)==f[key+'_final_receipt_sha256']
    fr=load(fp)
    assert sha(fr['manifest_path'])==fr['manifest_sha256']==f[key+'_final_manifest_sha256']
    assert sha(fr['report_path'])==fr['report_sha256']
    am=load(fr['manifest_path'])
    assert len(am['sha256'])==fr['binding_count']
    for path,digest in am['sha256'].items():assert fm['sha256'].get(path)==digest,path
lp=W/'source_budget_build_receipt.json'
assert sha(lp)=='ce9f0e0208f7d01346863c55848e322ca36bdc744ffa3c2da83dcbc21d74ac8c'
l=load(lp)
assert [x['exit_code'] for x in l['attempts']]==[1,0]
assert [x['credited_pass'] for x in l['attempts']]==[False,True]
actual=[]
for x in l['attempts']:
    assert x['post_integrity']['all_unchanged'] and not x['post_integrity']['failed_bindings']
    for k in ['snapshot','builder_snapshot','started_receipt','log']:
        assert sha(x[k])==x[k+'_sha256'],k
    start=load(x['started_receipt'])
    assert start['source_sha256']==x['source_sha256']==x['snapshot_sha256']
    assert start['command']==x['command'] and start['started_utc']==x['started_utc']
    if x['olean']:assert sha(x['olean'])==x['olean_sha256']
    for label,check in x['post_integrity']['checks'].items():
        assert check['unchanged'] and check['actual_sha256']==check['expected_sha256']
        if label!='source':assert sha(check['path'])==check['expected_sha256'],label
    actual.append({k:x[k] for k in ['attempt','started_utc','finished_utc','exit_code','credited_pass','source_sha256','snapshot_sha256','log_sha256','olean_sha256']})
initial=(W/'source_budget_attempt01_source_PREEXEC.lean.txt').read_text(encoding='utf-8')
current=(W/'FriableSourceBudget.lean').read_text(encoding='utf-8')
old='  have hden : 0 < 8192 * sourceU N * sourceEll N := by positivity'
new='  have hden : 0 < 8192 * sourceU N * sourceEll N :=\n    mul_pos (mul_pos (by norm_num) g.u_pos) hell'
assert initial.count(old)==1 and initial.replace(old,new)==current
imports={}
for root,name in [(W,'build_receipt.json'),(W,'extension_build_receipt.json'),(W,'aggregation_build_receipt.json'),
                  (W,'source_budget_build_receipt.json'),(B/'round20/role4_geometry','geometry_build_receipt.json')]:
    for module in load(root/name)['successful_modules'].values():
        for k in ['source','olean']:
            assert sha(module[k])==module[k+'_sha256']
            imports[Path(module[k]).relative_to(B).as_posix()]=module[k+'_sha256']
assert len(imports)==20
obs={'round':20,'observed_at_utc':datetime.now(timezone.utc).isoformat(),
     'global_FINAL6':{'receipt_sha256':sha(six),'report_sha256':f['report_sha256'],
                    'manifest_sha256':f['manifest_sha256'],'all677_bindings_verified':True,
                    'full_global_report_receipt_read':'83a35c','full_composite_annex_report_receipt_read':'83fd57'},
     'actual_source_budget_attempts':actual,'source_budget_ledger_sha256':sha(lp),
     'full_initial_source_read':'c4e4a7','full_actual_FAIL_log':'95168b',
     'full_PASS_log_and_only_repair_delta_read':'4b6ad0','only_source_repair_exactly_verified':True,
     'total_friable_and_geometry_author_passes':10,'total_actual_author_attempts':24,'technical_failures':14,
     'frozen_new_import_bindings':imports,'source_budget_scope':'actual theta-demand on F0-or-F1 plus unique F1 reciprocals',
     'source_budget_only_size_premise':'SourceOnset log N>=10^24',
     'source_budget_upper_bound':'N/(8192*log N*loglog N)',
     'F0_minus_F1_nonfriable_reciprocal_paid':False,'whole_ledger_paid':False,
     'independent_Judge20_done':False,'root_lean_executions':0,'root_mathematical_executions':0,'victory':False}
out=C/'messages/round20_final6_and_source_budget_root_observation.json';save(out,obs)
cp_path=C/'checkpoint.json';cp=load(cp_path)
cp['phase']='ROUND20_EXCEPTIONAL_SOURCE_BUDGET_AUTHOR_PASS_FINAL6_FROZEN_FORMAL3_IN_PROGRESS'
for item in cp['in_flight_executors']:
    if item['role']==6:item['status']='GLOBAL_FINAL6_TWO_NEW_BANKS_677_BINDINGS_ROOT_VERIFIED'
    if item['role']==4:item['status']='NINE_OWN_PLUS_ONE_GEOMETRY_FROZEN_PASS_SOURCE_BUDGET_ACTUAL_FINAL4_PENDING'
cp['last_progress']+=' FINAL6FULL83a35c/annex83fd57 all677bytes verified, no replay. Budget real[1,0]/delta exactlypositivitywrapper/stdaxioms,10PASSes24actuals inclgeo, actual exceptional sourcecost<=N/(8192uℓ) onsetseul. NoF0minusF1nonfriable/fullledger/Judge20/Win; feedbackconceptual tasked.'
cp_path.write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'observation':str(out),'sha256':sha(out),'verified_FINAL6_bindings':677,
                  'friable_author_passes_including_geometry':10,'actual_author_attempts':24,'root_math':0,'victory':False}))
