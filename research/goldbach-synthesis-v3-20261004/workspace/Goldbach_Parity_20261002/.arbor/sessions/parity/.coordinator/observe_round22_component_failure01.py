"""ROOT records actor's technical failure; metadata only, no mathematical evaluation."""
import hashlib, json, subprocess, sys
from pathlib import Path
from datetime import datetime, timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C=B/'.arbor/sessions/parity/.coordinator';P=B/'round22/role6/thermal_h1';A=P/'actual_component22'
def read(p): return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
receipt=read(A/'actual_receipt.json');post=read(A/'POSTEXEC_integrity.json');prep=read(P/'component_preparation22.json')
assert receipt['scope']=='THERMAL_COMPONENT_AUX_ONLY' and receipt['exit_code']==1
assert receipt['launch_error'] is None and receipt['result_sha256'] is None
assert not (A/'component_result22.json').exists()
assert receipt['post_integrity'] and post['all_unchanged']
assert post['preparation_unchanged'] and post['gate_unchanged']
assert receipt['log_sha256']==sha(A/'actual.log')=='5e311aa6a0bcd7fa6d8a92134a1dd9f56a183540f1031b698c6539f81ae66d45'
assert receipt['sqrt_certificate_sha256']==sha(A/'component_sqrt_certificates22.jsonl')=='eadd921cb6c220f3d870d6ec0ce7af51bfe8cb41a681a1c83431af86c0eb94a8'
assert sha(P/'component_preparation22.json')==receipt['preparation_sha256']=='b417be88862b3adb9636d90214243c943c4d8e054856dff3e93baf9be1280a5e'
gate=C/'messages/round22_thermal_component_authorization.json'
assert sha(gate)==receipt['root_gate_sha256']=='0eb9fef5c1796253b985c331a74b1b557c6dc57ca456c32fd93bef9f4f8b96d5'
assert len(post['bindings'])==len(prep['bindings'])==25
assert [(r['path'],r['actual_sha256']) for r in post['bindings']]==[(r['path'],r['sha256']) for r in prep['bindings']]
for row in prep['bindings']:
    path=Path(row['path']);assert sha(path)==row['sha256'] and path.stat().st_size==row['bytes']
for field in ('Lean_invocations','global_H1_invocations','old_bank_replays','coefficient_N_invocations'):
    assert receipt[field]==0
assert receipt['D_N_claim'] is False and receipt['WIN'] is False
archives=read(B/'round22/previous_artifacts_sha256.json')
assert archives['file_count']==3089
for relative,expected in archives['sha256'].items():assert sha(B/relative)==expected,relative
observation={'schema':'ROUND22_COMPONENT_FAILURE01_METADATA_OBSERVATION_V1',
 'observed_utc':datetime.now(timezone.utc).isoformat(),'node':'15.3',
 'status':'TECHNICAL_SERIALIZATION_FAILURE_NO_COMPLETE_RESULT',
 'actor_diagnosis':'ROLE6_67b1e1_FULL_LOG_ValueError_integer_string_conversion_limit4300',
 'root_FULL_reads':{'receipt':'326f41','log':'b75f26','post':'19d1bc'},
 'actual_START':receipt['actual_START'],'actual_FINISH':receipt['actual_FINISH'],
 'exit_code':1,'receipt_sha256':sha(A/'actual_receipt.json'),
 'log_sha256':sha(A/'actual.log'),'POSTEXEC_sha256':sha(A/'POSTEXEC_integrity.json'),
 'isqrt_file_sha256':sha(A/'component_sqrt_certificates22.jsonl'),
 'failure_site':'component_bank22.py:141 -> FourBudgets.as_json -> rational_json E_function',
 'bindings_verified':25,'protected_archive_paths_verified':3089,
 'attempt_consumed':True,'retry_allowed':False,'partial_PASS_allowed':False,
 'mathematical_counterexample_demonstrated':False,
 'next_step':'ROLE6 distinct SOURCE revision with constructed outward radius rounding; new gate required',
 'official_modules':62,'official_auxiliary_declarations':1049,
 'root_numeric_invocations':0,'root_Lean_invocations':0,
 'H1_numeric_certified':False,'H1_formal_certified':False,'D_N_paid':False,'WIN':False}
out=C/'messages/round22_component_failure01_observation.json'
with out.open('x',encoding='utf-8') as f:json.dump(observation,f,ensure_ascii=False,indent=2);f.write('\n')
insight='H1 component attempt01 ended exit1 after 208seconds: exact Fraction E_function JSON export exceeded Python4300-digit integer conversion limit. No complete result and no partial Gamma/EM/DFT PASS; no analytic counterexample demonstrated.25bindings+3089archives unchanged. Attempt closed without retry. Distinct outward-radius SOURCE revision pending new gate; globalH1/coefficientN/D_N/WIN open.'
helper=r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py'
for command,items in [('record',['--node-id','15.3','--raw-report','# Component technical failure01\n\n'+insight+'\n','--score','0','--insight',insight,'--result','TECHNICAL_SERIALIZATION_FAILURE_NO_COMPLETE_RESULT','--no-propagate']),('update',['--node-id','15.3','--status','running','--insight',insight])]:
    r=subprocess.run([sys.executable,'-B','-X','utf8',helper,command,'--cwd',str(B),'--run-name','parity',*items],capture_output=True,text=True,encoding='utf-8')
    assert r.returncode==0,(r.stdout,r.stderr)
cp_path=C/'checkpoint.json';cp=read(cp_path)
cp['phase']='ROUND22_H1_COMPONENT_TECHNICAL_FAILURE01_NEW_SOURCE_REVISION_AUTHOR_BATCHES_PREPARING'
cp['last_progress']=insight
for actor in cp['in_flight_executors']:
    if actor['role']==6:actor['status']='COMPONENT_TECHNICAL_FAILURE01_CLOSED_DISTINCT_SOURCE_REVISION_PREPARING'
cp['previous_goal_turn_evidence'].append('.arbor/sessions/parity/.coordinator/messages/round22_component_failure01_observation.json')
cp_path.write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
with (B/'REPORT.md').open('a',encoding='utf-8') as f:
    f.write('\nH1 composantes, tentative01 : exécution réelle 10:06:52–10:10:21 UTC, exit1. Échec technique de sérialisation du rayon E_function (>4300 chiffres), sans résultat complet et sans PASS partiel. Les25 liaisons et3089 archives sont intactes. Aucun contre-exemple analytique démontré. Tentative close ; nouvelle révision SOURCE des rayons arrondis vers l’extérieur en préparation, nouvelle autorisation interne nécessaire avant calcul. Les compilations H1 restent non exécutées ; officiel62modules/1049déclarations auxiliaires, aucune victoire.\n')
print(json.dumps(observation,ensure_ascii=False,indent=2))
