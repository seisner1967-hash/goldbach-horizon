"""ROOT metadata: preserve actual failure and authorize a distinct revision."""
import hashlib,json,subprocess,sys
from pathlib import Path
from datetime import datetime,timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C=B/'.arbor/sessions/parity/.coordinator'
P=B/'round22/role3/h1_psi/revision02'; OLD=P.parent/'psi_batch01_attempt01'
def read(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
mp=P/'psi_source_manifest22.json';m=read(mp)
assert sha(mp)=='ac2e76173f00e65e20914de041f654ba8394cfff2eaa7da2529c963deccc8ebf'
assert sha(P/'psi_prepared_receipt22.json')=='3bbf392f96aa67dfa3032d738e29c3573c1ad2c364ebaae2827bcbc8d835aa01'
assert sha(P/'run_psi_batch_once22.py')=='7d228a424b8b9ba19ea8046b4cf8ec2a7a845abd3dc4b782ed924e8701ebb2d4'
assert sha(P/'prepare_psi_metadata22.ps1')=='32f1a0bb779f2f67703e8ca4d0da2dc8fc0bc88422d2bc15c65e7927cb4970b4'
assert sha(P/'final_read_receipt22.json')=='a2b65eadd2f89cbb382eb61b72ce2311b3a2f77344aa34bef1ff2638dae90d7f'
assert m['status']=='PREPARED_SOURCE_ONLY' and m['compiler_invocations']==0
assert m['modules']==['GammaPsiCore22','GammaPsiBetaLimit22','GammaPsiIntegral22','GammaPsiDuplication22']
assert len(m['inputs'])==56 and m['declarations']==54
assert [r['declaration_count'] for r in m['catalog']]==[19,23,10,2]
for r in m['inputs']:
    p=Path(r['path']);assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes'],r['path']
for r in m['catalog']:
    assert sha(Path(r['path']))==sha(P/(r['module']+'.lean'))==r['sha256']
    assert len(r['declarations'])==r['declaration_count']
closure=read(Path(m['cache_closure_path']))
assert sha(Path(m['cache_closure_path']))=='90b9cf230702ca94abb0e055bc6b7bd5f6283371bcc7d471f7e47fc545c16d43'
assert closure['module_count']==len(closure['nodes'])==3238
assert closure['artifact_count']==len(closure['artifacts'])==6476
assert any(r['module']=='Init' for r in closure['nodes'])
for r in closure['artifacts']:
    p=Path(r['path']);assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes'],r['path']
assert sha(Path(m['python_path']))==m['python_sha256']=='4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c'
assert sha(Path(m['lean_path']))==m['lean_sha256']=='8a1ef18583d74d917194bba4743ce9765bad64b00c52bada002ee44796fb9e08'
assert sha(B/'round22/judge5/batch02_attempt01/GammaPrerequisites22.olean')==m['readonly_gamma_olean_sha256']=='fc0dad0b550f13a5c3a5b1e7cf1cfa22fc3a233822fc548cce155ab7a7274477'
nr=m['numeric_evidence'];actual=read(Path(nr['receipt_path']))
assert sha(Path(nr['receipt_path']))==nr['receipt_sha256']=='2c7409087b6f4c18d9de616592d3c8b3274622bd05feb9fd12d54f93a0548f48'
assert actual['exit_code']==1 and actual['result_sha256'] is None and actual['post_integrity']
assert not nr['numeric_PASS'] and not nr['counterexample_established']
assert sha(OLD/'receipt.json')=='273774ecce0500c970ecac573a6a541be786dae1ea9d52e647aaad21ef048f20'
assert sha(OLD/'GammaPsiCore22.log')=='1128364831728b06a269a279a56534a2d3c4144fa0da80d7c34c641f9e6a38ed'
old=read(OLD/'receipt.json');post=read(OLD/'POSTEXEC.json')
assert old['actual_child_invocations']==1 and old['rows'][0]['exit_code']==1
assert old['rows'][0]['olean_sha256'] is None and old['all_inputs_unchanged']
assert post['all_inputs_unchanged'] and len(post['inputs'])==47
assert len(post['cache_artifacts_hash_only_readonly'])==6476
assert all(r['status']=='NOT_INVOKED_PREVIOUS_MODULE_FAILED' for r in old['rows'][1:])
archives=read(B/'round22/previous_artifacts_sha256.json');assert archives['file_count']==3089
for rel,expected in archives['sha256'].items():assert sha(B/rel)==expected,rel
assert not (P/'psi_batch02_attempt01').exists()
gate={'schema':'ROUND22_ROLE3_H1_PSI_BATCH02_AUTHORIZATION_V1','created_utc':datetime.now(timezone.utc).isoformat(),
 'role':'ROLE3','node_id':'15.3','stage':'H1_PSI_BATCH02','attempt':'psi_batch02_attempt01',
 'authorized':True,'modules':m['modules'],'numeric_pass_required':False,'numeric_PASS':False,
 'numeric_counterexample_established':False,'numeric_receipt_sha256':nr['receipt_sha256'],'numeric_receipt_exit_code':1,
 'source_manifest_sha256':sha(mp),'launcher_sha256':sha(P/'run_psi_batch_once22.py'),
 'python_sha256':m['python_sha256'],'lean_sha256':m['lean_sha256'],'no_win':True,
 'readonly_gamma_olean_sha256':m['readonly_gamma_olean_sha256'],'compiler_invocations_maximum':4,
 'stop_first_failure':True,'retry_count':0,'verified_inputs':56,'verified_cache_artifacts':6476,
 'verified_cache_modules':3238,'protected_archives_verified':3089,
 'root_FULL_reads':{'Core':'2c186d','Beta':'740cee','Integral':'15b61e','Duplication':'9802c8',
 'launcher':'756bc2','builder':'5c7f0c','preparation_scope':'c8b2bc','prepared_finalread_receipts':'0a18c6',
 'failure_log':'01dcbf','failure_receipt':'113a6e','failure_diagnosis':'f8b4dc'},
 'manifest_scope':'Complete JSON parsed and all56bindings verified; header projection1dbe18, no FULL raw manifest/cache/API claim',
 'mathematical_source_review_owner':'ROLE3 author; ROLE4 original SOURCE a84072/41e749 and revision Core TARGETED65c06b',
 'global_H1_paid':False,'C5_paid':False,'D_N_paid':False,'WIN':False,
 'root_numeric_invocations':0,'root_compiler_invocations':0}
gp=C/'messages/round22_role3_psi_batch02_authorization1.json'
with gp.open('x',encoding='utf-8') as f:json.dump(gate,f,ensure_ascii=False,indent=2);f.write('\n')
insight='Psi author01 real Core exit1/no olean;3 following modules not invoked. Composition reduction and interval notation elaboration failures;17 standard prints and2 generated sorryAx give no PASS.47inputs/6476cache unchanged. Frozen distinct revision02 authorized four children STOPFIRSTFAIL. No analytic parity counterexample established; H1/D_N/WIN open.'
helper=r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py'
for command,items in [('record',['--node-id','15.3','--raw-report',insight,'--score','0','--insight',insight,'--result','PSI_CORE_AUTHOR01_TECHNICAL_LEAN_FAILURE','--no-propagate']),('update',['--node-id','15.3','--status','running','--insight',insight])]:
    child=subprocess.run([sys.executable,'-B','-X','utf8',helper,command,'--cwd',str(B),'--run-name','parity',*items],capture_output=True,text=True,encoding='utf-8')
    assert child.returncode==0,(child.stdout,child.stderr)
cpp=C/'checkpoint.json';cp=read(cpp)
cp['phase']='ROUND22_ANALYTIC_AND_COMPONENT_R01_RUNNING_PSI_FOUR_REVISION02_CHILDREN_AUTHORIZED'
cp['last_progress']=insight
for a in cp['in_flight_executors']:
    if a['role']==3:a['status']='PSI_BATCH02_FOUR_AUTHOR_CHILDREN_AUTHORIZED_NOT_STARTED'
cp['previous_goal_turn_evidence'].append(str(gp.relative_to(B)))
cpp.write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
with (B/'REPORT.md').open('a',encoding='utf-8') as f:
    f.write('\nψ auteur01 : Core seul exécuté10:28:31–10:29:02 UTC, exit1/aucun olean. Composition non réduite et notation intégrale mal lexée ;3 modules suivants non invoqués.17prints standards/2sorryAx générés ne constituent pas un PASS. Log et reçu conservés. Révision02 distincte de54déclarations autorisée sous STOPFIRSTFAIL après56bindings/6476cache/3089archives vérifiés. Aucun contre-exemple analytique/parité établi ; officiel62/1049inchangé, H1/D_N/WIN ouverts.\n')
print(json.dumps({'gate_path':str(gp),'gate_sha256':sha(gp),'verified_inputs':56,'verified_cache_artifacts':6476,
 'archives_verified':3089,'root_math_invocations':0,'root_compiler_invocations':0,'WIN':False},indent=2))
