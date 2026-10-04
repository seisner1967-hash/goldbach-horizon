"""Record actor verdicts and byte conservation only; no Lean or mathematics."""
import hashlib,json,subprocess,sys
from pathlib import Path
from datetime import datetime,timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002');C=B/'.arbor/sessions/parity/.coordinator'
P=B/'round22/role3/h1_psi/revision03/psi_batch03_attempt01'
def read(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(P/'receipt.json')=='350be4276efe5013e9530037cc3ad22aeee6ce17231d45ffb1ed1883a9b5a1bf'
assert sha(P/'POSTEXEC.json')=='48c0e0684a1ddcbf8420dd64eaabb8483a6a78062c3a1634af17e9964d4e155c'
r=read(P/'receipt.json');post=read(P/'POSTEXEC.json')
assert r['status']=='AUTHOR_PSI_BATCH_FAILED' and r['actual_child_invocations']==2 and not r['hidden_retries']
assert r['all_inputs_unchanged'] and post['all_inputs_unchanged']
assert len(post['inputs'])==65 and len(post['cache_artifacts_hash_only_readonly'])==6476
for row in post['inputs']+post['cache_artifacts_hash_only_readonly']:assert sha(Path(row['path']))==row['sha256'],row['path']
core,beta=r['rows'][:2]
assert core['status']=='AUTHOR_LEAN_AUX_PASS' and core['exit_code']==0 and core['exact_axiom_coverage_standard_only']
assert len(core['axiom_rows'])==19 and sha(P/'GammaPsiCore22.olean')==core['olean_sha256']=='15f66830eab0ee8e192d4fffee9518abd001b3167c28c527881bbdaabefb9a4b'
assert beta['status']=='AUTHOR_LEAN_FAIL' and beta['exit_code']==1 and beta['olean_sha256'] is None
assert [x['status'] for x in r['rows'][2:]]==['NOT_INVOKED_PREVIOUS_MODULE_FAILED']*2
for row in (core,beta):assert sha(P/(row['module']+'.log'))==row['log_sha256']
archives=read(B/'round22/previous_artifacts_sha256.json');assert len(archives['sha256'])==archives['file_count']==3089
for rel,digest in archives['sha256'].items():assert sha(B/rel)==digest,rel
o={'schema':'ROUND22_PSI03_AUTHOR_CORE_PASS_BETA_FAILURE_OBSERVATION','time_utc':datetime.now(timezone.utc).isoformat(),
 'receipt_sha256':sha(P/'receipt.json'),'POST_sha256':sha(P/'POSTEXEC.json'),'receipt_FULL_read':'3fdcfb','Beta_log_FULL_read':'ceed0d',
 'Core_status':'AUTHOR_PASS19_INDEPENDENT_JUDGE_PENDING','Core_source_sha256':core['source_sha256'],'Core_olean_sha256':core['olean_sha256'],
 'Core_START':core['started_at'],'Core_FIN':core['finished_at'],'Beta_START':beta['started_at'],'Beta_FIN':beta['finished_at'],
 'Beta_status':'FOUR_TECHNICAL_ERRORS_NO_OLEAN_NO_PASS',
 'actor_diagnostic':'Complex.ofNat_re absent; t nonneg evidence for positivity; betaDifferenceIntegrand unfolding; function negation transport',
 'launcher_diagnostic':'linewise parser captured17/23 multiline axiom records; wholetext correction required without weakening sorryAx rejection',
 'later_modules_not_invoked':2,'inputs_verified':65,'cache_artifacts_verified':6476,'archives_verified':3089,
 'official_count_delta':0,'source_or_compile_failure_is_parity_counterexample':False,
 'root_compiler_invocations':0,'root_numeric_invocations':0,'H1_paid':False,'D_N_paid':False,'WIN':False}
op=C/'messages/round22_psi03_author_observation.json'
with op.open('x',encoding='utf-8') as f:json.dump(o,f,ensure_ascii=False,indent=2);f.write('\n')
insight='Psi03 Core actual authorPASS19 pending independent Judge; Beta exit1 four technical API/simplification errors/noolean, two later NOTINVOKED. Wholetext axiom parser required for multiline23 coverage. Psi04 three-module SOURCE reuses readonly Core; no target/DCT premise removed. Official count delta0; globalH1/D_N/WIN open.'
helper=r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py'
for cmd,args in [('record',['--node-id','15.3','--raw-report',insight,'--score','0','--insight',insight,'--result','PSI03_CORE_AUTHOR_PASS_BETA_TECHNICAL_FAIL','--no-propagate']),('update',['--node-id','15.3','--status','running','--insight',insight])]:
 child=subprocess.run([sys.executable,'-B','-X','utf8',helper,cmd,'--cwd',str(B),'--run-name','parity',*args],capture_output=True,text=True,encoding='utf-8');assert child.returncode==0,(child.stdout,child.stderr)
cpp=C/'checkpoint.json';cp=read(cpp);cp['last_progress']=insight
cp['previous_goal_turn_evidence'].append(str(op.relative_to(B)))
cpp.write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
with (B/'REPORT.md').open('a',encoding='utf-8') as f:f.write('\nψ03 : Core auteur PASS19 à10:59:30UTC, contrôle indépendant restant. Beta exit1 à11:00:03UTC : quatre erreurs API/simplification, aucun olean ; Integral et Dup non invoqués. Parseur des axiomes à corriger pour les sorties multilignes, sans affaiblir le rejet de sorryAx. ψ04 distinct réutilisera Core en lecture seule. Conservation65entrées/6476artefacts/3089archives. Aucun contre-exemple arithmétique établi, aucun crédit officiel supplémentaire ni H1/D_N/WIN.\n')
print(json.dumps(o,ensure_ascii=False,indent=2))
