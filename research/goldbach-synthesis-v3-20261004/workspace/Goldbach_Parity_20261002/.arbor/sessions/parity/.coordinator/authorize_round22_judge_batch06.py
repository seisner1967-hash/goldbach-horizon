"""ROOT metadata gate only; no Lean or numerical invocation."""
import hashlib, json
from pathlib import Path
from datetime import datetime, timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C=B/'.arbor/sessions/parity/.coordinator'; P=B/'round22/judge5/batch06'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p): return json.loads(p.read_text(encoding='utf-8-sig'))
expected={
 'prepared_manifest.json':'3ac0f1daf0dc8735f11ea6635bdb9405f38f8121252ac874269bf341e2edb929',
 'run_once.py':'c79764dbd3e70c2cf3eca90fc40c63ef17824a96189632950ac899e33dd02d56',
 'prepare_metadata.py':'a5f3a8d4b1c0d2287332b7daddd88c69fde009d48fcbcaa2e30efc408a4c2435',
 'preparation.md':'21f155df36fcd428c136d738f21f2053087b0c092b0341bf17b42645cb01beeb',
 'catalog.json':'4688c42445bea83f7da683863c392e03fb0d407be4f41c9c0408ac4d8246fc4a',
 'read_receipts.json':'ff7698f80e0978bf2725b70d8da5598cf9a15596bbf4024b0b95d60d88ca5838',
 'prepared_receipt.json':'8243cc24096ebd79e1e3a760c6e82d39bf9b0235c541762422cf44dc41792909',
 'import_bindings.json':'3a423d9273512b972345f8a72d559cbc7e61adcc2227b38007ce236789a51f67',
 'closed_judge_bindings.json':'6990b368dff55d76964031c30b7972db85f58754044916df463038adcafa7e67'}
for name,digest in expected.items(): assert sha(P/name)==digest,name
m=read(P/'prepared_manifest.json'); r=read(P/'prepared_receipt.json'); cat=read(P/'catalog.json')
imports=read(P/'import_bindings.json'); old=read(P/'closed_judge_bindings.json')
assert m['status']==r['status']=='PREPARED_SOURCE_ONLY_GATE_CLOSED'
assert not m['unresolved_modules'] and not imports['unresolved']
assert m['modules']==[x['module'] for x in cat['modules']]
assert len(m['modules'])==9 and cat['total_declarations']==88 and cat['theorem_count']==78 and cat['definition_count']==10
assert len(m['immutable_inputs'])==7019 and len(old['inputs'])==270 and imports['module_count']==3354
assert {'Init','Init.Prelude'} <= {x['module'] for x in imports['entries']}
assert not m['author_olean_used'] and m['compiler_invocations']==m['numeric_invocations']==0
assert not cat['non_DUP_modules_author_PASS_claimed'] and r['Dup05_author_PASS_only']
deps=['GammaPrerequisites22','GammaDerivative22','GammaBoxBounds22','GammaContourComponent22','GammaPsiCore22','GammaPsiBetaLimit22','GammaPsiIntegral22']
assert m['readonly_local_dependencies']==deps
for x in m['immutable_inputs']: assert sha(Path(x['path']))==x['sha256'],x['path']
for x in old['inputs']: assert sha(Path(x['path']))==x['sha256'],x['path']
for x in cat['modules']:
 assert sha(Path(x['source']))==sha(Path(x['original_source']))==x['source_sha256']
 assert len(x['qualified_prints'])==x['theorem_count']+x['definition_count']
for dep in cat['dependency_bindings']:
 receipt=read(Path(dep['independent_receipt']))
 row=next(x for x in receipt['rows'] if x['module']==dep['module'])
 assert receipt['all_inputs_unchanged'] and row['status']=='INDEPENDENT_LEAN_AUX_PASS'
 assert row['exit_code']==0 and row['exact_axiom_coverage_standard_only']
 assert sha(Path(dep['source']))==row['source_sha256']==dep['source_sha256']
 assert sha(Path(dep['olean_copy']))==sha(Path(dep['independent_olean']))==row['olean_sha256']==dep['olean_sha256']
archive=read(B/'round22/previous_artifacts_sha256.json')
assert archive['file_count']==len(archive['sha256'])==3089
for name,digest in archive['sha256'].items(): assert sha(B/name)==digest,name
cp=read(C/'checkpoint.json')
assert cp['official_auxiliary_validation']['modules']==68 and cp['official_auxiliary_validation']['declarations']==1132
assert not (P/'batch06_attempt01').exists()
gate=dict(schema='ROUND22_JUDGE5_BATCH06_AUTHORIZATION', time_utc=datetime.now(timezone.utc).isoformat(),
 role='ROLE5', authorized=True, attempt='batch06_attempt01', modules=m['modules'], compiler_invocations_maximum=9,
 source_manifest_sha256=expected['prepared_manifest.json'], launcher_sha256=expected['run_once.py'],
 preparation_receipt_sha256=expected['prepared_receipt.json'],
 python_sha256='4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c',
 lean_sha256='8a1ef18583d74d917194bba4743ce9765bad64b00c52bada002ee44796fb9e08',
 readonly_local_dependencies=deps, independent_audit=True, author_olean_allowed=False, no_win=True,
 ROOT_FULL_read_receipts=dict(launcher='1f0405',builder='1d7424',source_audit='21fe32',
  catalog=['0f80be','928127'],reads='cc3cfb',prepared_receipt='d88f70'),
 source_math_review_owner='ROLE5; ROOT binds review and hashes, does not perform mathematical audit',
 large_JSON_scope='Completely parsed and every bound byte hashed; no raw FULL import/runtime text claim',
 inputs_verified=7019,old_judge_files_verified=270,archives_verified=3089,
 stop_first_failure=True,retries=0,root_compiler_invocations=0,root_numeric_invocations=0,
 H1_paid=False,C5_global_paid=False,D_N_paid=False,WIN=False)
path=C/'messages/round22_judge5_batch06_authorization.json'
with path.open('x',encoding='utf-8') as target: json.dump(gate,target,ensure_ascii=False,indent=2);target.write('\n')
print(json.dumps(dict(gate=str(path),gate_sha256=sha(path),inputs=7019,old_judge_files=270,archives=3089,ROOT_compiler_invocations=0)))
