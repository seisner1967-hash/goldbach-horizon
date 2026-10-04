"""Reusable ROOT metadata-only gate for a new, explicitly locked Judge stage."""
import argparse,hashlib,json,re
from datetime import datetime,timezone
from pathlib import Path
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C=B/'.arbor/sessions/parity/.coordinator'
def sha(p):
 d=hashlib.sha256()
 with p.open('rb') as f:
  for block in iter(lambda:f.read(1048576),b''):d.update(block)
 return d.hexdigest()
def read(p):return json.loads(p.read_text(encoding='utf-8-sig'))
parser=argparse.ArgumentParser()
parser.add_argument('--batch',required=True)
parser.add_argument('--prior-modules',type=int,required=True)
parser.add_argument('--prior-declarations',type=int,required=True)
parser.add_argument('--module-count',type=int,required=True)
parser.add_argument('--declaration-count',type=int,required=True)
parser.add_argument('--theorem-count',type=int,required=True)
parser.add_argument('--definition-count',type=int,required=True)
parser.add_argument('--ROOT-full-read-receipts',required=True)
names=['manifest','launcher','builder','audit','catalog','reads','receipt','imports','closed']
for name in names:parser.add_argument('--'+name+'-sha',required=True)
args=parser.parse_args()
assert re.fullmatch(r'batch[0-9]{2}',args.batch)
P=B/'round22/judge5'/args.batch
file_names=['prepared_manifest.json','run_once.py','prepare_metadata.py','preparation.md','catalog.json','read_receipts.json','prepared_receipt.json','import_bindings.json','closed_judge_bindings.json']
expected={filename:getattr(args,name+'_sha') for name,filename in zip(names,file_names)}
for filename,digest in expected.items():
 assert re.fullmatch('[0-9a-f]{64}',digest) and sha(P/filename)==digest,filename
m=read(P/'prepared_manifest.json');r=read(P/'prepared_receipt.json');cat=read(P/'catalog.json')
imports=read(P/'import_bindings.json');old=read(P/'closed_judge_bindings.json')
assert m['status']==r['status']=='PREPARED_SOURCE_ONLY_GATE_CLOSED'
assert not m['unresolved_modules'] and not imports['unresolved']
assert m['modules']==[x['module'] for x in cat['modules']]
assert len(m['modules'])==cat['module_count']==args.module_count
assert cat['total_declarations']==r['declarations']==args.declaration_count
assert cat['theorem_count']==args.theorem_count and cat['definition_count']==args.definition_count
assert args.theorem_count+args.definition_count==args.declaration_count
assert len(m['immutable_inputs'])==r['inputs']
assert len(old['inputs'])==r['closed_judge_files'] and imports['module_count']==r['imports']
assert {'Init','Init.Prelude'} <= {x['module'] for x in imports['entries']}
assert not m['author_olean_used'] and m['compiler_invocations']==m['numeric_invocations']==0
assert cat['readonly_local_dependencies']==m['readonly_local_dependencies']
assert not set(m['modules'])&set(m['readonly_local_dependencies'])
for x in m['immutable_inputs']:assert sha(Path(x['path']))==x['sha256'],x['path']
for x in old['inputs']:assert sha(Path(x['path']))==x['sha256'],x['path']
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
archive_path=B/'round22/previous_artifacts_sha256.json'
assert sha(archive_path)=='875cebdd8e510fe3341b05009a76991801777b2a060a07229c5323033226ba99'
archive=read(archive_path)
assert archive['file_count']==len(archive['sha256'])==3089
for relative,digest in archive['sha256'].items():
 p=(B/relative).resolve();assert p.is_relative_to(B.resolve()) and sha(p)==digest,relative
cp=read(C/'checkpoint.json')
assert cp['official_auxiliary_validation']['modules']==args.prior_modules
assert cp['official_auxiliary_validation']['declarations']==args.prior_declarations
attempt=args.batch+'_attempt01';assert not (P/attempt).exists()
gate=dict(schema='ROUND22_JUDGE5_'+args.batch.upper()+'_AUTHORIZATION',time_utc=datetime.now(timezone.utc).isoformat(),
 role='ROLE5',authorized=True,attempt=attempt,modules=m['modules'],compiler_invocations_maximum=args.module_count,
 source_manifest_sha256=expected['prepared_manifest.json'],launcher_sha256=expected['run_once.py'],
 preparation_receipt_sha256=expected['prepared_receipt.json'],
 python_sha256='4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c',
 lean_sha256='8a1ef18583d74d917194bba4743ce9765bad64b00c52bada002ee44796fb9e08',
 readonly_local_dependencies=m['readonly_local_dependencies'],independent_audit=True,author_olean_allowed=False,no_win=True,
 ROOT_FULL_read_receipts=args.ROOT_full_read_receipts,source_math_review_owner='ROLE5',
 large_JSON_scope='All entries parsed and bound bytes hashed; raw FULL import source text not claimed',
 inputs_verified=len(m['immutable_inputs']),old_judge_files_verified=len(old['inputs']),archives_verified=3089,
 prior_modules=args.prior_modules,prior_declarations=args.prior_declarations,
 stop_first_failure=True,retries=0,ROOT_compiler_invocations=0,ROOT_numeric_invocations=0,
 H1_paid=False,C5_global_paid=False,D_N_paid=False,WIN=False)
path=C/'messages'/('round22_judge5_'+args.batch+'_authorization.json')
with path.open('x',encoding='utf-8') as f:json.dump(gate,f,ensure_ascii=False,indent=2);f.write('\n')
print(json.dumps(dict(gate=str(path),gate_sha256=sha(path),inputs=gate['inputs_verified'],
 old_judge_files=gate['old_judge_files_verified'],archives=3089,modules=args.module_count,
 declarations=args.declaration_count,ROOT_compiler_invocations=0,ROOT_numeric_invocations=0)))
