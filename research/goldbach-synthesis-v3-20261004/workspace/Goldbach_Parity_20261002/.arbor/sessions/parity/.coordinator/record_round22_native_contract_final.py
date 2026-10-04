"""ROOT byte bindings and documentary checkpoint only, never compiler or math."""
import argparse, hashlib, json, subprocess, sys
from datetime import datetime, timezone
from pathlib import Path
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C=B/'.arbor/sessions/parity/.coordinator'
parser=argparse.ArgumentParser()
for n in ['delivery-path','delivery-sha','delivery-reads-path','delivery-reads-sha','ROOT-full-reads']:
 parser.add_argument('--'+n,required=True)
args=parser.parse_args()
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for block in iter(lambda:f.read(1048576),b''):h.update(block)
 return h.hexdigest()
def read(p):return json.loads(p.read_text(encoding='utf-8-sig'))
fixed=[
 ('round22/role4/circle_native_revision02/source_handoff22.json','889d4e221911bdfe75104361d62f36accf3770a17f48f29d84a9ba8d1952da88'),
 ('round22/role4/circle_native_build_source01/source_handoff22.json','12a414e0b96d068f65f0130474683bd3db27223ad9fc76f4f2b09c5946d3b8d1'),
 ('round22/role4/circle_native_build_source02/source_handoff22.json','13ee77e4b0dd922596c390e64f399b8ea423d075bb9eb5f25fa29785d94c3027'),
 ('round22/judge5/circle_native_build_controls_source_review01.md','a973cf3a34b61bd9d5c6dfa3272fccbf84ae829fc9be2fca7fa19999e74c7662'),
 ('round22/judge5/circle_native_controls_source_review02.md','205bf40885e9458d8e72684903cb2b67d586b05fd632ab0a786b90c6825cd81e'),
 ('round22/judge5/circle_native_build_controls_source_review02.md','1fee0de6627591ae3fb91e26c72649f66d026039230b2b6b6f6d11f10dbe6720'),
 ('round22/role3/native_build_metadata01/preflight_observation_manifest22.json','52a0686c1e03e4341dd29679c97a8bc50e7f64303f3373d0c03d3e244ce3f5e5'),
 ('round22/role3/native_build_metadata01/preflight_read_receipts22.json','b30f4a900038944aa917b37e22f717204557ce686b71c1f976ffcbf9d44cba26'),
 (args.delivery_path,args.delivery_sha),(args.delivery_reads_path,args.delivery_reads_sha)]
entries=[];bound={}
def binding(x):
 p=Path(x['path']);k=str(p.resolve()).casefold()
 if k in bound:assert (bound[k]['sha256'],bound[k]['bytes'])==(x['sha256'],x['bytes']),k
 bound[k]=x
for name,digest in fixed:
 p=B/name;assert p.resolve().is_relative_to(B.resolve()) and sha(p)==digest,str(p)
 entries.append(dict(path=name,sha256=digest,bytes=p.stat().st_size))
for name,_ in fixed[:3]:
 data=read(B/name);assert data['binding_count']==len(data['bindings'])
 for x in data['bindings']:binding(x)
snapshot=read(B/'round22/role4/circle_native_revision02/closure_snapshot22.json')
assert len(snapshot['bindings'])==6332
for x in snapshot['bindings']:binding(x)
support=read(B/'round22/role3/native_build_metadata01/preflight_observation_manifest22.json')
assert support['binding_count']==len(support['bindings'])==13
assert not support['compiler_loader_prerequisite_paid'] and support['compiler_invocations']==support['candidate_invocations']==0
for x in support['bindings']:binding(x)
delivery_reads=read(B/args.delivery_reads_path)
assert delivery_reads['binding_count']==len(delivery_reads['bindings'])==12
for x in delivery_reads['bindings']:binding(x)
for x in bound.values():
 p=Path(x['path']);assert p.stat().st_size==x['bytes'] and sha(p)==x['sha256'],str(p)
reg=B/'round22/previous_artifacts_sha256.json'
assert sha(reg)=='875cebdd8e510fe3341b05009a76991801777b2a060a07229c5323033226ba99'
archives=read(reg)['sha256'];assert len(archives)==3089
for name,digest in archives.items():
 p=(B/name).resolve();assert p.is_relative_to(B.resolve()) and sha(p)==digest,name
for rel in ['round22/role4/circle_native_revision02/build-final','round22/role4/circle_native_revision02/build_receipt22.json','round22/role4/circle_native_build_source01/actual_build01_attempt01','round22/role4/circle_native_build_source02/actual_build02_attempt01','round22/role4/circle_native_build_source02/build_preparation22.json','.arbor/sessions/parity/.coordinator/messages/round22_native_build02_authorization.json']:
 assert not (B/rel).exists(),rel
cp_path=C/'checkpoint.json';cp=read(cp_path)
assert cp['official_auxiliary_validation']['modules']==78 and cp['official_auxiliary_validation']['declarations']==1304
o=dict(schema='ROUND22_ROOT_NATIVE_SOURCE_AND_NUMERIC_CONTRACT_CHECKPOINT',time_utc=datetime.now(timezone.utc).isoformat(),status='CONTRACT_WITH_COMPILED_ERROR_DELIVERED_NATIVE_EXECUTION_UNPREPARED',entries=entries,ROOT_FULL_reads=args.ROOT_full_reads,bound_unique_files_physically_rehashed=len(bound),snapshot_binding_count=6332,protected_archives_physically_rehashed=3089,large_catalogue_scope='ALL_ENTRIES_PARSED_AND_ALL_BOUND_BYTES_VERIFIED_NOT_RAW_FULL',independent_source_math_owner='ROLE3_ROLE4_ROLE5',SOURCE_CWD_repair_reviewed=True,compiler_loader_prerequisite_paid=False,native_build_prepared=False,build_gate_created=False,compiler_invocations=0,native_numeric_invocations=0,new_Lean_credit=0,official_modules=78,official_declarations=1304,global_coefficient_N_computed=False,H1_uniform_paid=False,D_N_paid=False,WIN=False)
out=C/'messages/round22_native_contract_final_observation.json'
with out.open('x',encoding='utf-8') as f:json.dump(o,f,ensure_ascii=False,indent=2);f.write('\n')
insight='Boucle22 contrat continu final avec identites13/15 et precision/enveloppe17 compilees; officiel78/1304 auxiliaires. SOURCE natif02/BUILD02 et correctionCWD revus; preflightROLE6 conditionnel, loaderglobal non paye et aucunbuild/programme/banc coefficientN1e8 effectue. AnciensSOURCEs/3089archives intacts, ROOT metadata uniquement. D_N/parite/WIN ouverts; node15.3 running, score0 sans propagation.'
helper=r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py'
for command,extra in [('record',['--node-id','15.3','--raw-report',insight,'--score','0','--insight',insight,'--result','CONTINUOUS_CONTRACT_DELIVERED_NATIVE_LOADER_OPEN','--no-propagate']),('update',['--node-id','15.3','--status','running','--insight',insight])]:
 result=subprocess.run([sys.executable,'-B','-X','utf8',helper,command,'--cwd',str(B),'--run-name','parity',*extra],capture_output=True,text=True,encoding='utf-8');assert result.returncode==0,(result.stdout,result.stderr)
cp['native_contract_final_observation']=o
cp['phase']='ROUND22_CONTINUOUS_CONTRACT_DELIVERED_NATIVE_LOADER_AND_PARITY_OPEN'
cp['last_progress']=insight
cp['previous_goal_turn_evidence'].append(str(out.relative_to(B)))
cp_path.write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
with (B/'REPORT.md').open('a',encoding='utf-8') as f:f.write('\n'+insight+'\nLivraison: '+args.delivery_path+' SHA '+args.delivery_sha+'; ROOTFULL '+args.ROOT_full_reads+'\n')
print(json.dumps(o,ensure_ascii=False,indent=2))
