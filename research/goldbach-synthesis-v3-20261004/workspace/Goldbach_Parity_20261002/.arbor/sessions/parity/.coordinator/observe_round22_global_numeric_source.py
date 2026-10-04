"""Bind a received SOURCE packet; no imports, parsing of Python or math runs."""
import hashlib,json,subprocess,sys
from pathlib import Path
from datetime import datetime,timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C=B/'.arbor/sessions/parity/.coordinator';P=B/'round22/role4/h1_global_numeric'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text(encoding='utf-8-sig'))
assert sha(P/'source_manifest22.json')=='e1caa3d115dd492cfa6d91478240b0e8418614b6faf8798f48e15312dfe11a51'
m=read(P/'source_manifest22.json');assert m['status']=='SOURCE_REVIEW_READY_THERMAL_C3_ONLY'
assert len(m['bindings'])==14 and m['runtime_python_modules']==9 and m['new_python_modules']==5
for row in m['bindings']:
 p=Path(row['path']);assert sha(p)==row['sha256'] and p.stat().st_size==row['bytes'],str(p)
assert all(value==0 for value in m['invocations'].values())
assert not m['numeric_result_exists'] and not m['gate_exists'] and not m['launcher_exists']
assert not m['structural_checker_is_interval_certificate'] and not m['runtime_cost_measured'] and not m['WIN'] and not m['old_results_are_inputs']
cpp=C/'checkpoint.json';cp=read(cpp)
assert cp['official_auxiliary_validation']['modules']==66 and cp['official_auxiliary_validation']['declarations']==1109
o={'schema':'ROUND22_GLOBAL_NUMERIC_SOURCE_ROOT_OBSERVATION','time_utc':datetime.now(timezone.utc).isoformat(),
 'status':'SOURCE_RECEIVED_INDEPENDENT_ANALYTIC_REVIEW_PENDING','manifest_sha256':sha(P/'source_manifest22.json'),
 'source_binding_count':14,'runtime_source_count':9,'new_source_count':5,
 'ROOT_FULL_reads':{'manifest':'a5375c','new_transport_envelopes_arithmetic':'69f784','producer':'fd7c38','checker':'b1529e','source_contract':'659e89','readonly_unit_transport':'44cbd6'},
 'prior_unchanged_ROOT_FULL_reads':{'dyadic_r01':'11d2a7','analytic_r01':'121f25','kernel_r01':'f633ac'},
 'scope':'Byte binding and source intake only; mathematical source audit delegated to ROLE3/ROLE5',
 'parameters':m['parameters'],'planned_catalogue':m['catalogue'],
 'numeric_run':False,'numeric_gate':False,'SOURCE_PREPARED':False,'numeric_PASS':False,
 'structural_checker_certifies_primitives':False,'runtime_cost_measured':False,
 'root_compiler_invocations':0,'root_numeric_invocations':0,'official_modules':66,'official_declarations':1109,
 'H1_paid':False,'C3_paid':False,'C5_paid':False,'D_N_paid':False,'WIN':False}
op=C/'messages/round22_global_numeric_source_observation.json'
with op.open('x',encoding='utf-8') as f:json.dump(o,f,ensure_ascii=False,indent=2);f.write('\n')
insight='Global thermal producer/checker SOURCE received:14 bytebindings9runtime5new, no execution/PREPARED/gate. ROLE3 independent numerical reviewer, ROLE5 paper error-envelope auditor, ROLE4 launcher SOURCE writer. Structural checker alone does not certify primitives. Official66/1109 unchanged; H1/C3/C5/coefficientN/D_N/WIN open.'
helper=r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py'
child=subprocess.run([sys.executable,'-B','-X','utf8',helper,'update','--cwd',str(B),'--run-name','parity','--node-id','15.3','--status','running','--insight',insight],capture_output=True,text=True,encoding='utf-8');assert child.returncode==0,(child.stdout,child.stderr)
cp['phase']='ROUND22_GLOBAL_NUMERIC_SOURCE_RECEIVED_INDEPENDENT_REVIEW_PENDING'
cp['last_progress']=insight;cp['previous_goal_turn_evidence'].append(str(op.relative_to(B)))
for actor in cp['in_flight_executors']:
 if actor['role']==3:actor['status']='ROLE6_GLOBAL_NUMERIC_SOURCE_INDEPENDENT_REVIEW_CONTOUR_MICRO_CHECKPOINT'
 elif actor['role']==4:actor['status']='GLOBAL_NUMERIC_SOURCE_HANDOFF_COMPLETE_LAUNCHER_SOURCE_WRITING'
 elif actor['role']==5:actor['status']='C5_SOURCE_AUDIT_CLOSED_PAPER_ERROR_CONTRACT_REVIEW'
cpp.write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
with (B/'REPORT.md').open('a',encoding='utf-8') as f:f.write('\nContrat numérique thermique global SOURCE reçu :14bindings/9runtime/5nouveaux vérifiés ROOT, paramètres N=1e8/Y=1e4/T=100/X=Q=R=1e6,204800nœuds verticaux/12288Arch/999999certificats prévus. Transport catalogue corrigé, dual16, mutant primal4 seul. Aucun résultat numérique/gate/PREPARED ni coût mesuré. Checker structurel ne certifie pas les primitives ; revue indépendante ROLE3 et enveloppes papier ROLE5 en cours. Launcher SOURCE ROLE4 en rédaction. Officiel66/1109 inchangé, H1/C3/C5/additif/D_N/WIN ouverts.\n')
print(json.dumps(o,ensure_ascii=False,indent=2))
