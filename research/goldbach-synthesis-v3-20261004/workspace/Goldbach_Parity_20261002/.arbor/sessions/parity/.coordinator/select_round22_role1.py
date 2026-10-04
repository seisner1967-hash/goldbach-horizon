"""Select frozen spectral concept22 for source preparation; byte metadata only."""
import json,hashlib,re,subprocess,sys
from pathlib import Path
from datetime import datetime,timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'); R=B/'round22'; C=B/'.arbor/sessions/parity/.coordinator'
H=Path(r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py')
def read(p): return json.loads(p.read_text(encoding='utf-8'))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def invoke(cmd,*args):
    p=subprocess.run([sys.executable,'-B','-X','utf8',str(H),cmd,'--cwd',str(B),'--run-name','parity',*args],capture_output=True,text=True,encoding='utf-8')
    if p.returncode: raise RuntimeError((p.returncode,p.stdout,p.stderr))
    return p.stdout
assert sha(R/'agent1_continuous.md')=='a2cbd2cc8664e6387c3117f9fdb7aaba4d0638a65ce5de0df60587863d19a2d4'
assert sha(R/'role1/manifest.json')=='8fe64dad218a8cc4ee20526c2a0c7263931c46492c15945a0036e6d64875c572'
assert sha(R/'role1/real_trace_annex.md')=='4736c056f047c84f4ebe38ed4f60b1a9c473481006dcee8341c168afdd9ea2b5'
m=read(R/'role1/manifest.json'); rd=read(R/'role1/read_receipts.json')
assert m['file_count']==len(m['files'])==11 and len(rd['local_reads'])==9
for row in m['files']: assert sha(Path(row['path']))==row['sha256'],row['path']
for row in rd['local_reads']: assert sha(Path(row['path']))==row['sha256'],row['path']
assert m['lean_invocations_22']==m['math_experiments_22']==m['producer_sources_22']==0 and not m['victory'] and not m['Dn_paid']
report=R/'role1/ideation_probe_candidates.md'; repair=R/'role1/repair_ideation.md'
def fourlines(p):
    lines=re.findall(r'^(?:Mechanism|Hypothesis|Observable|Conflicts):[^\n]+',p.read_text(encoding='utf-8'),re.M)
    assert len(lines)==4 and [x.split(':',1)[0] for x in lines]==['Mechanism','Hypothesis','Observable','Conflicts']
    return '\n'.join(lines)
before=read(C/'idea_tree.json'); assert '15' not in before['nodes']
# Depth1 is the category supplied by ROLE1's probe/five-field declaration;
# depth2 are the concrete compact test and its frozen real-test repair.
broad='\n'.join(['Mechanism: Dualité spectrale globale premiers-zéros et géométrie continue des fonctions test indépendantes des premiers.','Hypothesis: La formule explicite complète offre une représentation continue de la contribution arithmétique globale, avec modes et queues effectivement construits.','Observable: Identité analytique exacte et contrat de troncature falsifiable avec toutes erreurs, avant toute revendication de raccord au D_N.','Conflicts: Le pivot utilisateur22 abandonne définitivement les méthodes locales bilinéaires/crible/Mobius/Vaughan/AP ; aucune RH, positivité ou cible équivalente supposée.'])
invoke('add','--parent-id','ROOT','--hypothesis',broad)
assert set(read(C/'idea_tree.json')['nodes'])-set(before['nodes'])=={'15'}
invoke('add','--parent-id','15','--hypothesis',fourlines(report))
invoke('add','--parent-id','15','--hypothesis',fourlines(repair))
invoke('update','--node-id','15.1','--insight','Frozen paper W2/W7 exact compact correlation proposed; current displayed bound NON_INFORMATIVE_BOUND atN1e8/T<=3e12, omissionAA invisible. No numeric execution authorized or planned for this bound; not an identity falsification or LeanFAIL. FullWeil/zeroCount/bridge remain unformalized.')
invoke('update','--node-id','15.2','--status','running','--insight','Frozen realWeil annex225e74/report241f0e, H1allmodes and H2-H6closed error proposed. Independent ROLE6paper audit only; Y10000,T100,XQR1e6,tol1/100 prospective. Source-writing preparation only, no math/Lean execution. Completezeros/evaluator/formula/zeroCount proof remains; no coefficientN orD_N payment.')
invoke('prompt-executor','--node-id','15.2','--workdir',str(B),'--additional-context','ROUND22 definitive continuous pivot. Frozen REAL_TRACE annex '+str(R/'role1/real_trace_annex.md')+' SHA4736c056f047c84f4ebe38ed4f60b1a9c473481006dcee8341c168afdd9ea2b5; source report '+str(R/'agent1_continuous.md')+' SHAa2cbd2cc8664e6387c3117f9fdb7aaba4d0638a65ce5de0df60587863d19a2d4. Ownership round22/role4/**,agent4_formalisation.md, actor to be dispatched after slot free. Read/proofsource preparation only; zero compiler/APIprobe/Pythonmath until own new informativebank rootreview and source/builder/prep FULL+SHA gate. H2Gamma decay via complexLaplace rotation and Holder, H3-H6 closed tails with all modes; sourceWeil and zeroCount substantial independent proofs, never final hWeil/free trace/small bound premise. Compact15.1 is noninformative, not to be run asPASS. Preserve all3089 archives, sourceu>=1e24, sharpN/realtrace/D_N distinct. No bilinear arithmetic/sieve/Mobius inversion/Vaughan/scalarAP or oldPASSreplay. IndependentJudge only later; noWin.')
prompt=C.parent/'experiments/15.2/executor_prompt.md'
obs={'status':'ROUND22_FINAL1_FROZEN_SELECTED15.2_SOURCE_PREPARATION_ONLY','created_utc':datetime.now(timezone.utc).isoformat(),'broad_node':'15','sharp_pending_node':'15.1','selected_real_annex_node':'15.2','files_verified':11,'read_inputs_verified':9,'root_FULL_report':'241f0e','root_FULL_annex':'225e74','root_FULL_numeric_contract':'455755','root_FULL_lean_contract':'83a3d6','root_FULL_ideation':'8abe14','root_FULL_repair':'7ff45b','root_FULL_manifest':'ebfe9d','root_FULL_read_receipts':'5c8e35','fresh_constraints_FULL':'aeb5ad','ideation_skill_FULL':'6aac0f','manifest_sha256':sha(R/'role1/manifest.json'),'executor_prompt_sha256':sha(prompt),'actual_math_or_Lean_authorized':False,'victory':False}
(C/'messages/round22_role1_selection.json').write_text(json.dumps(obs,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
cp=read(C/'checkpoint.json'); cp['current_nodes']=['15.2']; cp['phase']='ROUND22_SPECTRAL_REALANNEX_SELECTED_GEOMETRIC_FINAL2_PENDING_GATES_CLOSED'
cp['in_flight_executors']=[{'role':2,'agent':'/root/round21_ideation1_signed','status':'GEOMETRIC_IDEATION_FINAL_PENDING'},{'role':3,'agent':'/root/round22_formal3_prepare','status':'READONLY_API_PREPARATION_NO_PROOF_OR_LEAN_YET'},{'role':6,'agent':'/root/round21_numeric_conservation','status':'EPSTEIN_AUX_SOURCE_PREPARATION_GATES_CLOSED'}]
cp['previous_goal_turn_evidence']+=['round22/agent1_continuous.md','round22/role1/real_trace_annex.md','round22/role1/manifest.json','.arbor/sessions/parity/.coordinator/messages/round22_role1_selection.json','.arbor/sessions/parity/experiments/15.2/executor_prompt.md']
(C/'checkpoint.json').write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps(obs,ensure_ascii=False,indent=2))
