"""Select frozen H1 contour concept for independent paper precritique; metadata only."""
import json, hashlib, re, subprocess, sys
from pathlib import Path
from datetime import datetime, timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'); P=B/'round22/role1_bridge'; C=B/'.arbor/sessions/parity/.coordinator'
H=Path(r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py')
def read(p): return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def invoke(cmd,*args):
    p=subprocess.run([sys.executable,'-B','-X','utf8',str(H),cmd,'--cwd',str(B),'--run-name','parity',*args],capture_output=True,text=True,encoding='utf-8'); assert p.returncode==0,(p.stdout,p.stderr)
mp=P/'paper_manifest22.json'; m=read(mp)
assert sha(mp)=='812bad4eb69d612208eae8380d8bdc1dd8ab4fb2605d39eaa790f0479f2b37e3'
assert len(m['artifacts'])==6 and len(m['inputs'])==8
for row in m['artifacts']: assert sha(Path(row['path']))==row['sha256'] and Path(row['path']).stat().st_size==row['bytes'],row['path']
for row in m['inputs']: assert sha((P/row['path']).resolve())==row['sha256'],row['path']
assert m['mathematical_numeric_invocations']==m['lean_invocations']==m['tree_mutations']==0 and not m['victory'] and not m['actual_H1_certified']
lines=re.findall(r'^(?:Mechanism|Hypothesis|Observable|Conflicts):[^\n]+',(P/'ideation_probe22.md').read_text(encoding='utf-8'),re.M)
assert len(lines)==4 and [x.split(':',1)[0] for x in lines]==['Mechanism','Hypothesis','Observable','Conflicts']
before=read(C/'idea_tree.json'); assert '15' in before['nodes'] and '15.3' not in before['nodes']
invoke('add','--parent-id','15','--hypothesis','\n'.join(lines))
assert set(read(C/'idea_tree.json')['nodes'])-set(before['nodes'])=={'15.3'}
insight='Frozen SOURCE/PAPER H1 contour812bad4e/42faea33: true A=(s-1)zeta two vertical lines, exact functional-equation archimedean term, full Lambda/dual/proper powers; closed vertical tail without N(t). ROLE3 paper signs consistent, no Lean. New N1e8,Y1e4 bank204800complex+12288Arch proposed with genuine enclosures and3mutants, independent ROLE6 paper precritique active before any execution. No H1 formal/complete-zero/coefficientN/D_N/Win credit; no future forbidden methods.'
invoke('update','--node-id','15.3','--status','running','--insight',insight)
invoke('prompt-executor','--node-id','15.3','--workdir',str(B),'--additional-context','Independent ROLE6 SOURCE/PAPER precritique only of '+str(mp)+' SHA812bad4eb69d612208eae8380d8bdc1dd8ab4fb2605d39eaa790f0479f2b37e3. Ownership round22/role6/contour_precritique22/**. FULL small sources and complete byte checks; assess C3-C9/EM/Stirling/DFT/node domains/arch/prime-power certification/cost and negative controls. No Math/probe/compiler/bank replay/install until distinct prepared producer and ROOT gate. True arithmetic ledger, logN>=1e24 preserved; N1e8 finite heat bank only. H1 exact identity not an assumption, continuous error must be derived; no RH/simple/partial-zero-list/positivity/freeerror. Juge22 batch02 preparation separately handles Unfold/Tail/Gamma authorPASS; official59/993. No victory/global D_N bound.')
prompt=C.parent/'experiments/15.3/executor_prompt.md'
obs={'created_utc':datetime.now(timezone.utc).isoformat(),'status':'H1_CONTOUR_SELECTED_15_3_INDEPENDENT_PAPER_PRECRITIQUE_ONLY','node':'15.3','artifacts_verified':6,'read_inputs_verified':8,'manifest_sha256':sha(mp),'executor_prompt_sha256':sha(prompt),'fresh_constraints_FULL':'21c7e1','ideation_skill_FULL':'cbf72d','fourmoves_probe_scratch_FULL':'dca4ab','source_contract_obligations_FULL':'818c39','report_manifest_reads_FULL':'dca4ab','Math_authorized':False,'compiler_authorized':False,'D_N_bound':False,'WIN':False}
with (C/'messages/round22_h1_contour_selection.json').open('x',encoding='utf-8') as f: json.dump(obs,f,ensure_ascii=False,indent=2); f.write('\n')
cp=read(C/'checkpoint.json'); cp['current_nodes']=['15.2','16.1','15.3']; cp['phase']='ROUND22_H1_CONTOUR_15_3_PAPER_PRECRITIQUE_JUDGE_BATCH02_SOURCE'
cp['previous_goal_turn_evidence']+=['round22/role1_bridge/paper_manifest22.json','.arbor/sessions/parity/.coordinator/messages/round22_h1_contour_selection.json']
for actor in cp['in_flight_executors']:
    if actor['role']==1: actor['status']='GLOBAL_H1_PAPER_FINAL_ACTOR_COMPLETE'
    if actor['role']==3: actor['status']='G0_FOUR_MODULES_AUTHOR_PASS_ACTOR_COMPLETE'
    if actor['role']==5: actor['status']='BATCH01_CLOSED_BATCH02_INDEPENDENT_SOURCE_PREPARATION'
    if actor['role']==6: actor['status']='OLD_G0_GAMMA_BANKS_CLOSED_NEW_CONTOUR_PAPER_PRECRITIQUE_ACTIVE'
(C/'checkpoint.json').write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
with (B/'REPORT.md').open('a',encoding='utf-8') as f: f.write('\nH1 contour15.3 sélectionné après probe/quatre mouvements : bundlepapier812bad4e,6artifacts+8inputs vérifiés, ROOTconstraints21c7e1/IDEATEcbf72d. PrécritiqueROLE6 active, aucun calculautorisé. Deuxdroites/Mellin/équationfonctionnelle etArchexact proposé, enveloppecontinuepapier, coût etcertificatsàvérifier. H1formelle/coeffN/D_N/WIN restentouverts. Jugebatch02 prépare séparément3nouveauxmodulesauteurPASS.\n')
print(json.dumps(obs,ensure_ascii=False,indent=2))
