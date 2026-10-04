"""Record paper actor critique and source plan; no numeric/Lean execution."""
import json, hashlib, subprocess, sys
from pathlib import Path
from datetime import datetime, timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'); C=B/'.arbor/sessions/parity/.coordinator'; P=B/'round22/role6/contour_precritique22'
def read(p): return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
m=read(P/'paper_manifest22.json')
assert sha(P/'paper_manifest22.json')=='fe767a6228af36575130dfb4f618352aa50732827d87862eca1316cefd709611'
assert m['status']=='PAPER_COHERENT_SOURCE_COMPONENTS_TO_PREPARE'
assert len(m['artifacts'])==3 and len(m['inputs'])==4
for row in m['artifacts']+m['inputs']:
    p=Path(row['path']); assert sha(p)==row['sha256'] and p.stat().st_size==row['bytes'],row['path']
assert m['math_invocations']==m['Lean_invocations']==m['old_bank_replays']==0
assert not m['numeric_H1_certified'] and not m['formal_H1_certified'] and not m['producer_PREPARED'] and not m['cost_measured'] and not m['WIN']
base=read(B/'round22/role1_bridge/paper_manifest22.json')
for row in base['artifacts']+base['inputs']:
    p=Path(row['path']); p=p if p.is_absolute() else (B/'round22/role1_bridge'/p).resolve()
    assert sha(p)==row['sha256'],row['path']
obs={'created_utc':datetime.now(timezone.utc).isoformat(),'node':'15.3','status':m['status'],'paper_manifest_sha256':sha(P/'paper_manifest22.json'),'paper_artifact_and_input_bindings_verified':7,'original_role1_bindings_verified':14,'root_reads':{'report':'FULL50b1ac before freeze; actor reports unchanged final bytes; current SHA verified','requirements':'FULL40ec6a final frozen bytes, earlier e267c3 superseded','reads_manifest':'FULLd2f02a'},'actor_paper_verdict':'C3-C6 and finite C7-C9 coherent on paper, mathematical certifications and numerics not completed','selected_source_plan':m['selected_plan'],'required_corrections':['vertical i^k integration factors','separate function/position/weight/accumulation budgets','Gamma exponential reduction with certified domains','fresh unit-modulus recurrence radii','grouped psi/Mellin integrands and paid exchanges'],'infinite_zero_trace_scope':'Finite contour residues and J_infty are distinct; infinite zero contour passage remains open','numeric_H1_certified':False,'formal_H1_certified':False,'cost_measured':False,'next_step':'New component sources and frozen falsifiable thermal H1 execution contract; no mathematical invocation before its distinct gate','official_modules':62,'official_auxiliary_declarations':1049,'root_compiler_invocations':0,'root_numeric_invocations':0,'D_N_paid':False,'WIN':False}
with (C/'messages/round22_h1_paper_precritique_observation.json').open('x',encoding='utf-8') as f: json.dump(obs,f,ensure_ascii=False,indent=2); f.write('\n')
insight='New H1 15.3 paper independently reviewed by ROLE6: C3-C6 and finite residue C7-C9 coherent on paper; no numerical or formal global PASS. Original6papers/8inputs conserved and precritique3artifacts/4inputs frozen. DFT optimized by fresh exact unit-modulus recurrences at all204800nodes; four error classes/vertical i^k/domain reduction required. Cost unmeasured. SOURCE components in preparation; no gate/no run. Infinite zero contour passage distinct from finite certified residue. CoefficientN/D_N and WIN unpaid.'
H=r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py'
for cmd,items in [('record',['--node-id','15.3','--raw-report','# H1 paper critique and new evaluator source plan\n\n'+insight+'\n','--score','0','--insight',insight,'--result','PAPER_COHERENT_EVALUATOR_SOURCE_REQUIRED_GLOBAL_OPEN','--no-propagate']),('update',['--node-id','15.3','--status','running','--insight',insight])]:
    p=subprocess.run([sys.executable,'-B','-X','utf8',H,cmd,'--cwd',str(B),'--run-name','parity',*items],capture_output=True,text=True,encoding='utf-8'); assert p.returncode==0,(p.stdout,p.stderr)
cp=read(C/'checkpoint.json'); cp['phase']='ROUND22_G0_GAMMA_CERTIFIED_H1_PAPER_COHERENT_EVALUATOR_AND_PSI_SOURCE'
cp['previous_goal_turn_evidence']+=['.arbor/sessions/parity/.coordinator/messages/round22_h1_paper_precritique_observation.json','round22/role6/contour_precritique22/paper_manifest22.json']
(C/'checkpoint.json').write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
with (B/'REPORT.md').open('a',encoding='utf-8') as f: f.write('\nH1/15.3 : précritique indépendante sur papier cohérente, manifeste fe767a62 lié ; aucun nouveau calcul ni preuve globale compilée. Le plan DFT conserve tous les nœuds, optimise leurs puissances par récurrences certifiées et sépare quatre budgets. Primitives et contrat exécutables encore en préparation ; coût non mesuré. La trace finie et le passage infini des contours restent distincts. Aucun paiement du coefficient N ou de D_N, aucun WIN.\n')
print(json.dumps(obs,ensure_ascii=False,indent=2))
