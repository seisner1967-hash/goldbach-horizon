"""Select frozen concept2 with fresh constraints and observed unique conservation; no math."""
import json,hashlib,re,sys,subprocess
from pathlib import Path
from datetime import datetime,timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'); R=B/'round21'; C=B/'.arbor/sessions/parity/.coordinator'
H=Path(r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py')
def read(p): return json.loads(p.read_text(encoding='utf-8'))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def invoke(command,*args):
    p=subprocess.run([sys.executable,'-B','-X','utf8',str(H),command,'--cwd',str(B),'--run-name','parity',*args],capture_output=True,text=True,encoding='utf-8')
    assert p.returncode==0,(p.stdout,p.stderr)
    return p.stdout
paths={
 R/'agent2_nonfriable.md':'35ef3537ff78fc1215d6481129d71e6df62b88cea2e5e80fdd6c7c41b7e76ac4',
 R/'role2/lean_contract.md':'ac1e6b2a5fd2bf5ce5cd083e1bc23b891d070cab1347f7137cde70eb8576d33e',
 R/'role2/numeric_contract.md':'8c9122a3854025edaf542a33d1eb55504f609640be3b5cdcd918089187d39a61',
 R/'role2/final_manifest.json':'f8ad7effc48387e5ac0d017725cb81a78c14fa817ef9b7798a03b85020825368',
 R/'role2/final_receipt.json':'1d8f387cedce90d01d7034de1b28d8a4df3e4ff71544f38a9f489bc86fead4ea',
 R/'role2/read_receipt.json':'7f51427e6c5f23b4b694b291bebfa495c585127f871aba1855ed873e4e4cedd3'}
for p,d in paths.items(): assert sha(p)==d,str(p)
f=read(R/'role2/final_receipt.json'); m=read(R/'role2/final_manifest.json'); rd=read(R/'role2/read_receipt.json')
assert f['status']=='FINAL2_IDEATION21_SOURCE_PARTIAL_PAYMENT_PROPOSED_NO_WIN'
assert f['actual_math_invocations']==f['actual_Lean_invocations']==f['actual_Judge_invocations']==0 and not f['victory']
assert f['output_files_frozen'] and f['all_read_inputs_unchanged_during_closure']
assert rd['full_count']==12 and rd['targeted_count']==5 and len(rd['entries'])==len(m['read_inputs'])==17
for path,d in m['bindings'].items(): assert sha(B/path)==d,path
for path,d in m['read_inputs'].items(): assert sha(Path(path))==d,path
for row in rd['entries']: assert m['read_inputs'][row['path']]==row['sha256']
assert sha(R/'role2/input_manifest.json')==f['input_manifest_sha256']
obs=read(C/'messages/round21_conservation_root_observation.json'); assert obs['credited_pass'] and obs['protected_byte_bindings_verified']==3028
report=R/'agent2_nonfriable.md'; txt=report.read_text(encoding='utf-8')
lines=re.findall(r'^(?:Mechanism|Hypothesis|Observable|Conflicts):[^\n]+',txt,re.M)
assert len(lines)==4 and [x.split(':',1)[0] for x in lines]==['Mechanism','Hypothesis','Observable','Conflicts']
before=read(C/'idea_tree.json'); assert before['nodes']['13.13']['status']=='running' and before['nodes']['14.5']['status']=='done'
invoke('add','--parent-id','14','--hypothesis','\n'.join(lines))
after=read(C/'idea_tree.json'); assert set(after['nodes'])-set(before['nodes'])=={'14.6'}
insight='Frozen FINAL2_21 FULLrootaefcce, contracts2dfec4/89530f, receipts0af8d1/d21739/manifestd46fca;17input hashes12FULL5TARGETED verified. Fresh37constraints FULLeb8022 with13.13running and3028actualconservationPASS beforeselection. True uniqueq F0-minus-F1 projection/rarity+globaltau² moment derived via gcd/lcm factorquad, CS and actual reciprocal sourceBracket budget35Nu^-14; extended20cost<=44Nu^-14<=N/(8192uell) prospective atsourceu>=1e24. Physical pair union retains intersections; complement/sourcebridge/parents/capacity/Gamma/TA/fullledgeropen/noWin. NewN1e8whole1001q2100100..2101100 +globalM2Nexact/oracle65536 prospective, allmath/Leanclosed.'
invoke('update','--node-id','14.6','--status','running','--insight',insight)
invoke('prompt-executor','--node-id','14.6','--workdir',str(B),'--additional-context',
 'ROUND21 selected ROLE2 FINAL='+str(report)+' SHA='+sha(report)+', contracts role2/lean_contract.md and numeric_contract.md. Ownership round21/role4/**,agent4_formalisation.md. Import Judge20/19/18/16/13 readonly; no oldPASSrebuild. New proofsource writing now, NO LEAN/compiler/APIprobe/math until new reciprocalbank21PASS rootreview and source/builder/prep FULL+hash gate. Derive actualglobaltau² moment, uniqueq projection/cardinality, CS/trueBracketcost35Nu^-14/extendedbudget/physicalunion, not free moment/cardinal/smallcost. Sourceonsetu>=1e24 only, N1e8guardsFALSE/Ytest4096 distinct. All actualFAIL PREEXECsource/command/log/exit archived; no unchangedPASSreplay; partialaux neverWin; root coordinator only; noGit/old3028write.')
pp=C.parent/'experiments/14.6/executor_prompt.md'; assert pp.is_file()
assert 'round21' in pp.read_text(encoding='utf-8') and 'round20/judge/run_once.py' not in pp.read_text(encoding='utf-8').replace('\\','/')
selection={'status':'ROUND21_ROLE2_ACTUALLY_SELECTED14.6_AFTER_FRESH_CONSTRAINTS_AND_UNIQUE_CONSERVATION',
 'created_utc':datetime.now(timezone.utc).isoformat(),'node':'14.6','parent':'14','depth':2,
 'report_sha256':sha(report),'manifest_sha256':sha(R/'role2/final_manifest.json'),'receipt_sha256':sha(R/'role2/final_receipt.json'),
 'lean_contract_sha256':sha(R/'role2/lean_contract.md'),'numeric_contract_sha256':sha(R/'role2/numeric_contract.md'),
 'input_paths_verified':17,'FULL_count':12,'TARGETED_count':5,'root_FULL_report_chunk':'aefcce',
 'root_FULL_lean_contract_chunk':'2dfec4','root_FULL_numeric_contract_chunk':'89530f',
 'root_FULL_final_receipt_chunk':'0af8d1','root_FULL_read_receipt_chunk':'d21739','root_FULL_manifest_chunk':'d46fca',
 'root_fresh_constraints_FULL_chunk':'eb8022','conservation_root_observation_sha256':sha(C/'messages/round21_conservation_root_observation.json'),
 'prompt_path':str(pp),'prompt_sha256':sha(pp),'sourcewriting_only_allowed':True,'Lean_or_numeric_execution_authorized':False,'victory':False}
(C/'messages/round21_role2_selection.json').write_text(json.dumps(selection,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
cp=read(C/'checkpoint.json'); cp['current_nodes']=['13.13','14.6']; cp['phase']='ROUND21_BOTH_CONCEPTS_SELECTED_SOURCEWRITING_ONLY_GATES_CLOSED'
cp['last_progress']+=' '+insight
cp['previous_goal_turn_evidence']+=['round21/agent2_nonfriable.md','round21/role2/final_receipt.json','.arbor/sessions/parity/.coordinator/messages/round21_role2_selection.json','.arbor/sessions/parity/experiments/14.6/executor_prompt.md']
(C/'checkpoint.json').write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
paper=C/'messages/round21_paper_directions_pending.json'; notes=read(paper); notes['role2']['root_validation']='Frozen FULLreportaefcce/contracts2dfec4/89530f/17inputsha verified;14.6selectedsourcewritingonly,no math/Lean result.'
paper.write_text(json.dumps(notes,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps(selection,ensure_ascii=False,indent=2))
