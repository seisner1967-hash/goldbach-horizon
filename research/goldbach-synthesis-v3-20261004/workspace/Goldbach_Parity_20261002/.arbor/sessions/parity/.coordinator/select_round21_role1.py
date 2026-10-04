"""Select frozen concept1 after actual conservation and fresh constraints; no math."""
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
report=R/'agent1_signed.md'; receipt=R/'role1/final_receipt.json'; manifest=R/'role1/final_manifest.json'
assert sha(report)=='0e6bac077503477d03f78c3c121b40134a67e1504b733bfb26175efeca884d70'
assert sha(receipt)=='4b11463da4c68dc8d550c99ffb1b6d3c850b8e6b7033793bfa0b5e58728d2615'
assert sha(manifest)=='271579f39a1f5a722c032cb0aa0842253da561042e9aaef37c389a4bf541fdb7'
f=read(receipt); m=read(manifest)
assert f['status']=='FINAL1_FROZEN_NO_WIN' and f['actual_Lean_invocations']==f['actual_math_Python_invocations']==f['actual_Judge_invocations']==0
assert not f['victory'] and f['input_integrity_unchanged'] and f['source_outputs_frozen']
for path,d in m['bindings'].items(): assert sha(B/path)==d,path
inputs=R/'role1/input_manifest.json'; assert sha(inputs)==f['input_manifest_sha256']==m['input_manifest_sha256']
entries=read(inputs)['entries']; assert len(entries)==f['input_count']==16
assert sum(x['read_mode']=='FULL' for x in entries)==13 and sum(x['read_mode']=='TARGETED' for x in entries)==3
for row in entries: assert sha(Path(row['path']))==row['sha256'],row['path']
obs=read(C/'messages/round21_conservation_root_observation.json')
assert obs['status']=='ROOT_VERIFIED_ACTUAL_UNIQUE_CONSERVATION21_PASS' and obs['credited_pass'] and obs['protected_byte_bindings_verified']==3028
# Freeze conservation documentation too, without invoking its source or launcher.
cf=read(R/'role6/conservation_final_receipt.json'); cm=read(R/'role6/conservation_final_manifest.json')
assert sha(R/'role6/conservation_final_receipt.json')=='9ca593f3111d88524e61668b96e9a1753dce10d2d84fa9c1896096753ac723ea'
assert sha(R/'role6/conservation_final_manifest.json')==cf['frozen_manifest_sha256']=='a84046127d46d062887b525a2863b8127c07fae5ad46f7f55062820d63dab275'
assert len(cm['bindings'])==cf['frozen_manifest_binding_count']==20
for path,d in cm['bindings'].items(): assert sha(B/path)==d,path
assert sha(R/'role6/conservation_final.md')==cf['report_sha256']=='6b38b1b410eb3b555e2ac4861de3ee4306da64220a96f275ed77ca4d7e4a3c11'
txt=report.read_text(encoding='utf-8'); block=re.search(r'```text\n(Mechanism:.*?\nConflicts:[^\n]+)\n```',txt,re.S).group(1)
assert len(block.splitlines())==4
assert [x.split(':',1)[0] for x in block.splitlines()]==['Mechanism','Hypothesis','Observable','Conflicts']
before=read(C/'idea_tree.json'); assert before['nodes']['13.12']['status']==before['nodes']['14.5']['status']=='done'
invoke('add','--parent-id','13','--hypothesis',block)
after=read(C/'idea_tree.json'); delta=set(after['nodes'])-set(before['nodes']); assert delta=={'13.13'}
insight='Frozen FINAL1_21 FULLroot9a0508/7520tokens,16readinputs13FULL3TARGETED verified, no math/Lean. Actualunique3028conservationPASS root61de9a and20documentarybindings verified; fresh37constraints FULL5fffe5 beforeselection. Physical-window/AP bridge plus finite jump/leftlimit envelope Ephys and true Abel variation bound32Ephys/7+16u/7 selected; E not small, SD/BV/M0/kappa/globalcapacity/fullledger remainopen/noWin. NewN1e8whole12.5m<j<=25m bank prospective, overlap19/20declared, code/runtimegatesclosed. Provenance static correction unobservedchunks documented beforefreeze; bytes/saveview support claimed.'
invoke('update','--node-id','13.13','--status','running','--insight',insight)
prompt=invoke('prompt-executor','--node-id','13.13','--workdir',str(B),'--additional-context',
 'ROUND21 selected ROLE1 FINAL source='+str(report)+' SHA='+sha(report)+'. Ownership round21/role3/** and agent3_formalisation.md. Import Judge20/19/18/16/13 oleans readonly; never rebuild old PASS or use author21oleans in independent Judge. Sourcewriting only now; NO LEAN/compiler/APIprobe/math until new numeric21PASS rootreview and frozen source/builder/prep FULL+hash gate. Actual physical-frame/AP finite envelope/variation/Abel/prices named20 required, no free small E/SD/Gamma or target premise. All actual failures PREEXECsource/command/log/exit archived; no unchangedPASSreplay. Sourceu>=1e24, finiteN1e8onsetFALSE, PP/Q/k1/wholeUa/fullledger kept; partialaux neverWin. Root coordinator only. No Git/mutation old3028.')
pp=C.parent/'experiments/13.13/executor_prompt.md'; assert pp.is_file()
assert 'round21' in pp.read_text(encoding='utf-8') and 'round20/judge/run_once.py' not in pp.read_text(encoding='utf-8').replace('\\','/')
selection={'status':'ROUND21_ROLE1_ACTUALLY_SELECTED13.13_AFTER_FRESH_CONSTRAINTS_AND_UNIQUE_CONSERVATION',
 'created_utc':datetime.now(timezone.utc).isoformat(),'node':'13.13','parent':'13','depth':2,'report_sha256':sha(report),
 'manifest_sha256':sha(manifest),'receipt_sha256':sha(receipt),'input_paths_verified':16,
 'root_FULL_report_chunk':'9a0508','root_FULL_receipt_chunk':'1b9d4b','root_FULL_provenance_chunk':'4f1926',
 'root_fresh_constraints_FULL_chunk':'5fffe5','conservation_root_observation_sha256':sha(C/'messages/round21_conservation_root_observation.json'),
 'prompt_path':str(pp),'prompt_sha256':sha(pp),'sourcewriting_only_allowed':True,'Lean_or_numeric_execution_authorized':False,'victory':False}
(C/'messages/round21_role1_selection.json').write_text(json.dumps(selection,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
cp=read(C/'checkpoint.json'); cp['current_nodes']=['13.13']; cp['phase']='ROUND21_ROLE1_SELECTED_SOURCEWRITING_ONLY_ROLE2_SELECTION_PENDING'
cp['last_progress']+=' '+insight
cp['previous_goal_turn_evidence']+=['round21/agent1_signed.md','round21/role1/final_receipt.json','.arbor/sessions/parity/.coordinator/messages/round21_role1_selection.json','.arbor/sessions/parity/experiments/13.13/executor_prompt.md']
(C/'checkpoint.json').write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
# Correct only mutable coordinator's record of an author-reported but unobserved chunk.
paper=C/'messages/round21_paper_directions_pending.json'; notes=read(paper)
notes['role1']['agent_reported_fresh_constraints_full_read_chunk']='Unobserved preparatory mention69f593 withdrawn; use saved view SHA8fa53bf40b5848895b11c9f600704ceadeeb97ee7de2b51a4efba64efffa306e'
notes['role1']['root_validation']='Frozen final report FULL9a0508 and16input hashes verified; node13.13selected only, no math/Lean result.'
paper.write_text(json.dumps(notes,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps(selection,ensure_ascii=False,indent=2))
