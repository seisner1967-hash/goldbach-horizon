"""Select frozen TypeII obstruction18; coordinator bookkeeping only."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
from hashlib import sha256
import json,subprocess
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C=B/'.arbor/sessions/parity/.coordinator'
H=Path(r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py')
def read(p):return json.loads(p.read_bytes())
def invoke(cmd,*args):
    p=subprocess.run([sys.executable,'-B','-X','utf8',str(H),cmd,'--cwd',str(B),'--run-name','parity',*args],capture_output=True,text=True,encoding='utf-8')
    if p.returncode:print(p.stdout,p.stderr);raise SystemExit(p.returncode)
r=read(C/'messages/round18_root_conservation.json')
assert r['status']=='ROOT_VERIFIED_EXISTING_UNIQUE_PREFLIGHT18' and r['actual_preflight_attempts']==1 and r['actual_preflight_exit_code']==0
assert r['exact_inventory997'] and r['originals_preserved']
report='round18/agent1_calibrated_typeii.md'
h='228766a630e37e4cee7f92bc46cb862582da59379b15653f4c00abcbc37313f0'
assert sha256((B/report).read_bytes()).hexdigest()==h
tree=read(C/'idea_tree.json');assert '13.10' not in tree['nodes'],'Already selected; do not rerun'
text=(B/report).read_text(encoding='utf-8')
block=text.split('```text\n',1)[1].split('\n```',1)[0]
lines=block.splitlines();assert len(lines)==4
assert [s.split(':',1)[0] for s in lines]==['Mechanism','Hypothesis','Observable','Conflicts']
invoke('add','--parent-id','13','--hypothesis',block)
assert read(C/'idea_tree.json')['nodes']['13.10']['hypothesis']==block
invoke('update','--node-id','13.10','--status','running','--insight',
 'FINAL1 full read and frozen SHA confirmed; fresh constraints31findings5pruned/maxdepth2 read before selection. New separated-column TypeII obstruction and quantitative CRT bound written, no globalNoGo or Win. Actual candidate product and beta structural mask retained. New whole d91 finite contract selected; no numerical results presumed. Source d must grow; fixed omitted11 and structural A>0 guarded. Mixed physical aggregation/Gamma/ledger remain open.')
invoke('prompt-executor','--node-id','13.10','--workdir',str(B),'--additional-context',
 'Read PROBE18, frozen FINAL1 SHA '+h+', messages/round18_formalization_guard.md and feedback17. Protect997. Only new d91/c7/r13 complete b879121..989010, j10m..20m, v11..20 whole/gcd and omittedell11 authorized. h39/429, scopes0/91, capsactual3940/base4472, beta without jprime, actualkappaperiod1001, J/A/rho rational, theta/II/IIraw and E91/L11 prices all separate. Keep candidate multiplicities and one physical capacity pervertex. Sourceu>=10^24 applies only with growingd/ranges andellguard; no sourceestimate applied atN1e8. Formalization may be written now but compile after canonical numerical PASS and exact gate inspected, unless role6 falsifies the actual identity and kills it. R2/R3 must be derived on actualobjects, R6 never assumed. Independent Judge after all required frozenFINAL; no oldbanks/W/PASS/Lean reruns.')
receipt=dict(node='13.10',report=report,report_sha256=h,contract='FINAL1 section8 all six checks',
 numerical_contract_authorized=True,numerical_result_presumed=False,protected_artifacts=997,finite_N=100000000,
 finite_d=91,finite_b_interval=[879121,989010],finite_candidate_x=20000000,source_candidate_x='N/4 for explicit growing-d illustration',
 source_u_minimum='10^24',omitted_prime_for_incompatibility=11,structural_A_positive_guard=True,
 formal_sources_authorized=True,compiler_waits_for_canonical_numeric_PASS=True,victory=False)
(C/'messages/round18_typeii_selection.json').write_text(json.dumps(receipt,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
p=C/'checkpoint.json';cp=read(p)
cp.update(phase='ROUND18_TYPEII_SELECTED_NUMERIC_AND_FORMAL_PREPARATION',current_nodes=['13.10'],victory=False,objective_complete=False)
cp['last_progress']+=' FINAL1 frozen/full read and source guards reviewed; node13.10 selected after fresh constraints. New entire d91 numeric contract authorized; formal writing permitted but compilation waits canonical numeric PASS. No mathematical result presumed; remaining whole aggregation/Gamma and D_N open.'
cp['previous_goal_turn_evidence']=list(dict.fromkeys(cp['previous_goal_turn_evidence']+[report,'.arbor/sessions/parity/.coordinator/messages/round18_typeii_selection.json','.arbor/sessions/parity/experiments/13.10/executor_prompt.md']))
p.write_text(json.dumps(cp,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print('NODE13.10_SELECTED; new whole d91 numeric authorized; source writing permitted; compilation waits numericPASS; no math producer/compiler/audit invoked')
