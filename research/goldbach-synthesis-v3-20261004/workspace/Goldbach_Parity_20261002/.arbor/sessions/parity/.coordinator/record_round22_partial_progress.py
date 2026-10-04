"""Record truthful partial running-node metadata, without running evaluation."""
import json, subprocess, sys
from pathlib import Path
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'); C=B/'.arbor/sessions/parity/.coordinator'
H=r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py'
def invoke(cmd,*args):
    p=subprocess.run([sys.executable,'-B','-X','utf8',H,cmd,'--cwd',str(B),'--run-name','parity',*args],capture_output=True,text=True,encoding='utf-8')
    assert p.returncode==0,(p.returncode,p.stdout,p.stderr)
    return p.stdout
rows=[('15.2','NOT_EXECUTED_FORMAL_AND_NUMERIC_SOURCE_PREPARATION','Frozen realWeil annex selected; actual ROLE4 source writes Gamma complex Laplace/rotation and explicit envelopes, not yet compiled. ROLE6 corresponding certified Gamma bank source preparation; no own math bank or Lean invocation authorized. Actual Weil formula/global zero count/trace evaluator/HEAT/coefficientN/D_N remain OPEN. NoWin.'),('16.1','ACTUAL_NUMERIC_AUX_PASS_FORMAL_PENDING','Actual unique ROLE6 Epstein24case AUX bank START06:49:45.399357..FIN06:49:54.814953UTC exit0. Full outputs and hashes observed by coordinator,23PREEXEC and21POST bindings verified.18finite routes agree,16qmutants detected,295198integer-square certificates. Source primitive/tail still paper-audited, author Lean/compiler/Judge not yet certified. Gamma/heat/scattering/coefficientN/D_N OPEN. NoWin.')]
for node,result,insight in rows:
    report='# Running experiment '+node+' — partial observation\n\n'+insight+'\n\nVictory score0 is a bookkeeping value, not a failed mathematical evaluation or a completion. Source development continues. Historical verified count57modules/942auxiliary theorems, zeroLean22. No old PASS replay.\n'
    invoke('record','--node-id',node,'--raw-report',report,'--score','0','--insight',insight,'--result',result,'--no-propagate')
    invoke('update','--node-id',node,'--status','running','--insight',insight)
out=invoke('check','--strict')
cp=json.loads((C/'checkpoint.json').read_text(encoding='utf-8'))
cp.setdefault('root_bookkeeping_incidents_round22',[]).append({'chunk':'962f8a','kind':'STRICT_CHECK_RUNNING_NODE_REPORT_METRICS_MISSING','mathematical_failure':False,'correction':'Truthful partial observations recorded with score0/no-propagate, nodes restored running; no evaluation or compiler.'})
(C/'checkpoint.json').write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(out)
