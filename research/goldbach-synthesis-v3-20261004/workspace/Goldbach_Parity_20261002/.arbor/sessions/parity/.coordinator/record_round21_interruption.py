"""Supply terminal bookkeeping for retired21 nodes; no experiment/eval is run."""
from pathlib import Path
import subprocess,sys,json
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'); C=B/'.arbor/sessions/parity/.coordinator'
H=Path(r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py')
def invoke(cmd,*args):
    p=subprocess.run([sys.executable,'-B','-X','utf8',str(H),cmd,'--cwd',str(B),'--run-name','parity',*args],capture_output=True,text=True,encoding='utf-8')
    if p.returncode: raise RuntimeError((p.returncode,p.stdout,p.stderr))
    return p.stdout
insight='Stopped by explicit definitive user continuous pivot22 before any new round21 mathbank or Lean invocation. Sources uncompiled; not a mathematical FAIL and no victory. Banned local bilinear/sieve/AP methods are retired permanently for future research. Original57modules942aux retained. Controller21 freezes60files+self; registry22 binds3089 unchanged archives.'
for node in ('13.13','14.6'):
    invoke('record','--node-id',node,'--raw-report','# Interrupted experiment '+node+'\n\n'+insight+'\n\nStatus: NOT_EXECUTED_USER_PIVOT. Victory score0 is bookkeeping, not a mathematical evaluation.\n','--score','0','--insight',insight,'--result','NOT_EXECUTED_USER_PIVOT; zero mathematical/Lean trials','--no-propagate')
    invoke('update','--node-id',node,'--status','pruned','--insight',insight)
print(invoke('check','--strict'))
cp=json.loads((C/'checkpoint.json').read_text(encoding='utf-8')); cp['root_bookkeeping_incidents_round22']=[{'chunk':'398f80','kind':'STRICT_TREE_CHECK_MISSING_TERMINAL_NODE_REPORTS_METRICS_AFTER_INTERRUPTION','mathematical_failure':False,'correction':'write NOT_EXECUTED_USER_PIVOT record then restore pruned; no evaluation executed'}]
(C/'checkpoint.json').write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
