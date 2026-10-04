import sys, os, subprocess, hashlib, json
from pathlib import Path
from datetime import datetime, timezone
sys.dont_write_bytecode=True
W=Path(__file__).resolve().parent
R=W.parents[1]
CACHE=Path(r'D:\Users\Utilisateur\Desktop\Maths\q356-canonical-binding-replay\.lake\packages')
DEPS=R/'round13'/'role3'/'dependencies'
PACKAGES=['aesop','batteries','importGraph','LeanSearchClient','mathlib','plausible','proofwidgets','Qq']
env=dict(os.environ)
env['LEAN_PATH']=';'.join(map(str,[W,R/'round16'/'role4',DEPS,*[CACHE/p/'.lake'/'build'/'lib' for p in PACKAGES]]))
LEAN=Path(r'C:\Users\Utilisateur\.elan\toolchains\leanprover--lean4---v4.15.0\bin\lean.exe')
SRC=W/sys.argv[1]
P=W/'build_receipt.json'
d=json.loads(P.read_text(encoding='utf-8')) if P.exists() else {'attempts':[],'old_Lean_rebuilds':0,'old_olean_read_only':str(DEPS),'victory':False}
n=len(d['attempts'])+1
snap=W/f'attempt{n:02d}_source.lean.txt'; snap.write_bytes(SRC.read_bytes())
sha=lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
cmd=[str(LEAN),'-o',str(W/(SRC.stem+'.olean')),str(SRC)]
x=subprocess.run(cmd,cwd=W,env=env,capture_output=True,text=True,encoding='utf-8',errors='replace')
log=W/f'attempt{n:02d}.log'; log.write_text(x.stdout+x.stderr,encoding='utf-8')
assert SRC.read_bytes()==snap.read_bytes(),'Concurrent source mutation'
d['attempts'].append({'attempt':n,'timestamp_utc':datetime.now(timezone.utc).isoformat(),'source':str(SRC),'source_sha256':sha(SRC),'snapshot':str(snap),'snapshot_sha256':sha(snap),'log':str(log),'log_sha256':sha(log),'exit_code':x.returncode,'command':cmd})
P.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print(json.dumps({'attempt':n,'source':SRC.name,'exit_code':x.returncode})); print(x.stdout+x.stderr)
sys.exit(x.returncode)
