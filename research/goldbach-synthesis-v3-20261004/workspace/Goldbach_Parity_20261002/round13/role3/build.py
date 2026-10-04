"""Round13 role3: rebuild only required dependencies, preserve every real attempt."""
import sys
sys.dont_write_bytecode = True
sys.stdout.reconfigure(encoding='utf-8', errors='replace')
from pathlib import Path
import hashlib, json, os, re, subprocess
from datetime import datetime, timezone
ROOT=Path(__file__).resolve().parents[1]
WORK=ROOT/'role3'; DEPS=WORK/'dependencies'; DEPS.mkdir(parents=True,exist_ok=True)
SRC=ROOT/'lean'/'PrimeSemiprimeSwitch.lean'
COMPILER=Path(r'C:\Users\Utilisateur\.elan\toolchains\leanprover--lean4---v4.15.0\bin\lean.exe')
CACHE=Path(r'D:\Users\Utilisateur\Desktop\Maths\q356-canonical-binding-replay\.lake\packages')
PACKAGES=['aesop','batteries','importGraph','LeanSearchClient','mathlib','plausible','proofwidgets','Qq']
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
bindings={'agent1_exchange.md':'2b64a5434c1dfde766436d5abd44b62a2714615992193a3f0e21bf90554d8c54','agent6.md':'00e234c7543fbb77d41f3f7d297c15b6bb649b6d940179509f7d916e68bb6bc0','numeric_manifest.json':'c8468f94a118555c842a47879772620bf9dca9d520a6b89cec54f2895a38f932','exchange.json':'d120360aeebf570b9cf75ca0922070bd40e750607e77d8362a8fff636eb6352d'}
for f,h in bindings.items(): assert sha(ROOT/f)==h,f
env=dict(os.environ);env['LEAN_PATH']=';'.join(map(str,[DEPS,*[CACHE/p/'.lake'/'build'/'lib' for p in PACKAGES]]))
version=subprocess.run([str(COMPILER),'--version'],capture_output=True,text=True,encoding='utf-8',errors='replace')
assert version.returncode==0 and '4.15.0' in version.stdout
receiptpath=WORK/'build_receipt.json'
receipt=json.loads(receiptpath.read_text(encoding='utf-8')) if receiptpath.exists() else {'attempts':[],'dependencies':[]}
for roundn,name,h,count in [(10,'ShortDivisorComplement','25f38fcb6f84b73551bf9d4131745d5c234a3187dd3e92a8402f8e81b721b447',17),(11,'ThreeAdicPrimePairing','b3c22b714566b3d6e1fa864c4414201c9a2215c506350bdf1c8373a598d26f48',19)]:
 old=ROOT.parent/f'round{roundn}'/'lean'/f'{name}.lean'; assert sha(old)==h
 ds=DEPS/f'{name}.lean'; do=DEPS/f'{name}.olean'
 if ds.exists():assert ds.read_bytes()==old.read_bytes()
 else:ds.write_bytes(old.read_bytes())
 if not do.exists():
  cmd=[str(COMPILER),'-o',str(do),str(ds)]
  done=subprocess.run(cmd,cwd=DEPS,env=env,capture_output=True,text=True,encoding='utf-8',errors='replace')
  log=WORK/f'dependency_{name}.log';log.write_text(done.stdout+done.stderr,encoding='utf-8')
  receipt['dependencies'].append({'source':str(ds),'source_sha256':sha(ds),'olean':str(do),'olean_sha256':sha(do) if do.exists() else None,'log':str(log),'log_sha256':sha(log),'exit_code':done.returncode,'fresh_round13_build':True,'historical_theorems_not_recounted':count,'command_argv':cmd})
  receiptpath.write_text(json.dumps(receipt,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
  assert done.returncode==0,done.stdout+done.stderr
attempt=len(receipt['attempts'])+1; stem=f'attempt{attempt:02d}'
snapshot=WORK/f'{stem}_source.lean.txt';snapshot.write_bytes(SRC.read_bytes());before=sha(snapshot)
olean=WORK/'PrimeSemiprimeSwitch.olean';cmd=[str(COMPILER),'-o',str(olean),str(SRC)]
done=subprocess.run(cmd,cwd=SRC.parent,env=env,capture_output=True,text=True,encoding='utf-8',errors='replace')
out=done.stdout+done.stderr;log=WORK/f'{stem}.log';log.write_text(out,encoding='utf-8')
assert sha(SRC)==before,'Concurrent source mutation'
receipt['attempts'].append({'attempt':attempt,'timestamp_utc':datetime.now(timezone.utc).isoformat(),'source_sha256':before,'snapshot':str(snapshot),'snapshot_sha256':sha(snapshot),'log':str(log),'log_sha256':sha(log),'exit_code':done.returncode,'command_argv':cmd})
receipt.update({'source':str(SRC),'source_sha256':sha(SRC),'compiler_version':version.stdout.strip(),'lean_path':env['LEAN_PATH'],'input_sha256':bindings,'status':'COMPILED_PARTIAL_REAL_SWITCH' if done.returncode==0 else 'COMPILER_ERROR','old_olean_copied':False,'old_PASS_replayed':False,'global_D_N':False,'victory':False})
if done.returncode==0:receipt.update({'olean':str(olean),'olean_sha256':sha(olean),'axiom_output':out})
receiptpath.write_text(json.dumps(receipt,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print(json.dumps({'attempt':attempt,'exit_code':done.returncode,'source_sha256':sha(SRC)},ensure_ascii=False));print(out)
sys.exit(done.returncode)
