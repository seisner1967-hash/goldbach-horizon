"""Fresh role4 Lean build; old sources remain byte-identical and inputs frozen."""
import sys
sys.dont_write_bytecode=True
sys.stdout.reconfigure(encoding='utf-8',errors='replace')
from pathlib import Path
import hashlib,json,os,re,subprocess
from datetime import datetime,timezone
ROOT=Path(__file__).resolve().parents[1]
BUILD=ROOT/'role4'
DEPS=BUILD/'dependencies'
DEPS.mkdir(parents=True,exist_ok=True)
SOURCE=ROOT/'lean'/'HarmonicKernelVariation.lean'
COMPILER=Path(r'C:\Users\Utilisateur\.elan\toolchains\leanprover--lean4---v4.15.0\bin\lean.exe')
CACHE=Path(r'D:\Users\Utilisateur\Desktop\Maths\q356-canonical-binding-replay\.lake\packages')
PACKAGES=['aesop','batteries','importGraph','LeanSearchClient','mathlib','plausible','proofwidgets','Qq']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(ROOT/'agent2_signed_operator.md')=='91946283d4ca1f5021de670b16167e0a0714d0945104d30c4070ca9a26bc9c46'
assert sha(ROOT/'agent1_exchange.md')=='2b64a5434c1dfde766436d5abd44b62a2714615992193a3f0e21bf90554d8c54'
assert sha(ROOT/'agent6.md')=='00e234c7543fbb77d41f3f7d297c15b6bb649b6d940179509f7d916e68bb6bc0'
assert sha(ROOT/'numeric_manifest.json')=='c8468f94a118555c842a47879772620bf9dca9d520a6b89cec54f2895a38f932'
manifest=json.loads((ROOT/'numeric_manifest.json').read_text(encoding='utf-8'))
assert len(manifest['sha256'])==11
for rel,value in manifest['sha256'].items():assert sha(ROOT/rel)==value
origins=[(ROOT.parent/'round10'/'lean'/'ShortDivisorComplement.lean','25f38fcb6f84b73551bf9d4131745d5c234a3187dd3e92a8402f8e81b721b447'),
 (ROOT.parent/'round11'/'lean'/'ThreeAdicPrimePairing.lean','b3c22b714566b3d6e1fa864c4414201c9a2215c506350bdf1c8373a598d26f48')]
libs=[CACHE/x/'.lake'/'build'/'lib' for x in PACKAGES]
assert all(x.is_dir() for x in libs)
env=dict(os.environ);env['LEAN_PATH']=';'.join(map(str,[DEPS,BUILD,*libs]))
version=subprocess.run([str(COMPILER),'--version'],capture_output=True,text=True,encoding='utf-8',errors='replace')
assert version.returncode==0 and '4.15.0' in version.stdout
receiptpath=BUILD/'attempts.json'
receipt=json.loads(receiptpath.read_text(encoding='utf-8')) if receiptpath.exists() else {'attempts':[],'dependencies':[]}
for origin,expected in origins:
 assert sha(origin)==expected
 copy=DEPS/origin.name
 if copy.exists():assert copy.read_bytes()==origin.read_bytes()
 else:copy.write_bytes(origin.read_bytes())
 olean=copy.with_suffix('.olean')
 if not olean.exists():
  cmd=[str(COMPILER),'-o',str(olean),str(copy)]
  done=subprocess.run(cmd,cwd=DEPS,env=env,capture_output=True,text=True,encoding='utf-8',errors='replace')
  log=BUILD/(copy.stem+'_fresh.log');log.write_text(done.stdout+done.stderr,encoding='utf-8')
  receipt['dependencies'].append({'origin':str(origin),'origin_sha256':expected,'copy':str(copy),'copy_sha256':sha(copy),
   'olean':str(olean),'olean_sha256':sha(olean) if olean.exists() else None,'log':str(log),'log_sha256':sha(log),
   'command_argv':cmd,'exit_code':done.returncode,'fresh_from_source':True,'old_olean_used':False})
  receiptpath.write_text(json.dumps(receipt,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
  assert done.returncode==0,done.stdout+done.stderr
attempt=len(receipt['attempts'])+1;stem=f'attempt{attempt:02d}'
snapshot=BUILD/(stem+'_source.lean');snapshot.write_bytes(SOURCE.read_bytes())
cmd=[str(COMPILER),'-o',str(BUILD/'HarmonicKernelVariation.olean'),str(SOURCE)]
done=subprocess.run(cmd,cwd=SOURCE.parent,env=env,capture_output=True,text=True,encoding='utf-8',errors='replace')
output=done.stdout+done.stderr;log=BUILD/(stem+'.log');log.write_text(output,encoding='utf-8')
assert sha(SOURCE)==sha(snapshot)
receipt['attempts'].append({'attempt':attempt,'timestamp_utc':datetime.now(timezone.utc).isoformat(),
 'command_argv':cmd,'source':str(SOURCE),'source_sha256':sha(SOURCE),'snapshot':str(snapshot),'snapshot_sha256':sha(snapshot),
 'log':str(log),'log_sha256':sha(log),'exit_code':done.returncode})
receipt.update({'compiler':str(COMPILER),'compiler_sha256':sha(COMPILER),'compiler_version':version.stdout.strip(),
 'lean_path':env['LEAN_PATH'],'source':str(SOURCE),'source_sha256':sha(SOURCE),
 'status':'COMPILED_ACTUAL_FINITE_VARIATION' if done.returncode==0 else 'ACTUAL_COMPILER_ERROR',
 'old_pass_replayed':False,'old_olean_used':False,'victory':False,'global_D_N':False})
if done.returncode==0:receipt.update({'olean':str(BUILD/'HarmonicKernelVariation.olean'),
 'olean_sha256':sha(BUILD/'HarmonicKernelVariation.olean')})
receiptpath.write_text(json.dumps(receipt,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print(json.dumps({'attempt':attempt,'exit_code':done.returncode,'source_sha256':sha(SOURCE),'receipt':str(receiptpath)},ensure_ascii=False))
print(output)
sys.exit(done.returncode)
