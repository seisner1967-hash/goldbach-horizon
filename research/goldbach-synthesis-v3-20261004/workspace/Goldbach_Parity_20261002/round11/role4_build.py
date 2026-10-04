"""Fresh offline build of unchanged U1 dependency and round11 actual pairing."""
import sys
sys.dont_write_bytecode = True
sys.stdout.reconfigure(encoding='utf-8', errors='replace')
from pathlib import Path
import hashlib, json, os, re, subprocess
from datetime import datetime, timezone
ROOT=Path(__file__).resolve().parent
SOURCE=ROOT/'lean'/'ThreeAdicPrimePairing.lean'
BUILD=ROOT/'role4_build'; BUILD.mkdir(exist_ok=True)
DEPS=BUILD/'dependency'; DEPS.mkdir(exist_ok=True)
COMPILER=Path(r'C:\Users\Utilisateur\.elan\toolchains\leanprover--lean4---v4.15.0\bin\lean.exe')
CACHE=Path(r'D:\Users\Utilisateur\Desktop\Maths\q356-canonical-binding-replay\.lake\packages')
PACKAGES=['aesop','batteries','importGraph','LeanSearchClient','mathlib','plausible','proofwidgets','Qq']
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
gatepath=ROOT/'paired_axes.json'; gate=json.loads(gatepath.read_text(encoding='utf-8'))
assert sha(gatepath)=='ff1f8526553f2861776e9aa3f492969274a664055b8e3fb6ea41bebe079c6173'
assert sha(ROOT/'paired_axes_checks.py')=='5c3f5d86120bbe5950dc4670e2b4854412de5f8077a3fc006a97a6d46343d2eb'
assert gate['status']=='PASS_NEW_PAIR_IDENTITY_ONLY' and not gate['victory']
assert all(x['status']=='PASS_FULL_FINITE_PARTITION_AND_P2_ONLY' for x in gate['full_partitions'].values())
assert set(gate['full_partitions'])=={'both_prime','one_prime_axis'}
assert all(x['disjoint_partition'] and x['P2_formal_scalar_identity'] and
 x['X_t']==[1,3,7] and x['D_t']==[1] and x['three_D_t']==[3] and x['F_t']==[7]
 for x in gate['full_partitions'].values())
assert sha(ROOT/'agent1_signed_compensation.md')=='41cf2ead5d3cb8aa399bfc148e1e29f0f543135ca8b225b0d92c7fb2253ed7dd'
previous=ROOT.parent/'round10'/'lean'/'ShortDivisorComplement.lean'
assert sha(previous)=='25f38fcb6f84b73551bf9d4131745d5c234a3187dd3e92a8402f8e81b721b447'
dependency=DEPS/'ShortDivisorComplement.lean'
if dependency.exists(): assert dependency.read_bytes()==previous.read_bytes()
else: dependency.write_bytes(previous.read_bytes())
libs=[CACHE/x/'.lake'/'build'/'lib' for x in PACKAGES]
assert all(x.is_dir() for x in libs)
env=dict(os.environ); env['LEAN_PATH']=';'.join(map(str,[DEPS,*libs]))
version=subprocess.run([str(COMPILER),'--version'],capture_output=True,text=True,encoding='utf-8',errors='replace')
assert version.returncode==0 and '4.15.0' in version.stdout
receiptpath=ROOT/'role4_build_receipt.json'
receipt=json.loads(receiptpath.read_text(encoding='utf-8')) if receiptpath.exists() else {'attempts':[]}
attempt=len(receipt['attempts'])+1; stem=f'attempt{attempt:02d}'
snapshot=BUILD/f'{stem}_source.txt'; snapshot.write_bytes(SOURCE.read_bytes())
source_sha_before=sha(snapshot)
dependency_olean=DEPS/'ShortDivisorComplement.olean'
if not dependency_olean.exists():
 dc=[str(COMPILER),'-o',str(dependency_olean),str(dependency)]
 done=subprocess.run(dc,cwd=DEPS,env=env,capture_output=True,text=True,encoding='utf-8',errors='replace')
 dl=BUILD/'dependency.log'; dl.write_text(done.stdout+done.stderr,encoding='utf-8')
 assert done.returncode==0,done.stdout+done.stderr
 receipt['dependency']={'source':str(dependency),'source_sha256':sha(dependency),'olean':str(dependency_olean),
  'olean_sha256':sha(dependency_olean),'log':str(dl),'log_sha256':sha(dl),'command_argv':dc,'fresh_round11_build':True}
olean=BUILD/'ThreeAdicPrimePairing.olean'
cmd=[str(COMPILER),'-o',str(olean),str(SOURCE)]
done=subprocess.run(cmd,cwd=SOURCE.parent,env=env,capture_output=True,text=True,encoding='utf-8',errors='replace')
output=done.stdout+done.stderr; log=BUILD/f'{stem}.log'; log.write_text(output,encoding='utf-8')
assert sha(SOURCE)==source_sha_before, 'Source changed during compilation; result inadmissible'
receipt['attempts'].append({'attempt':attempt,'timestamp_utc':datetime.now(timezone.utc).isoformat(),
 'command_argv':cmd,'source_sha256':sha(SOURCE),'snapshot':str(snapshot),'log':str(log),
 'log_sha256':sha(log),'exit_code':done.returncode,'gate_sha256':sha(gatepath),'gate_script_sha256':sha(ROOT/'paired_axes_checks.py')})
receipt.update({'source':str(SOURCE),'source_sha256':sha(SOURCE),'compiler_version':version.stdout.strip(),
 'lean_path':env['LEAN_PATH'],'status':'COMPILED_AUXILIARY_P1_P2' if done.returncode==0 else 'COMPILER_ERROR',
 'old_producer_olean_used':False,'old_pass_bank_replayed':False,'victory':False,
 'unresolved':['singleton and face compensation','H2 and J0/J1','physical-band onset','covered e']})
if done.returncode==0: receipt.update({'olean':str(olean),'olean_sha256':sha(olean),'axiom_output':output})
receiptpath.write_text(json.dumps(receipt,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print(json.dumps({'attempt':attempt,'exit_code':done.returncode,'source_sha256':sha(SOURCE),'receipt':str(receiptpath)},ensure_ascii=False))
print(output)
sys.exit(done.returncode)
