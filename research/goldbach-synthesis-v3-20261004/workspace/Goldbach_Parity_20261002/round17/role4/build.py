import sys, os, subprocess, hashlib, json
from pathlib import Path
from datetime import datetime, timezone
sys.dont_write_bytecode = True
W = Path(__file__).resolve().parent
R = W.parents[1]
CACHE = Path(r'D:\Users\Utilisateur\Desktop\Maths\q356-canonical-binding-replay\.lake\packages')
PACKAGES = ['aesop','batteries','importGraph','LeanSearchClient','mathlib','plausible','proofwidgets','Qq']
env = dict(os.environ)
env['LEAN_PATH'] = ';'.join(map(str, [W,R/'round17'/'role3',*[CACHE/p/'.lake'/'build'/'lib' for p in PACKAGES]]))
LEAN = Path(r'C:\Users\Utilisateur\.elan\toolchains\leanprover--lean4---v4.15.0\bin\lean.exe')
SRC = W / sys.argv[1]
P = W / 'build_receipt.json'
record = json.loads(P.read_text(encoding='utf-8')) if P.exists() else {'attempts': [], 'old_Lean_rebuilds': 0, 'victory': False}
number = len(record['attempts']) + 1
snapshot = W / f'attempt{number:02d}_source.lean.txt'
snapshot.write_bytes(SRC.read_bytes())
output = W / f'attempt{number:02d}.olean'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
cmd = [str(LEAN), '-o', str(output), str(SRC)]
run = subprocess.run(cmd,cwd=W,env=env,capture_output=True,text=True,encoding='utf-8',errors='replace')
log = W / f'attempt{number:02d}.log'
log.write_text(run.stdout+run.stderr,encoding='utf-8')
assert SRC.read_bytes() == snapshot.read_bytes(), 'Concurrent source mutation'
record['attempts'].append({'attempt': number, 'timestamp_utc': datetime.now(timezone.utc).isoformat(),
  'source': str(SRC), 'source_sha256': sha(SRC), 'snapshot': str(snapshot), 'snapshot_sha256': sha(snapshot),
  'log': str(log), 'log_sha256': sha(log), 'exit_code': run.returncode, 'command': cmd,
  'olean': str(output) if output.exists() else None, 'olean_sha256': sha(output) if output.exists() else None})
if run.returncode == 0:
    final_output = W / (SRC.stem + '.olean')
    final_output.write_bytes(output.read_bytes())
    record['last_success'] = {'attempt': number,'source': str(SRC),'source_sha256': sha(SRC),
      'olean': str(final_output),'olean_sha256': sha(final_output)}
P.write_text(json.dumps(record,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print(json.dumps({'attempt': number,'source': SRC.name,'exit_code': run.returncode}))
print(run.stdout+run.stderr)
sys.exit(run.returncode)
