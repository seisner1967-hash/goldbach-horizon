"""Canonical NEW round16 producer once; snapshots/logs for every real failure."""
import sys
sys.dont_write_bytecode=True
sys.stdout.reconfigure(encoding='utf-8',errors='replace')
from pathlib import Path
from hashlib import sha256
import subprocess,json,argparse,re
ROOT=Path(__file__).resolve().parent;WORK=ROOT/'role6';WORK.mkdir(exist_ok=True)
parser=argparse.ArgumentParser();parser.add_argument('bank');args=parser.parse_args()
assert re.fullmatch(r'[a-z][a-z0-9_]{1,40}',args.bank)
src=ROOT/f'{args.bank}_checks.py';assert src.is_file() and src.parent==ROOT
marker=WORK/f'{args.bank}_canonical_success.json';assert not marker.exists(),'Canonical PASS already obtained; do not rerun'
existing=sorted(WORK.glob(f'{args.bank}_attempt*_source.txt'));attempt=len(existing)+1;stem=f'{args.bank}_attempt{attempt:02d}'
snapshot=WORK/f'{stem}_source.txt';snapshot.write_bytes(src.read_bytes())
cmd=[sys.executable,str(src)];done=subprocess.run(cmd,cwd=ROOT,capture_output=True,text=True,encoding='utf-8',errors='replace')
log=WORK/f'{stem}.log';log.write_text(done.stdout+done.stderr,encoding='utf-8')
assert src.read_bytes()==snapshot.read_bytes(),'Concurrent source mutation'
entry={'attempt':attempt,'exit_code':done.returncode,'producer':str(src),'producer_sha256':sha256(src.read_bytes()).hexdigest(),'source_snapshot':str(snapshot),'source_snapshot_sha256':sha256(snapshot.read_bytes()).hexdigest(),'log':str(log),'log_sha256':sha256(log.read_bytes()).hexdigest(),'command_argv':cmd}
if done.returncode==0:
 output=ROOT/f'{args.bank}.json';assert output.is_file();entry.update({'output':str(output),'output_sha256':sha256(output.read_bytes()).hexdigest(),'status':'CANONICAL_NEW_SUCCESS_DO_NOT_RERUN'})
 marker.write_text(json.dumps(entry,indent=2)+'\n',encoding='utf-8')
else:(WORK/f'{stem}_failure.json').write_text(json.dumps(entry,indent=2)+'\n',encoding='utf-8')
print(json.dumps(entry));print(done.stdout+done.stderr);sys.exit(done.returncode)
