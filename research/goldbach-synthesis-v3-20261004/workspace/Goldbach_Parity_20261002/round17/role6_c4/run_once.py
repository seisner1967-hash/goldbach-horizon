"""Canonical new C4 only, with snapshots/logs for every real attempt."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
from hashlib import sha256
import subprocess,json
ROOT=Path(__file__).resolve().parent;source=ROOT/'moment_checks.py';marker=ROOT/'canonical_success.json'
assert not marker.exists(),'C4 canonical PASS already frozen'
attempt=len(list(ROOT.glob('attempt*_source.txt')))+1;stem=f'attempt{attempt:02d}'
snapshot=ROOT/(stem+'_source.txt');snapshot.write_bytes(source.read_bytes())
cmd=[sys.executable,'-B','-X','utf8',str(source)];done=subprocess.run(cmd,cwd=ROOT,capture_output=True,text=True,encoding='utf-8',errors='replace')
log=ROOT/(stem+'.log');log.write_text(done.stdout+done.stderr,encoding='utf-8');assert source.read_bytes()==snapshot.read_bytes()
entry={'attempt':attempt,'exit_code':done.returncode,'source_sha256':sha256(source.read_bytes()).hexdigest(),
 'snapshot_sha256':sha256(snapshot.read_bytes()).hexdigest(),'log_sha256':sha256(log.read_bytes()).hexdigest(),'command_argv':cmd}
if done.returncode==0:
 entry['output_sha256']=sha256((ROOT/'moment.json').read_bytes()).hexdigest();entry['status']='CANONICAL_NEW_C4_SUCCESS_DO_NOT_RERUN'
 marker.write_text(json.dumps(entry,indent=2)+'\n',encoding='utf-8')
else:(ROOT/(stem+'_failure.json')).write_text(json.dumps(entry,indent=2)+'\n',encoding='utf-8')
print(json.dumps(entry));print(done.stdout+done.stderr);sys.exit(done.returncode)
