"""One launch, capturing stdout and exit at execution; refuses repeat logging."""
import sys
sys.dont_write_bytecode=True
import subprocess,json
from pathlib import Path
from hashlib import sha256
from datetime import datetime,timezone
HERE=Path(__file__).resolve().parent
def digest(p):return sha256(p.read_bytes()).hexdigest()
receipt=HERE/'audit_launch_receipt.json';guard=HERE/'audit_launch_started.json'
assert not receipt.exists() and not guard.exists(),'Final audit already launched'
command=[sys.executable,'-B','-X','utf8',str(HERE/'run-audit.py')]
guard.write_text(json.dumps(dict(command=command,started_utc=datetime.now(timezone.utc).isoformat()))+'\n',encoding='utf-8')
completed=subprocess.run(command,cwd=HERE,capture_output=True,text=True,encoding='utf-8',errors='replace')
log=HERE/'audit_launch.log';log.write_text(completed.stdout+completed.stderr,encoding='utf-8')
data=dict(status='OBSERVED_SINGLE_FINAL_AUDIT',completed_utc=datetime.now(timezone.utc).isoformat(),
    command=command,exit_code=completed.returncode,invocations=1,audit_reexecuted_for_logging=False,
    numeric_producer_executed_by_judge=False,old_Lean_or_dependency_recompiled=False,
    log_sha256=digest(log),script_sha256=digest(HERE/'run-audit.py'),
    input_manifest_sha256=digest(HERE/'input_sha256.json'))
receipt.write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8')
print(completed.stdout+completed.stderr,end='');print(json.dumps(data,indent=2))
sys.exit(completed.returncode)
