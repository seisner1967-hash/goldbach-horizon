"""Single-use launcher. started marker forbids all post-PASS reruns."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import hashlib,json,subprocess,os
from datetime import datetime,timezone
HERE=Path(__file__).resolve().parent
started=HERE/'launch_started.json'
fd=os.open(started,os.O_WRONLY|os.O_CREAT|os.O_EXCL)
os.write(fd,(json.dumps({'started_utc':datetime.now(timezone.utc).isoformat(),'post_PASS_rerun_forbidden':True})+'\n').encode());os.close(fd)
source=HERE/'run-audit.py';snapshot=HERE/'audit_source.py.txt';snapshot.write_bytes(source.read_bytes())
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
command=[sys.executable,'-B','-X','utf8',str(source)]
with (HERE/'audit.log').open('w',encoding='utf-8') as log:
 p=subprocess.Popen(command,cwd=HERE,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,encoding='utf-8',errors='replace')
 for line in p.stdout:log.write(line);log.flush();print(line,end='',flush=True)
 code=p.wait()
receipt={'status':'COMPLETED_UNIQUE_AUDIT_LAUNCH','exit_code':code,'command':command,'source_sha256':h(source),'snapshot_sha256':h(snapshot),'log_sha256':h(HERE/'audit.log'),
 'input_manifest_sha256':h(HERE/'input_sha256.json'),'started_marker_sha256':h(started),'completed_utc':datetime.now(timezone.utc).isoformat(),'post_PASS_rerun_forbidden':True}
(HERE/'launch_receipt.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n',encoding='utf-8')
print(json.dumps(receipt),flush=True);sys.exit(code)
