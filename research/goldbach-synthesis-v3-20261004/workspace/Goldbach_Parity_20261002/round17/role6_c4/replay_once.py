"""Exactly one separate replay of the new C4 annexe after PASS."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import subprocess,json
sys.path.insert(0,str(Path(__file__).resolve().parent))
import shared as c
ROOT=c.ROOT;dest=ROOT/'replay_receipt.json';assert not dest.exists()
marker=json.loads((ROOT/'canonical_success.json').read_text(encoding='utf-8'));source=ROOT/'moment_checks.py';canonical=ROOT/'moment.json'
assert c.digest(source)==marker['source_sha256'] and c.digest(canonical)==marker['output_sha256']
before=c.verify();isolated=ROOT/'isolated';assert not isolated.exists();isolated.mkdir()
cmd=[sys.executable,'-B','-X','utf8',str(source),'--output-dir',str(isolated)]
done=subprocess.run(cmd,cwd=ROOT,capture_output=True,text=True,encoding='utf-8',errors='replace')
log=ROOT/'isolated_replay.log';log.write_text(done.stdout+done.stderr,encoding='utf-8');assert done.returncode==0,done.stdout+done.stderr
assert canonical.read_bytes()==(isolated/'moment.json').read_bytes()
assert json.loads(canonical.read_text(encoding='utf-8'))==json.loads((isolated/'moment.json').read_text(encoding='utf-8'))
assert c.digest(source)==marker['source_sha256']
receipt={'status':'PASS_NEW_C4_SEPARATE_ISOLATED_BYTES_AND_FIELDS_REPLAY','exit_code':0,'source_sha256':marker['source_sha256'],
 'output_sha256':marker['output_sha256'],'bytes_identical':True,'all_fields_identical':True,'command_argv':cmd,
 'log_sha256':c.digest(log),'conservation_before':before,'conservation_after':c.verify(),
 'old_bank_kernel_Lean_render_replayed':False,'whole_D_N_uncontrolled':True,'score':0,'victory':False}
dest.write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n',encoding='utf-8')
print(json.dumps({'status':receipt['status'],'output_sha256':receipt['output_sha256'],'victory':False}))
