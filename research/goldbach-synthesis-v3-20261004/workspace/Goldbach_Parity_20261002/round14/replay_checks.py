"""One isolated run of each NEW producer after canonical success; freeze afterward."""
import sys
sys.dont_write_bytecode=True
sys.stdout.reconfigure(encoding='utf-8',errors='replace')
from pathlib import Path
from hashlib import sha256
import subprocess,json
ROOT=Path(__file__).resolve().parent;sys.path.insert(0,str(ROOT))
import shared as s
dest=ROOT/'numerical_replay.json';assert not dest.exists(),'New banks already replayed and frozen'
before=s.conservation.verify();results=[]
for name in ('coverage','complement'):
 marker=json.loads((ROOT/'role6'/f'{name}_canonical_success.json').read_text(encoding='utf-8'))
 src=ROOT/f'{name}_checks.py';canonical=ROOT/f'{name}.json'
 assert sha256(src.read_bytes()).hexdigest()==marker['producer_sha256']
 assert sha256(canonical.read_bytes()).hexdigest()==marker['output_sha256']
 outputdir=ROOT/f'isolated_{name}';assert not outputdir.exists();outputdir.mkdir()
 cmd=[sys.executable,str(src),'--output-dir',str(outputdir)]
 done=subprocess.run(cmd,cwd=ROOT,capture_output=True,text=True,encoding='utf-8',errors='replace')
 log=ROOT/'role6'/f'{name}_isolated_replay.log';log.write_text(done.stdout+done.stderr,encoding='utf-8')
 assert done.returncode==0,done.stdout+done.stderr
 replay=outputdir/f'{name}.json'
 assert canonical.read_bytes()==replay.read_bytes(),'Byte mismatch'
 assert json.loads(canonical.read_text(encoding='utf-8'))==json.loads(replay.read_text(encoding='utf-8')),'Field mismatch'
 assert sha256(src.read_bytes()).hexdigest()==marker['producer_sha256']
 results.append({'bank':name,'exit_code':done.returncode,'canonical':str(canonical),'isolated':str(replay),'source_sha256':marker['producer_sha256'],'output_sha256':marker['output_sha256'],'bytes_identical':True,'all_fields_identical':True,'log':str(log),'log_sha256':sha256(log.read_bytes()).hexdigest(),'command_argv':cmd})
after=s.conservation.verify()
data={'status':'PASS_NEW_ROUND14_TWO_SEPARATE_ISOLATED_BYTES_AND_FIELDS_REPLAY','runs':results,'separate_isolated_directories':True,'only_new_round14_producers_executed':True,'old_PASS_replayed':False,'old_Lean_recompiled':False,'conservation_before':before,'conservation_after':after,'strict_rational_only':True,'global_D_N':False,'asymptotic':False,'payments':False,'Lean_called':False,'victory':False}
dest.write_text(json.dumps(data,indent=2,sort_keys=True)+'\n',encoding='utf-8')
print(json.dumps({'status':data['status'],'outputs_sha256':{r['bank']:r['output_sha256'] for r in results},'protected603':'PRESERVED','victory':False}))
