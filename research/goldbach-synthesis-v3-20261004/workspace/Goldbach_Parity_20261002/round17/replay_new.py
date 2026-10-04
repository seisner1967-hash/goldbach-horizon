"""One separate isolated replay per selected NEW successful round17 bank."""
import sys
sys.dont_write_bytecode=True
sys.stdout.reconfigure(encoding='utf-8',errors='replace')
from pathlib import Path
from hashlib import sha256
import subprocess,json,argparse,re
ROOT=Path(__file__).resolve().parent;sys.path.insert(0,str(ROOT))
import shared as s
parser=argparse.ArgumentParser();parser.add_argument('bank');args=parser.parse_args()
assert re.fullmatch(r'[a-z][a-z0-9_]{1,40}',args.bank)
dest=ROOT/'role6'/f'{args.bank}_replay_receipt.json';assert not dest.exists(),'Already replayed and frozen'
marker=json.loads((ROOT/'role6'/f'{args.bank}_canonical_success.json').read_text(encoding='utf-8'))
src=ROOT/f'{args.bank}_checks.py';canonical=ROOT/f'{args.bank}.json'
assert sha256(src.read_bytes()).hexdigest()==marker['producer_sha256']
assert sha256(canonical.read_bytes()).hexdigest()==marker['output_sha256']
before=s.conservation.verify();outputdir=ROOT/f'isolated_{args.bank}';assert not outputdir.exists();outputdir.mkdir()
cmd=[sys.executable,str(src),'--output-dir',str(outputdir)]
done=subprocess.run(cmd,cwd=ROOT,capture_output=True,text=True,encoding='utf-8',errors='replace')
log=ROOT/'role6'/f'{args.bank}_isolated_replay.log';log.write_text(done.stdout+done.stderr,encoding='utf-8')
assert done.returncode==0,done.stdout+done.stderr
replay=outputdir/f'{args.bank}.json';assert canonical.read_bytes()==replay.read_bytes(),'Byte mismatch'
assert json.loads(canonical.read_text(encoding='utf-8'))==json.loads(replay.read_text(encoding='utf-8')),'Field mismatch'
assert sha256(src.read_bytes()).hexdigest()==marker['producer_sha256']
data={'status':'PASS_NEW_ROUND17_SEPARATE_ISOLATED_BYTES_AND_FIELDS_REPLAY','bank':args.bank,'exit_code':done.returncode,
 'canonical':str(canonical),'isolated':str(replay),'source_sha256':marker['producer_sha256'],'output_sha256':marker['output_sha256'],
 'bytes_identical':True,'all_fields_identical':True,'log':str(log),'log_sha256':sha256(log.read_bytes()).hexdigest(),'command_argv':cmd,
 'only_new_round17_producer_executed':True,'old_PASS_replayed':False,'old_Lean_recompiled':False,
 'conservation_before':before,'conservation_after':s.conservation.verify(),'global_D_N':False,'asymptotic':False,'payments':False,'Lean_called':False,'victory':False}
dest.write_text(json.dumps(data,indent=2,sort_keys=True)+'\n',encoding='utf-8')
print(json.dumps({'status':data['status'],'bank':args.bank,'output_sha256':data['output_sha256'],'protected799':'PRESERVED','victory':False}))
