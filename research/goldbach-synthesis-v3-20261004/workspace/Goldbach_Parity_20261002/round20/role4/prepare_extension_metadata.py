"""Metadata only. No mathematical producer or Lean invocation."""
import json, hashlib
from pathlib import Path
from datetime import datetime, timezone
W = Path(__file__).resolve().parent
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
base = json.loads((W/'build_receipt.json').read_text(encoding='utf-8'))
assert len(base['successful_modules']) == 6 and len(base['attempts']) == 16
bindings = {}
for module in base['successful_modules'].values():
    for k in ['source','olean']:
        p = Path(module[k])
        assert sha(p) == module[k+'_sha256']
        bindings[str(p)] = module[k+'_sha256']
data = {'round':20,'role':4,'node':'14.5','status':'PREPARED_NOT_COMPILED',
    'at_utc':datetime.now(timezone.utc).isoformat(),'new_extension_Lean_invocations':0,
    'base_build_receipt_sha256':sha(W/'build_receipt.json'),
    'base_frozen_import_bindings':bindings,'builder_sha256':sha(W/'build_extension.py'),
    'initial_reviewed_source_sha256':{'FriablePhysicalDemand.lean':sha(W/'FriablePhysicalDemand.lean')},
    'historical_dependencies_manifest_sha256':sha(W/'dependencies_readonly.json'),
    'original_builder_sha256':sha(W/'build.py'),'victory':False,
    'post_integrity_checks':True,'unchanged_failure_replay_prohibited':True,
    'prior_preparation_sha256':sha(W/'extension_preparation.json')}
with (W/'extension_preparation_v2.json').open('x',encoding='utf-8') as h:
    h.write(json.dumps(data,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'prepared':True,'base_PASS_modules':6,'extension_Lean_invocations':0}))
