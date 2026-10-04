"""Metadata only, seven existing PASS imports; no compiler or mathematical producer."""
import json, hashlib
from pathlib import Path
from datetime import datetime, timezone
W = Path(__file__).resolve().parent
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
base = json.loads((W/'build_receipt.json').read_text(encoding='utf-8'))
extension = json.loads((W/'extension_build_receipt.json').read_text(encoding='utf-8'))
assert len(base['successful_modules']) == 6 and len(base['attempts']) == 16
assert set(extension['successful_modules']) == {'FriablePhysicalDemand.lean'}
bindings = {}
for module in [*base['successful_modules'].values(),*extension['successful_modules'].values()]:
    for k in ['source','olean']:
        p = Path(module[k])
        assert sha(p) == module[k+'_sha256']
        bindings[str(p)] = module[k+'_sha256']
data = {'round':20,'role':4,'node':'14.5','status':'AGGREGATION_PREPARED_NOT_COMPILED',
    'at_utc':datetime.now(timezone.utc).isoformat(),'new_aggregation_Lean_invocations':0,
    'base_build_receipt_sha256':sha(W/'build_receipt.json'),
    'extension_build_receipt_sha256':sha(W/'extension_build_receipt.json'),
    'base_frozen_import_bindings':bindings,'builder_sha256':sha(W/'build_aggregation.py'),
    'initial_reviewed_source_sha256':{'FriableDemandAggregation.lean':sha(W/'FriableDemandAggregation.lean')},
    'historical_dependencies_manifest_sha256':sha(W/'dependencies_readonly.json'),
    'original_builder_sha256':sha(W/'build.py'),'extension_builder_sha256':sha(W/'build_extension.py'),
    'post_integrity_checks':True,'unchanged_failure_replay_prohibited':True,'victory':False}
with (W/'aggregation_preparation.json').open('x',encoding='utf-8') as h:
    h.write(json.dumps(data,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'prepared':True,'PASS_import_modules':7,'aggregation_Lean_invocations':0}))
