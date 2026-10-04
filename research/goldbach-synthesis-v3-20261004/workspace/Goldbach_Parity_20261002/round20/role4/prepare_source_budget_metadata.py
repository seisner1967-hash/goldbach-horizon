"""Metadata only. Requires actual nine PASS imports before preparing the budget gate."""
import json,hashlib
from pathlib import Path
from datetime import datetime,timezone
W=Path(__file__).resolve().parent
G=W.parent/'role4_geometry'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
ledgers=[W/'build_receipt.json',W/'extension_build_receipt.json',
         W/'aggregation_build_receipt.json',G/'geometry_build_receipt.json']
data_ledgers=[json.loads(p.read_text(encoding='utf-8')) for p in ledgers]
assert [len(r['successful_modules']) for r in data_ledgers]==[6,1,1,1]
bindings={}
for r in data_ledgers:
    for module in r['successful_modules'].values():
        passed=next(a for a in r['attempts'] if a['attempt']==module['attempt'])
        assert passed['exit_code']==0
        if 'credited_pass' in passed:
            assert passed['credited_pass'] and passed['post_integrity']['all_unchanged']
        for k in ['source','olean']:
            p=Path(module[k])
            assert sha(p)==module[k+'_sha256']
            bindings[str(p)]=module[k+'_sha256']
data={'round':20,'role':4,'node':'14.5','status':'SOURCE_BUDGET_PREPARED_NOT_COMPILED',
 'at_utc':datetime.now(timezone.utc).isoformat(),'new_source_budget_Lean_invocations':0,
 'base_build_receipt_sha256':sha(ledgers[0]),'extension_build_receipt_sha256':sha(ledgers[1]),
 'aggregation_build_receipt_sha256':sha(ledgers[2]),'geometry_build_receipt_sha256':sha(ledgers[3]),
 'geometry_builder_sha256':sha(G/'compile_once.py'),
 'base_frozen_import_bindings':bindings,'builder_sha256':sha(W/'build_source_budget.py'),
 'initial_reviewed_source_sha256':{'FriableSourceBudget.lean':sha(W/'FriableSourceBudget.lean')},
 'historical_dependencies_manifest_sha256':sha(W/'dependencies_readonly.json'),
 'post_integrity_checks':True,'unchanged_failure_replay_prohibited':True,
 'F0_minus_F1_nonfriable_reciprocal_paid':False,'whole_ledger_paid':False,'victory':False}
with (W/'source_budget_preparation.json').open('x',encoding='utf-8') as h:
    h.write(json.dumps(data,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'prepared':True,'PASS_import_modules':9,'budget_Lean_invocations':0}))
