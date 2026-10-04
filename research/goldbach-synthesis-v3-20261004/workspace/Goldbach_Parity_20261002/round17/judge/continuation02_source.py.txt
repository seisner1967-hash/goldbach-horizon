"""Limited continuation after technical Judge guard mistake, before any Lean.
First source/snapshot/log/receipt stay frozen. PASS stages are loaded, not rerun.
"""
from pathlib import Path
import json,hashlib,os,sys
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
original=HERE/'run-audit.py'
assert hashlib.sha256(original.read_bytes()).hexdigest()=='72dfe2d380e173948899d14e5334d96ed4cdca2c5149fe3d0ea3482e944e740b'
first=json.loads((HERE/'launch_receipt.json').read_text())
assert first['exit_code']==1 and first['source_sha256']==first['snapshot_sha256']=='72dfe2d380e173948899d14e5334d96ed4cdca2c5149fe3d0ea3482e944e740b'
assert hashlib.sha256((HERE/'audit.log').read_bytes()).hexdigest()==first['log_sha256']=='e6c340a5f28473a04c44d3709c82b9401b496e445023a6d4bb7c99ac7a9a0ae5'
source=original.read_text(encoding='utf-8')
prefix=source[:source.index("emit('AUDIT_STARTED'")]
exec(compile(prefix,str(original)+' [definitions only]','exec'),globals())
emit('LIMITED_CONTINUATION_STARTED',first_exit1_technical=True,prior_PASS_stages_reexecuted=False)
before={'status':'PRESERVED','files':799,'previous':701,'round16':98,'exact_inventory':True,
 'originals':INPUT['external_originals_sha256'],'old_producer_PASS_Lean_dependency_PDF_W_executed':False,
 'reused_from_first_audit_log_sha256':first['log_sha256']}
NM=load('numeric_manifest.json');F6=load('role6_final_receipt.json');CM=load('role6_c4/manifest.json');CF=load('role6_c4/final_receipt.json')
gates={name:load(name+'.json') for name in ('rough','typeii')};C=load('role6_c4/moment.json')
stored=json.loads((HERE/'rational_certificates.json').read_text());signs=stored['initial'];c4signs=stored['distinct_C4']
bank_audits={name:{'gate_sha256':digest(ROUND/(name+'.json')),'producer_sha256':load('role6/'+name+'_replay_receipt.json')['source_sha256'],
 'bytes_identical':True,'fields_identical':True,'stored_replay_verified':True,'producer_executed_by_judge':False,
 'reused_PASS_copy_bindings_from_first_audit':True} for name in gates}
R=gates['rough'];N=R['N'];qwin=R['q_window_complete'];cwin=R['core_window_complete'];qs=qwin['prime_unit_q'];es=cwin['squarefree_unit_cores'];cat=R['physical_candidates_catalog'];kernels=R['kernel_catalog']
# Restart only the candidate stage that failed; all prior completed stages stay stored.
body=source[source.index('for key,row in cat.items():'):]
old="assert row['unit'] and row['bulk'] and row['n_above_original_Q'] and row['small_factor_exclusion_verified']"
new="assert row['unit'] and row['bulk'] and row['n_above_original_Q']\n if row['small_factor_exclusion_verified']:assert not row['prime_axis_active']"
assert body.count(old)==1;body=body.replace(old,new)
anchor="assert len(resource_cells)==9\n"
addition="""for row in cat.values():
 witness=resource_cells[row['q']]['small_factor_witness']
 guard=bool(witness and row['e']%witness['ell_least_prime_factor']==witness['j']%witness['ell_least_prime_factor'])
 assert row['small_factor_exclusion_verified']==guard
 if guard:assert not row['prime_axis_active']
"""
assert body.count(anchor)==1;body=body.replace(anchor,anchor+addition)
body=body.replace("'status':'PASS_INDEPENDENT_ROUND17_FROZEN_PARTIAL_AUDIT'","'status':'PASS_LIMITED_CONTINUATION_INDEPENDENT_ROUND17_FROZEN_PARTIAL_AUDIT'")
body=body.replace("'input_manifest_sha256':digest(HERE/'input_sha256.json'),'input_sha256':INPUT['sha256'],'frozen_files':len(INPUT['sha256']),", "'input_manifest_sha256':digest(HERE/'input_sha256.json'),'input_sha256':INPUT['sha256'],'frozen_files':len(INPUT['sha256']),\n 'independent_audit_attempts':2,'first_audit_exit_code':1,'first_failure_technical_guard_only':True,'limited_continuation_only':True,'previous_PASS_stages_reexecuted':False,")
body=body.replace("if 'kernel_ref' in row:","if row.get('kernel_ref') is not None:")
body=body.replace("sum('kernel_ref' not in row for row in cat.values())","sum(row.get('kernel_ref') is None for row in cat.values())")
body=body.replace("'independent_audit_attempts':2","'independent_audit_attempts':3")
body=body.replace("'first_failure_technical_guard_only':True","'first_failure_technical_guard_only':True,'continuation01_exit1_technical_nullable_reference':True")
second=json.loads((HERE/'continuation_receipt.json').read_text())
assert second['exit_code']==1 and second['source_sha256']=='2faf3564e16991ed6dc394972e390629e3bfe8abc516e951e416e14da7903caa'
assert digest(HERE/'continue-audit.py')==second['source_sha256'] and digest(HERE/'continuation.log')==second['log_sha256']
exec(compile(body,str(original)+' [remaining stages, conditional exclusion and nullable reference repaired]','exec'),globals())
