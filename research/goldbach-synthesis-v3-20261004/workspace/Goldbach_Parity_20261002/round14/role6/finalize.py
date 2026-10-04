"""Freeze numeric-only artifacts and final conceptual SHA bindings; no bank run."""
import sys
sys.dont_write_bytecode=True
sys.stdout.reconfigure(encoding='utf-8',errors='replace')
from pathlib import Path
from hashlib import sha256
import json
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
import shared as s
def sha(p):return sha256(p.read_bytes()).hexdigest()
final_inputs={'agent1_coverage.md':'4224fdd0f202da0a1dae1787965cb24aaeb7cf88fbcba8e92f607aff98716aec','agent2_complement.md':'b512cffb393253b004660442dd5cdde7af228d1550dbdc8c926d8e899c186d67'}
for f,h in final_inputs.items():assert sha(ROOT/f)==h,f
conservation=s.conservation.verify()
coverage=json.loads((ROOT/'coverage.json').read_text(encoding='utf-8'))
complement=json.loads((ROOT/'complement.json').read_text(encoding='utf-8'))
replay=json.loads((ROOT/'numerical_replay.json').read_text(encoding='utf-8'))
supplement=json.loads((ROOT/'coverage_pair_supplement.json').read_text(encoding='utf-8'))
audit=json.loads((ROOT/'role6'/'read_only_audit.json').read_text(encoding='utf-8'))
for name in ('coverage','complement'):
 marker=json.loads((ROOT/'role6'/f'{name}_canonical_success.json').read_text(encoding='utf-8'))
 assert marker['exit_code']==0
 assert sha(ROOT/f'{name}_checks.py')==marker['producer_sha256'] and sha(ROOT/f'{name}.json')==marker['output_sha256']
 canonical=(ROOT/f'{name}.json').read_bytes();isolated=(ROOT/f'isolated_{name}'/f'{name}.json').read_bytes()
 assert canonical==isolated
assert all(v['exit_code']==0 and v['bytes_identical'] and v['all_fields_identical'] for v in replay['runs'])
assert supplement['checked_unique_pairs']==7 and audit['distinct_actual_vertices']==78 and audit['complement_all_descent_X5_edges_checked']==44
assert coverage['graph_all']['prefix_deficit']==5 and coverage['graph_interior']['prefix_deficit']==4
assert complement['C1']['parent_count']==10 and complement['C2']['parent_count']==1
assert complement['C1']['Gamma_all_distinct_count']==21 and complement['C2']['Gamma_all_distinct_count']==23
falsifiers=coverage['ERROR_FALSIFIER']+complement['ERROR_FALSIFIER'];assert len(falsifiers)==4
for g in ('C1','C2'):
 assert complement[g]['strict_positive_debt_certificate']['sign']=='POSITIVE'
 assert complement[g]['capacity_sign_certificate']['sign']=='POSITIVE'
 assert complement[g]['defect_sign_certificate']['sign']=='NEGATIVE'
for f,h in s.IMPORTS.items():assert sha(s.BASE/f)==h
files=['conservation.py','previous_artifacts_sha256.json','conservation.json','shared.py','prepare_candidates.py','candidate_proposal.json','coverage_checks.py','coverage.json','complement_checks.py','complement.json','run_new.py','replay_checks.py','numerical_replay.json','coverage_pair_supplement.py','coverage_pair_supplement.json','agent6.md','isolated_coverage/coverage.json','isolated_complement/complement.json']
files+=sorted(p.relative_to(ROOT).as_posix() for p in (ROOT/'role6').rglob('*') if p.is_file())
assert len(files)==len(set(files))
bindings={f:sha(ROOT/f) for f in sorted(files)}
manifest={'status':'FROZEN_NUMERICAL_INPUTS_TERMINATED','round':14,'file_count':len(bindings),'sha256':bindings,'final_conceptual_report_sha256':final_inputs,'historical_inert_helper_sha256':s.IMPORTS,'conservation':conservation,'new_canonical_banks':2,'separate_isolated_replays':2,'all_JSON_fields_and_bytes_replayed':True,'targeted_stored_vector_supplements':2,'strict_rational_sign_certificates':27,'local_ERROR_FALSIFIER_count':4,'genuine_failed_new_bank_attempts':{'coverage':[],'complement':[1]},'all_failed_bank_sources_and_logs_preserved':True,'old_PASS_replayed':False,'old_Lean_recompiled':False,'old_PDF_rerendered':False,'source_u_minimum':'10^24','finite_N':100000000,'finite_N_outside_source':True,'global_D_N':False,'asymptotic':False,'payments':False,'Lean_called':False,'score':0,'victory':False}
dest=ROOT/'numeric_manifest.json';assert not dest.exists(),'Manifest already frozen'
dest.write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n',encoding='utf-8')
receipt={'status':'FINAL_ROLE6_TERMINATED_READ_ONLY_FREEZE','round':14,'manifest':str(dest),'manifest_sha256':sha(dest),'report_sha256':sha(ROOT/'agent6.md'),'protected_603_exactly_preserved':True,'final_conceptual_report_sha256':final_inputs,'new_banks_source_sha256':{n:sha(ROOT/f'{n}_checks.py') for n in ('coverage','complement')},'new_banks_output_sha256':{n:sha(ROOT/f'{n}.json') for n in ('coverage','complement')},'separate_isolated_runs':replay['runs'],'supplement_sha256':sha(ROOT/'coverage_pair_supplement.json'),'stored_vector_audit_sha256':sha(ROOT/'role6'/'read_only_audit.json'),'allowed_write_scope':'round14/** numeric only; excludes reports1/2 and role1/role2 directories','numeric_files_bound':len(bindings),'old_PASS_replayed':False,'old_Lean_recompiled':False,'old_PDF_rerendered':False,'global_D_N':False,'payments':False,'Lean_called':False,'score':0,'victory':False}
rd=ROOT/'role6_final_receipt.json';assert not rd.exists();rd.write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n',encoding='utf-8')
assert s.conservation.verify()['files']==603
print(json.dumps({'status':receipt['status'],'numeric_files_bound':len(bindings),'manifest_sha256':sha(dest),'report_sha256':sha(ROOT/'agent6.md'),'receipt_sha256':sha(rd),'coverage_sha256':sha(ROOT/'coverage.json'),'complement_sha256':sha(ROOT/'complement.json'),'replay_sha256':sha(ROOT/'numerical_replay.json'),'protected603':'PRESERVED','victory':False}))
