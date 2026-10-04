"""Read-only verification followed by role3 final receipt, no compilation/replay."""
import sys
sys.dont_write_bytecode=True
sys.stdout.reconfigure(encoding='utf-8',errors='replace')
from pathlib import Path
import hashlib,json,re
from datetime import datetime,timezone
ROOT=Path(__file__).resolve().parents[1];WORK=ROOT/'role3'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
buildpath=WORK/'build_receipt.json';build=json.loads(buildpath.read_text(encoding='utf-8'))
source=Path(build['source']);text=source.read_text(encoding='utf-8')
last=build['attempts'][-1];assert last['exit_code']==0 and sha(source)==last['source_sha256']
assert not re.search(r'\b(?:sorry|admit|native_decide)\b|^\s*axiom\b',text,re.M)
names=re.findall(r'^theorem\s+(\w+)',text,re.M);assert len(names)==23 and len(set(names))==23
out=Path(last['log']).read_text(encoding='utf-8');assert 'error:' not in out and 'sorryAx' not in out
axioms={name:[a.strip() for a in ax.replace('\n',' ').split(',') if a.strip()] for name,ax in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",out)}
permitted={'propext','Classical.choice','Quot.sound'}
assert len(axioms)==35 and all(set(x)==permitted for x in axioms.values())
ns='GoldbachRound13.PrimeSemiprimeSwitch.'
assert all(ns+n in axioms for n in names)
for attempt in build['attempts']:
 assert sha(Path(attempt['snapshot']))==attempt['source_sha256']==attempt['snapshot_sha256']
 assert sha(Path(attempt['log']))==attempt['log_sha256']
for dep in build['dependencies']:
 assert dep['exit_code']==0 and dep['fresh_round13_build']
 assert sha(Path(dep['source']))==dep['source_sha256']
 assert sha(Path(dep['olean']))==dep['olean_sha256']
 assert sha(Path(dep['log']))==dep['log_sha256']
numeric=json.loads((ROOT/'numeric_manifest.json').read_text(encoding='utf-8'))
assert numeric['file_count']==11
for f,h in numeric['sha256'].items():assert sha(ROOT/f)==h,f
registry=json.loads((ROOT/'previous_artifacts_sha256.json').read_text(encoding='utf-8'))
protected=registry['sha256'];assert len(protected)==registry['file_count']==514
for f,h in protected.items():
 p=Path(f)
 if not p.is_absolute():p=ROOT.parent/p
 assert sha(p)==h,str(p)
for f,item in registry['original_sources'].items():assert sha(Path(f))==item['expected_sha256'],f
report=ROOT/'agent3_formalisation.md';assert report.is_file()
owned=[source,report,*sorted(p for p in WORK.rglob('*') if p.is_file())]
receipt={'status':'FINAL_COMPILED_REAL_SWITCH_PARTIAL_ONLY','timestamp_utc':datetime.now(timezone.utc).isoformat(),'role':3,'source':str(source),'source_sha256':sha(source),'report':str(report),'report_sha256':sha(report),'build_receipt':str(buildpath),'build_receipt_sha256':sha(buildpath),'compiler_version':build['compiler_version'],'final_attempt':last,'all_attempts_preserved':True,'failed_real_attempts':[a['attempt'] for a in build['attempts'] if a['exit_code']!=0],'successful_real_attempts':[a['attempt'] for a in build['attempts'] if a['exit_code']==0],'new_theorem_count':len(names),'new_theorems':names,'new_definition_count':0,'imported_definitions_audited':12,'axioms_by_declaration':axioms,'only_standard_axioms':True,'forbidden_proof_commands_absent':True,'dependencies':build['dependencies'],'historical_theorems_not_recounted':[17,19],'fresh_producer_olean':str(Path(build['olean'])),'fresh_producer_olean_sha256':sha(Path(build['olean'])),'input_sha256':build['input_sha256'],'numeric_manifest_all_11_bindings_verified':True,'conservation':{'status':'PRESERVED_READ_ONLY_SHA_AUDIT','protected_previous_artifacts':514,'registry_sha256':sha(ROOT/'previous_artifacts_sha256.json'),'original_sources_unchanged':True},'allowed_write_scope':['round13/lean/PrimeSemiprimeSwitch.lean','round13/role3/**','round13/agent3_formalisation.md','round13/role3_final_receipt.json'],'owned_artifacts_sha256':{str(p.relative_to(ROOT)):sha(p) for p in owned},'old_producer_olean_copied':False,'old_PASS_replayed':False,'old_Lean_tests_replayed':False,'historical_sources_compiled_only_as_required_dependencies':True,'old_PDF_rerendered':False,'proved':['literal_short_divisors_parent_and_image','real_prefix_antisymmetry','real_Moebius_and_vonMangoldt_values','X4_actual_source_coefficients','downward_arithmetic_displacement','X5_actual_source_pair_with_W_variation_retained','canonical_parent_and_image_five_factor_recovery','parent_image_disjointness','literal_N_minus_m_bulk_prime_above_Q_corollary'],'not_proved':['X7_harmonic_two_front_variation_separate_role4','analytic_21N31over32u2_payment','positive_density_or_existence_of_paired_set','cardinal_lower_bound_K','global_J0_J1remaining_J2remaining_compensation','whole_D_N_bound'],'source_u_minimum':'10^24','finite_numeric_N':100000000,'finite_numeric_N_outside_source':True,'global_D_N':False,'asymptotic_payment_certified':False,'score':0,'victory':False}
dest=ROOT/'role3_final_receipt.json';dest.write_text(json.dumps(receipt,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print(json.dumps({'status':receipt['status'],'new_theorems':len(names),'source_sha256':sha(source),'report_sha256':sha(report),'receipt_sha256':sha(dest),'final_log_sha256':sha(Path(last['log'])),'producer_olean_sha256':sha(Path(build['olean'])),'protected_514':'PRESERVED','victory':False},ensure_ascii=False))
