"""Read-only input audit and dependency axiom audit; emits role4 final receipt."""
import sys
sys.dont_write_bytecode=True
sys.stdout.reconfigure(encoding='utf-8',errors='replace')
from pathlib import Path
import hashlib,json,os,re,subprocess
ROOT=Path(__file__).resolve().parents[1];BUILD=ROOT/'role4';DEPS=BUILD/'dependencies'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
attempts=json.loads((BUILD/'attempts.json').read_text(encoding='utf-8'))
last=attempts['attempts'][-1]
assert last['exit_code']==0
SOURCE=Path(attempts['source']);assert sha(SOURCE)==last['source_sha256']
text=SOURCE.read_text(encoding='utf-8')
assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',text)
new_theorems=re.findall(r'^theorem\s+(\w+)',text,re.M)
new_defs=re.findall(r'^(?:noncomputable )?def\s+(\w+)',text,re.M)
assert len(new_theorems)==16 and len(new_defs)==5
def audit_prints(output,names):
 found={}
 for name,statement in re.findall(r"'([^']+)' (depends on axioms: \[.*?\]|does not depend on any axioms)",output,re.S):
  axioms=[] if statement.startswith('does') else re.findall(r'\b[A-Za-z_][\w.]*\b',statement.split('[',1)[1].split(']',1)[0])
  assert set(axioms)<= {'propext','Classical.choice','Quot.sound'},(name,axioms)
  assert name not in found
  found[name]=axioms
 assert set(found)==set(names),(set(names)-set(found),set(found)-set(names))
 return found
prefix='GoldbachRound13.HarmonicKernelVariation.'
new_names=[prefix+x for x in new_defs+new_theorems]
new_output=Path(last['log']).read_text(encoding='utf-8')
assert not re.search(r'\b(error|warning):|sorryAx|Try this:',new_output)
new_axioms=audit_prints(new_output,new_names)
old_names=[];old_counts={}
for filename,prefix in [('ShortDivisorComplement.lean','GoldbachRound10.ShortDivisorComplement.'),('ThreeAdicPrimePairing.lean','GoldbachRound11.')]:
 p=DEPS/filename;s=p.read_text(encoding='utf-8')
 names=re.findall(r'^(?:theorem|(?:noncomputable )?def)\s+(\w+)',s,re.M)
 theorems=re.findall(r'^theorem\s+(\w+)',s,re.M)
 old_names += [prefix+x for x in names]
 old_counts[filename]={'theorems':len(theorems),'definitions':len(names)-len(theorems),'recounted_as_new':False}
assert old_counts['ShortDivisorComplement.lean']['theorems']==17
assert old_counts['ThreeAdicPrimePairing.lean']['theorems']==19
audit_source=DEPS/'DependencyAudit.lean'
audit_source.write_text('import ThreeAdicPrimePairing\n\n'+'\n'.join('#print axioms '+x for x in old_names)+'\n',encoding='utf-8')
env=dict(os.environ);env['LEAN_PATH']=attempts['lean_path']
cmd=[attempts['compiler'],'-o',str(DEPS/'DependencyAudit.olean'),str(audit_source)]
done=subprocess.run(cmd,cwd=DEPS,env=env,capture_output=True,text=True,encoding='utf-8',errors='replace')
log=BUILD/'dependency_axioms.log';log.write_text(done.stdout+done.stderr,encoding='utf-8')
assert done.returncode==0 and not re.search(r'\b(error|warning):|sorryAx',done.stdout+done.stderr)
old_axioms=audit_prints(done.stdout+done.stderr,old_names)
registry=json.loads((ROOT/'previous_artifacts_sha256.json').read_text(encoding='utf-8'))
assert len(registry['sha256'])==514
for rel,value in registry['sha256'].items():assert sha(ROOT.parent/rel)==value,rel
for path,entry in registry['original_sources'].items():assert sha(Path(path))==entry['expected_sha256']
manifest=json.loads((ROOT/'numeric_manifest.json').read_text(encoding='utf-8'))
for rel,value in manifest['sha256'].items():assert sha(ROOT/rel)==value,rel
for filename,expected in [('agent1_exchange.md','2b64a5434c1dfde766436d5abd44b62a2714615992193a3f0e21bf90554d8c54'),
 ('agent2_signed_operator.md','91946283d4ca1f5021de670b16167e0a0714d0945104d30c4070ca9a26bc9c46')]:assert sha(ROOT/filename)==expected
files=[SOURCE,BUILD/'build.py',BUILD/'finalize.py',BUILD/'attempts.json',BUILD/'HarmonicKernelVariation.olean',
 audit_source,DEPS/'DependencyAudit.olean',log]
for entry in attempts['dependencies']:
 files += [Path(entry[x]) for x in ['copy','olean','log']]
for entry in attempts['attempts']:
 files += [Path(entry[x]) for x in ['snapshot','log']]
binding={str(p.relative_to(ROOT)):sha(p) for p in files}
receipt={'status':'COMPILED_ACTUAL_KERNEL_FINITE_VARIATION_WITH_WRITTEN_POWER_PAYMENT',
 'compiler':attempts['compiler'],'compiler_sha256':attempts['compiler_sha256'],'compiler_version':attempts['compiler_version'],
 'lean_path':attempts['lean_path'],'source':str(SOURCE),'source_sha256':sha(SOURCE),
 'module_olean':attempts['olean'],'module_olean_sha256':attempts['olean_sha256'],
 'sha256':binding,'attempts':attempts['attempts'],'dependencies':attempts['dependencies'],
 'actual_failed_attempts':[x for x in attempts['attempts'] if x['exit_code']!=0],
 'new_theorem_count':16,'new_definition_count':5,'new_axioms':new_axioms,
 'old_dependency_counts':old_counts,'old_dependency_axioms':old_axioms,
 'dependency_audit_command':cmd,'dependency_audit_exit_code':done.returncode,
 'quantitative_finite_variation_compiled':True,'phi_square_half_written_only':True,
 'power_decay_21_written_only':True,'total_switch_cost_written_only':True,
 'source_onset_written_only':'log N >= 10^24','global_compensation_proved':False,
 'conservation':{'status':'PRESERVED','previous_files':514,'registry_sha256':sha(ROOT/'previous_artifacts_sha256.json'),
  'numeric_manifest_sha256':sha(ROOT/'numeric_manifest.json'),'all_11_numeric_bindings_unchanged':True,
  'agent1_sha256':sha(ROOT/'agent1_exchange.md'),'agent2_sha256':sha(ROOT/'agent2_signed_operator.md'),
  'original_pdf_zip_preserved':True},
 'old_olean_used':False,'old_PASS_replayed':False,'Lean_called':True,'score':0,'victory':False,
 'unresolved':['Global capacity/coverage of matched parents','J0 and J1 remainder','unmatched J2, singles/faces/H2',
  'bilateral c1/reference/long complement','effective BV physical-band onset','covered e']}
(ROOT/'role4_final_receipt.json').write_text(json.dumps(receipt,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print(json.dumps({'status':receipt['status'],'new_theorems':16,'definitions':5,'old_counts':old_counts,
 'real_compiler_failures':len(receipt['actual_failed_attempts']),'all_axioms_standard':True,'conservation514':'PRESERVED',
 'source_sha256':sha(SOURCE),'receipt_sha256':sha(ROOT/'role4_final_receipt.json'),'victory':False},ensure_ascii=False,indent=2))
