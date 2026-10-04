"""Protect exactly 651 previous + 50 final round15 artifacts; read-only preflight."""
import sys
sys.dont_write_bytecode=True
from hashlib import sha256
from pathlib import Path
import argparse,json,os,re

ROOT=Path(__file__).resolve().parent;BASE=ROOT.parent
CURRENT_ROUND=16
BASELINE=ROOT/'previous_artifacts_sha256.json'
PREVIOUS_BASELINE=BASE/'round15'/'previous_artifacts_sha256.json'
CONTROLLER=BASE/'round15'/'controller_manifest.json'
EXPECTED_BASELINE15='d43941b27a4325a841282d389476c9c6fa9af920138b9b0deebe1c484a4ff7f4'
EXPECTED_CONTROLLER15='7b2522fbeec0c17965b9bfba4df418552f0e31b2b4881c91edff00b79a81869f'
EXPECTED_PREVIOUS,EXPECTED_NEW,EXPECTED_COUNT=651,50,701
SKIP={'.lake','.git','.arbor','__pycache__','.pytest_cache','.mypy_cache','.ruff_cache'}

def digest(p):return sha256(p.read_bytes()).hexdigest()

def excluded_directory(name):
 if name in SKIP:return True
 match=re.fullmatch(r'round([0-9]+)',name)
 return bool(match and int(match.group(1))>=CURRENT_ROUND)

def current_records():
 records={}
 for directory,children,files in os.walk(BASE,followlinks=False):
  children[:]=sorted(name for name in children if not excluded_directory(name))
  for name in sorted(files):
   path=Path(directory)/name
   if path==BASE/'REPORT.md':continue
   records[path.relative_to(BASE).as_posix()]=digest(path)
 return dict(sorted(records.items()))

def source_integrity():
 expected=json.loads((BASE/'INPUT_HASHES.json').read_text(encoding='utf-8'));result={}
 for path,expected_hash in sorted(expected.items()):
  actual=digest(Path(path));assert actual==expected_hash,(path,expected_hash,actual)
  result[path]={'expected_sha256':expected_hash,'actual_sha256':actual,'status':'PRESERVED'}
 assert len(result)==2;return result

def controller_bindings():
 assert digest(CONTROLLER)==EXPECTED_CONTROLLER15
 controller=json.loads(CONTROLLER.read_text(encoding='utf-8'))
 assert controller['round']==15 and controller['victory'] is False and controller['score']==0
 bound=controller['bindings_sha256'];assert len(bound)==49
 for relative,expected in bound.items():assert digest(BASE/'round15'/relative)==expected,relative
 assert controller['judge_report_sha256']==bound['agent5.md']
 assert controller['judge_receipt_sha256']==bound['judge/judge_receipt.json']
 assert controller['original_sources_sha256']==json.loads((BASE/'INPUT_HASHES.json').read_text(encoding='utf-8'))
 # Read the stored numeric manifest and all three full copies, never run their producers.
 numeric=json.loads((BASE/'round15'/'numeric_manifest.json').read_text(encoding='utf-8'))
 assert numeric['files']==len(numeric['sha256'])==35
 for relative,expected in numeric['sha256'].items():assert bound[relative]==expected
 for relative,expected in numeric['reports_FINAL_sha256'].items():assert bound[relative]==expected
 for name in ('incidence','fusion','incidence_moment'):
  canonical=BASE/'round15'/(name+'.json');isolated=BASE/'round15'/('isolated_'+name)/(name+'.json')
  assert canonical.read_bytes()==isolated.read_bytes()
  assert json.loads(canonical.read_text(encoding='utf-8'))==json.loads(isolated.read_text(encoding='utf-8'))
  replay=json.loads((BASE/'round15'/'role6'/(name+'_replay_receipt.json')).read_text(encoding='utf-8'))
  assert replay['bytes_identical'] and replay['all_fields_identical'] and replay['exit_code']==0
  assert replay['output_sha256']==digest(canonical)==bound[name+'.json']
 return bound

def initialize():
 assert digest(PREVIOUS_BASELINE)==EXPECTED_BASELINE15
 previous=json.loads(PREVIOUS_BASELINE.read_text(encoding='utf-8'))['sha256']
 assert len(previous)==EXPECTED_PREVIOUS
 bound=controller_bindings();expected=dict(previous)
 expected.update({f'round15/{relative}':expected_hash for relative,expected_hash in bound.items()})
 expected['round15/controller_manifest.json']=EXPECTED_CONTROLLER15
 assert len(expected)==EXPECTED_COUNT
 records=current_records()
 changed={relative:{'expected':expected_hash,'actual':records.get(relative,'MISSING')} for relative,expected_hash in expected.items() if records.get(relative)!=expected_hash}
 added=sorted(set(records)-set(expected));removed=sorted(set(expected)-set(records))
 if changed or added or removed or len(records)!=EXPECTED_COUNT:
  diagnostic={'status':'EXACT_SCOPE_DISCREPANCY','expected_files':EXPECTED_COUNT,'actual_files':len(records),'changed':changed,'added':added,'removed':removed}
  (ROOT/'baseline_discrepancy.json').write_text(json.dumps(diagnostic,indent=2)+'\n',encoding='utf-8')
  raise AssertionError(diagnostic)
 if not BASELINE.exists():
  payload={'scope':'All final production through round15; exactly 651 previous + 49 controller-bound round15 files + controller15 itself; parsed roundNN>=16, caches, .arbor, .git and live REPORT.md excluded',
   'last_frozen_round':15,'file_count':len(records),'round15_file_count':EXPECTED_NEW,'previous_protected_count':EXPECTED_PREVIOUS,
   'previous_baseline_sha256':EXPECTED_BASELINE15,'round15_controller_sha256':EXPECTED_CONTROLLER15,'round15_bound_file_count':len(bound),
   'round15_numeric_bindings_verified':35,'round15_three_full_copies_bytes_and_fields_identical':True,
   'original_sources':source_integrity(),'sha256':records}
  BASELINE.write_text(json.dumps(payload,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
 else:
  payload=json.loads(BASELINE.read_text(encoding='utf-8'));assert payload['sha256']==records and payload['file_count']==EXPECTED_COUNT
 return records

def verify():
 records=initialize();current=current_records()
 changed={relative:{'previous':expected,'current':current.get(relative,'MISSING')} for relative,expected in records.items() if current.get(relative)!=expected}
 added=sorted(set(current)-set(records));removed=sorted(set(records)-set(current))
 assert not changed and not added and not removed,{'changed':changed,'added':added,'removed':removed}
 return {'status':'PRESERVED','files':len(records),'round15_files':EXPECTED_NEW,'previous_protected_files':EXPECTED_PREVIOUS,
  'round15_controller_sha256':EXPECTED_CONTROLLER15,'controller_49_bindings_verified':True,'numeric35_bindings_preserved':True,
  'three_round15_copies_bytes_and_fields_preserved':True,'exact_inventory_additions_and_removals_checked':True,
  'baseline_sha256':digest(BASELINE),'registry':str(BASELINE),'original_sources':source_integrity(),
  'old_PASS_replayed':False,'old_Lean_recompiled':False,'old_dependency_recompiled':False,'old_PDF_rerendered':False,
  'numeric_contract_round16_launched':False,'mathematical_identity_round16_certified':False}

def output_directory(argument=None):
 directory=(Path(argument) if argument else ROOT).resolve()
 assert directory==ROOT or ROOT in directory.parents,'Output must remain in round16'
 directory.mkdir(parents=True,exist_ok=True);return directory

if __name__=='__main__':
 parser=argparse.ArgumentParser();parser.add_argument('--output-dir',type=Path,default=ROOT)
 result=verify();directory=output_directory(parser.parse_args().output_dir)
 (directory/'conservation.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
 print(json.dumps(result,indent=2))
