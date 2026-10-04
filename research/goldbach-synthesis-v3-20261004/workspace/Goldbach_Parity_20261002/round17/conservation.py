"""Protect exact799=701 previous+98 final16 artifacts, including real failures."""
import sys
sys.dont_write_bytecode=True
from hashlib import sha256
from pathlib import Path
import argparse,json,os,re

ROOT=Path(__file__).resolve().parent;BASE=ROOT.parent
CURRENT_ROUND=17
BASELINE=ROOT/'previous_artifacts_sha256.json'
PREVIOUS_BASELINE=BASE/'round16'/'previous_artifacts_sha256.json'
CONTROLLER=BASE/'round16'/'controller_manifest.json'
EXPECTED_BASELINE16='5939d791139dbb3f9b26e5d1f372bbdf98d1927f9aaf2c5e9c22aa0a4e35d043'
EXPECTED_CONTROLLER16='10d9f68fc649d965aa5eecac96fecf5fd20f705527d42f52b855662acec02332'
EXPECTED_PREVIOUS,EXPECTED_NEW,EXPECTED_COUNT=701,98,799
SKIP={'.lake','.git','.arbor','__pycache__','.pytest_cache','.mypy_cache','.ruff_cache'}

def digest(path):return sha256(path.read_bytes()).hexdigest()

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
 assert digest(CONTROLLER)==EXPECTED_CONTROLLER16
 controller=json.loads(CONTROLLER.read_text(encoding='utf-8'))
 assert controller['round']==16 and controller['victory'] is False and controller['score']==0
 bound=controller['bindings_sha256'];assert len(bound)==97
 for relative,expected in bound.items():assert digest(BASE/'round16'/relative)==expected,relative
 assert controller['judge_report_sha256']==bound['agent5.md']
 assert controller['judge_receipt_sha256']==bound['judge/judge_receipt.json']
 assert controller['judge_final_receipt_sha256']==bound['judge/final_receipt.json']
 assert controller['original_sources_sha256']==json.loads((BASE/'INPUT_HASHES.json').read_text(encoding='utf-8'))
 numeric=json.loads((BASE/'round16'/'numeric_manifest.json').read_text(encoding='utf-8'))
 assert numeric['files']==len(numeric['sha256'])==30
 for relative,expected in numeric['sha256'].items():assert bound[relative]==expected
 for relative,expected in numeric['reports_FINAL_sha256'].items():assert bound[relative]==expected
 for name in ('typei','capacity'):
  canonical=BASE/'round16'/(name+'.json');isolated=BASE/'round16'/('isolated_'+name)/(name+'.json')
  # Stored bytes/fields only: no old producer, W calculation or sign recomputation.
  assert canonical.read_bytes()==isolated.read_bytes()
  assert json.loads(canonical.read_text(encoding='utf-8'))==json.loads(isolated.read_text(encoding='utf-8'))
  replay=json.loads((BASE/'round16'/'role6'/(name+'_replay_receipt.json')).read_text(encoding='utf-8'))
  assert replay['bytes_identical'] and replay['all_fields_identical'] and replay['exit_code']==0
  assert replay['output_sha256']==digest(canonical)==bound[name+'.json']
 # Preserve the actual nine failures and all thirteen role3 invocation pairs.
 failures=controller['actual_failed_lean_attempts'];assert len(failures)==9
 assert [v['attempt'] for v in failures]==[1,2,3,5,6,7,8,10,12]
 for entry in failures:
  number=entry['attempt'];assert entry['exit_code']==1 and entry['parity_diagnostic'] is False
  assert bound[f'role3/attempt{number:02d}_source.lean.txt']==entry['source_sha256']
  assert bound[f'role3/attempt{number:02d}.log']==entry['log_sha256']
 for number in range(1,14):
  assert f'role3/attempt{number:02d}_source.lean.txt' in bound
  assert f'role3/attempt{number:02d}.log' in bound
 for name,owner in [('EulerAnchor','role3'),('LeastMissingPrimeMargin','role4')]:
  assert bound[f'judge/build/{name}.lean']==bound[f'{owner}/{name}.lean']
  assert f'judge/build/{name}.olean' in bound and f'{owner}/{name}.olean' in bound
 return bound

def initialize():
 assert digest(PREVIOUS_BASELINE)==EXPECTED_BASELINE16
 previous=json.loads(PREVIOUS_BASELINE.read_text(encoding='utf-8'))['sha256']
 assert len(previous)==EXPECTED_PREVIOUS
 bound=controller_bindings();expected=dict(previous)
 expected.update({f'round16/{relative}':expected_hash for relative,expected_hash in bound.items()})
 expected['round16/controller_manifest.json']=EXPECTED_CONTROLLER16
 assert len(expected)==EXPECTED_COUNT
 records=current_records()
 changed={relative:{'expected':expected_hash,'actual':records.get(relative,'MISSING')} for relative,expected_hash in expected.items() if records.get(relative)!=expected_hash}
 added=sorted(set(records)-set(expected));removed=sorted(set(expected)-set(records))
 if changed or added or removed or len(records)!=EXPECTED_COUNT:
  diagnostic={'status':'EXACT_SCOPE_DISCREPANCY','expected_files':EXPECTED_COUNT,'actual_files':len(records),'changed':changed,'added':added,'removed':removed}
  (ROOT/'baseline_discrepancy.json').write_text(json.dumps(diagnostic,indent=2)+'\n',encoding='utf-8')
  raise AssertionError(diagnostic)
 if not BASELINE.exists():
  payload={'scope':'All final production through round16; exact701 previous+97 controller-bound round16 files+controller16 itself; roundNN>=17, conventional caches, .arbor, .git and live REPORT.md excluded',
   'last_frozen_round':16,'file_count':len(records),'round16_file_count':EXPECTED_NEW,'previous_protected_count':EXPECTED_PREVIOUS,
   'previous_baseline_sha256':EXPECTED_BASELINE16,'round16_controller_sha256':EXPECTED_CONTROLLER16,'round16_bound_file_count':len(bound),
   'round16_numeric_bindings_verified':30,'round16_two_full_numeric_copies_bytes_and_fields_identical':True,
   'round16_all_13_role3_invocation_logs_and_snapshots_included':True,'round16_nine_real_failures_included':True,
   'round16_fresh_judge_sources_oleans_logs_and_manifests_included':True,'original_sources':source_integrity(),'sha256':records}
  BASELINE.write_text(json.dumps(payload,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
 else:
  payload=json.loads(BASELINE.read_text(encoding='utf-8'));assert payload['sha256']==records and payload['file_count']==EXPECTED_COUNT
 return records

def verify():
 records=initialize();current=current_records()
 changed={relative:{'previous':expected,'current':current.get(relative,'MISSING')} for relative,expected in records.items() if current.get(relative)!=expected}
 added=sorted(set(current)-set(records));removed=sorted(set(records)-set(current))
 assert not changed and not added and not removed,{'changed':changed,'added':added,'removed':removed}
 return {'status':'PRESERVED','scope':'READ_ONLY_CONSERVATION_VERIFICATION','files':len(records),
  'round16_files':EXPECTED_NEW,'previous_protected_files':EXPECTED_PREVIOUS,'round16_controller_sha256':EXPECTED_CONTROLLER16,
  'controller_97_bindings_verified':True,'numeric30_bindings_preserved':True,'two_round16_numeric_copies_bytes_and_fields_preserved':True,
  'all13_role3_invocation_log_snapshot_pairs_preserved':True,'nine_real_failed_Lean_attempts_preserved':True,
  'fresh_judge_Lean_sources_oleans_logs_manifests_preserved':True,'exact_inventory_additions_and_removals_checked':True,
  'baseline_sha256':digest(BASELINE),'registry':str(BASELINE),'original_sources':source_integrity(),
  'old_producer_executed_by_this_verification':False,'old_PASS_replayed':False,'old_Lean_recompiled':False,
  'old_dependency_recompiled':False,'old_PDF_rerendered':False,'old_W_recomputed':False,
  'numeric_contract_launched_by_this_verification':False,'mathematical_identity_certified_by_conservation':False,
  'flags_describe_this_readonly_verification_not_global_execution':True}

def output_directory(argument=None):
 directory=(Path(argument) if argument else ROOT).resolve()
 assert directory==ROOT or ROOT in directory.parents,'Output must remain in round17'
 directory.mkdir(parents=True,exist_ok=True);return directory

if __name__=='__main__':
 parser=argparse.ArgumentParser();parser.add_argument('--output-dir',type=Path,default=ROOT)
 result=verify();directory=output_directory(parser.parse_args().output_dir)
 (directory/'conservation.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
 print(json.dumps(result,indent=2))
