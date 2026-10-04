"""Protect exactly 603 previous + 48 final round14 artifacts, no old test run."""
import sys
sys.dont_write_bytecode=True
from hashlib import sha256
from pathlib import Path
import argparse,json,os,re
ROOT=Path(__file__).resolve().parent;BASE=ROOT.parent
CURRENT_ROUND=15
BASELINE=ROOT/'previous_artifacts_sha256.json'
PREVIOUS_BASELINE=BASE/'round14'/'previous_artifacts_sha256.json'
CONTROLLER=BASE/'round14'/'controller_manifest.json'
EXPECTED_CONTROLLER14='6795b8ed10872337ac8d0f7caf7ef428b8611b6f35376e575c22661ff68e30bf'
EXPECTED_PREVIOUS,EXPECTED_NEW,EXPECTED_COUNT=603,48,651
SKIP={'.lake','.git','.arbor','__pycache__','.pytest_cache','.mypy_cache','.ruff_cache'}
def digest(p):return sha256(p.read_bytes()).hexdigest()
def excluded_directory(name):
 if name in SKIP:return True
 m=re.fullmatch(r'round([0-9]+)',name)
 return bool(m and int(m.group(1))>=CURRENT_ROUND)
def current_records():
 records={}
 for directory,children,files in os.walk(BASE,followlinks=False):
  children[:]=sorted(n for n in children if not excluded_directory(n))
  for name in sorted(files):
   p=Path(directory)/name
   if p==BASE/'REPORT.md':continue
   records[p.relative_to(BASE).as_posix()]=digest(p)
 return dict(sorted(records.items()))
def source_integrity():
 expected=json.loads((BASE/'INPUT_HASHES.json').read_text(encoding='utf-8'));result={}
 for p,h in sorted(expected.items()):
  actual=digest(Path(p));assert actual==h,(p,h,actual)
  result[p]={'expected_sha256':h,'actual_sha256':actual,'status':'PRESERVED'}
 assert len(result)==2;return result
def controller_bindings():
 assert digest(CONTROLLER)==EXPECTED_CONTROLLER14
 ctrl=json.loads(CONTROLLER.read_text(encoding='utf-8'))
 assert ctrl['round']==14 and not ctrl['victory'] and ctrl['score']==0
 bound=ctrl['bindings_sha256'];assert len(bound)==47
 for f,h in bound.items():assert digest(BASE/'round14'/f)==h,f
 assert ctrl['judge_report_sha256']==bound['agent5.md']
 assert ctrl['judge_receipt_sha256']==bound['judge/judge_receipt.json']
 return bound
def initialize():
 previous=json.loads(PREVIOUS_BASELINE.read_text(encoding='utf-8'))['sha256'];assert len(previous)==EXPECTED_PREVIOUS
 bound=controller_bindings();expected=dict(previous)
 expected.update({f'round14/{f}':h for f,h in bound.items()})
 expected['round14/controller_manifest.json']=EXPECTED_CONTROLLER14
 assert len(expected)==EXPECTED_COUNT
 records=current_records()
 changed={f:{'expected':h,'actual':records.get(f,'MISSING')} for f,h in expected.items() if records.get(f)!=h}
 added=sorted(set(records)-set(expected));removed=sorted(set(expected)-set(records))
 if changed or added or removed or len(records)!=EXPECTED_COUNT:
  diag={'status':'EXACT_SCOPE_DISCREPANCY','expected_files':EXPECTED_COUNT,'actual_files':len(records),'changed':changed,'added':added,'removed':removed}
  (ROOT/'baseline_discrepancy.json').write_text(json.dumps(diag,indent=2)+'\n',encoding='utf-8');raise AssertionError(diag)
 if not BASELINE.exists():
  payload={'scope':'All final production through round14; exactly 603 previous + 47 controller-bound round14 files + controller14 itself; parsed roundNN>=15, caches, .arbor, .git and live REPORT.md excluded','last_frozen_round':14,'file_count':len(records),'round14_file_count':EXPECTED_NEW,'previous_protected_count':EXPECTED_PREVIOUS,'previous_baseline_sha256':digest(PREVIOUS_BASELINE),'round14_controller_sha256':EXPECTED_CONTROLLER14,'round14_bound_file_count':len(bound),'original_sources':source_integrity(),'sha256':records}
  BASELINE.write_text(json.dumps(payload,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
 else:
  payload=json.loads(BASELINE.read_text(encoding='utf-8'));assert payload['sha256']==records and payload['file_count']==EXPECTED_COUNT
 return records
def verify():
 records=initialize();current=current_records()
 changed={f:{'previous':h,'current':current.get(f,'MISSING')} for f,h in records.items() if current.get(f)!=h}
 added=sorted(set(current)-set(records));assert not changed and not added,{'changed':changed,'added':added}
 return {'status':'PRESERVED','files':len(records),'round14_files':EXPECTED_NEW,'previous_protected_files':EXPECTED_PREVIOUS,'round14_controller_sha256':EXPECTED_CONTROLLER14,'controller_47_bindings_verified':True,'exact_inventory_additions_and_removals_checked':True,'baseline_sha256':digest(BASELINE),'registry':str(BASELINE),'original_sources':source_integrity(),'old_PASS_replayed':False,'old_Lean_recompiled':False,'old_dependency_recompiled':False,'old_PDF_rerendered':False}
def output_directory(argument=None):
 d=(Path(argument) if argument else ROOT).resolve();assert d==ROOT or ROOT in d.parents,'Output must remain in round15'
 d.mkdir(parents=True,exist_ok=True);return d
if __name__=='__main__':
 parser=argparse.ArgumentParser();parser.add_argument('--output-dir',type=Path,default=ROOT)
 result=verify();d=output_directory(parser.parse_args().output_dir)
 (d/'conservation.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8');print(json.dumps(result,indent=2))
