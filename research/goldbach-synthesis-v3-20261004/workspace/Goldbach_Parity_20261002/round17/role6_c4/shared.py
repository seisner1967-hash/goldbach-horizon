"""C4-only helpers; verify all799 archives and the frozen initial numeric FINAL."""
import sys
sys.dont_write_bytecode=True
if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)
from pathlib import Path
from hashlib import sha256
from importlib.util import spec_from_file_location,module_from_spec
import json
ROOT=Path(__file__).resolve().parent;ROUND=ROOT.parent
MANIFEST_SHA='c6e1efe0ef1e4c2448bb9d53eb6df1635b29eb9a077723620ce62d4f45a6b1e4'
ROUGH_SHA='e4dd2c8e12cbfd34c90208ffb90745472bc8e2c3a3f777681a9d52735fcadfbb'
def digest(path):return sha256(path.read_bytes()).hexdigest()
assert digest(ROUND/'numeric_manifest.json')==MANIFEST_SHA
INITIAL=json.loads((ROUND/'numeric_manifest.json').read_text(encoding='utf-8'))
assert len(INITIAL['sha256'])==33
assert digest(ROUND/'shared.py')==INITIAL['sha256']['shared.py']
spec=spec_from_file_location('goldbach_round17_c4_inert_helpers',ROUND/'shared.py')
s=module_from_spec(spec);sys.modules[spec.name]=s;spec.loader.exec_module(s)
def verify():
 assert digest(ROUND/'numeric_manifest.json')==MANIFEST_SHA
 for relative,expected in INITIAL['sha256'].items():assert digest(ROUND/relative)==expected,relative
 for relative,expected in INITIAL['reports_FINAL_sha256'].items():assert digest(ROUND/relative)==expected,relative
 assert digest(ROUND/'PROBE_BLOCK.md')==INITIAL['probe_sha256']
 assert digest(ROUND/'rough.json')==ROUGH_SHA
 return {'status':'PRESERVED_799_AND_FROZEN_INITIAL_FINAL6','old799':s.conservation.verify(),
  'initial33_numeric_bindings_verified':True,'initial_numeric_manifest_sha256':MANIFEST_SHA,
  'initial_reports_and_addendum_unchanged':True,'old_or_initial_producer_kernel_sign_Lean_render_executed':False}
def output_directory(path):
 path=Path(path).resolve();assert path==ROOT or ROOT in path.parents;path.mkdir(parents=True,exist_ok=True);return path
