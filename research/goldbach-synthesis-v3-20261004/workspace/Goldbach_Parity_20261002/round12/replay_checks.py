"""Replay only NEW round12 witnesses, deletion and star/detector contracts."""
import sys
sys.dont_write_bytecode=True
from importlib.util import spec_from_file_location,module_from_spec
from pathlib import Path
from hashlib import sha256
from concurrent.futures import ThreadPoolExecutor
import subprocess
import json

ROOT=Path(__file__).resolve().parent
spec=spec_from_file_location('round12_shared_replay',ROOT/'shared.py')
X=module_from_spec(spec);spec.loader.exec_module(X)
BANKS=(('witness_search.py','witnesses.json'),('deletion_checks.py','deletion.json'),
       ('star_detector_checks.py','star_detector.json'))


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


if __name__=='__main__':
    output=X.output_directory();before=X.verify()
    isolated=output/'isolated_output_probe';isolated.mkdir(parents=True,exist_ok=True)
    originals={receipt:(ROOT/receipt).read_bytes() for _,receipt in BANKS}
    sources={script:digest(ROOT/script) for script,_ in BANKS}
    def run_bank(bank):
        script,receipt=bank
        command=[sys.executable,'-B','-X','utf8',str(ROOT/script),'--output-dir',str(isolated)]
        result=subprocess.run(command,cwd=ROOT,capture_output=True,text=True,encoding='utf-8')
        assert result.returncode==0,(script,result.returncode,result.stdout,result.stderr)
        original=originals[receipt];replayed=(isolated/receipt).read_bytes()
        assert original==replayed and json.loads(original)==json.loads(replayed),receipt
        assert (ROOT/receipt).read_bytes()==original and digest(ROOT/script)==sources[script]
        return dict(script=script,receipt=receipt,command=command,exit_code=result.returncode,
            all_JSON_fields_equal=True,exact_bytes_equal=True,canonical_unchanged=True,
            script_sha256=sources[script],canonical_sha256=sha256(original).hexdigest(),
            replay_sha256=sha256(replayed).hexdigest(),bytes=len(original),
            status=json.loads(original)['status'])
    with ThreadPoolExecutor(max_workers=len(BANKS)) as pool:
        banks=list(pool.map(run_bank,BANKS))
    names=('conservation.py','shared.py','witness_search.py','deletion_checks.py',
        'star_detector_checks.py','replay_checks.py','previous_artifacts_sha256.json',
        'conservation.json','witnesses.json','deletion.json','star_detector.json')
    result=dict(status='PASS_NEW_ROUND12_BYTES_AND_FIELDS_REPLAY',N=X.N,banks=banks,
        artifact_sha256={name:digest(ROOT/name) for name in names},
        conservation_before=before,conservation_after=X.verify(),
        old_passed_banks_executed=False,old_production_modified=False,bytecode_written=False,
        global_D_N=False,asymptotic=False,payments=False,Lean_called=False,victory=False)
    (output/'numerical_replay.json').write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
    print(json.dumps(dict(status=result['status'],banks=len(banks),all_bytes_equal=True,
        conservation=result['conservation_after']['status']),indent=2))
