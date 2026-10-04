"""Replay only the three NEW round11 banks in an isolated output directory."""
import sys
sys.dont_write_bytecode=True
from importlib.util import spec_from_file_location,module_from_spec
from pathlib import Path
from hashlib import sha256
from concurrent.futures import ThreadPoolExecutor
import subprocess
import json

ROOT=Path(__file__).resolve().parent
spec=spec_from_file_location('round11_shared_replay',ROOT/'shared.py')
shared=module_from_spec(spec);spec.loader.exec_module(shared)
BANKS=(('contract_witnesses.py','witnesses.json'),
       ('ap_prefix_checks.py','ap_prefix.json'),
       ('paired_axes_checks.py','paired_axes.json'))


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


if __name__=='__main__':
    output=shared.output_directory();before=shared.verify()
    isolated=output/'isolated_output_probe';isolated.mkdir(parents=True,exist_ok=True)
    original={receipt:(ROOT/receipt).read_bytes() for _,receipt in BANKS}
    sources={script:digest(ROOT/script) for script,_ in BANKS}
    def run_bank(bank):
        script,receipt=bank
        command=[sys.executable,'-B','-X','utf8',str(ROOT/script),'--output-dir',str(isolated)]
        result=subprocess.run(command,cwd=ROOT,capture_output=True,text=True,encoding='utf-8')
        assert result.returncode==0,(script,result.returncode,result.stdout,result.stderr)
        canonical=original[receipt];replayed=(isolated/receipt).read_bytes()
        assert canonical==replayed,receipt
        assert json.loads(canonical)==json.loads(replayed),receipt
        assert (ROOT/receipt).read_bytes()==canonical and digest(ROOT/script)==sources[script]
        return dict(script=script,receipt=receipt,command=command,exit_code=result.returncode,
            all_JSON_fields_equal=True,exact_bytes_equal=True,canonical_unchanged=True,
            script_sha256=sources[script],canonical_sha256=sha256(canonical).hexdigest(),
            replay_sha256=sha256(replayed).hexdigest(),bytes=len(canonical),
            status=json.loads(canonical)['status'])
    with ThreadPoolExecutor(max_workers=len(BANKS)) as pool:
        banks=list(pool.map(run_bank,BANKS))
    after=shared.verify()
    artifact_names=('conservation.py','shared.py','exact11.py','contract_witnesses.py',
        'ap_prefix_checks.py','paired_axes_checks.py','replay_checks.py',
        'previous_artifacts_sha256.json','conservation.json',
        'witnesses.json','ap_prefix.json','paired_axes.json',
        'agent1_signed_compensation.md','agent2_bilateral_compensation.md')
    result=dict(status='PASS_NEW_ROUND11_BYTES_AND_FIELDS_REPLAY',N=shared.N,
        banks=banks,artifact_sha256={name:digest(ROOT/name) for name in artifact_names},
        conservation_before=before,conservation_after=after,
        old_passed_banks_executed=False,old_production_modified=False,bytecode_written=False,
        global_D_N=False,asymptotic=False,payments=False,Lean_called=False,victory=False)
    (output/'numerical_replay.json').write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
    print(json.dumps(dict(status=result['status'],replayed=len(banks),
        byte_equal=all(b['exact_bytes_equal'] for b in banks),conservation=after['status']),indent=2))
