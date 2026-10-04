"""Verified explicit historical arithmetic imports for NEW round12 contracts only."""
import sys
sys.dont_write_bytecode=True
from importlib.util import module_from_spec,spec_from_file_location
from fractions import Fraction
from hashlib import sha256
from pathlib import Path
import argparse
import json

ROOT=Path(__file__).resolve().parent
BASE=ROOT.parent
IMPORTS={}
PROTECTED=json.loads((ROOT/'previous_artifacts_sha256.json').read_text(encoding='utf-8'))['sha256']


def load_explicit(name,relative):
    path=(BASE/relative).resolve();digest=sha256(path.read_bytes()).hexdigest()
    if not relative.startswith('round12/'):
        assert PROTECTED[relative]==digest,(relative,PROTECTED[relative],digest)
    previous=sys.modules.get(name)
    if previous is not None:
        assert Path(previous.__file__).resolve()==path,(name,previous.__file__,str(path))
        module=previous
    else:
        spec=spec_from_file_location(name,path);assert spec is not None and spec.loader is not None
        module=module_from_spec(spec);sys.modules[name]=module
        saved_path=list(sys.path)
        try:
            spec.loader.exec_module(module)
        finally:
            sys.path[:]=saved_path
    IMPORTS[relative]=digest
    return module


conservation=load_explicit('goldbach_round12_conservation','round12/conservation.py')
parity=load_explicit('parity_checks','numerical/parity_checks.py')
round2=load_explicit('round2_checks','numerical/round2_checks.py')
multifibre=load_explicit('multifibre_checks','round3/multifibre_checks.py')
exact=load_explicit('goldbach_round12_raw_tools','round6/exact_tools.py')
inverse=load_explicit('goldbach_round12_inverse','round4/inverse_checks.py')
legacy_shared=load_explicit('goldbach_round12_legacy_shared','round11/shared.py')
arithmetic=load_explicit('goldbach_round12_arithmetic','round11/exact11.py')

N=parity.N
ALPHA,A,Q=100,3163,999999
assert (ALPHA-1)**4<N<=ALPHA**4
assert (A-1)**16<N**7<=A**16 and Q==(N-1)//ALPHA
factor,divisors,mu=parity.factor,parity.divisors,parity.mu
actual_profile=exact.actual_profile
vector_add,multiply_vectors=exact.vector_add,exact.multiply_vectors
parse_log_vector=exact.parse_log_vector
reduce_phases,cyclic_convolution=inverse.reduce_phases,inverse.cyclic_convolution
phi,prime,theta,Lambda,kernels=arithmetic.phi,arithmetic.prime,arithmetic.theta,arithmetic.Lambda,arithmetic.kernels
prefix,sign_certificate=arithmetic.prefix,arithmetic.sign_certificate
initialize,verify=conservation.initialize,conservation.verify


def serialize(vector):
    return {','.join(map(str,key)):str(value) for key,value in sorted(vector.items()) if value}


def log_vector(n):
    return {(p,):Fraction(e) for p,e in factor(n)}


def output_directory():
    parser=argparse.ArgumentParser();parser.add_argument('--output-dir',type=Path,default=ROOT,
        help='Write NEW receipts under round12; never write earlier production')
    return conservation.output_directory(parser.parse_args().output_dir)
