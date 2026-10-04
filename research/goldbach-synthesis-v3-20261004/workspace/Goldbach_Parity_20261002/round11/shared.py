"""Explicit verified helper paths for round11; historical modules stay read-only."""
import sys
sys.dont_write_bytecode = True
from importlib.util import module_from_spec, spec_from_file_location
from fractions import Fraction
from hashlib import sha256
from pathlib import Path
import argparse

ROOT = Path(__file__).resolve().parent
BASE = ROOT.parent
IMPORTS = {}


def load_explicit(name, relative):
    path = (BASE / relative).resolve()
    previous = sys.modules.get(name)
    if previous is not None:
        assert Path(previous.__file__).resolve() == path, (name, previous.__file__, str(path))
        module = previous
    else:
        spec = spec_from_file_location(name, path)
        assert spec is not None and spec.loader is not None
        module = module_from_spec(spec)
        sys.modules[name] = module
        saved_path = list(sys.path)
        try:
            spec.loader.exec_module(module)
        finally:
            sys.path[:] = saved_path
    IMPORTS[relative] = sha256(path.read_bytes()).hexdigest()
    return module


parity = load_explicit('parity_checks', 'numerical/parity_checks.py')
round2 = load_explicit('round2_checks', 'numerical/round2_checks.py')
multifibre = load_explicit('multifibre_checks', 'round3/multifibre_checks.py')
exact = load_explicit('goldbach_round11_exact_tools', 'round6/exact_tools.py')
inverse = load_explicit('goldbach_round11_inverse_checks', 'round4/inverse_checks.py')
conservation = load_explicit('goldbach_round11_conservation', 'round11/conservation.py')

N = parity.N
factor = parity.factor
divisors = parity.divisors
mu = parity.mu
actual_profile = exact.actual_profile
vector_add = exact.vector_add
multiply_vectors = exact.multiply_vectors
polynomial_sign_certificate = exact.polynomial_sign_certificate
parse_log_vector = exact.parse_log_vector
reduce_phases = inverse.reduce_phases
cyclic_convolution = inverse.cyclic_convolution
initialize = conservation.initialize
verify = conservation.verify


def serialize(vector):
    return {','.join(map(str, key)):str(value) for key, value in sorted(vector.items()) if value}


def log_vector(n):
    return {(p,):Fraction(e) for p, e in factor(n)}


def output_directory():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output-dir', type=Path, default=ROOT,
                        help='Write only new receipts under round11; all older production is frozen')
    return conservation.output_directory(parser.parse_args().output_dir)
