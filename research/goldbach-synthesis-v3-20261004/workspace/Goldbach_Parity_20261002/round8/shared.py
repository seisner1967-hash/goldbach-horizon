"""Exact imports for round8; earlier modules are read without bytecode writes."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
ROOT=Path(__file__).resolve().parent
BASE=ROOT.parent
sys.path.insert(0,str(BASE/'round6'))
from exact_tools import (N,factor,divisors,mu,actual_profile,vector_add,
    multiply_vectors,polynomial_sign_certificate,parse_log_vector)
sys.path.insert(0,str(BASE/'round4'))
from inverse_checks import reduce_phases,cyclic_convolution

def primitive_logs(p):
    assert factor(p)==((p,1),)
    for generator in range(2,p):
        logs={pow(generator,j,p):j for j in range(p-1)}
        if len(logs)==p-1:return generator,logs
    raise AssertionError('No primitive generator found')

def serialize(v):
    return {','.join(map(str,key)):str(c) for key,c in sorted(v.items())}

def log_vector(n):
    return {(p,):e for p,e in factor(n)}

def output_directory():
    import argparse
    parser=argparse.ArgumentParser()
    parser.add_argument('--output-dir',type=Path,default=ROOT,
                        help='Write numerical JSON receipts here; the conservation registry remains fixed in round8')
    directory=parser.parse_args().output_dir.resolve()
    directory.mkdir(parents=True,exist_ok=True)
    return directory
