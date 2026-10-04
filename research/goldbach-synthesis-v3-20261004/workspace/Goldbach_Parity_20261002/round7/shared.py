"""Round 7 exact imports; no bytecode or writes to earlier rounds."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
ROOT=Path(__file__).resolve().parent
BASE=ROOT.parent
sys.path.insert(0,str(BASE/'round6'))
from exact_tools import (N,factor,divisors,mu,actual_profile,vector_add,
    multiply_vectors,polynomial_sign_certificate)

def log_vector(n):
    return {(p,):e for p,e in factor(n)}

def serialize(v):
    return {','.join(map(str,key)):str(value) for key,value in sorted(v.items())}
