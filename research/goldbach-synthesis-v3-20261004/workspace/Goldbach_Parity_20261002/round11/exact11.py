"""Exact new-contract arithmetic and rational polynomial sign intervals for round11."""
import sys
sys.dont_write_bytecode=True
if hasattr(sys,'set_int_max_str_digits'):
    sys.set_int_max_str_digits(0)
from importlib.util import spec_from_file_location,module_from_spec
from pathlib import Path
from functools import lru_cache
from fractions import Fraction
from math import gcd,prod

ROOT=Path(__file__).resolve().parent
spec=spec_from_file_location('round11_shared_exact',ROOT/'shared.py')
shared=module_from_spec(spec);spec.loader.exec_module(shared)
N,ALPHA,A,Q=shared.N,100,3163,999999
factor,divisors,mu=shared.factor,shared.divisors,shared.mu
add,multiply=shared.vector_add,shared.multiply_vectors
log_vector,serialize=shared.log_vector,shared.serialize


def prime(n):
    return 1<n<=N and factor(n)==((n,1),)


def theta(n):
    return log_vector(n) if prime(n) and gcd(n,N)==1 else {}


def Lambda(n):
    fs=factor(n)
    return log_vector(fs[0][0]) if len(fs)==1 else {}


@lru_cache(None)
def phi(n):
    return prod(p**(e-1)*(p-1) for p,e in factor(n))


def logr(m,k):
    value=log_vector(m);add(value,log_vector(k),-1)
    return value


def prefix(m,cut):
    value={}
    for r in divisors(m):
        if r<=cut:
            add(value,log_vector(r),mu(r))
    return value


@lru_cache(None)
def kernels(m,min_k=1):
    assert 0<m<=N-2
    n=N-m;D,W={},{};R=min(Q,(m-1)//A)
    for k in divisors(m):
        if min_k<=k<=Q and A*k<m:
            add(D,logr(m,k),-mu(k))
    for k in range(min_k,R+1):
        if gcd(k,n*N)==1:
            add(W,logr(m,k),Fraction(-mu(k),phi(k)))
    return D,W,R


@lru_cache(None)
def log_grid(p,terms,bits):
    scale=1<<bits
    lo,hi=shared.multifibre.log_prime_bounds(p,terms)
    lower=(lo.numerator*scale)//lo.denominator
    upper=(hi.numerator*scale+hi.denominator-1)//hi.denominator
    assert 0<=Fraction(lower,scale)<=lo<=hi<=Fraction(upper,scale)
    return lower,upper


def sign_certificate(value):
    if not value:
        return dict(sign='ZERO',lower='0',upper='0',terms=0,bits=0)
    for terms,bits in ((6,96),(12,128),(24,192),(48,256)):
        scale=1<<bits;lower=upper=Fraction(0)
        for key,c in value.items():
            gridlo=gridhi=1
            for p in key:
                lo,hi=log_grid(p,terms,bits);gridlo*=lo;gridhi*=hi
            denominator=scale**len(key)
            lower+=c*Fraction(gridlo if c>0 else gridhi,denominator)
            upper+=c*Fraction(gridhi if c>0 else gridlo,denominator)
        assert lower<=upper
        if lower>0 or upper<0:
            return dict(sign='POSITIVE' if lower>0 else 'NEGATIVE',
                lower=str(lower),upper=str(upper),terms=terms,bits=bits)
    return dict(sign='UNRESOLVED',lower=str(lower),upper=str(upper),terms=terms,bits=bits)
