"""Exact shared helpers for round6; importing does not write old artifacts."""
import sys
sys.dont_write_bytecode=True
from fractions import Fraction
from functools import lru_cache
from hashlib import sha256
from math import gcd
from pathlib import Path

ROOT=Path(__file__).resolve().parent
BASE=ROOT.parent
sys.path.insert(0,str(BASE/'numerical'))
sys.path.insert(0,str(BASE/'round3'))
from parity_checks import N,factor,divisors,mu,rough
from round2_checks import local_term
from multifibre_checks import log_prime_bounds


def normalize(vector):
    return {key:value for key,value in vector.items() if value}


def vector_add(target,source,scale=1):
    for key,c in source.items():
        target[key]=target.get(key,Fraction(0))+scale*c
        if target[key]==0:
            del target[key]


def multiply_vectors(left,right):
    output={}
    for key,c in left.items():
        for other,d in right.items():
            combined=tuple(sorted(key+other))
            output[combined]=output.get(combined,Fraction(0))+c*d
    return normalize(output)


def parse_log_vector(vector):
    return {(int(p),):Fraction(c) for p,c in vector.items()}


@lru_cache(None)
def actual_profile(m):
    """Unit-masked F_N(m)=fII(N-m)*(D-W), without a fabricated Mobius sign.

    All masks and endpoints are computed at the actual argument m. The
    diagnostic callers must state any further squarefree/rough selectors.
    """
    if not 0<m<N:
        return {},dict(m=m,n=N-m,front_admitted=False)
    if N-m<=1:
        return {},dict(m=m,n=N-m,rho1=False)
    if m==1:
        return {},dict(m=m,n=N-1,unit=True,front_admitted=True,prefix=0,
                       D={},W={},reason='Strict face alpha*k<m admits no positive k')
    if gcd(m,N)!=1:
        return {},dict(m=m,n=N-m,unit=False)
    metadata,_=local_term(m)
    f=parse_log_vector(metadata['fII'])
    kernel=parse_log_vector(metadata['D_minus_W'])
    return multiply_vectors(f,kernel),metadata


def polynomial_sign_certificate(vector):
    if not vector:
        return dict(sign='ZERO',lower='0/1',upper='0/1',terms=0)
    for terms in (6,12,24,48):
        lower=upper=Fraction(0)
        for key,c in vector.items():
            term_lower=term_upper=Fraction(1)
            for prime in key:
                lo,hi=log_prime_bounds(prime,terms)
                term_lower*=lo
                term_upper*=hi
            if c>0:
                lower+=c*term_lower
                upper+=c*term_upper
            else:
                lower+=c*term_upper
                upper+=c*term_lower
        assert lower<=upper
        if upper<0 or lower>0:
            return dict(sign='NEGATIVE' if upper<0 else 'POSITIVE',terms=terms,
                        lower=f'{lower.numerator}/{lower.denominator}',
                        upper=f'{upper.numerator}/{upper.denominator}')
    return dict(sign='UNRESOLVED',terms=terms,
                lower=f'{lower.numerator}/{lower.denominator}',
                upper=f'{upper.numerator}/{upper.denominator}')


def squarefree_divisor_expansion(n):
    assert 1<=n<=N
    total=sum(mu(d) for d in divisors(n) if n%(d*d)==0)
    assert total==mu(n)*mu(n)
    return total


def squarefree_CRT(C,d,e):
    """Return exact zeta class for d²|zeta, e²|N-C*zeta, or None."""
    assert C>0 and d>0 and e>0
    coefficient=C*d*d
    modulus=e*e
    g=gcd(coefficient,modulus)
    if N%g:
        return None
    reduced=modulus//g
    t0=0 if reduced==1 else ((N//g)*pow(coefficient//g,-1,reduced))%reduced
    residue=d*d*t0
    period=d*d*reduced
    assert residue%(d*d)==0 and (N-C*residue)%(e*e)==0
    return residue,period


def script_hash(path):
    return sha256(Path(path).read_bytes()).hexdigest()
