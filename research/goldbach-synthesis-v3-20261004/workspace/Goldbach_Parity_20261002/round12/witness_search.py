"""NEW arithmetic witness searches; no candidate identity or analytic gate claimed."""
import sys
sys.dont_write_bytecode=True
from importlib.util import spec_from_file_location,module_from_spec
from pathlib import Path
from hashlib import sha256
from math import gcd
import json

ROOT=Path(__file__).resolve().parent
spec=spec_from_file_location('round12_shared_witness',ROOT/'shared.py')
X=module_from_spec(spec);spec.loader.exec_module(X)
N,ALPHA,A,Q=X.N,X.ALPHA,X.A,X.Q


def row(m):
    n=N-m
    assert 0<m<N-1
    return dict(m=m,n=n,m_factors=X.factor(m),n_factors=X.factor(n),mu_m=X.mu(m),
        mu_n=X.mu(n),n_prime=X.prime(n),unit_N=gcd(m,N)==1,
        first_Lambda=X.serialize(X.Lambda(n)),theta=X.serialize(X.theta(n)))


def generate():
    witnesses={};counts={}
    attempts=0
    for p in X.parity.PRIMES:
        if not 17<=p<1000 or p in (3,11) or gcd(p,N)!=1:
            continue
        attempts+=1;m=33*p
        if X.prime(N-m):
            value=row(m);assert value['mu_m']==-1 and len(value['m_factors'])==3
            witnesses['new_negative_reference']=dict(**value,p=p)
            break
    counts['new_negative_reference']=attempts
    attempts=0
    for p in X.parity.PRIMES:
        if not 107<=p<1000 or gcd(p,3*N)!=1:
            continue
        attempts+=1
        if X.prime(N-9*p):
            value=row(9*p);assert value['mu_m']==0
            witnesses['new_nonsquarefree_prime_axis']=dict(**value,repeated_prime=3,p=p)
            break
    counts['new_nonsquarefree_prime_axis']=attempts
    assert 'new_nonsquarefree_prime_axis' in witnesses
    attempts=0
    for p in X.parity.PRIMES:
        if not 17<=p<1000 or gcd(p,N)!=1:
            continue
        attempts+=1
        if X.prime(N-p):
            value=row(p);assert value['mu_m']==-1
            witnesses['new_prime_pair']=dict(**value,p=p)
            break
    counts['new_prime_pair']=attempts
    assert 'new_prime_pair' in witnesses
    for name,c in (('J1_two_small',3*1061),('J1_three_small',7*13*37)):
        assert c>A and X.mu(c)!=0
        attempts=0
        for p in X.parity.PRIMES:
            if p<=A or c*p>N-Q-1 or gcd(p,c*N)!=1:
                continue
            attempts+=1
            if X.prime(N-c*p):
                value=row(c*p);assert value['unit_N'] and value['mu_m']!=0
                witnesses[name]=dict(**value,c=c,p=p,
                    U_a=X.serialize(X.prefix(c*p,A)),U_alpha=X.serialize(X.prefix(c*p,ALPHA)),
                    c_short_fiber_complete=False)
                break
        counts[name]=attempts
        assert name in witnesses
    attempts=0
    for p in X.parity.PRIMES:
        if not 8000<p<10000 or gcd(p,N)!=1:
            continue
        attempts+=1;n=p*p;m=N-n
        if m>1 and gcd(m,N)==1 and X.mu(m)!=0:
            value=row(m);assert not value['n_prime'] and value['mu_n']==0
            multiplier=dict(X.Lambda(n));X.vector_add(multiplier,X.log_vector(n),-1)
            witnesses['new_properpower_axis']=dict(**value,p=p,
                raw_fII_multiplier=X.serialize(multiplier),mu_n_squared_Lambda={},
                whole_raw_not_computed=True)
            break
    counts['new_properpower_axis']=attempts
    assert 'new_negative_reference' in witnesses and 'new_properpower_axis' in witnesses
    return dict(witnesses=witnesses,search_counts=counts)


if __name__=='__main__':
    output=X.output_directory();before=X.verify();values=generate()
    result=dict(status='VERIFIED_NEW_ARITHMETIC_WITNESSES_ONLY',N=N,alpha=ALPHA,a=A,Q=Q,
        **values,imports=X.IMPORTS,script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
        shared_sha256=sha256((ROOT/'shared.py').read_bytes()).hexdigest(),
        conservation_before=before,conservation_after=X.verify(),
        candidate_gate=False,global_D_N=False,asymptotic=False,payments=False,Lean_called=False,victory=False)
    (output/'witnesses.json').write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
    print(json.dumps(values,indent=2))
