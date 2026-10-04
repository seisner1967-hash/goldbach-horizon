"""New round11 witnesses for AP coefficients, full prefixes and actual paired axes."""
import sys
sys.dont_write_bytecode=True
from importlib.util import spec_from_file_location,module_from_spec
from pathlib import Path
from hashlib import sha256
from math import gcd
import json

ROOT=Path(__file__).resolve().parent
spec=spec_from_file_location('round11_shared_witnesses',ROOT/'shared.py')
shared=module_from_spec(spec);spec.loader.exec_module(shared)
N,ALPHA,A,Q=shared.N,100,3163,999999


def prime(n):
    return 1<n<=N and shared.factor(n)==((n,1),)


def row(m):
    n=N-m
    assert 1<n<N and gcd(n,N)==1 and prime(n)
    return dict(m=m,n=n,m_factors=shared.factor(m),n_factors=shared.factor(n),mu_m=shared.mu(m))


def generate():
    points=dict(low_prefix=row(11),low_plus_band=row(411),square_tail=row(31047267))
    count=0
    for p in shared.parity.PRIMES:
        if not 100<p<1000:
            continue
        count+=1
        if prime(N-9*p):
            points['square_intersection']=dict(**row(9*p),p=p,attempted=count)
            break
    assert 'square_intersection' in points
    count=0
    for p in shared.parity.PRIMES:
        if not 19<=p<1000 or p in (3,7) or gcd(p,N)!=1:
            continue
        count+=1
        if prime(N-21*p):
            value=row(21*p)
            assert value['mu_m']==-1 and len(value['m_factors'])==3
            points['negative_reference']=dict(**value,p=p,attempted=count)
            break
    assert 'negative_reference' in points
    p,q=3167,3169
    assert prime(p) and prime(q) and A<p<q
    t=p*q
    pairs=dict(both_prime=dict(c=1,p=p,q=q,t=t,base=row(t),tripled=row(3*t)))
    count=0
    for candidate in shared.parity.PRIMES:
        if candidate<=q or p*candidate>N//6:
            continue
        count+=1
        first=N-p*candidate;second=N-3*p*candidate
        if prime(first)!=prime(second):
            pairs['one_prime_axis']=dict(c=1,p=p,q=candidate,t=p*candidate,
                n=first,n3=second,n_factors=shared.factor(first),n3_factors=shared.factor(second),
                n_prime=prime(first),n3_prime=prime(second),attempted=count)
            break
    assert 'one_prime_axis' in pairs
    count=0
    for candidate in shared.parity.PRIMES:
        if candidate<=p or 7*p*candidate>N-Q-1:
            continue
        count+=1
        if prime(N-7*p*candidate):
            m=7*p*candidate
            assert 3*m>N-Q-1
            pairs['c7_missing_face']=dict(c=7,p=p,q=candidate,t=p*candidate,
                base=row(m),tripled_m=3*m,tripled_n=N-3*m,
                base_face=True,tripled_face=False,attempted=count)
            break
    assert 'c7_missing_face' in pairs
    proper_n=9;proper_m=N-proper_n
    assert shared.factor(proper_n)==((3,2),) and gcd(proper_n,N)==1
    assert shared.mu(proper_n)==0 and shared.mu(proper_m)!=0
    proper=dict(n=proper_n,m=proper_m,n_factors=shared.factor(proper_n),
        m_factors=shared.factor(proper_m),n_prime=False,unit_N=True,
        mu_n=shared.mu(proper_n),mu_m=shared.mu(proper_m))
    return dict(points=points,pairs=pairs,properpower_axis=proper)


if __name__=='__main__':
    output=shared.output_directory();before=shared.verify()
    result=dict(status='VERIFIED_NEW_FINITE_WITNESSES_ONLY',N=N,alpha=ALPHA,a=A,Q=Q,
        witnesses=generate(),script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
        imports=shared.IMPORTS,conservation_before=before,conservation_after=shared.verify(),
        global_D_N=False,asymptotic=False,payments=False,Lean_called=False,victory=False)
    (output/'witnesses.json').write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
    print(json.dumps(result['witnesses'],indent=2))
