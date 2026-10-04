"""NEW J2/J1 exchange p -> r*s=p±2, actual prime incidence and full kernels."""
import sys
sys.dont_write_bytecode=True
from importlib.util import spec_from_file_location,module_from_spec
from pathlib import Path
from hashlib import sha256
from fractions import Fraction
from math import gcd
import json

ROOT=Path(__file__).resolve().parent
spec=spec_from_file_location('round13_shared_exchange',ROOT/'shared.py')
X=module_from_spec(spec);spec.loader.exec_module(X)
N,A,Q=X.N,X.A,X.Q
M=1000000
assert (M-1)**4<N**3<=M**4


def scale(value,c):
    return {key:v*c for key,v in value.items() if v*c}


def find(direction,both=True):
    c=3;trials=dict(p=0,q=0,parent_prime=0)
    for p in X.parity.PRIMES:
        if p<=A or c*p*p>N-Q-1 or gcd(p,N)!=1:
            continue
        trials['p']+=1;rs=p+direction*2;factors=X.factor(rs)
        if len(factors)!=2 or any(e!=1 for _,e in factors):
            continue
        r,s=(v[0] for v in factors)
        if c in (r,s) or gcd(c*r*s,N)!=1 or c*r>A or c*s>A or rs<=A:
            continue
        for q in X.parity.PRIMES:
            if q<=p or c*max(p,rs)*q>N-Q-1 or gcd(q,N)!=1:
                continue
            trials['q']+=1
            n0=N-c*p*q;n1=N-c*rs*q
            if not X.prime(n0):
                continue
            trials['parent_prime']+=1
            if X.prime(n1)==both:
                return dict(c=c,p=p,q=q,r=r,s=s,direction=direction,
                    m0=c*p*q,m1=c*rs*q,n0=n0,n1=n1,search_counts=trials)
    raise AssertionError(('No actual exchange witness',direction,both,trials))


def branch(m):
    n=N-m
    assert M<=m<=N-Q-1 and gcd(m,N)==1 and X.mu(m)!=0
    D,W,R=X.kernels(m)
    C=scale(D,-X.mu(m));X.vector_add(C,W,X.mu(m))
    D2,W2,_=X.kernels(m,2)
    removed=scale(D2,-X.mu(m));X.vector_add(removed,W2,X.mu(m));assert C==removed
    low=X.prefix(m,X.ALPHA);full=X.prefix(m,A);band=dict(full);X.vector_add(band,low,-1)
    return dict(m=m,n=n,m_factors=X.factor(m),n_factors=X.factor(n),mu_m=X.mu(m),
        theta=X.theta(n),Lambda=X.Lambda(n),U_a=full,U_alpha=low,U_band_alpha_a=band,D=D,W=W,R=R,C=C,
        bracket=X.multiply_vectors(X.theta(n),C),all_k_equals_ge2=True)


def check(witness):
    c,p,q,r,s=(witness[k] for k in ('c','p','q','r','s'))
    assert X.prime(c) and A<p<q and all(X.prime(v) for v in (p,q,r,s))
    assert c<r<s and len({c,p,q,r,s})==5 and gcd(c*p*q*r*s,N)==1
    assert c*r<=A and c*s<=A<r*s and c*r*s>A
    first,second=branch(witness['m0']),branch(witness['m1'])
    assert first['U_a']==scale(X.log_vector(c),-1) and second['U_a']==X.log_vector(c)
    assert first['mu_m']==-1 and second['mu_m']==1
    C0=dict(X.log_vector(c));X.vector_add(C0,first['W'],-1)
    C1=scale(X.log_vector(c),-1);X.vector_add(C1,second['W'])
    assert first['C']==C0 and second['C']==C1
    theta_difference=dict(first['theta']);X.vector_add(theta_difference,second['theta'],-1)
    entropy=X.multiply_vectors(X.log_vector(c),theta_difference)
    signed_kernel=X.multiply_vectors(second['theta'],second['W'])
    X.vector_add(signed_kernel,X.multiply_vectors(first['theta'],first['W']),-1)
    identity=dict(entropy);X.vector_add(identity,signed_kernel)
    whole=dict(first['bracket']);X.vector_add(whole,second['bracket']);assert whole==identity
    model_constant=entropy;model_S=theta_difference
    whole_sign=X.sign_certificate(whole)
    model_sign=X.sign_certificate(model_S);constant_sign=X.sign_certificate(model_constant)
    assert 'UNRESOLVED' not in (whole_sign['sign'],model_sign['sign'],constant_sign['sign'])
    if first['theta'] and second['theta']:
        target='NEGATIVE' if witness['direction']==-1 else 'POSITIVE'
        assert model_sign['sign']==constant_sign['sign']==target
    else:
        assert first['theta'] and not second['theta'] and model_sign['sign']=='POSITIVE'
    def serialize_branch(b):
        return {key:(X.serialize(value) if isinstance(value,dict) else value) for key,value in b.items()}
    return dict(**witness,first=serialize_branch(first),second=serialize_branch(second),
        whole_actual_pair=X.serialize(whole),exact_entropy=X.serialize(entropy),
        exact_signed_kernel=X.serialize(signed_kernel),whole_sign=whole_sign,
        principal_constant=X.serialize(model_constant),principal_S=X.serialize(model_S),
        principal_constant_sign=constant_sign,principal_S_sign=model_sign,
        S_N_not_evaluated=True,source_onset_not_assumed_at_finite_N=True,
        large_factor_kernel_changed=True,incomplete_small_fibre_retained=True)


def finite_W_difference(record):
    m0,m1=record['m0'],record['m1'];n0,n1=record['n0'],record['n1']
    assert m1<m0 and X.prime(n0) and X.prime(n1) and n0>Q and n1>Q
    _,W0,R0=X.kernels(m0);_,W1,R1=X.kernels(m1)
    assert R1==min(Q,(m1-1)//A) and R0==min(Q,(m0-1)//A) and R1<=R0
    head=sum((Fraction(X.mu(k),X.phi(k)) for k in range(1,R1+1) if gcd(k,N)==1),Fraction(0))
    logratio=X.log_vector(m0);X.vector_add(logratio,X.log_vector(m1),-1)
    tail={};tail_terms=[]
    for k in range(R1+1,R0+1):
        if gcd(k,N)==1:
            logkm0=X.log_vector(k);X.vector_add(logkm0,X.log_vector(m0),-1)
            coefficient=Fraction(X.mu(k),X.phi(k))
            X.vector_add(tail,logkm0,coefficient)
            tail_terms.append(dict(k=k,mu=X.mu(k),phi=X.phi(k),coefficient=str(coefficient)))
    expected=scale(logratio,head);X.vector_add(expected,tail,-1)
    actual=dict(W1);X.vector_add(actual,W0,-1);assert actual==expected
    omitted_tail=scale(logratio,head);residual=dict(omitted_tail);X.vector_add(residual,actual,-1)
    certificate=X.sign_certificate(residual)
    assert residual and certificate['sign']!='UNRESOLVED'
    return dict(status='PASS_NEW_LITERAL_TWO_FRONT_W_IDENTITY_ONLY',m0=m0,m1=m1,R0=R0,R1=R1,
        front_formula='min(Q,(m-1)//a)',A_N_R1=str(head),k1_included=True,
        log_m0_over_m1=X.serialize(logratio),tail=X.serialize(tail),tail_terms=tail_terms,
        actual_difference=X.serialize(actual),identity_difference=X.serialize(expected),
        source_uniformity_requires_both_axes_prime_above_Q=True,
        analytical_variation_bound_numerically_tested=False,
        false_tail_omitted=dict(status='ERROR_FALSIFIER',residual=X.serialize(residual),sign=certificate))


if __name__=='__main__':
    output=X.output_directory();before=X.verify()
    records=dict(minus_two_joint=check(find(-1,True)),plus_two_joint=check(find(1,True)),
        minus_two_unmatched_parent=check(find(-1,False)))
    downward=records['minus_two_joint']
    assert downward['first']['U_alpha']==X.serialize(scale(X.log_vector(3),-1))
    assert not downward['first']['U_band_alpha_a'] and not downward['second']['U_alpha']
    assert downward['second']['U_band_alpha_a']==X.serialize(X.log_vector(3))
    result=dict(status='PASS_NEW_CROSS_KERNEL_EXCHANGE_IDENTITY_ONLY',N=N,alpha=X.ALPHA,a=A,Q=Q,M=M,
        exchanges=records,
        literal_W_difference=finite_W_difference(records['minus_two_joint']),
        false_direction_ignored=dict(status='ERROR_FALSIFIER',witness='plus_two_joint',
            principal_S_sign=records['plus_two_joint']['principal_S_sign']),
        false_parent_coverage=dict(status='ERROR_FALSIFIER',witness='minus_two_unmatched_parent',
            actual_incidence=records['minus_two_unmatched_parent']['principal_S_sign']),
        false_bare_downward_pair_nonpositive=dict(status='ERROR_FALSIFIER',witness='minus_two_joint',
            actual_sign=records['minus_two_joint']['whole_sign'],
            scope='Bare finite pair <= 0, without retained commutator correction',
            source_commutator_bound_tested=False,global_no_go=False),
        imports=X.IMPORTS,script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
        shared_sha256=sha256((ROOT/'shared.py').read_bytes()).hexdigest(),
        conservation_before=before,conservation_after=X.verify(),
        global_D_N=False,asymptotic=False,payments=False,Lean_called=False,victory=False)
    (output/'exchange.json').write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
    print(json.dumps(dict(status=result['status'],witnesses={name:dict(
        **{key:record[key] for key in ('c','p','q','r','s','m0','m1','n0','n1')},
        whole_sign=record['whole_sign']['sign'],principal_S_sign=record['principal_S_sign']['sign']) for name,record in records.items()},
        conservation='PRESERVED'),indent=2))
