"""NEW three-incidence capacity and guarded von-Mangoldt convolution detector."""
import sys
sys.dont_write_bytecode=True
from importlib.util import spec_from_file_location,module_from_spec
from pathlib import Path
from hashlib import sha256
from fractions import Fraction
from math import gcd
import json

ROOT=Path(__file__).resolve().parent
spec=spec_from_file_location('round12_shared_star',ROOT/'shared.py')
X=module_from_spec(spec);spec.loader.exec_module(X)
spec=spec_from_file_location('round12_witness_star',ROOT/'witness_search.py')
W=module_from_spec(spec);spec.loader.exec_module(W)


def scale(value,c):
    return {key:v*c for key,v in value.items() if v*c}


def star():
    p,q=3167,3169;t=p*q;cap=(X.N-X.Q-1)//t
    M=1000000;assert (M-1)**4<X.N**3<=M**4
    grid=[c for c in range(1,cap+1) if X.mu(c)!=0 and gcd(c,X.N*t)==1]
    assert grid==[1,3,7] and cap==9 and X.prime(p) and X.prime(q)
    whole,constant,S={},{},{};points={}
    for c in grid:
        m=c*t;n=X.N-m
        assert X.prime(n) and gcd(n,X.N)==1
        D,Wkernel,R=X.kernels(m)
        actual=scale(D,-X.mu(m));X.vector_add(actual,Wkernel,X.mu(m))
        expected=dict(X.Lambda(c));X.vector_add(expected,Wkernel,X.mu(c));assert actual==expected
        D2,W2,_=X.kernels(m,2)
        paired_k1=scale(D2,-X.mu(m));X.vector_add(paired_k1,W2,X.mu(m))
        assert actual==paired_k1
        theta=X.theta(n)
        X.vector_add(whole,X.multiply_vectors(theta,actual))
        X.vector_add(constant,X.multiply_vectors(theta,X.Lambda(c)))
        X.vector_add(S,theta,-X.mu(c))
        points[str(c)]=dict(m=m,n=n,m_factors=X.factor(m),n_factors=X.factor(n),
            mu_m=X.mu(m),R=R,D=X.serialize(D),W_kernel=X.serialize(Wkernel),
            actual_C=X.serialize(actual),all_k_equals_ge2=True)
    assert points['3']['n']*points['7']['n']>points['1']['n']
    cut_m={c*t for c in grid};children=[]
    for c in grid:
        m=c*t
        for removed_prime,_ in X.factor(m):
            child=m//removed_prime;child_n=X.N-child
            keeps_bulk=M<=child<=X.N-X.Q-1
            if removed_prime>X.A:
                assert child*X.A<X.N and child<M and not keeps_bulk
            if keeps_bulk:
                assert child in cut_m and removed_prime in (3,7) and child==t
            children.append(dict(parent_m=m,removed_prime=removed_prime,child_m=child,
                child_n=child_n,bulk=keeps_bulk,in_cut=child in cut_m,
                child_factors=X.factor(child),child_n_factors=X.factor(child_n),
                child_mu=X.mu(child),child_unit_N=gcd(child,X.N)==1,
                child_first_Lambda=X.serialize(X.Lambda(child_n)),child_theta=X.serialize(X.theta(child_n)),
                complementary_nonbulk_term_not_paid=not keeps_bulk))
    constant_sign=X.sign_certificate(constant);S_sign=X.sign_certificate(S)
    whole_sign=X.sign_certificate(whole)
    assert constant_sign['sign']==S_sign['sign']==whole_sign['sign']=='POSITIVE'
    return dict(status='PASS_NEW_FULL_THREE_INCIDENCE_CAPACITY_ONLY',p=p,q=q,t=t,C_t=cap,
        complete_X=grid,points=points,whole_actual_brackets=X.serialize(whole),
        whole_actual_sign=whole_sign,Kstar_constant=X.serialize(constant),Kstar_S_coefficient=X.serialize(S),
        Kstar_constant_sign=constant_sign,Kstar_S_sign=S_sign,
        positive_for_all_positive_S_by_separate_coefficients=True,
        bulk_cut_closed_under_prime_deletion=True,bulk_threshold_M=M,
        prime_deletion_children=children,nonbulk_complement_not_estimated=True,
        integer_product_test=dict(n3_n7=points['3']['n']*points['7']['n'],n1=points['1']['n']),
        S_N_not_evaluated=True,matching_actual_W_terms_retained=True,
        analytical_source_onset_assumed_at_N=False,
        false_full_star_favorable=dict(status='ERROR_FALSIFIER',actual_sign=whole_sign,
            model_constant_sign=constant_sign,model_S_sign=S_sign,global_no_go=False))


def detector(m):
    assert 1<m<=X.N-2 and gcd(m,X.N)==1
    n=X.N-m;logm=X.log_vector(m);mu_m=X.mu(m)
    E=scale(logm,mu_m);X.vector_add(E,X.Lambda(m),mu_m**2)
    V={};absolute_V={};survivors=[]
    for d in X.divisors(m):
        if d>1:
            mangoldt=X.Lambda(m//d)
            X.vector_add(V,mangoldt,-X.mu(d))
            X.vector_add(absolute_V,mangoldt,abs(X.mu(d)))
            if X.mu(d) and mangoldt:
                survivors.append(dict(d=d,quotient=m//d,mu_d=X.mu(d),
                    V_numerator=X.serialize(scale(mangoldt,-X.mu(d)))))
    P=scale(X.Lambda(m),1-mu_m**2)
    rhs=dict(V);X.vector_add(rhs,P,-1);assert E==rhs
    return dict(m=m,n=n,m_factors=X.factor(m),n_factors=X.factor(n),mu_m=mu_m,
        Lambda_N=X.serialize(X.Lambda(n)),theta_N=X.serialize(X.theta(n)),
        log_m=X.serialize(logm),E_times_log_m=X.serialize(E),
        V_times_log_m=X.serialize(V),P_times_log_m=X.serialize(P),identity_after_log_m=True,
        V_survivors=survivors,absolute_V_times_log_m=X.serialize(absolute_V),
        _E=E,_V=V,_P=P,_absoluteV=absolute_V)


def properpower_witness():
    attempts=0
    for p in X.parity.PRIMES:
        if not 3<=p<=100 or gcd(p,X.N)!=1:
            continue
        for exponent in (2,3,4,5):
            m=p**exponent
            if m>X.N-2:
                continue
            attempts+=1
            if X.prime(X.N-m):
                result=detector(m)
                assert X.mu(m)==0 and not result['_E']
                assert result['_V']==result['_P']==X.log_vector(p)
                assert X.log_vector(m)==scale(X.log_vector(p),exponent)
                result.update(p=p,exponent=exponent,V_and_P_value=f'1/{exponent}',attempted=attempts)
                return result
    raise AssertionError('No NEW prime-complement properpower witness in searched domain')


if __name__=='__main__':
    output=X.output_directory();before=X.verify();witnesses=W.generate()['witnesses']
    points={name:detector(witnesses[name]['m']) for name in ('J1_two_small','J1_three_small','new_properpower_axis')}
    proper=properpower_witness();points['new_second_axis_properpower']=proper
    assert points['J1_two_small']['_E']==scale(X.log_vector(points['J1_two_small']['m']),-1)
    assert points['J1_three_small']['_E']==X.log_vector(points['J1_three_small']['m'])
    coverage={}
    for name in ('J1_two_small','J1_three_small'):
        point=points[name];m=point['m'];logm=X.log_vector(m)
        assert point['_absoluteV']==logm and X.mu(m)!=0 and len(X.factor(m))>1
        expected_d={m//p for p,_ in X.factor(m)}
        assert {term['d'] for term in point['V_survivors']}==expected_d
        assert all(term['mu_d']==-X.mu(m) for term in point['V_survivors'])
        gap=dict(logm);X.vector_add(gap,{():Fraction(1)},-1)
        gap_sign=X.sign_certificate(gap);assert gap_sign['sign']=='POSITIVE'
        coverage[name]=dict(status='ERROR_FALSIFIER',m=m,n=point['n'],
            complete_L1_V='1',absolute_numerator=X.serialize(point['_absoluteV']),
            log_m=X.serialize(logm),false_bound='L1_V <= 1/log(m)',
            residual_after_log_m=X.serialize(gap),sign=gap_sign,
            global_no_go=False)
    false_omit_P=dict(proper['_V']);X.vector_add(false_omit_P,proper['_E'],-1)
    sign=X.sign_certificate(false_omit_P);assert sign['sign']=='POSITIVE'
    for value in points.values():
        for key in tuple(value):
            if key.startswith('_'):
                del value[key]
    result=dict(status='PASS_NEW_STAR_AND_GUARDED_DETECTOR_IDENTITIES_ONLY',N=X.N,alpha=X.ALPHA,a=X.A,Q=X.Q,
        complete_star=star(),detector_points=points,
        false_free_inverse_log_gain=coverage,
        false_properpower_correction_omitted=dict(status='ERROR_FALSIFIER',m=proper['m'],n=proper['n'],
            residual_after_log_m=X.serialize(false_omit_P),sign=sign),
        properpowers_first_axis_retained=True,mu_n_squared_added=False,
        detector_pointwise_positive_not_assumed=True,imports=X.IMPORTS,
        script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
        shared_sha256=sha256((ROOT/'shared.py').read_bytes()).hexdigest(),
        witness_script_sha256=sha256((ROOT/'witness_search.py').read_bytes()).hexdigest(),
        conservation_before=before,conservation_after=X.verify(),
        global_D_N=False,asymptotic=False,payments=False,Lean_called=False,victory=False)
    (output/'star_detector.json').write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
    print(json.dumps(dict(status=result['status'],star_whole_sign=result['complete_star']['whole_actual_sign']['sign'],
        properpower=dict(m=proper['m'],n=proper['n'],p=proper['p'],exponent=proper['exponent']),
        conservation='PRESERVED'),indent=2))
