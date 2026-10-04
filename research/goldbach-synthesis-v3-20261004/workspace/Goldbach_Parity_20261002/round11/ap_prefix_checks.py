"""New AP/lcm prefix contract; finite coefficients and explicitly restricted prime E."""
import sys
sys.dont_write_bytecode=True
from importlib.util import spec_from_file_location,module_from_spec
from pathlib import Path
from hashlib import sha256
from fractions import Fraction
from math import gcd,lcm,prod
import json

ROOT=Path(__file__).resolve().parent
spec=spec_from_file_location('round11_exact_AP',ROOT/'exact11.py')
X=module_from_spec(spec);spec.loader.exec_module(X)
spec=spec_from_file_location('round11_witness_AP',ROOT/'contract_witnesses.py')
W=module_from_spec(spec);spec.loader.exec_module(W)
N,ALPHA,A,Q=X.N,X.ALPHA,X.A,X.Q


def finite_coefficient(r,P,unit_mask=True):
    if unit_mask and gcd(r,N)!=1:
        return Fraction(0)
    product=prod(P)
    return sum((Fraction(X.mu(d),X.phi(lcm(r,d*d)))
        for d in X.divisors(product) if gcd(d,N)==1),Fraction(0))


def coefficient_checks():
    P=(3,5,7,11,13)
    V=prod(1-Fraction(1,p*(p-1)) for p in P if N%p)
    assert finite_coefficient(1,P)==V
    P_unit=(3,7,11,13)
    product_unit=prod(P_unit)
    B6=[]
    assert gcd(product_unit,N)==1 and X.mu(product_unit)!=0
    for r in X.divisors(product_unit):
        expected_B6=Fraction(1,r)*prod(1-Fraction(1,p*(p-1))
            for p in P_unit if r%p)
        actual_B6=finite_coefficient(r,P_unit)
        assert actual_B6==expected_B6
        B6.append(dict(r=r,actual=str(actual_B6),expected=str(expected_B6)))
    expected={3:Fraction(2,5),7:Fraction(6,41),21:Fraction(12,205)}
    ratios={}
    for r,ratio in expected.items():
        actual=finite_coefficient(r,P)/V;assert actual==ratio
        ratios[str(r)]=str(actual)
    assert finite_coefficient(9,P)==finite_coefficient(27,P)==0
    assert finite_coefficient(5,P)==0 and finite_coefficient(5,P,False)==V/4
    local_one=Fraction(1,X.phi(3))-Fraction(1,X.phi(9))
    local_two=Fraction(1,X.phi(9))-Fraction(1,X.phi(9))
    local_bad=Fraction(1,X.phi(3))-Fraction(1,X.phi(27))
    assert local_one==Fraction(1,3) and local_two==0 and local_bad==Fraction(4,9)
    assert lcm(3,3**2)==9 and 3*3**2==27
    return dict(status='PASS_FINITE_LOCAL_IDENTITY_ONLY',prime_set=list(P),V_P=str(V),
        B6_guarded_finite_product=dict(status='PASS_IDENTITY_ONLY',P=product_unit,
            prime_set=list(P_unit),unit_N=True,squarefree=True,all_divisors=B6,
            d_support='d divides P, distinct from d <= D AP head'),
        ratios=ratios,infinite_tail_evaluated=False,
        local_exponent_one=str(local_one),local_exponent_two=str(local_two),
        nonunit_r5=dict(status='ERROR_FALSIFIER',actual='0',without_mask=str(V/4)),
        nonsquarefree_r9=dict(status='ERROR_FALSIFIER',actual='0',incorrect_sf_ratio='2/5'),
        intersection=dict(status='ERROR_FALSIFIER',r=3,d=3,lcm=9,wrong_product=27,
            correct_local=str(local_one),wrong_local=str(local_bad),
            incorrect_coprime_restriction_ratio='3/5',correct_ratio='2/5'))


def square_divisors(m):
    return [d for d in X.divisors(m) if m%(d*d)==0]


def psi_E(E,modulus):
    value={}
    for n in E:
        assert X.prime(n) and gcd(n,N)==1
        if n%modulus==N%modulus:
            X.add(value,X.log_vector(n))
    return value


def AP_head(E,cut,D):
    active=[d for d in range(1,D+1) if gcd(d,N)==1 and X.mu(d)!=0
            and any((N-n)%(d*d)==0 for n in E)]
    value={};nonzero=0
    for r in range(1,cut+1):
        if gcd(r,N)!=1 or X.mu(r)==0:
            continue
        for d in active:
            psi=psi_E(E,lcm(r,d*d))
            if psi:
                nonzero+=1
                X.add(value,X.multiply(X.log_vector(r),psi),X.mu(r)*X.mu(d))
    return value,active,nonzero


def expansion_checks(points):
    E=sorted(row['n'] for row in points.values())
    cuts=(ALPHA,A);Ds=(1,2,3,16,3216,3217)
    records=[]
    for cut in cuts:
        full={}
        for n in E:
            m=N-n
            assert sum(X.mu(d) for d in square_divisors(m))==X.mu(m)**2
            X.add(full,X.multiply(X.log_vector(n),X.prefix(m,cut)),X.mu(m)**2)
        for D in Ds:
            point_head,tail={},{}
            for n in E:
                m=N-n;term=X.multiply(X.log_vector(n),X.prefix(m,cut))
                X.add(point_head,term,sum(X.mu(d) for d in square_divisors(m) if d<=D))
                X.add(tail,term,sum(X.mu(d) for d in square_divisors(m) if d>D))
            ap,active,nonzero=AP_head(E,cut,D)
            assert ap==point_head
            total=dict(ap);X.add(total,tail);assert total==full
            records.append(dict(cut=cut,D=D,active_d=active,nonzero_AP_cells=nonzero,
                physical= X.serialize(full),head=X.serialize(ap),tail=X.serialize(tail)))
    bad_point=points['square_tail'];m=bad_point['m'];n=bad_point['n']
    assert square_divisors(m)==[1,3217] and X.prefix(m,A)=={(3,):Fraction(-1)}
    head=X.multiply(X.log_vector(n),X.prefix(m,A));tail={}
    X.add(tail,head,-1);assert head and tail and not X.mu(m)**2
    n_intersect=points['square_intersection']['n']
    assert (N-n_intersect)%9==0 and (N-n_intersect)%27!=0
    correct=psi_E([n_intersect],9);wrong=psi_E([n_intersect],27)
    assert correct and not wrong
    return dict(status='PASS_IDENTITY_ONLY_WITH_RESTRICTED_E',prime_E=E,
        global_Psi_prime_not_enumerated=True,records=records,
        omitted_tail=dict(status='ERROR_FALSIFIER',m=m,n=n,D=16,
            head=X.serialize(head),required_tail=X.serialize(tail),whole={}),
        actual_intersection=dict(status='ERROR_FALSIFIER',m=N-n_intersect,n=n_intersect,
            r=3,d=3,correct_Psi=X.serialize(correct),wrong_product_Psi=X.serialize(wrong)))


def scope_and_reference_checks(points):
    rows={}
    for name in ('low_prefix','low_plus_band','negative_reference'):
        m=points[name]['m'];low=X.prefix(m,ALPHA);whole=X.prefix(m,A)
        band=dict(whole);X.add(band,low,-1)
        assert low
        actual={};X.add(actual,X.Lambda(m),-X.mu(m)**2);X.add(actual,whole,-X.mu(m)**2)
        wrong={};X.add(wrong,X.Lambda(m),-X.mu(m)**2);X.add(wrong,band,-X.mu(m)**2)
        assert actual!=wrong
        rows[name]=dict(m=m,n=points[name]['n'],low=X.serialize(low),band=X.serialize(band),
            whole=X.serialize(whole),physical_reference_preserved=X.serialize(actual),
            wrong_drop_low=X.serialize(wrong),status='ERROR_FALSIFIER')
    reference=points['negative_reference'];m=reference['m']
    assert X.mu(m)==-1 and not X.Lambda(m) and X.prime(reference['n'])
    return dict(status='DISTINCT_LOW_PREFIX_AND_BAND_VERIFIED',rows=rows,
        false_pointwise_G_nonnegative=dict(status='ERROR_FALSIFIER',m=m,n=reference['n'],
            Lambda_m={},mu_m=-1,G_over_S_N='-1',S_N_infinite_product_not_evaluated=True,
            global_no_go=False))


def properpower_guard(row):
    n,m=row['n'],row['m']
    assert not X.prime(n) and gcd(n,N)==1 and X.mu(n)==0 and X.mu(m)!=0
    theta=X.theta(n);lambda_n=X.Lambda(n)
    raw_multiplier=dict(lambda_n);X.add(raw_multiplier,X.log_vector(n),-1)
    assert not theta and lambda_n=={(3,):Fraction(1)}
    assert raw_multiplier=={(3,):Fraction(-1)}
    return dict(status='ERROR_FALSIFIER',n=n,m=m,n_factors=X.factor(n),
        m_factors=X.factor(m),prime_Psi_weight=X.serialize(theta),
        Lambda_N=X.serialize(lambda_n),incorrect_mu_n_squared_Lambda_N={},
        raw_fII_multiplier=X.serialize(raw_multiplier),full_raw_sum_not_enumerated=True,
        meaning='Proper prime power excluded from prime-only Psi, retained by Lambda_N and raw fII')


if __name__=='__main__':
    output=X.shared.output_directory();before=X.shared.verify()
    witnesses=W.generate();points=witnesses['points']
    result=dict(status='PASS_NEW_FINITE_CONTRACTS_ONLY',N=N,alpha=ALPHA,a=A,Q=Q,
        finite_coefficients=coefficient_checks(),prefix_expansion=expansion_checks(points),
        scope_and_reference=scope_and_reference_checks(points),imports=X.shared.IMPORTS,
        properpower_first_axis=properpower_guard(witnesses['properpower_axis']),
        script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
        exact_helper_sha256=sha256((ROOT/'exact11.py').read_bytes()).hexdigest(),
        shared_sha256=sha256((ROOT/'shared.py').read_bytes()).hexdigest(),
        witness_script_sha256=sha256((ROOT/'contract_witnesses.py').read_bytes()).hexdigest(),
        conservation_before=before,conservation_after=X.shared.verify(),
        global_D_N=False,asymptotic=False,payments=False,Lean_called=False,victory=False,
        properpowers_removed_from_raw=False,mu_n_squared_added=False)
    (output/'ap_prefix.json').write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
    print(json.dumps(dict(status=result['status'],prime_E=result['prefix_expansion']['prime_E'],
        finite_ratios=result['finite_coefficients']['ratios'],conservation='PRESERVED'),indent=2))
