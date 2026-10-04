"""Only new round10 contracts: matched raised-face coefficients and singular ratio.

Full matched finite kernels, verified prime first axes and rational sign bounds.
No analytical payment or global D_N bound is tested at N=10^8.
"""
import sys
sys.dont_write_bytecode = True
if hasattr(sys,'set_int_max_str_digits'):
    sys.set_int_max_str_digits(0)
from importlib.util import module_from_spec,spec_from_file_location
from pathlib import Path
from hashlib import sha256
from functools import lru_cache
from fractions import Fraction
from math import gcd,prod
import json

ROOT=Path(__file__).resolve().parent
spec=spec_from_file_location('round10_shared_cofactors',ROOT/'shared.py')
shared=module_from_spec(spec); spec.loader.exec_module(shared)
spec=spec_from_file_location('round10_witness_contracts',ROOT/'witness_search.py')
witness=module_from_spec(spec); spec.loader.exec_module(witness)
N,A,Q=shared.N,3163,999999
factor,divisors,mu=shared.factor,shared.divisors,shared.mu
add,log_vector,serialize=shared.vector_add,shared.log_vector,shared.serialize


def Lambda(n):
    fs=factor(n)
    return log_vector(fs[0][0]) if len(fs)==1 else {}


@lru_cache(None)
def phi(k):
    return prod(p**(e-1)*(p-1) for p,e in factor(k))


def logr(m,k):
    result=log_vector(m)
    add(result,log_vector(k),-1)
    return result


def kernels(m,min_k=1):
    n=N-m
    D,W={},{}
    prefix=min(Q,(m-1)//A)
    for k in divisors(m):
        if min_k<=k<=Q and A*k<m:
            add(D,logr(m,k),-mu(k))
    for k in range(min_k,prefix+1):
        if gcd(k,n*N)==1:
            add(W,logr(m,k),Fraction(-mu(k),phi(k)))
    return D,W,prefix


def T(m):
    value={}
    for r in divisors(m):
        if r>A:
            assert m//r<=Q
            add(value,log_vector(r),mu(r))
    return value


def linear_certificate(value):
    """Outward rational dyadic log bounds avoid products of unrelated denominators."""
    if not value:
        return dict(sign='ZERO',lower='0',upper='0',terms=0,bits=0)
    assert all(len(key)==1 for key in value)
    for terms,bits in ((6,96),(12,128),(24,192),(48,256)):
        scale=1<<bits
        lower=upper=Fraction(0)
        for (p,),coefficient in value.items():
            lo,hi=shared.multifibre.log_prime_bounds(p,terms)
            gridlo=(lo.numerator*scale)//lo.denominator
            gridhi=(hi.numerator*scale+hi.denominator-1)//hi.denominator
            assert Fraction(gridlo,scale)<=lo<=hi<=Fraction(gridhi,scale)
            lower+=coefficient*(gridlo if coefficient>0 else gridhi)
            upper+=coefficient*(gridhi if coefficient>0 else gridlo)
        lower/=scale;upper/=scale
        assert lower<=upper
        if lower>0 or upper<0:
            return dict(sign='POSITIVE' if lower>0 else 'NEGATIVE',
                        lower=str(lower),upper=str(upper),terms=terms,bits=bits)
    return dict(sign='UNRESOLVED',lower=str(lower),upper=str(upper),terms=terms,bits=bits)


def matched_checks(rows):
    results={}
    for name,row in rows.items():
        if 'm' not in row:
            continue
        m,n=row['m'],row['n']
        assert witness.prime(n) and gcd(n,N)==1 and m<=N-2
        D,W,prefix=kernels(m)
        L={key:-mu(m)*c for key,c in D.items() if mu(m)*c}
        dual={}
        add(dual,Lambda(m),-1)
        for r in divisors(m):
            if r<=A:
                add(dual,log_vector(r),-mu(r))
        dual={key:mu(m)**2*c for key,c in dual.items() if mu(m)**2*c}
        assert L==dual
        raw_T=T(m)
        assert L=={key:mu(m)**2*c for key,c in raw_T.items() if mu(m)**2*c}
        C=dict(L);add(C,W,mu(m))
        D2,W2,_=kernels(m,2)
        C2={}
        add(C2,D2,-mu(m));add(C2,W2,mu(m))
        assert C==C2
        Wpositive={key:-c for key,c in W.items()}
        positive_formula={key:mu(m)**2*c for key,c in raw_T.items() if mu(m)**2*c}
        add(positive_formula,Wpositive,-mu(m))
        assert C==positive_formula
        if name=='rough_prime_bulk':
            expected={};add(expected,log_vector(m),-1);add(expected,W,-1)
            assert C==expected and L=={key:-c for key,c in log_vector(m).items()}
        if name=='rough_semiprime_bulk':
            assert not L and C==W and not raw_T
        if name=='small3_two_large_bulk':
            assert L==log_vector(3)
            expected=log_vector(3);add(expected,W,-1);assert C==expected
        if name=='nonsquarefree_bulk':
            assert mu(m)==0 and not L and not C and raw_T==log_vector(3)
        sector=None;small_core=None;short_fibre={}
        if mu(m)!=0:
            large=[p for p,e in factor(m) if p>A]
            sector=len(large);assert sector<=2
            small_core=prod(p for p,e in factor(m) if p<=A)
            for d in divisors(small_core):
                if d<=A:
                    add(short_fibre,log_vector(d),mu(d))
            if sector==2:
                assert small_core<=(N-2)//((A+1)**2)<A
                assert L==Lambda(small_core)
                expected=dict(Lambda(small_core));add(expected,W,mu(small_core))
                assert C==expected
            if name=='one_large_incomplete_small_fibre':
                assert sector==1 and small_core==3183>A
                assert short_fibre!= {key:-v for key,v in Lambda(small_core).items()}
                assert L==log_vector(3183)
            if name=='all_small_bulk':
                assert sector==0 and m>=1000000 and n>Q
        results[name]=dict(**row,prefix=prefix,
            D_kernel=serialize(D),W_kernel=serialize(W),W_positive=serialize(Wpositive),
            raw_T=serialize(raw_T),L=serialize(L),C=serialize(C),
            W_kernel_sign=linear_certificate(W),C_sign=linear_certificate(C),
            large_prime_sector=sector,small_core=small_core,U_small=serialize(short_fibre),
            full_matched_model=True,k1_joint_cancellation=True)
    return results


def small_cofactor_checks(rows,matched):
    keys=('rough_prime_bulk','one_large_small_prime','one_large_small_squarefree_plus',
          'one_large_small_squarefree_minus','one_large_small_nonsquarefree')
    results={}
    for name in keys:
        row=rows[name];p=row['parameters']['p'];c=row['parameters'].get('c',1)
        assert 1<=c<=min(A,Q)<p and gcd(p,c)==1 and witness.prime(p)
        m=row['m'];assert m==p*c
        D,W,_=kernels(m)
        raw_T=T(m)
        expected_T=Lambda(c) if c>1 else {key:-v for key,v in log_vector(p).items()}
        assert raw_T==expected_T
        Wpositive={key:-v for key,v in W.items()}
        unified=dict(Wpositive);add(unified,Lambda(c),-1)
        if c==1:
            add(unified,log_vector(p),-1)
        unified={key:mu(c)*v for key,v in unified.items() if mu(c)*v}
        actual={};add(actual,D,-mu(m));add(actual,W,mu(m))
        assert unified==actual
        results[name]=dict(p=p,c=c,mu_c=mu(c),raw_T=serialize(raw_T),
                           unified_coefficient=serialize(unified))
    large=rows['rough_semiprime_bulk'];c=large['parameters']['p']
    assert c>A and T(large['m'])!=Lambda(c)
    small=rows['small_p_extrapolation'];csmall=small['parameters']['c']
    assert small['parameters']['p']<=A and T(small['m'])!=Lambda(csmall)
    nonsf=rows['one_large_small_nonsquarefree'];assert nonsf['parameters']['c']==9
    assert T(nonsf['m'])==log_vector(3) and not matched['one_large_small_nonsquarefree']['C']
    return dict(status='PASS_IDENTITY_ONLY',cases=results,
        false_c_large=dict(status='ERROR_FALSIFIER',m=large['m'],c=c,
            actual_T=serialize(T(large['m'])),incorrect_Lambda_c=serialize(Lambda(c))),
        false_p_small=dict(status='ERROR_FALSIFIER',m=small['m'],p=3,c=csmall,
            actual_T=serialize(T(small['m'])),incorrect_Lambda_c=serialize(Lambda(csmall))),
        false_drop_mu_squared=dict(status='ERROR_FALSIFIER',m=nonsf['m'],c=9,
            raw_T=serialize(T(nonsf['m'])),actual_bracket={},
            reason='T identity can hold for nonsquarefree c, while whole bracket vanishes'),
        false_complete_small_fibre=dict(status='ERROR_FALSIFIER',
            m=rows['one_large_incomplete_small_fibre']['m'],c=3183,
            actual_U=matched['one_large_incomplete_small_fibre']['U_small'],
            incorrectly_completed_U=serialize({key:-v for key,v in Lambda(3183).items()})))


def singular_multiplier_from_primes(primes):
    return prod(Fraction(p-1,p-2) for p in sorted(set(primes)) if p>2)


def singular_checks(rows):
    base_primes=[p for p,e in factor(N)]
    SN=singular_multiplier_from_primes(base_primes)
    ns=sorted({3}|{row['n'] for row in rows.values() if 'n' in row})
    ratios={};correction={};difference={}
    for n in ns:
        assert witness.prime(n) and gcd(n,N)==1 and n>2
        actual=singular_multiplier_from_primes(base_primes+[n])/SN
        expected=1+Fraction(1,n-2)
        assert actual==expected
        ratios[str(n)]=str(actual)
        add(correction,log_vector(n),Fraction(1,n-2))
        add(difference,log_vector(n),actual-1)
    assert correction==difference and correction[(3,)]==1
    actual_nonunit=singular_multiplier_from_primes(base_primes+[5])/SN
    assert actual_nonunit==1 and actual_nonunit!=1+Fraction(1,5-2)
    actual_power=singular_multiplier_from_primes(base_primes+[p for p,e in factor(9)])/SN
    assert actual_power==2 and actual_power!=1+Fraction(1,9-2)
    canonical=rows['one_large_small_prime'];n=canonical['n'];m=canonical['m']
    representations=[(3167,7),(7,3167)]
    assert all(p*c==m for p,c in representations)
    valid=[(p,c) for p,c in representations if 1<=c<=A<p]
    assert valid==[(3167,7)]
    correct={};duplicate={}
    add(correct,log_vector(n),Fraction(1,n-2))
    for p,c in representations:
        add(duplicate,log_vector(n),Fraction(1,n-2))
    assert duplicate!=correct
    return dict(status='PASS_IDENTITY_ONLY',normalization='S(N) factored out; no infinite C2 evaluated',
        SN_finite_multiplier=str(SN),prime_ratios=ratios,
        normalized_distinct_prime_correction=serialize(correction),
        n_small_3_retained=True,analytic_harmonic_bound_tested=False,
        nonunit_extension=dict(status='ERROR_FALSIFIER',n=5,actual=str(actual_nonunit),
                               incorrect=str(1+Fraction(1,3))),
        properpower_extension=dict(status='ERROR_FALSIFIER',n=9,actual=str(actual_power),
                                  incorrect=str(1+Fraction(1,7))),
        multiplicity=dict(status='ERROR_FALSIFIER',n=n,m=m,representations=representations,
            canonical=valid,distinct_correction=serialize(correct),
            incorrectly_duplicated_correction=serialize(duplicate)))


if __name__=='__main__':
    output=shared.output_directory();before=shared.verify()
    assert (A-1)**16<N**7<=A**16 and A**3>N and Q*(A+1)>N-1
    rows=witness.search();matched=matched_checks(rows)
    assert matched['rough_prime_bulk']['C_sign']['sign']=='NEGATIVE'
    assert matched['rough_semiprime_bulk']['C_sign']['sign']=='NEGATIVE'
    assert matched['small3_two_large_bulk']['C_sign']['sign']=='POSITIVE'
    assert matched['one_large_small_nonsquarefree']['C_sign']['sign']=='ZERO'
    assert matched['nonsquarefree_bulk']['C_sign']['sign']=='ZERO'
    phase_m=rows['small3_two_large_bulk']['m']
    assert phase_m%3==0 and A*3<phase_m and (N-phase_m)%3==N%3==1
    result=dict(status='PASS_FINITE_IDENTITIES_ONLY',N=N,a9=A,Q=Q,
        dual_and_matched=dict(status='PASS_IDENTITY_ONLY',cases=matched),
        small_cofactor=small_cofactor_checks(rows,matched),singular=singular_checks(rows),
        structural_witness_exclusion=rows['excluded_square_bulk_search'],
        false_all_J2_favorable=dict(status='ERROR_FALSIFIER',
            m=rows['small3_two_large_bulk']['m'],c=3,
            exact_C=matched['small3_two_large_bulk']['C'],
            sign_certificate=matched['small3_two_large_bulk']['C_sign']),
        native_physical_phase=dict(q=3,k=3,m=phase_m,r=phase_m//3,
            n_residue=(N-phase_m)%3,N_residue=N%3,character_ratio=1),
        observed_signs={name:dict(W_kernel=row['W_kernel_sign']['sign'],C=row['C_sign']['sign'])
                        for name,row in matched.items()},
        asymptotic_signs_validated=False,analytical_payments_tested=False,
        properpowers_removed_from_raw=False,global_D_N_estimated=False,victory=False,
        Lean_called=False,imports=shared.IMPORTS,
        script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
        witness_script_sha256=sha256((ROOT/'witness_search.py').read_bytes()).hexdigest(),
        conservation_before=before,conservation_after=shared.verify())
    path=output/'paired_cofactors.json'
    path.write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
    print(json.dumps(dict(status=result['status'],observed_signs=result['observed_signs'],
                         output=str(path),conservation=result['conservation_after']['status']),indent=2))
