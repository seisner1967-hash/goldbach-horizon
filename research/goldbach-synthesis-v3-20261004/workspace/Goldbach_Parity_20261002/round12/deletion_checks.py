"""NEW normalized prime-factor deletion gate; exact log-polynomial certificates."""
import sys
sys.dont_write_bytecode=True
from importlib.util import spec_from_file_location,module_from_spec
from pathlib import Path
from hashlib import sha256
from fractions import Fraction
from math import gcd
import json

ROOT=Path(__file__).resolve().parent
spec=spec_from_file_location('round12_shared_deletion',ROOT/'shared.py')
X=module_from_spec(spec);spec.loader.exec_module(X)
spec=spec_from_file_location('round12_witness_deletion',ROOT/'witness_search.py')
W=module_from_spec(spec);spec.loader.exec_module(W)


def scale(value,c):
    return {key:v*c for key,v in value.items() if v*c}


def difference(left,right):
    value=dict(left);X.vector_add(value,right,-1);return value


def local(m):
    assert 1<m<=X.N-2 and gcd(m,X.N)==1
    n=X.N-m;logm=X.log_vector(m);mu_m=X.mu(m)
    deletion={};pairs=[]
    for p,_ in X.factor(m):
        c=m//p
        X.vector_add(deletion,X.log_vector(p),X.mu(c))
        if X.mu(c)!=0 and c%p:
            pairs.append(dict(p=p,c=c,mu_c=X.mu(c),c_short=c<=X.A))
    lhs=scale(logm,mu_m)
    rhs=scale(deletion,-mu_m**2)
    assert lhs==rhs
    constant=scale(X.multiply_vectors(X.Lambda(m),logm),mu_m**2)
    S_coefficient=lhs
    transferred_constant={};transferred_S={};short_S={};long_S={}
    for pair in pairs:
        p,c,mu_c=pair['p'],pair['c'],pair['mu_c']
        if c==1:
            X.vector_add(transferred_constant,X.multiply_vectors(X.log_vector(p),logm))
        term=scale(X.log_vector(p),-mu_c)
        X.vector_add(transferred_S,term)
        X.vector_add(short_S if c<=X.A else long_S,term)
    assert constant==transferred_constant and S_coefficient==transferred_S
    recombined=dict(short_S);X.vector_add(recombined,long_S);assert recombined==transferred_S
    Lambda_n=X.Lambda(n)
    assert Lambda_n and gcd(n,X.N)==1
    weighted_constant=X.multiply_vectors(Lambda_n,constant)
    weighted_S=X.multiply_vectors(Lambda_n,S_coefficient)
    wrong_no_guard=scale(deletion,-1)
    wrong_no_denominator=X.multiply_vectors(logm,transferred_S)
    return dict(m=m,n=n,m_factors=X.factor(m),n_factors=X.factor(n),mu_m=mu_m,
        Lambda_N=X.serialize(Lambda_n),theta_N=X.serialize(X.theta(n)),
        log_m=X.serialize(logm),sum_mu_c_log_p=X.serialize(deletion),pairs=pairs,
        normalized_identity_after_log_m=dict(lhs=X.serialize(lhs),rhs=X.serialize(rhs)),
        guarded_G_transfer_after_log_m=dict(constant=X.serialize(constant),S=X.serialize(S_coefficient),
            transferred_constant=X.serialize(transferred_constant),transferred_S=X.serialize(transferred_S)),
        raw_weighted_after_log_m=dict(constant=X.serialize(weighted_constant),S=X.serialize(weighted_S)),
        complementary_cofactor_sectors=dict(short_S=X.serialize(short_S),long_S=X.serialize(long_S),
            cut=X.A,full_S=X.serialize(transferred_S)),
        _S=S_coefficient,_wrong_no_guard=wrong_no_guard,_wrong_no_denominator=wrong_no_denominator,
        _weighted_S=weighted_S,_long_S=long_S,_short_S=short_S)


def matching_model_root_checks():
    primes=(2,3,5,7,11,13,17,19,23,29)
    cores=(1,33,51,187)
    records=[]
    for c in cores:
        assert gcd(c,X.N)==1
        ratio=Fraction(1)
        for ell in primes:
            roots=[x for x in range(ell) if x*(X.N-c*x)%ell==0]
            expected=1 if (c*X.N)%ell==0 else 2
            assert len(roots)==expected
            baseline=1 if X.N%ell==0 else 2
            local=Fraction(ell*(ell-len(roots)),(ell-1)**2)
            local_base=Fraction(ell*(ell-baseline),(ell-1)**2)
            assert local_base>0
            ratio*=local/local_base
            records.append(dict(c=c,prime=ell,roots=roots,rho=expected))
        expected_ratio=Fraction(1)
        for ell,_ in X.factor(c):
            assert ell in primes and ell>2
            expected_ratio*=Fraction(ell-1,ell-2)
        assert ratio==expected_ratio
    bad_c,bad_ell=5,5
    bad_roots=[x for x in range(bad_ell) if x*(X.N-bad_c*x)%bad_ell==0]
    assert len(bad_roots)==5
    return dict(status='PASS_NEW_FINITE_MATCHING_ROOT_IDENTITY_ONLY',cores=list(cores),
        primes=list(primes),records=records,finite_singularity_ratios_verified=True,
        formal_density_not_assumed=True,infinite_product_not_evaluated=True,
        false_unit_guard_omitted=dict(status='ERROR_FALSIFIER',c=bad_c,prime=bad_ell,
            actual_roots=bad_roots,actual_rho=5,incorrect_rho=1))


def selected_polynomial_probe():
    selected=(29,561)
    coefficients={1:{},2:{},3:{}}
    for m in selected:
        assert gcd(m,X.N)==1 and X.prime(X.N-m) and X.mu(m)!=0
        omega=sum(e for _,e in X.factor(m))
        X.vector_add(coefficients[omega],X.Lambda(X.N-m))
    gap=X.multiply_vectors(coefficients[2],coefficients[2])
    X.vector_add(gap,X.multiply_vectors(coefficients[1],coefficients[3]),-1)
    sign=X.sign_certificate(gap);assert sign['sign']=='NEGATIVE'
    return dict(status='ERROR_FALSIFIER',selected_m=list(selected),
        coefficients={str(k):X.serialize(v) for k,v in coefficients.items()},
        a2_squared_minus_a1_a3=X.serialize(gap),sign=sign,
        assertion_rejected='log-concavity on EVERY selected physical set',
        global_polynomial_property_tested=False,global_no_go=False,
        properpower_first_axis_kept_in_other_gate=True)


if __name__=='__main__':
    output=X.output_directory();before=X.verify();witnesses=W.generate()['witnesses']
    records={name:local(row['m']) for name,row in witnesses.items()}
    non_sf=records['new_nonsquarefree_prime_axis']
    no_guard_error=difference(non_sf['_wrong_no_guard'],non_sf['_S'])
    assert non_sf['mu_m']==0 and not non_sf['pairs'] and no_guard_error
    no_guard_sign=X.sign_certificate(no_guard_error);assert no_guard_sign['sign']=='NEGATIVE'
    triprime=records['new_negative_reference']
    omitted_denominator=difference(triprime['_wrong_no_denominator'],triprime['_S'])
    no_denominator_sign=X.sign_certificate(omitted_denominator)
    assert no_denominator_sign['sign']=='NEGATIVE'
    unweighted=-sum(pair['mu_c'] for pair in triprime['pairs'])
    assert triprime['mu_m']==-1 and unweighted==-3
    proper=records['new_properpower_axis']
    assert not proper['theta_N'] and proper['Lambda_N'] and proper['_weighted_S']
    assert proper['_long_S'] and not proper['_short_S']
    dropped_long_sign=X.sign_certificate(difference(proper['_short_S'],proper['_S']))
    assert dropped_long_sign['sign']=='NEGATIVE'
    endpoint_n=X.N-1;endpoint=dict(m=1,n=endpoint_n,mu_m=1,delta_one=1,
        prime_factor_sum={},Lambda_N=X.serialize(X.Lambda(endpoint_n)),
        model_endpoint='S(N)*Lambda_N(N-1) retained; happens to be zero at this N')
    assert not endpoint['Lambda_N']
    for value in records.values():
        for key in tuple(value):
            if key.startswith('_'):
                del value[key]
    result=dict(status='PASS_NEW_NORMALIZED_DELETION_IDENTITY_ONLY',N=X.N,alpha=X.ALPHA,a=X.A,Q=X.Q,
        matching_model=matching_model_root_checks(),selected_polynomial_probe=selected_polynomial_probe(),
        points=records,endpoint=endpoint,same_selected_m_in_both_finite_transfer_sides=True,
        false_guardless_deletion=dict(status='ERROR_FALSIFIER',m=non_sf['m'],n=non_sf['n'],
            residual=X.serialize(no_guard_error),sign=no_guard_sign),
        false_denominator_omitted=dict(status='ERROR_FALSIFIER',m=triprime['m'],
            residual_after_log_m=X.serialize(omitted_denominator),sign=no_denominator_sign),
        false_unweighted_prime_deletion=dict(status='ERROR_FALSIFIER',m=triprime['m'],
            correct_mu=-1,wrong_mu=unweighted,overcount_factor=3),
        false_short_cofactor_completion=dict(status='ERROR_FALSIFIER',m=proper['m'],
            residual=X.serialize(difference({},X.log_vector(proper['m']))),sign=dropped_long_sign),
        properpower_first_axis_retained=True,mu_n_squared_added=False,S_N_not_evaluated=True,
        denominator_log_m_crossmultiplied_exactly=True,imports=X.IMPORTS,
        script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
        shared_sha256=sha256((ROOT/'shared.py').read_bytes()).hexdigest(),
        witness_script_sha256=sha256((ROOT/'witness_search.py').read_bytes()).hexdigest(),
        conservation_before=before,conservation_after=X.verify(),
        global_D_N=False,asymptotic=False,payments=False,Lean_called=False,victory=False)
    (output/'deletion.json').write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
    print(json.dumps(dict(status=result['status'],points=len(records),
        nonsquarefree_witness=non_sf['m'],new_prime_pair=records['new_prime_pair']['m'],
        conservation='PRESERVED'),indent=2))
