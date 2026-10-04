"""New c/3c pairing contract, actual prime incidence and retained geometric defect."""
import sys
sys.dont_write_bytecode=True
from importlib.util import spec_from_file_location,module_from_spec
from pathlib import Path
from hashlib import sha256
from math import gcd
import json

ROOT=Path(__file__).resolve().parent
spec=spec_from_file_location('round11_exact_pairs',ROOT/'exact11.py')
X=module_from_spec(spec);spec.loader.exec_module(X)
spec=spec_from_file_location('round11_witness_pairs',ROOT/'contract_witnesses.py')
W=module_from_spec(spec);spec.loader.exec_module(W)
N,A,Q=X.N,X.A,X.Q


def branch(c,p,q):
    m=c*p*q;n=N-m
    admitted=1<=m<=N-Q-1
    assert X.mu(c)!=0 and gcd(c*p*q,N)==1 and X.prime(p) and X.prime(q) and A<p<q
    if not admitted:
        return dict(m=m,n=n,face=False,theta={},C={},W={},R=0,pair_term={})
    assert c<=(N-2)//((A+1)**2)<A
    D,kernel,R=X.kernels(m)
    C={};X.add(C,D,-X.mu(m));X.add(C,kernel,X.mu(m))
    expected=dict(X.Lambda(c));X.add(expected,kernel,X.mu(c));assert C==expected
    D2,W2,_=X.kernels(m,2);removed={};X.add(removed,D2,-X.mu(m));X.add(removed,W2,X.mu(m))
    assert C==removed
    theta=X.theta(n)
    return dict(m=m,n=n,face=True,n_factors=X.factor(n),theta=theta,C=C,W=kernel,R=R,
        mu_m=X.mu(m),pair_term=X.multiply(theta,C))


def check_pair(c,p,q):
    assert c%3 and gcd(c,p*q)==1
    first,second=branch(c,p,q),branch(3*c,p,q)
    actual=dict(first['pair_term']);X.add(actual,second['pair_term'])
    entropy=X.multiply(first['theta'],X.Lambda(c))
    X.add(entropy,X.multiply(second['theta'],X.Lambda(3*c)))
    signed=X.multiply(first['theta'],first['W'])
    X.add(signed,X.multiply(second['theta'],second['W']),-1)
    signed={key:X.mu(c)*v for key,v in signed.items() if X.mu(c)*v}
    formula=dict(entropy);X.add(formula,signed);assert actual==formula
    principal_normalized={};X.add(principal_normalized,second['theta'],X.mu(c))
    X.add(principal_normalized,first['theta'],-X.mu(c))
    # delta_i = W_i + S, represented with S as an unevaluated formal scalar.
    delta_S={};X.add(delta_S,first['theta'],X.mu(c));X.add(delta_S,second['theta'],-X.mu(c))
    total_S=dict(delta_S);X.add(total_S,principal_normalized);assert not total_S
    def record(b):
        return {key:(X.serialize(value) if isinstance(value,dict) else value) for key,value in b.items()}
    return dict(c=c,p=p,q=q,first=record(first),second=record(second),
        whole_pair=X.serialize(actual),entropy=X.serialize(entropy),signed_kernel=X.serialize(signed),
        principal_over_S_N=X.serialize(principal_normalized),
        formal_S_delta_coefficient=X.serialize(delta_S),formal_S_cancelled=True,
        pair_sign=X.sign_certificate(actual),entropy_sign=X.sign_certificate(entropy),
        principal_sign=X.sign_certificate(principal_normalized),S_N_not_evaluated=True)


def partition_checks(p,q):
    t=p*q;cap=(N-Q-1)//t
    domain=[c for c in range(1,cap+1) if X.mu(c)!=0 and gcd(c,N*t)==1]
    bases=[d for d in domain if d%3 and 3*d<=cap]
    faces=[d for d in domain if d%3 and 3*d>cap]
    tripled=[3*d for d in bases]
    assert set(domain)==set(bases)|set(tripled)|set(faces)
    assert not set(bases)&set(tripled) and not set(bases)&set(faces)
    assert not set(tripled)&set(faces) and len(domain)==len(bases)+len(tripled)+len(faces)
    branches={c:branch(c,p,q) for c in domain}
    whole,H2,principal_coefficient={},{},{}
    for c,b in branches.items():
        assert b['face'] and b['n']>Q
        X.add(whole,b['pair_term'])
        X.add(H2,X.multiply(b['theta'],X.Lambda(c)))
        X.add(principal_coefficient,b['theta'],-X.mu(c))
    partitioned,common,single,face_coefficient={},{},{},{}
    positive_common_bases=[]
    for d in bases:
        b,b3=branches[d],branches[3*d]
        X.add(partitioned,b['pair_term']);X.add(partitioned,b3['pair_term'])
        i,j=bool(b['theta']),bool(b3['theta'])
        if i and j:
            quotient=X.log_vector(b3['n']);X.add(quotient,X.log_vector(b['n']),-1)
            X.add(common,quotient,X.mu(d))
            if X.mu(d)<0:
                positive_common_bases.append(d)
        elif j:
            X.add(single,b3['theta'],X.mu(d))
        elif i:
            X.add(single,b['theta'],-X.mu(d))
    face_terms={}
    for d in faces:
        X.add(partitioned,branches[d]['pair_term'])
        X.add(face_terms,branches[d]['pair_term'])
        X.add(face_coefficient,branches[d]['theta'],-X.mu(d))
    assert partitioned==whole
    delta_total=dict(common);X.add(delta_total,single);X.add(delta_total,face_coefficient)
    assert delta_total==principal_coefficient
    assert cap==9 and domain==[1,3,7] and bases==[1] and faces==[7]
    assert not positive_common_bases
    sign=X.sign_certificate(whole);assert sign['sign']=='POSITIVE'
    return dict(status='PASS_FULL_FINITE_PARTITION_AND_P2_ONLY',p=p,q=q,t=t,C_t=cap,
        X_t=domain,D_t=bases,three_D_t=tripled,F_t=faces,disjoint_partition=True,
        axis_incidence={str(c):dict(n=b['n'],prime=bool(b['theta']),mu_m=b['mu_m'],
            theta=X.serialize(b['theta']),n_factors=b['n_factors']) for c,b in branches.items()},
        whole_actual_brackets=X.serialize(whole),partition_actual_brackets=X.serialize(partitioned),
        retained_face_actual_brackets=X.serialize(face_terms),whole_actual_sign=sign,
        H2=X.serialize(H2),principal_S_coefficient=X.serialize(principal_coefficient),
        Delta_common=X.serialize(common),Delta_single=X.serialize(single),
        Delta_face=X.serialize(face_coefficient),P2_formal_scalar_identity=True,
        positive_common_mu_negative_bases=positive_common_bases,
        positive_common_asymptotic_budget_numerically_validated=False,
        S_N_not_evaluated=True,actual_kernels_not_replaced=True)


if __name__=='__main__':
    output=X.shared.output_directory();before=X.shared.verify();witnesses=W.generate()['pairs']
    pairs={name:check_pair(row['c'],row['p'],row['q']) for name,row in witnesses.items()}
    both=pairs['both_prime'];one=pairs['one_prime_axis'];face=pairs['c7_missing_face']
    assert both['first']['theta'] and both['second']['theta']
    assert both['principal_sign']['sign']=='NEGATIVE'
    assert both['pair_sign']['sign']=='POSITIVE' and both['entropy_sign']['sign']=='POSITIVE'
    assert not one['first']['theta'] and one['second']['theta']
    assert one['principal_sign']['sign']=='POSITIVE' and one['pair_sign']['sign']=='POSITIVE'
    n,n3=one['first']['n'],one['second']['n']
    incorrect=X.log_vector(n3);X.add(incorrect,X.log_vector(n),-1)
    incorrect_sign=X.sign_certificate(incorrect);assert incorrect_sign['sign']=='NEGATIVE'
    assert face['first']['face'] and not face['second']['face'] and face['first']['theta']
    assert not face['second']['pair_term'] and face['pair_sign']['sign']=='POSITIVE'
    partitions={name:partition_checks(row['p'],row['q'])
        for name,row in witnesses.items() if name in ('both_prime','one_prime_axis')}
    result=dict(status='PASS_NEW_PAIR_IDENTITY_ONLY',N=N,a=A,Q=Q,pairs=pairs,
        full_partitions=partitions,
        false_pair_favorable=dict(status='ERROR_FALSIFIER',witness='both_prime',
            negative_model_over_S=both['principal_sign'],positive_whole_pair=both['pair_sign']),
        incidence_defect=dict(status='ERROR_FALSIFIER',witness='one_prime_axis',
            actual_principal_sign=one['principal_sign'],incorrect_log_ratio=X.serialize(incorrect),
            incorrect_sign=incorrect_sign),
        missing_face=dict(status='ERROR_FALSIFIER',c=7,tripled_c=21,
            m=face['first']['m'],tripled_m=face['second']['m'],
            tripled_n=face['second']['n'],unpaired_term=face['whole_pair']),
        imports=X.shared.IMPORTS,script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
        exact_helper_sha256=sha256((ROOT/'exact11.py').read_bytes()).hexdigest(),
        shared_sha256=sha256((ROOT/'shared.py').read_bytes()).hexdigest(),
        witness_script_sha256=sha256((ROOT/'contract_witnesses.py').read_bytes()).hexdigest(),
        conservation_before=before,conservation_after=X.shared.verify(),
        global_D_N=False,asymptotic=False,payments=False,Lean_called=False,victory=False,
        properpowers_removed_from_raw=False,mu_n_squared_added=False,
        principal_substituted_for_actual_kernels=False,global_no_go=False)
    (output/'paired_axes.json').write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
    print(json.dumps(dict(status=result['status'],signs={name:dict(pair=row['pair_sign']['sign'],
        principal=row['principal_sign']['sign']) for name,row in pairs.items()},conservation='PRESERVED'),indent=2))
