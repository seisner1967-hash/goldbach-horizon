"""Exact determinant/HNF filter retaining actual Mobius values and HH masks."""
import sys
sys.dont_write_bytecode = True
from hashlib import sha256
from math import gcd
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parent
BASE = ROOT.parent
sys.path.insert(0,str(BASE/'numerical'))
from parity_checks import N, factor, mu, direct_HU, rough
from conservation import initialize,verify


def det(M):
    return M[0][0]*M[1][1]-M[0][1]*M[1][0]


def multiply(A,B):
    return tuple(tuple(sum(A[i][k]*B[k][j] for k in range(2)) for j in range(2))
                 for i in range(2))


def masks(u,v,s,t):
    b,k,w,z,alpha,Q,y = 13,1,1,1,100,999999,2
    a,r = u*v*w,s*t*z
    n,m = a*b,r*k
    assert n+m == N
    return dict(positive=all(x > 0 for x in (b,k,w,z,u,v,s,t)),
                unit_N=gcd(n,N)==1,
                squarefree_first=mu(n)!=0,squarefree_complement=mu(m)!=0,
                first_axis_W2_rough=rough(n,2),core_a_b_le_m=a<=m and b<=m,
                four_large_factors=all(x>y for x in (u,v,s,t)),
                complementary_r_gt_alpha=r>alpha,
                literal_k_cap_and_strict_face=k<=Q and alpha*k<m)


def tuple_data(ell):
    u,t = 3,12577
    v,s = 7+ell*t,7951-39*ell
    mask = masks(u,v,s,t)
    n,m,a,r = 39*v,s*t,3*v,s*t
    sign = mu(u)*mu(v)*mu(s)*mu(t)
    weight = {}
    for p,e in factor(r):
        weight[f'{min(13,p)},{max(13,p)}'] = sign*e
    return dict(ell=ell,shear_j=-13*ell,b=13,u=u,v=v,w=1,k=1,s=s,t=t,z=1,
                n=n,m=m,a=a,r=r,CRT_modulus_a_times_r=a*r,
                factor_n=factor(n),factor_m=factor(m),factor_v=factor(v),factor_s=factor(s),
                masks=mask,accepted=all(mask.values()),
                actual_Mobius_u_v_s_t=[mu(u),mu(v),mu(s),mu(t)],
                actual_HH_expanded_sign=sign,
                Mobius_n_times_m=mu(n)*mu(m),
                complete_H2_a=direct_HU(a,2)[0],complete_H2_r=direct_HU(r,2)[0],
                signed_log13_logr_coefficients=weight)


def run():
    initialize()
    u,s,B,D = 3,7951,91,12577
    M = ((u,s),(-D,B))
    assert det(M) == N and gcd(B,N)==gcd(s,N)==gcd(B,D)==1
    lam = s*pow(B,-1,N) % N
    assert lam == 73626461 and gcd(lam,N)==1
    numerator_A,numerator_C = u+lam*D,s-lam*B
    assert numerator_A % N == numerator_C % N == 0
    A,C = numerator_A//N,numerator_C//N
    G,H = ((A,C),(-D,B)),((N,lam),(0,1))
    assert G == ((9260,-67),(-12577,91)) and det(G)==1
    assert multiply(H,G) == M
    assert A*B+C*D==1
    records = []
    counts = {'positive_integer_shears':0,'accepted_original_masks':0,'positive_expanded_sign':0,'negative_expanded_sign':0}
    for ell in range(204):
        row = tuple_data(ell)
        j = row['shear_j']
        T = ((1,j),(0,1))
        transformed = multiply(M,T)
        assert det(T)==1 and det(transformed)==N
        assert transformed == ((3,row['s']),(-D,13*row['v']))
        assert multiply(H,multiply(G,T)) == transformed
        counts['positive_integer_shears'] += 1
        if row['accepted']:
            new_B = transformed[1][1]
            assert gcd(new_B,N)==1
            assert row['s']*pow(new_B,-1,N)%N == lam
            counts['accepted_original_masks'] += 1
            counts['positive_expanded_sign' if row['actual_HH_expanded_sign']>0 else 'negative_expanded_sign'] += 1
        if ell in (0,2,4,6) or row['accepted'] and len(records)<12:
            records.append(row)
    base,switched = tuple_data(0),tuple_data(6)
    assert base['accepted'] and switched['accepted']
    assert switched['factor_v'] == ((163,1),(463,1))
    assert switched['factor_s'] == ((7717,1),)
    assert (base['actual_HH_expanded_sign'],switched['actual_HH_expanded_sign']) == (1,-1)
    assert (base['complete_H2_a']*base['complete_H2_r'],
            switched['complete_H2_a']*switched['complete_H2_r']) == (4,0)
    assert base['signed_log13_logr_coefficients'] != switched['signed_log13_logr_coefficients']
    invalid_sf,invalid_unit = tuple_data(2),tuple_data(4)
    assert not invalid_sf['masks']['squarefree_first']
    assert not invalid_unit['masks']['unit_N']
    result = dict(status='PASS',N=N,M=M,H=H,G=G,lambda_modN=lam,counts=counts,
                  exact_quotients=dict(A=A,C=C,divisibility=True,AB_plus_CD=1),
                  shear_domain='ell=0..203, j=-13*ell; every shear retains the exact integer HH factorization and positive factors',
                  samples=records,
                  automatic_signed_descent_counterexample=dict(base=base,switched=switched,
                                                              verdict='FALSE: actual expanded Mobius sign and signed log weight change in the same HNF class'),
                  selector_counterexamples=dict(shear_minus26=invalid_sf,shear_minus52=invalid_unit),
                  limitations='Exact class constancy of the arithmetic weight is falsified; no claim against future weighted cancellation over a class and no D_N bound',
                  previous_artifacts=verify(),
                  script_sha256=sha256(Path(__file__).read_bytes()).hexdigest())
    (ROOT/'hecke.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(status=result['status'],N=N,lambda_modN=lam,G=G,counts=counts,
                         base_expanded_sign=base['actual_HH_expanded_sign'],
                         switched_expanded_sign=switched['actual_HH_expanded_sign'],
                         previous_artifacts=result['previous_artifacts'],script_sha256=result['script_sha256']),indent=2))


if __name__ == '__main__':
    run()
