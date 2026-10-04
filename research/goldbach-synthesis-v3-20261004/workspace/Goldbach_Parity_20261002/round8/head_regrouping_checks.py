"""Exact physical head reindexing by q=b²*c on selected m at N=1e8.

The full AP prefix is not numerically enumerated. Each selected m keeps
its own Lambda_N(N-m) and every cut tail is retained as an exact vector.
"""
import sys
sys.dont_write_bytecode=True
from fractions import Fraction
from hashlib import sha256
from math import gcd,isqrt
from pathlib import Path
import json
from conservation import initialize,verify
from shared import ROOT,N,factor,divisors,mu,vector_add,multiply_vectors,log_vector,serialize
from shared import output_directory
from compensation_checks import Lambda_N

ALPHA=100
H=1000
B_PHYSICAL=1
Q=999999


def fiber_sum(b,c,complete=False):
    out={}
    for g in divisors(b):
        if complete or ALPHA<c*g<=H:vector_add(out,log_vector(c*g),mu(g))
    return out


def weight(b,c):
    assert mu(b)**2==mu(c)**2==1 and gcd(b,c)==gcd(b*c,N)==1
    return {key:mu(b)*mu(c)*v for key,v in fiber_sum(b,c).items()}


def selected_m(m):
    assert 1<m<=N-2 and gcd(m,N)==1
    direct={}
    r_terms=0
    for r in divisors(m):
        if not ALPHA<r<=H:continue
        k=m//r
        coeff=mu(r)*mu(k)**2*int(gcd(k,r)==1)
        vector_add(direct,log_vector(r),coeff)
        r_terms+=1
    q_terms={}
    pairs=[]
    for b in range(1,isqrt(m)+1):
        if m%(b*b) or mu(b)==0:continue
        for c in divisors(m//(b*b)):
            if mu(c)==0 or gcd(b,c)>1 or gcd(b*c,N)>1:continue
            q=b*b*c
            W=weight(b,c)
            if not W:continue
            assert q<=m and m%q==0
            assert q not in q_terms # unique square-part b and squarefree c.
            q_terms[q]=W
            pairs.append((b,c,q))
    grouped={}
    for W in q_terms.values():vector_add(grouped,W)
    assert grouped==direct
    lam=Lambda_N(N-m)
    weighted=multiply_vectors(direct,lam)
    one={}
    if ALPHA<m<=H:one={key:mu(m)*v for key,v in log_vector(m).items()}
    no_one=dict(direct)
    vector_add(no_one,one,-1)
    explicit={}
    for r in divisors(m):
        k=m//r
        if ALPHA<r<=H and k>=2 and gcd(k,r)==1:vector_add(explicit,log_vector(r),mu(r)*mu(k)**2)
    assert no_one==explicit
    cuts=[]
    for B in (1,2,4,8,16,128):
        head,tail={},{ }
        for b,c,q in pairs:vector_add(head if b<=B else tail,q_terms[q])
        total=dict(head)
        vector_add(total,tail)
        assert total==direct
        cuts.append(dict(B=B,head_coefficients=serialize(head),tail_coefficients=serialize(tail),
                         head_weighted_active=bool(multiply_vectors(head,lam)),
                         tail_weighted_active=bool(multiply_vectors(tail,lam))))
    return dict(m=m,n=N-m,factor_m=factor(m),factor_n=factor(N-m),mu_m=mu(m),
                original_r_slots=r_terms,modulus_terms=len(q_terms),full_coefficients=serialize(direct),
                full_weighted_terms=len(weighted),Lambda_N=serialize(lam),cuts=cuts,
                k1_coefficients=serialize(one),k_ge_2_coefficients=serialize(no_one),
                k1_removed_exactly=True)


def repeated_factor_falsifier():
    r,k=303,63
    correct=mu(k)**2*int(gcd(k,r)==1)
    wrong=lcm_fixed=restricted=0
    for d in range(1,isqrt(k)+1):
        if k%(d*d):continue
        for t in divisors(r):
            coeff=mu(d)*mu(t)
            if k%(d*d*t)==0:wrong+=coeff
            # lcm(d²,t) is the general S2 divisibility condition.
            period=d*d*t//gcd(d*d,t)
            if k%period==0:lcm_fixed+=coeff
            if gcd(d,r*N)==1 and k%(d*d*t)==0:restricted+=coeff
    assert correct==lcm_fixed==restricted==0 and wrong==-1
    n=N-r*k
    assert factor(n)==((n,1),) and Lambda_N(n)
    return dict(r=r,k=k,n=n,factor_k=factor(k),factor_n=factor(n),correct=correct,
                illegal_product_formula=wrong,corrected_lcm=lcm_fixed,corrected_d_restriction=restricted,
                verdict='Allowing d to share r while keeping d²*t gives a spurious active coefficient; retain gcd(d,r)=1 or use the general lcm')


def fibers():
    examples=[]
    for b,c in ((1,101),(3,101),(7,101),(21,101),(3,41)):
        assert mu(b)**2==mu(c)**2==1 and gcd(b,c)==1
        full=fiber_sum(b,c,True)
        expected=log_vector(c) if b==1 else ({(b,):-1} if factor(b)==((b,1),) else {})
        assert full==expected
        partial=fiber_sum(b,c)
        physical_complete=c>ALPHA and c*b<=H
        if physical_complete:assert partial==full
        else:assert partial!=full
        examples.append(dict(b=b,c=c,all_divisor_sum=serialize(full),actual_cut_sum=serialize(partial),
                             complete_in_physical_head=physical_complete,
                             verdict='Use -Lambda(b) only on complete fibers; keep every incomplete fiber literal'))
    return examples


def run():
    initialize()
    assert H**8<=N**3<(H+1)**8
    assert B_PHYSICAL**32<=N<(B_PHYSICAL+1)**32
    assert Q*(ALPHA+1)>N-1
    selected=(173,303,311,369,841,909,10201,30603,44541,112211,658911,99999727)
    receipts=[selected_m(m) for m in selected]
    square=next(v for v in receipts if v['m']==112211)
    assert square['mu_m']==0 and square['full_coefficients']=={}
    cut=square['cuts'][0]
    assert cut['head_coefficients']=={'101':'-1'} and cut['tail_coefficients']=={'101':'1'}
    assert cut['head_weighted_active'] and cut['tail_weighted_active']
    prime=next(v for v in receipts if v['m']==173)
    assert prime['Lambda_N'] and prime['k1_coefficients']=={'173':'-1'} and prime['k_ge_2_coefficients']=={}
    count_receipts=[]
    for q in (3,101,303,369,10201,112211,44541):
        positive_count=(N-2)//q
        assert Fraction(positive_count)<=Fraction(N,q)
        count_receipts.append(dict(q=q,positive_v_count=positive_count,bound=str(Fraction(N,q)),
                                   endpoint_n_one_removed=bool((N-1)%q==0)))
    result=dict(status='PASS_HEAD_IDENTITY_ONLY',N=N,alpha=ALPHA,H=H,B_physical=B_PHYSICAL,
                head_identity='sum_r mu(r)log(r)sum_k mu(k)^2 Lambda_N(N-r*k)1_(k,r)=sum_(b,c)w(b²c)psi_N(N-1;b²c,N)',
                selection_scope='Verified coefficientwise at the twelve listed m; the same selection mask is retained on both sides. Complete AP prefixes/head are not enumerated',
                square_part_weight='mu(b)mu(c)*sum_(g|b,alpha<c*g<=H)mu(g)log(c*g)',
                b_c_support='b,c squarefree,gcd(b,c)=1,gcd(b*c,N)=1',selected_arguments=receipts,
                physical_cuts='B=1 is floor(N^(1/32)); other integer B values are finite algebra stress cuts, not alternate asymptotic parameters',
                incomplete_fibers=fibers(),repeated_factor_falsifier=repeated_factor_falsifier(),
                special_prefix_counts=count_receipts,
                prefix_count_scope='No +1 is needed for n=N-q*v,1<=v<=floor((N-2)/q), this special full prefix only; other interval/fiber +1 terms are retained',
                nonsquarefree_cut_diagnostic='m=112211 has prime n=99887789: full head zero, B=1 head=-log101*log99887789 and tail=+log101*log99887789',
                k1_diagnostic='m=173,n=99999827 both prime: all-k head retains -log173*log99999827; k>=2 head removes it, or HARM cancels it jointly',
                previous_artifacts=verify(),script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                limitations='No analytical tail bound, no acquired I payment recomputed, no complete head/complement enumeration and no whole D_N claim')
    (output_directory()/'head_regrouping.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(status=result['status'],N=N,selected_m=len(selected),H=H,B=B_PHYSICAL,
                         previous_artifacts=result['previous_artifacts'],script_sha256=result['script_sha256']),indent=2))


if __name__=='__main__':run()
