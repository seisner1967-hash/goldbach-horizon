"""Exact two-square expansion, compatible CRT and full two-axis twists.

All arithmetic is integral. N=100000000 is fixed. Listed finite fibres are
diagnostics, never an enumeration of the complete HH support or D_N.
"""
import sys
sys.dont_write_bytecode=True
from fractions import Fraction
from hashlib import sha256
from itertools import product
from math import gcd,lcm
from pathlib import Path
import json

from exact_tools import N,ROOT,factor,divisors,mu,squarefree_divisor_expansion
from conservation import initialize,verify


def cmul(a,b):
    return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])


def cconj(a):
    return (a[0],-a[1])


def chi5(x,order):
    x%=5
    if x==0:return (0,0)
    if order==2:return (1 if x in (1,4) else -1,0)
    assert order==4
    return {1:(1,0),2:(0,1),4:(-1,0),3:(0,-1)}[x]


def rad(n):
    value=1
    for p,_ in factor(n):value*=p
    return value


def small_primorial(W):
    value=1
    for p in range(2,W+1):
        if factor(p)==((p,1),):value*=p
    return value


def square_divisors(n):
    return [d for d in divisors(n) if n%(d*d)==0 and mu(d)]


def compatible_CRT(A,C,d,e,f,ell):
    """Solve the actual congruence before taking any modular inverse.

    Use L=lcm(d²,f) in the general S2 cells. On restricted S3 cells
    gcd(d,f)=1 and L=f*d². Compatibility g|N is retained before every
    inverse, even when the initial S3 contract does not force g=1.
    """
    assert min(A,C,d,e,f,ell)>0
    B=lcm(f,d*d)
    M=lcm(A,e*e,ell)
    g=gcd(C*B,M)
    if N%g:return None
    reduced=M//g
    v0=0 if reduced==1 else (N//g)*pow(C*B//g,-1,reduced)%reduced
    residue=B*v0
    period=B*reduced
    assert (N-C*residue)%M==0
    return dict(B=B,M=M,g=g,v0=v0,residue=residue,period=period,
                reduced_modulus=reduced)


def enumerate_class(cell,lo,hi):
    if cell is None:return []
    residue,period=cell['residue'],cell['period']
    first=lo+(residue-lo)%period
    return list(range(first,hi+1,period))


def complete_twist(A,C,x,zeta):
    assert A*x+C*zeta==N and gcd(A*x*C*zeta,N)==1
    result={}
    for order in (2,4):
        a,b,c,z=chi5(A,order),chi5(x,order),chi5(C,order),chi5(zeta,order)
        actual=cmul(cmul(a,b),cmul(cconj(c),cconj(z)))
        assert actual==chi5(-1,order)
        complementary=cmul(chi5(N-C*zeta,order),cconj(z))
        assert complementary==chi5(-C,order)
        assert cmul(chi5(A*x,order),cconj(chi5(C*zeta,order)))==actual
        result[str(order)]=dict(full_product=actual,missing_C_product=complementary,
                                isolated_zeta=chi5(zeta,order))
    return result


def front_admitted(b,u,v,k,s,t,zeta):
    A=b*u*v
    C=k*s*t
    n=N-C*zeta
    if not n>0 or n%A:return False
    x=n//A
    a=u*v*x
    r=s*t*zeta
    m=C*zeta
    direct=(x>=1 and a<=m and b<=m and r>100 and k<=999999 and 100*k<m)
    lower=max((N+C*(b+1)-1)//(C*(b+1)),(b+C-1)//C,100//(s*t)+1)
    upper=(N-A)//C
    byfront=(lower<=zeta<=upper and k<=999999 and 100*k<m)
    assert direct==byfront
    return direct


def physical_point(b,u,v,k,s,t,zeta):
    A=b*u*v
    C=k*s*t
    if not front_admitted(b,u,v,k,s,t,zeta):return None
    n=N-C*zeta
    m=C*zeta
    if gcd(n,N)!=1 or mu(n)==0 or mu(m)==0:return None
    assert all(vv>2 for vv in (u,v,s,t))
    x=n//A
    return dict(b=b,u=u,v=v,k=k,s=s,t=t,zeta=zeta,x=x,A=A,C=C,n=n,m=m,
                factor_n=factor(n),factor_m=factor(m),W=2,y=2,
                four_Mobius_signs=[mu(u),mu(v),mu(s),mu(t)],
                four_Mobius_product=mu(u)*mu(v)*mu(s)*mu(t),
                twists=complete_twist(A,C,x,zeta))


def pointwise_expansion(A,C,zeta,W):
    """Compare S2 and restricted compatible cells at one exact argument.

    Restrictions after inclusion-exclusion are tested as a regrouping,
    with signed coefficients retained before any absolute value.
    """
    n=N-C*zeta
    assert 0<n<N and mu(A)**2==mu(C)**2==1 and gcd(A,C*N)==1 and gcd(C,N)==1
    K=C*N
    P=small_primorial(W)
    Ds=square_divisors(zeta)
    Es=square_divisors(n)
    # K can exceed N; its factor table is the certified union of C and N.
    radK=lcm(rad(C),rad(N))
    Fs=divisors(gcd(zeta,radK))
    Ls=divisors(gcd(n,P))
    left=mu(C)**2*mu(zeta)**2*mu(n)**2*int(gcd(zeta,K)==1)*int(gcd(n,P)==1)*int(n%A==0)
    raw=restricted=0
    checked=0
    if n%A==0:
        for d,e,f,ell in product(Ds,Es,Fs,Ls):
            coeff=mu(d)*mu(e)*mu(f)*mu(ell)
            raw+=coeff
            if gcd(d,A*e*K)!=1 or gcd(e,C*N)!=1 or gcd(ell,C*N)!=1 or gcd(f,5)!=1:
                continue
            cell=compatible_CRT(A,C,d,e,f,ell)
            if cell is None:continue
            assert gcd(d,ell)==1 # here required by actual divisibilities
            assert cell['g']==1 and gcd(cell['M'],5)==1
            assert (zeta-cell['residue'])%cell['period']==0
            restricted+=coeff
            checked+=1
    assert left==raw
    # f sharing the conductor is omitted only in the twisted identity:
    # chi(zeta)=0 then. Never claim an untwisted identity after this step.
    if zeta%5:assert left==restricted
    assert squarefree_divisor_expansion(zeta)==mu(zeta)**2
    assert squarefree_divisor_expansion(n)==mu(n)**2
    assert mu(C*zeta)**2==mu(C)**2*mu(zeta)**2*int(gcd(C,zeta)==1)
    for order in (2,4):
        chi=chi5(zeta,order)
        assert (left*chi[0],left*chi[1])==(restricted*chi[0],restricted*chi[1])
    return dict(active=bool(left),CRT_cells=checked,raw_cells=len(Ds)*len(Es)*len(Fs)*len(Ls))


def CRT_diagnostics():
    incomplete=[]
    for A,C,d,ell in ((273,187,19,19),(273,10403,11,11)):
        e=f=1
        K=C*N
        assert gcd(d,A*e*K)==gcd(e,C*N)==gcd(ell,C*N)==gcd(f,5)==1
        M=lcm(A,e*e,ell)
        coefficient=C*f*d*d
        g=gcd(coefficient,M)
        assert g>1 and N%g and compatible_CRT(A,C,d,e,f,ell) is None
        incomplete.append(dict(A=A,C=C,d=d,e=e,f=f,ell=ell,M=M,coefficient=coefficient,
                               gcd=g,N_mod_gcd=N%g,S3_written=True,cell='EMPTY',inverse='NOT_ATTEMPTED'))
    A,C=273,10403
    lo,hi=1,(N-A)//C
    cell=compatible_CRT(A,C,1,3,1,1)
    points=enumerate_class(cell,lo,hi)
    assert cell['M']==819 and cell['v0']==107 and len(points)==12
    direct=[z for z in range(lo,hi+1) if (N-C*z)%A==0 and (N-C*z)%9==0]
    assert points==direct
    wrongmod=A*9
    wrongres=N*pow(C,-1,wrongmod)%wrongmod
    wrong=[z for z in range(lo,hi+1) if (z-wrongres)%wrongmod==0]
    assert len(wrong)==4 and set(wrong)<set(points)
    illegal=compatible_CRT(A,C,2,2,1,1)
    illegal_points=enumerate_class(illegal,lo,hi)
    assert illegal_points and all(gcd(z,C*N)>1 and gcd(N-C*z,N)>1 for z in illegal_points)
    overlap=compatible_CRT(101,309,3,1,3,1)
    overlap_points=enumerate_class(overlap,1,4000)
    overlap_direct=[z for z in range(1,4001) if z%9==0 and z%3==0 and (N-309*z)%101==0]
    assert overlap_points==overlap_direct and overlap['B']==9
    assert any(z%27 for z in overlap_points)
    periods=[]
    for e in (1,3):
        c=compatible_CRT(A,C,1,e,1,1)
        assert gcd(c['M'],5)==1
        for order in (2,4):
            isolated=[chi5(c['v0']+c['M']*j,order) for j in range(5)]
            assert tuple(map(sum,zip(*isolated)))==(0,0)
            unit_period=[chi5(c['v0']+c['M']*j,order) if gcd(c['v0']+c['M']*j,N)==1 else (0,0)
                         for j in range(10)]
            assert tuple(map(sum,zip(*unit_period)))==(0,0)
            periods.append(dict(e=e,M=c['M'],order=order,primitive_period=5,unit_N_mask_period=10,
                                primitive_sum=[0,0],unit_masked_sum=[0,0]))
    # Dropping gcd(M,5)=1 changes the character; this is outside the contract.
    bad=[chi5(1+5*j,4) for j in range(5)]
    assert all(z==(1,0) for z in bad)
    return dict(incomplete_S3_counterexamples=incomplete,
                e_shares_A=dict(A=A,C=C,e=3,J=[lo,hi],correct_M=819,points=points,
                                erroneous_product_modulus=wrongmod,erroneous_count=len(wrong),
                                interpretation='These are signed square-divisor expansion cells; not squarefree HH points'),
                illegal_d_e_share_N=dict(d=2,e=2,compatible_cell=illegal,point_count=len(illegal_points),
                                        physical_mask='ZERO on every point; retained before regrouping'),
                general_overlap_d_f=dict(A=101,C=309,d=3,f=3,L=9,incorrect_f_d_squared=27,
                                        J=[1,4000],points=overlap_points,
                                        interpretation='General S2 cell outside restricted S3; use lcm(d²,f), not f*d²'),
                isolated_periods=periods,nonunit_affine_slope_counterexample=dict(M=5,v0=1,order=4,period_sum=[5,0]))


def run():
    initialize()
    crt=CRT_diagnostics()
    # Finite head and a long-zeta physical window, with the first H congruence.
    samples=[(273,10403,z,W) for z in range(1,513) for W in (2,19)]
    samples.extend((273,187,z,W) for z in range(40000,45001) if (N-187*z)%273==0 for W in (2,19))
    samples.extend((273,99999727,1,W) for W in (2,19))
    samples.extend((1113121,213,244769,W) for W in (2,19))
    summaries=[pointwise_expansion(*args) for args in samples]
    longpoints=[p for z in range(40000,45001) if (p:=physical_point(13,3,7,1,11,17,z))]
    assert longpoints
    for order in ('2','4'):
        assert len({tuple(p['twists'][order]['isolated_zeta']) for p in longpoints})>1
        assert len({tuple(p['twists'][order]['full_product']) for p in longpoints})==1
    zeta1=physical_point(13,3,7,1,7951,12577,1)
    assert zeta1 and zeta1['n']==273 and zeta1['m']==99999727
    thin=physical_point(101,103,107,1,3,71,244769)
    assert thin and thin['x']==43
    A,C=thin['A'],thin['C']
    upper=(N-A)//C
    residue=N*pow(C,-1,A)%A
    thin_congruence=list(range(residue or A,upper+1,A))
    assert upper>10000 and upper<A and thin_congruence==[244769]
    length=Fraction(N,A*C)
    assert length<1
    result=dict(status='PASS_CORRECTED_CONTRACT',N=N,
                central_identity='Two-square expansion S2 and compatible CRT; full product chi(n)*conj(chi(m))=chi(-1)',
                correction='Initial S3 does not imply invertibility; test gcd(C*f*d²,M)|N before inverse, or retain gcd(d,ell)=1 in the invertible contract',
                CRT=crt,pointwise_expansion=dict(cases=len(samples),active=sum(v['active'] for v in summaries),
                    compatible_CRT_cells=sum(v['CRT_cells'] for v in summaries),raw_signed_cells=sum(v['raw_cells'] for v in summaries),
                    domains=['A=273,C=10403,zeta=1..512,W in {2,19}',
                             'A=273,C=187,zeta=40000..45000 with A|(N-C*zeta),W in {2,19}',
                             'A=273,C=99999727,zeta=1,W in {2,19}',
                             'A=1113121,C=213,zeta=244769,W in {2,19}']),
                physical_long_window=dict(J=[40000,45000],A=273,C=187,
                    true_congruence_points=sum((N-187*z)%273==0 for z in range(40000,45001)),
                    accepted_original_masks=len(longpoints),points=longpoints,
                    twist_verdict='Isolated zeta character varies; complete two-axis product is constant: +1 quadratic, -1 order4'),
                zeta_one=zeta1,
                thin_true_fibre=dict(point=thin,raw_zeta_interval=[1,upper],congruence_period=A,
                    all_congruence_points=thin_congruence,N_over_AC=f'{length.numerator}/{length.denominator}',
                    verdict='Raw interval exceeds sqrt(N), but has one actual point although N/(A*C)<1; the counting +1 is indispensable'),
                arithmetic='Integer/Fraction and Gaussian integer character values; no floating identity oracle',
                previous_artifacts=verify(),script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                limitations='Finite domains explicitly listed; no asymptotic gain, no small correlation, no global HH or D_N calculation')
    (ROOT/'squarefree.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(status=result['status'],N=N,cases=len(samples),CRT_cells=result['pointwise_expansion']['compatible_CRT_cells'],
                         long_window_points=len(longpoints),thin_point=thin['zeta'],previous_artifacts=result['previous_artifacts'],
                         script_sha256=result['script_sha256']),indent=2))


if __name__=='__main__':run()
