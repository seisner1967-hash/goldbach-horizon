"""Exact native character Gram matrices, CRT tensors and coupled defects.

N=100000000. Integer phase polynomials are reduced cyclotomically. No
floating eigenvalue oracle, HH separability assumption, or Lean call.
"""
import sys
sys.dont_write_bytecode=True
from hashlib import sha256
from itertools import product
from math import gcd,lcm
from pathlib import Path
import json
from conservation import initialize,verify
from shared import (ROOT,N,factor,mu,actual_profile,multiply_vectors,
    polynomial_sign_certificate,primitive_logs,reduce_phases,cyclic_convolution)
from shared import output_directory


def phase(L,e,c=1):
    v=[0]*L
    if e is not None:v[e%L]=c
    return v


def conjugate(v):
    L=len(v)
    return [v[(-i)%L] for i in range(L)]


def add(v,w,c=1):
    for i,x in enumerate(w):v[i]+=c*x


def equal(v,w):
    assert len(v)==len(w)
    return reduce_phases(v,len(v))==reduce_phases(w,len(w))


def G_exponents(p,j):
    assert N%p
    _,logs=primitive_logs(p)
    L=p-1
    matrix=[]
    for a in range(p):
        row=[]
        for b in range(p):
            x=(N-a*b)%p
            row.append(None if x==0 else j*(logs[x]-logs[N%p])%L)
        matrix.append(row)
    assert all(matrix[0][b]==matrix[a][0]==0 for a in range(p) for b in range(p))
    return matrix,logs


def gram_expected(p,j,logs,a,c,unit=False,reverse=False):
    L=p-1
    v=phase(L,0,p*int(a==c))
    if a and c:
        exponent=j*(logs[a]-logs[c])%L
        if reverse:exponent=-exponent
        add(v,phase(L,exponent),-1)
    if unit:add(v,phase(L,0),-1)
    return v


def energy_certificate(p,j,G,logs):
    L=p-1
    M=lcm(L,4)
    embed=M//L
    beta=[(b%3-1,b%2) for b in range(p)]
    bphase=[]
    for re,im in beta:
        v=phase(M,0,re)
        add(v,phase(M,M//4,im))
        bphase.append(v)
    actual=[0]*M
    for a in range(p):
        row=[0]*M
        for b in range(p):
            if G[a][b] is not None:
                add(row,cyclic_convolution(phase(M,G[a][b]*embed),bphase[b],M))
        add(actual,cyclic_convolution(row,conjugate(row),M))
    norm=sum(re*re+im*im for re,im in beta)
    projection=[0]*M
    for b in range(1,p):
        add(projection,cyclic_convolution(phase(M,j*logs[b]*embed),bphase[b],M))
    expected=phase(M,0,p*norm)
    add(expected,cyclic_convolution(projection,conjugate(projection),M),-1)
    assert equal(actual,expected)
    return dict(beta='(b%3-1)+i*(b%2)',identity='||G beta||²=q||beta||²-|sum_b chi(b)*beta_b|²',
                exact_reduced_value=list(reduce_phases(actual,M)),cyclotomic_modulus=M)


def prime_check(p):
    L=p-1
    cases=0
    orientations=0
    energies=[]
    for j in range(1,L):
        G,logs=G_exponents(p,j)
        for a in range(p):
            for c in range(p):
                full=[0]*L
                reverse=[0]*L
                unit=[0]*L
                for b in range(p):
                    x,y=G[a][b],G[c][b]
                    if x is not None and y is not None:
                        full[(x-y)%L]+=1
                        reverse[(y-x)%L]+=1
                        if b:unit[(x-y)%L]+=1
                assert equal(full,gram_expected(p,j,logs,a,c))
                assert equal(reverse,gram_expected(p,j,logs,a,c,reverse=True))
                if a and c:assert equal(unit,gram_expected(p,j,logs,a,c,unit=True))
                cases+=1
                if j==L//4 and L%4==0 and a and c and a!=c:
                    wrong=gram_expected(p,j,logs,a,c,reverse=True)
                    orientations+=not equal(full,wrong)
        energies.append(energy_certificate(p,j,G,logs))
    if L%4==0:assert orientations>0
    G,logs=G_exponents(p,L//2)
    quadratic=[[0 if e is None else 1 if e==0 else -1 for e in row] for row in G]
    artificial=sum(x*x for row in quadratic for x in row)
    assert artificial==p*p-p+1 and artificial*artificial>p**3
    return dict(q=p,nonprincipal_characters=L-1,Gram_entries_tested=cases,
                full_Gram='q*Id-chi(a)*conjchi(c), with chi(0)=0',
                unit_Gram='q*Id-1*1star-v*vstar, v_a=chi(a)',
                order4_wrong_conjugation_falsifiers=orientations,energy_certificates=energies,
                exact_full_operator_norm='sqrt(q): upper bound from the Gram; equality on beta=e0 since column 0 is all ones',
                coupled_weight_counterexample=dict(W='G_quadratic(a,b), bounded by 1',alpha='ones',beta='ones',
                    value=artificial,claimed_bare_bound_squared=p**3,actual_squared=artificial**2,
                    verdict='False transfer to arbitrary bounded coupled weights; not a counterexample to the actual HH estimate'))


def matmul(A,B):
    n=len(A)
    return [[sum(A[i][k]*B[k][j] for k in range(n)) for j in range(n)] for i in range(n)]


def characteristic(A):
    n=len(A)
    B=[[int(i==j) for j in range(n)] for i in range(n)]
    coefficients=[1]
    for k in range(1,n+1):
        product=matmul(A,B)
        tr=sum(product[i][i] for i in range(n))
        assert tr%k==0
        c=-tr//k
        coefficients.append(c)
        B=product
        for i in range(n):B[i][i]+=c
    assert all(x==0 for row in B for x in row)
    return list(reversed(coefficients))


def poly_product(a,b):
    out=[0]*(len(a)+len(b)-1)
    for i,c in enumerate(a):
        for j,d in enumerate(b):out[i+j]+=c*d
    return out


def principal_spectral(p):
    A=[[int((N-a*b)%p!=0) for b in range(p)] for a in range(p)]
    fixed=sum(a*a%p==N%p for a in range(1,p))
    assert fixed==2 # N=10000² and p not dividing N.
    plus=((p-1)-fixed)//2
    minus=((p-1)+fixed)//2-1
    expected=[-1,-(p-1),1]
    for _ in range(plus):expected=poly_product(expected,[-1,1])
    for _ in range(minus):expected=poly_product(expected,[1,1])
    assert characteristic(A)==expected
    unit=[[A[a][b] for b in range(1,p)] for a in range(1,p)]
    assert all(sum(row)==p-2 for row in unit)
    return dict(p=p,characteristic_polynomial_ascending=expected,
                invariant_2_by_2_matrix=[[1,p-1],[1,p-2]],
                rho_polynomial=[-1,-(p-1),1],
                exact_norm='rho_p=((p-1)+sqrt((p-1)^2+4))/2',
                certificate='Real symmetric matrix; two roots of x²-(p-1)x-1 on span(e0,unit-ones), remaining eigenvalues ±1',
                unit_operator_norm=p-2,unit_certificate='J-P permutation; constant eigenvector has p-2, zero-sum singular values 1')


def local_gram(p,j,a,c,M):
    if j==0:
        if a==c==0:value=p
        elif a==0 or c==0 or a==c:value=p-1
        else:value=p-2
        return phase(M,0,value)
    _,logs=primitive_logs(p)
    native=gram_expected(p,j,logs,a,c)
    out=[0]*M
    for e,value in enumerate(native):out[e*(M//(p-1))]+=value
    return out


def CRT_tensor(p,r,j,k):
    q=p*r
    assert gcd(q,N)==1
    M=lcm(p-1 if j else 1,r-1 if k else 1)
    Gp,_=G_exponents(p,j) if j else (None,None)
    Gr,_=G_exponents(r,k) if k else (None,None)
    G=[]
    for a in range(q):
        row=[]
        for b in range(q):
            x,y=(N-a*b)%p,(N-a*b)%r
            if not x or not y:row.append(None);continue
            exponent=0
            if j:exponent+=Gp[a%p][b%p]*(M//(p-1))
            if k:exponent+=Gr[a%r][b%r]*(M//(r-1))
            row.append(exponent%M)
        G.append(row)
    for a in range(q):
        for c in range(q):
            full=[0]*M
            for b in range(q):
                x,y=G[a][b],G[c][b]
                if x is not None and y is not None:full[(x-y)%M]+=1
            expected=cyclic_convolution(local_gram(p,j,a%p,c%p,M),local_gram(r,k,a%r,c%r,M),M)
            assert equal(full,expected)
    return dict(q=q,local_primes=[p,r],character_indices=[j,k],Gram_entries=q*q,
                exact_tensor=True,local_principal=[j==0,k==0],
                norm_factors=['rho_'+str(p) if not j else 'sqrt('+str(p)+')',
                              'rho_'+str(r) if not k else 'sqrt('+str(r)+')'],
                verdict='All CRT character components retained, including local principal ones')


def raw_coupling():
    table=[[actual_profile(h*ell)[0] for ell in (101,311)] for h in (1,3)]
    assert not table[0][0] and table[0][1] and table[1][0]
    determinant=multiply_vectors(table[0][1],table[1][0])
    determinant={key:-c for key,c in determinant.items()}
    certificate=polynomial_sign_certificate(determinant)
    assert certificate['sign']=='POSITIVE'
    return dict(h=[1,3],ell=[101,311],actual_arguments=[[101,311],[303,933]],
                determinant_certificate=certificate,
                verdict='Generic raw F_N(h*ell) is not rank one on this 2x2 domain; no separability substitution used',
                scope='h=1 is outside the reduced L2 prime coverage; this is not a nonseparability certificate for its full log(h)/log(h*ell) coefficient')


def prime_coverage_coupling():
    # The zero corner avoids approximate log quotients: all positive
    # denominators can be cleared and the other product decides the sign.
    table=[[actual_profile(h*ell)[0] for ell in (101,311)] for h in (3,13)]
    assert all(factor(p)==((p,1),) for p in (3,13,101,311))
    assert all(ell%h for h in (3,13) for ell in (101,311))
    assert table[0][0] and table[0][1] and table[1][0] and not table[1][1]
    determinant=multiply_vectors(table[0][1],table[1][0])
    determinant={key:-c for key,c in determinant.items()}
    certificate=polynomial_sign_certificate(determinant)
    assert certificate['sign']=='POSITIVE'
    assert mu(N-1313)==0 and factor(N-4043)==((N-4043,1),)
    return dict(h=[3,13],ell=[101,311],actual_arguments=[[303,933],[1313,4043]],
                raw_minor_certificate=certificate,
                exact_L2_coefficient='mu(ell)*log(h)/log(h*ell)*F_N(h*ell)',
                coefficient_minor_sign='POSITIVE: zero first product; the positive log factors and denominators preserve the second-product sign',
                first_axis_1313_nonsquarefree=True,
                scope='Rank-one separation on these admissible L2 indices is false; richer decompositions and weighted HH estimates remain open')


def run():
    initialize()
    primes=(3,7,11,13,19)
    prime=[prime_check(p) for p in primes]
    principal=[principal_spectral(p) for p in primes]
    tensors=[CRT_tensor(p,r,j,k) for p,r in ((3,7),(3,11)) for j,k in
             ((0,(r-1)//2),((p-1)//2,0),((p-1)//2,(r-1)//2),(0,0))]
    G,_=G_exponents(7,3)
    assert all(G[0][z]==0 for z in range(7)) # zero exponent means value one.
    result=dict(status='PASS_ALGEBRA_ONLY',N=N,prime_Grams=prime,
                Gram_entries=sum(v['Gram_entries_tested'] for v in prime),principal_spectral=principal,
                composite_CRT=tensors,composite_Gram_entries=sum(v['Gram_entries'] for v in tensors),
                native_k7=dict(n=47864203,m=52135797,k=7,C_mod_7=0,G_C_zeta='1 for all zeta',
                    native_centered_row='5/6',new_bipolar_twists='0; their nonunit remainder must remain'),
                actual_raw_coupling=raw_coupling(),
                actual_L2_coupling=prime_coverage_coupling(),
                arithmetic='Integer phase polynomials reduced by exact cyclotomic polynomials; integer characteristic polynomials',
                previous_artifacts=verify(),script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                limitations='Finite identities and transfer falsifiers only; no HH gain, no coefficient separation, no whole D_N calculation')
    (output_directory()/'native_gram.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(status=result['status'],N=N,Gram_entries=result['Gram_entries'],
                         composite_Gram_entries=result['composite_Gram_entries'],previous_artifacts=result['previous_artifacts'],
                         script_sha256=result['script_sha256']),indent=2))


if __name__=='__main__':run()
