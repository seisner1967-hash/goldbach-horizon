"""Native centered row versus new two-axis twists and exact trace.

This checks the actual algebraic connection, including p|k and p|ar sectors.
No new asymptotic estimate or global trace control is inferred.
"""
import sys
sys.dont_write_bytecode=True
from fractions import Fraction
from hashlib import sha256
from math import gcd
from pathlib import Path
import json
from conservation import initialize,verify
from shared import ROOT,BASE,N,factor,mu
from jacobi_checks import primitive_logs,twist_phase
sys.path.insert(0,str(BASE/'round4'))
from inverse_checks import reduce_phases
sys.path.insert(0,str(BASE/'round6'))
from squarefree_checks import physical_point


def native_centered(p):
    g,logs=primitive_logs(p)
    L=p-1
    cases=0
    for n in range(1,p):
        m=N-n
        centered=Fraction(int(m%p==0))-Fraction(1,L)
        native=[Fraction(0)]*L
        for j in range(1,L):native[(j*(logs[n]-logs[N%p]))%L]+=Fraction(1,L)
        expected=(centered,) if centered else ()
        assert reduce_phases(native,L)==expected
        cases+=1
        if m%p==0:
            assert centered==Fraction(p-2,p-1)>0
            assert all(twist_phase(p,logs,j,n,m) is None for j in range(1,L))
    return dict(p=p,cases=cases,identity='1_(p|m)-1/(p-1)=sum_(chi nonprincipal) chi(n)*conjchi(N)/(p-1)',
                hypotheses='p prime,p not dividing N or n',
                native_factor='conjchi(N)',new_factor='conjchi(m)',
                new_twist_zero_on_p_divides_m=True)


def old_trace(q,m):
    assert mu(q)**2==1 and gcd(q,m)==1
    P=phi=1
    for p,_ in factor(q):
        P*=((p-1)*int(m%p==0)-1)
        phi*=p-1
    value=Fraction(mu(q)*P,phi)
    assert value==Fraction(1,phi)
    return value


def run():
    initialize()
    native=[native_centered(p) for p in (3,7,11,13,17,19)]
    base=physical_point(13,3,7,1,7951,12577,1)
    assert base
    zero_branches=[]
    for q,location in ((3,'a'),(7,'a'),(7951,'r'),(12577,'r')):
        assert factor(q)==((q,1),) and N%q
        assert base['n']%q==0 or base['m']%q==0
        zero_branches.append(dict(q=q,divides=location,n=base['n'],m=base['m'],
                                  all_nonprincipal_twists='ZERO by character extension at a nonunit',
                                  enumeration='Structural factor certificate; no enumeration of all characters at large q'))
    kpoint=physical_point(101,103,107,7,3,71,34967)
    assert kpoint and kpoint['n']==47864203 and kpoint['m']==52135797
    q=7
    assert kpoint['k']%q==0 and kpoint['n']%q!=0 and kpoint['m']%q==0
    _,logs=primitive_logs(q)
    assert all(twist_phase(q,logs,j,kpoint['n'],kpoint['m']) is None for j in range(1,q-1))
    native_value=Fraction(1)-Fraction(1,q-1)
    assert native_value==Fraction(5,6)
    trace_cases=0
    for q in (1,3,7,11,21,33,77,101,143):
        for m in range(1,1025):
            if gcd(q,m)==1:
                old_trace(q,m)
                trace_cases+=1
    assert mu(9)==0
    result=dict(status='PASS_EXACT_CONNECTION_ONLY',N=N,native_rows=native,
                branch_nonunit_diagnostics=zero_branches,
                p_divides_k=dict(point=kpoint,p=7,new_twists='ALL ZERO',R_p='Entire selected fibre weight',
                                native_centered_row=str(native_value),
                                verdict='The new two-axis twist does not replace the native centered row'),
                old_trace=dict(cases=trace_cases,q_values=[1,3,7,11,21,33,77,101,143],m_domain=[1,1024],
                               identity='mu(q)*P_q(m)/phi(q)=1/phi(q) for squarefree q and gcd(q,m)=1',
                               nonsquarefree_counterexample='q=9,m=1: mu(q)*P/phi=0 differs from 1/phi=1/6'),
                previous_artifacts=verify(),script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                limitations='Native finite identity and structural nonunit diagnostics; no new trace theorem or signed/global D_N estimate')
    (ROOT/'trace.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(status=result['status'],N=N,native_cases=sum(v['cases'] for v in native),
                         trace_cases=trace_cases,previous_artifacts=result['previous_artifacts'],script_sha256=result['script_sha256']),indent=2))


if __name__=='__main__':run()
