"""Exact rational filter for constant affine HH charts; no asymptotics."""
import sys
sys.dont_write_bytecode = True
from fractions import Fraction
from hashlib import sha256
from itertools import product
from math import gcd, prod
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parent
BASE = ROOT.parent
sys.path.insert(0,str(BASE/'numerical'))
from parity_checks import N, factor, mu, rough


def evaluate(form,xy):
    c,a,b = form
    x,y = xy
    return c+a*x+b*y


def determinant(left,right):
    return left[1]*right[2]-left[2]*right[1]


def common_zero(left,right):
    c,a,b = left
    f,d,e = right
    det = a*e-b*d
    assert det != 0
    solution = Fraction(b*f-c*e,det),Fraction(c*d-a*f,det)
    assert evaluate(left,solution) == evaluate(right,solution) == 0
    return solution


def polynomial_product(forms):
    coefficients = {(0,0):Fraction(1)}
    for c,a,b in forms:
        affine = {(0,0):Fraction(c),(1,0):Fraction(a),(0,1):Fraction(b)}
        output = {}
        for (i,j),coefficient in coefficients.items():
            for (k,l),weight in affine.items():
                key = i+k,j+l
                output[key] = output.get(key,Fraction(0))+coefficient*weight
        coefficients = {key:value for key,value in output.items() if value}
    return coefficients


def chart_polynomial(left,right):
    coefficients = polynomial_product(left)
    for key,value in polynomial_product(right).items():
        coefficients[key] = coefficients.get(key,Fraction(0))+value
        if not coefficients[key]:
            del coefficients[key]
    return coefficients


def gradient_rank(forms):
    if any(determinant(a,b) for a in forms for b in forms):
        return 2
    return int(any(a or b for _,a,b in forms))


def branch_value(forms,xy):
    return prod(evaluate(form,xy) for form in forms)


def serialize_fraction(value):
    return f'{value.numerator}/{value.denominator}' if isinstance(value,Fraction) else str(value)


def run():
    independent_pairs = 0
    for c,a,b,f,d,e in product(range(-2,3),repeat=6):
        left,right = (c,a,b),(f,d,e)
        if determinant(left,right) == 0:
            continue
        xy = common_zero(left,right)
        # Arbitrary other affine factors cannot prevent either whole
        # product from vanishing at this rational intersection.
        branch_a = (left,(2,1,0),(1,0,1),(3,0,0))
        branch_b = (right,(1,-1,2),(4,2,0),(1,0,0))
        assert branch_value(branch_a,xy)+branch_value(branch_b,xy) == 0
        independent_pairs += 1

    left = ((13,0,0),(3,7951,0),(7,0,0),(1,0,0))
    right = ((1,0,0),(7951,0,0),(12577,-91,0),(1,0,0))
    assert chart_polynomial(left,right) == {(0,0):Fraction(N)}
    assert gradient_rank(left+right) == 1
    assert all(determinant(a,b) == 0 for a in left for b in right)
    positive_points = 0
    actual_HH_faces = []
    rejected = {'unit_or_squarefree':0}
    for X in range(101):
        for Y in (-3,0,5):
            xy = Fraction(X),Fraction(Y)
            assert all(evaluate(form,xy) > 0 for form in left+right)
            assert branch_value(left,xy)+branch_value(right,xy) == N
            positive_points += 1
        b,u,v,w = (evaluate(form,(X,0)) for form in left)
        k,s,t,z = (evaluate(form,(X,0)) for form in right)
        n,m = b*u*v*w,k*s*t*z
        a,r = u*v*w,s*t*z
        assert n+m == N and u>2 and v>2 and s>2 and t>2
        assert a <= m and b <= m and r > 100
        if gcd(n,N) != 1 or mu(n) == 0 or mu(m) == 0:
            rejected['unit_or_squarefree'] += 1
            continue
        assert rough(n,2)
        actual_HH_faces.append(dict(X=X,b=b,u=u,v=v,w=w,k=k,s=s,t=t,z=z,
                                   n=n,m=m,factor_n=factor(n),factor_m=factor(m)))
    assert actual_HH_faces and actual_HH_faces[0]['X'] == 0

    degenerate_left = ((13,0,0),(0,1,0),(0,0,1),(0,0,0))
    constant_right = ((N,0,0),(1,0,0),(1,0,0),(1,0,0))
    assert chart_polynomial(degenerate_left,constant_right) == {(0,0):Fraction(N)}
    assert gradient_rank(degenerate_left+constant_right) == 2
    assert branch_value(degenerate_left,(1,1)) == 0
    zero_left = ((1,0,0),(0,1,0),(0,0,1),(1,0,0))
    zero_right = ((-1,0,0),(0,1,0),(0,0,1),(1,0,0))
    assert chart_polynomial(zero_left,zero_right) == {}
    assert gradient_rank(zero_left+zero_right) == 2
    assert branch_value(zero_left,(1,1)) == 1 and branch_value(zero_right,(1,1)) == -1
    # Original geometry: independently changing u and v leaves a mixed
    # coefficient that no frozen affine complementary branch can cancel.
    mixed = 13*(11*17-11*7-3*17+3*7)
    assert mixed == 1040
    frozen = chart_polynomial(((13,0,0),(0,1,0),(0,0,1),(1,0,0)),
                              ((1,0,0),(7951,0,0),(12577,0,0),(1,0,0)))
    assert frozen[(1,1)] == 13 and frozen != {(0,0):Fraction(N)}
    assert 13*3*7+7951*12577 == N

    result = dict(status='PASS',N=N,
                  independent_cross_pairs_exhaustive=independent_pairs,
                  coefficient_domain='Every c,a,b,f,d,e in {-2,-1,0,1,2} with a*e-b*d nonzero',
                  common_zero_formula=['X=(b*f-c*e)/(a*e-b*d)','Y=(c*d-a*f)/(a*e-b*d)'],
                  positive_rank1_chart=dict(left=left,right=right,
                                           polynomial_identity='13*(3+7951X)*7+7951*(12577-91X)=100000000 for all rational X,Y',
                                           rank=1,positive_integer_points=positive_points,
                                           X_interval=[0,100],Y_values=[-3,0,5],
                                           actual_unit_squarefree_HH_faces=len(actual_HH_faces),
                                           rejected_faces=rejected,examples=actual_HH_faces[:5]),
                  degenerate_counterexample=dict(left=degenerate_left,right=constant_right,rank=2,
                                                 HH_sum=N,failed_hypothesis='The first branch contains an identically zero affine factor'),
                  zero_N_counterexample=dict(left=zero_left,right=zero_right,rank=2,
                                            nonzero_branch_values_at_1_1=[1,-1],failed_hypothesis='N nonzero'),
                  pointwise_only_counterexample=dict(positive_point=[3,7],HH_sum_at_point=N,
                                                    nonconstant_XY_coefficient=13,
                                                    mixed_u_3_to_11_v_7_to_17=mixed,
                                                    failed_hypothesis='Identity as a polynomial/all rational parameters'),
                  limitations='Tests the precise affine-polynomial obstruction only; original HH hypersurface may use nonlinear charts or other analytic methods',
                  script_sha256=sha256(Path(__file__).read_bytes()).hexdigest())
    (ROOT/'affine.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:result[k] for k in ('status','N','independent_cross_pairs_exhaustive',
                                         'degenerate_counterexample','zero_N_counterexample','script_sha256')},indent=2))
    print(json.dumps(dict(positive_chart_points=positive_points,
                         actual_unit_squarefree_HH_faces=len(actual_HH_faces)),indent=2))


if __name__ == '__main__':
    run()
