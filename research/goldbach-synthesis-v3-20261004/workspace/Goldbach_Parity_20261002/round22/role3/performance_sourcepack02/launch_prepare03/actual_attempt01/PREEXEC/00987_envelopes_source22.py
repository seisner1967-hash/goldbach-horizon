"""Closed rational majorants of the fixed paper envelopes, SOURCE ONLY.

No residue/observed discrepancy is an input. Proof debts remain in the paper
and Lean audit: pi>3, log(1e6)<16, exp(-1)<3/8 and the exact H1 rest formulas.
This module does not turn those proofs into a numerical PASS or a new axiom.
"""
from fractions import Fraction as F

N, Y, T, X, Q, R = 100000000, 10000, 100, 1000000, 1000000, 1000000
TAU = F(1, 1000000)
W = 1024*Y*Y+32*T+2560
W_ARCH = 128*Y+F(32, Y)+32


def analytic_envelopes():
    # a=pi/4>3/4; Y^(3/2)=1e6, Y^(-1/2)=1/100.
    vertical = F(3, 8)**75/F(3)*(32*1000000*(F(4*(T+2), 3)+F(16, 9))
                                +F(8, 100)*(F(4*(T+8), 3)+F(16, 9)))
    alias = F(1, 2)**128/(1-F(1, 2)**128)
    quadrature = F(2*T, 3)*W*(F(1, 3)**65/(1-F(1, 3))+alias/(1-F(1, 3)))
    primal = F(3, 8)**100*((X+Y)*16+Y+F(2*Y*Y, X))
    dual = F(17, Y*Q)
    arch_tail = F(4, 3)*(F(3, 8)**100+F(1, 2*Y*R*R)+F(2, Y*R))
    arch_alias = F(1, 2)**96/(1-F(1, 2)**96)
    arch_quad = 16*W_ARCH*(F(1, 4)**33/(1-F(1, 4))+arch_alias/(1-F(1, 4)))
    return dict(E_vert=vertical, E_quad=quadrature, E_prim=primal,
                E_dual=dual, E_arch=arch_tail, E_quad_arch=arch_quad)


def continuity_contract():
    # Documentation, not a proof object. Actual continuous envelopes before
    # these rational specialisations are in numeric_precontract22.md.
    return {"Y_domain": "Y>0", "T_domain": "T>=0",
            "X_Q_R_domain": "X,Q,R>1", "observed_residual_used": False,
            "Lean_continuity_proofs_complete": False}
