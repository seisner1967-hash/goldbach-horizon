from __future__ import annotations
from dataclasses import dataclass, asdict
from fractions import Fraction
from typing import Any, Callable
import mpmath as mp

@dataclass
class NumericCertificate:
    kind: str; statement: str; verified: bool; metadata: dict[str, Any]
    def to_dict(self): return asdict(self)

def certify_exp_leq(x, upper, dps=80):
    mp.mp.dps = dps; lhs = mp.exp(mp.mpf(str(x))); rhs = mp.mpf(str(upper))
    return NumericCertificate("exp_leq", f"exp({x})<={upper}", bool(lhs<=rhs),
        {"x":str(x),"upper":str(upper),"lhs":mp.nstr(lhs,30),"margin":mp.nstr(rhs-lhs,30),"dps":dps})

def certify_log_geq(x, lower, dps=80):
    mp.mp.dps = dps; lhs = mp.log(mp.mpf(str(x))); rhs = mp.mpf(str(lower))
    return NumericCertificate("log_geq", f"log({x})>={lower}", bool(lhs>=rhs),
        {"x":str(x),"lower":str(lower),"lhs":mp.nstr(lhs,30),"margin":mp.nstr(lhs-rhs,30),"dps":dps})

def certify_log_of_exp_witness(x, y, dps=80):
    c = certify_exp_leq(x=x, upper=y, dps=dps)
    return NumericCertificate("log_via_exp", f"log({y})>={x} via exp({x})<={y}", c.verified,
        {"exp_certificate":c.to_dict(),"dps":dps})

def scan_grid_upper_bound(f, a, b, n, claimed_upper, dps=80):
    mp.mp.dps = dps; aa,bb,ub = mp.mpf(str(a)), mp.mpf(str(b)), mp.mpf(str(claimed_upper))
    worst_x, worst_val, ok = aa, f(aa), True
    for k in range(n+1):
        x = aa + (bb-aa)*mp.mpf(k)/mp.mpf(n); fx = f(x)
        if fx > worst_val: worst_val, worst_x = fx, x
        if fx > ub: ok = False
    return NumericCertificate("grid_upper_bound", f"f(x)<={claimed_upper} on [{a},{b}]", ok,
        {"a":str(a),"b":str(b),"n":n,"worst":mp.nstr(worst_val,30),"margin":mp.nstr(ub-worst_val,30),"dps":dps})

def write_certificate_json(path, cert):
    import json; path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(cert.to_dict(), ensure_ascii=False, indent=2), encoding="utf-8")
