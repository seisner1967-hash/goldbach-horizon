"""Independent integer/rational checker DRAFT SOURCE; not imported or run.

Checks every emitted node and arithmetic integer, actual four-budget folding,
closed tail formulas, guards, final interval decisions and mandatory mutants.
It does NOT replay transcendental evaluations or prove their analytic rest
formulas; source review and future Lean are separate duties. A structural PASS
cannot manufacture an analytic enclosure or H1 theorem from arbitrary boxes.
No producer, dyadic module, analytic evaluator or historic output is imported.
"""
import json
from fractions import Fraction as F

S = 1 << 512
EPS = F(1, S)


def decimal_integer(value):
    if type(value) is not str or not value or len(value)>2048:
        raise ValueError("bounded exact decimal integer string required")
    digits = value[1:] if value[0]=="-" else value
    if not digits or any(c not in "0123456789" for c in digits):
        raise ValueError("invalid exact decimal integer string")
    return int(value)


def rational(item):
    n, d = decimal_integer(item["numerator"]), decimal_integer(item["denominator"])
    if d <= 0:
        raise ValueError("nonpositive rational denominator")
    return F(n, d)


def interval(item):
    lo, hi, denominator = map(decimal_integer, (item["lo_integer"], item["hi_integer"], item["denominator"]))
    if denominator != S or lo > hi:
        raise ValueError("invalid512 dyadic interval")
    return lo, hi


def ceil(q):
    return -((-q.numerator)//q.denominator)


def add(a, b):
    return a[0]+b[0], a[1]+b[1]


def subtract(a, b):
    return a[0]-b[1], a[1]-b[0]


def widen(a, radius):
    step = ceil(radius*S)
    return a[0]-step, a[1]+step


def overlap(a, b):
    return max(a[0], b[0]) <= min(a[1], b[1])


def point_and_radius(data):
    real,imag = interval(data["real"]),interval(data["imag"])
    pr,pi = (real[0]+real[1])//2,(imag[0]+imag[1])//2
    radius = F(max(pr-real[0],real[1]-pr)+max(pi-imag[0],imag[1]-pi),S)
    return pr,pi,radius


def catalogue_geometry(result):
    geometry = {}
    for kind,m in (("vertical",128),("arch",96)):
        catalogue = result["catalogue"][kind]
        if len(catalogue)!=m or [item["j"] for item in catalogue]!=list(range(m)):
            raise ValueError("complete roots/weights catalogue required")
        for item in catalogue:
            cr,ci,rho = point_and_radius(item["circle_box"])
            wr,wi,rw = point_and_radius(item["weight_box"])
            if rho>F(1,1<<200) or rw>F(1,1<<200):
                raise ValueError("constructed circle/weight guard failed")
            geometry[kind,item["j"]]=(cr,ci,rho,wr,wi,rw)
    length = interval(result["arch_diagnostics"]["logR"])
    if not 12*S<length[0]<=length[1]<16*S:
        raise ValueError("complete logR domain failed")
    mid = F(length[0]+length[1],2*S)
    rho_length = max(mid-F(length[0],S),F(length[1],S)-mid)
    if rational(result["arch_diagnostics"]["logR_midpoint"])!=mid or rational(result["arch_diagnostics"]["logR_radius"])!=rho_length:
        raise ValueError("actual logR midpoint/radius mismatch")
    return geometry,rho_length


def verify_sample_geometry(record, geometry, rho_length):
    key = record["key"]
    kind,j = key[0],key[2] if key[0]=="vertical" else key[2]
    _,_,rho,wr,wi,rw = geometry[kind,j]
    pr,pi,rf = point_and_radius(record["evaluation_box"])
    if (decimal_integer(record["point_real"]),decimal_integer(record["point_imag"]))!=(pr,pi) or rational(record["E_function"])!=rf:
        raise ValueError("function radius not derived from the actual evaluation box")
    if kind=="vertical":
        w = 1024*10000*10000+32*100+2560
        rp = F(ceil(8*w*rho*S),S)
        if key[1]=="left":
            wr,wi = -wr,-wi
    else:
        wa = 128*10000+F(32,10000)+32
        rp = F(ceil(16*wa*(rho+F(2*key[1]+1,256)*rho_length)*S),S)
        rw = F(ceil((rw+rho_length/F(96*96))*S),S)
    if rational(record["E_position"])!=rp or rational(record["E_weight"])!=rw or (decimal_integer(record["weight_real"]),decimal_integer(record["weight_imag"]))!=(wr,wi):
        raise ValueError("position/weight budgets not derived from catalogue enclosures")


def closed_errors():
    y, t, x = 10000, 100, 1000000
    a128 = F(1, 2)**128/(1-F(1, 2)**128)
    a96 = F(1, 2)**96/(1-F(1, 2)**96)
    w = 1024*y*y+32*t+2560
    wa = 128*y+F(32, y)+32
    return dict(E_vert=F(3, 8)**75/3*(32000000*(F(4*(t+2),3)+F(16,9))
                                            +F(8,100)*(F(4*(t+8),3)+F(16,9))),
                E_quad=F(2*t,3)*w*(F(1,3)**65/(1-F(1,3))+a128/(1-F(1,3))),
                E_prim=F(3,8)**100*((x+y)*16+y+F(2*y*y,x)),
                E_dual=F(17,y*x),
                E_arch=F(4,3)*(F(3,8)**100+F(1,2*y*x*x)+F(2,y*x)),
                E_quad_arch=16*wa*(F(1,4)**33/(1-F(1,4))+a96/(1-F(1,4))))


class Fold:
    def __init__(self):
        self.real = self.imag = self.nodes = 0
        self.function = self.position = self.weights = self.accumulation = F(0)

    def add(self, record):
        pr, pi = decimal_integer(record["point_real"]), decimal_integer(record["point_imag"])
        wr, wi = decimal_integer(record["weight_real"]), decimal_integer(record["weight_imag"])
        rf, rp, rw = map(rational, (record["E_function"],record["E_position"],record["E_weight"]))
        if min(rf,rp,rw) < 0 or rf > F(1,1<<81) or rp > F(1,1<<81):
            raise ValueError("invalid actual node error guard")
        raw_real, raw_imag = pr*wr-pi*wi, pr*wi+pi*wr
        real, imag = (raw_real+S//2)//S, (raw_imag+S//2)//S
        rounding = F(abs(raw_real-real*S)+abs(raw_imag-imag*S),S*S)
        if rounding > 2*EPS:
            raise ValueError("point product round certificate failed")
        self.real += real
        self.imag += imag
        self.function += (F(abs(wr)+abs(wi),S)+rw)*rf
        self.position += (F(abs(wr)+abs(wi),S)+rw)*rp
        self.weights += F(abs(pr)+abs(pi),S)*rw
        self.accumulation += rounding
        self.nodes += 1

    def error(self):
        return self.function+self.position+self.weights+self.accumulation

    def verify_result(self, data, enclosure, count):
        if self.nodes != count or data["nodes"] != count:
            raise ValueError("incomplete node count")
        for key, actual in (("E_function",self.function),("E_position",self.position),
                            ("E_weights",self.weights),("E_accumulation",self.accumulation)):
            if rational(data[key]) != actual:
                raise ValueError("four-budget sum mismatch:"+key)
        if interval(data["point"]["real"]) != (self.real,self.real) or interval(data["point"]["imag"]) != (self.imag,self.imag):
            raise ValueError("actual integrated point mismatch")
        if interval(enclosure["real"]) != widen((self.real,self.real),self.error()) or interval(enclosure["imag"]) != widen((self.imag,self.imag),self.error()):
            raise ValueError("actual integrated enclosure mismatch")
        if self.weights > F(1,1<<72) or self.accumulation > F(1,1<<72):
            raise ValueError("weight/accumulation efficiency guard exceeded")


def exact_prime(p):
    if type(p) is not int or p < 2:
        return False
    if p == 2:
        return True
    if p%2 == 0:
        return False
    d = 3
    while d*d <= p:
        if p%d == 0:
            return False
        d += 2
    return True


def verify_arithmetic_stream(path, expected):
    n, seen, pp, proper, composite = 2, set(), 0, 0, 0
    four_seen = False
    with path.open(encoding="utf-8") as source:
        for line in source:
            record = json.loads(line)
            if record["n"] != n or n > 1000000:
                raise ValueError("arithmetic stream order/completeness failed")
            p,e,r = record["p"],record["exponent"],record["cofactor"]
            if any(type(k) is not int for k in (p,e,r)) or e<1 or r<1:
                raise ValueError("invalid exact factor witness")
            if p not in seen:
                if not exact_prime(p):
                    raise ValueError("new prime certificate failed")
                seen.add(p)
            if p**e*r != n or r%p == 0:
                raise ValueError("prime-power product/coprimality failed")
            mask = r == 1
            if record["is_prime_power"] != mask or record["proper_prime_power"] != (mask and e>=2):
                raise ValueError("exact prime-power mask failed")
            if n == 4:
                four_seen = (p,e,r)==(2,2,1)
            pp += mask
            proper += mask and e>=2
            composite += not mask
            n += 1
    if n != 1000001 or not four_seen:
        raise ValueError("missing exact integer/four certificate")
    actual = dict(all_integers_before_mask=999999, prime_power_count=pp,
                  proper_prime_power_count=proper, ordinary_composite_count=composite,
                  prime_certificates=len(seen),old_prime_table_used=False)
    if actual != expected:
        raise ValueError("arithmetic count certificate mismatch")


def expected_keys():
    for side in ("right","left"):
        for j in range(128):
            for k in range(800):
                yield ["vertical",side,j,k]
    for k in range(128):
        for j in range(96):
            yield ["arch",k,j]


def verify_global_source(output_dir):
    """Future structural invocation only; caller binds reviewed source bytes."""
    from pathlib import Path
    output_dir = Path(output_dir)
    with (output_dir/"global_thermal_result.json").open(encoding="utf-8") as source:
        result = json.load(source)
    if result["schema"] != "GLOBAL_THERMAL_H1_SOURCE_22" or result["parameters"] != dict(N=100000000,Y=10000,T=100,X=1000000,Q=1000000,R=1000000):
        raise ValueError("fixed thermal catalogue changed")
    trace,arch = Fold(),Fold()
    geometry,rho_length = catalogue_geometry(result)
    keys = iter(expected_keys())
    with (output_dir/"new_nodes.ndjson").open(encoding="utf-8") as source:
        for line in source:
            record = json.loads(line)
            key = next(keys,None)
            if key is None or record["key"] != key:
                raise ValueError("missing/reordered/repeated functional node")
            verify_sample_geometry(record,geometry,rho_length)
            (trace if key[0]=="vertical" else arch).add(record)
    if next(keys,None) is not None:
        raise ValueError("incomplete functional catalogue")
    trace.verify_result(result["four_budgets_trace"],result["trace"],204800)
    arch.verify_result(result["four_budgets_arch"],result["arch"],12288)
    if result["complete_vertical_nodes"]!=204800 or result["complete_arch_nodes"]!=12288:
        raise ValueError("reported functional catalogue count mismatch")
    if result["analytic_counts"]!=dict(em=204800,gamma=204800,psi=1,arch=12288,direct_power=32512):
        raise ValueError("actual analytic counter catalogue mismatch")
    if result["trace_diagnostics"]["seed_tracks"]!=32768 or result["trace_diagnostics"]["actual_track_advances"]!=26181632:
        raise ValueError("actual transport catalogue count mismatch")
    verify_arithmetic_stream(output_dir/"new_arithmetic.ndjson",result["arithmetic_stream"])
    finite,cterm = interval(result["finite_arithmetic"]),interval(result["constants_term"])
    if F(finite[1]-finite[0],S)>F(1,1<<50) or F(cterm[1]-cterm[0],S)>F(1,1<<50):
        raise ValueError("arithmetic/constants actual widths too large")
    errors = closed_errors()
    errors.update(E_arithmetic_round=F(finite[1]-finite[0],S),
                  E_constants_round=F(cterm[1]-cterm[0],S),
                  E_actual_trace=trace.error(),E_actual_arch=arch.error(),E_final_grid=8*EPS)
    if set(errors) != set(result["errors"]) or any(rational(result["errors"][k])!=v for k,v in errors.items()):
        raise ValueError("observed/free error inserted or closed formula changed")
    total = sum(errors.values(),F(0))
    if rational(result["E_total"])!=total or total>=F(1,100000000) or rational(result["tau"])!=F(1,1000000):
        raise ValueError("actual total envelope guard failed")
    lhs = add(finite,(0,ceil((errors["E_prim"]+errors["E_dual"])*S)))
    rhs = subtract(subtract(subtract((10001*S,10001*S),
                   widen(interval(result["trace"]["real"]),errors["E_vert"]+errors["E_quad"])),cterm),
                   widen(interval(result["arch"]["real"]),errors["E_arch"]+errors["E_quad_arch"]))
    if interval(result["lhs"])!=lhs or interval(result["rhs"])!=rhs or interval(result["residual"])!=subtract(lhs,rhs):
        raise ValueError("H1 sign/mode/residual mismatch")
    four = interval(result["primal_four"])
    if F(four[0],S)<=F(1,10000):
        raise ValueError("constructed primal4 bound is not informative")
    mutants = dict(omit_Y=(lhs,subtract(rhs,(10000*S,10000*S))),
                   omit_one=(lhs,subtract(rhs,(S,S))),remove_primal_four=(subtract(lhs,four),rhs))
    if set(result["mutants"])!=set(mutants):
        raise ValueError("mandatory mutant catalogue mismatch")
    informative = True
    for name,(a,b) in mutants.items():
        mutant = result["mutants"][name]
        decision = not overlap(a,b)
        if interval(mutant["lhs"])!=a or interval(mutant["rhs"])!=b or mutant["disjoint"]!=decision:
            raise ValueError("independent mutation decision mismatch")
        informative = informative and decision
    imaginary = all(interval(result[k]["imag"])[0]<=0<=interval(result[k]["imag"])[1] for k in ("trace","arch"))
    residual = subtract(lhs,rhs)
    agreement = overlap(lhs,rhs) and F(max(abs(residual[0]),abs(residual[1])),S)<=F(1,1000000)
    status = ("THERMAL_TRACE_NUMERIC_AGREEMENT" if agreement and imaginary and informative
              else "ENCLOSURE_CONFLICT" if not overlap(lhs,rhs) or not imaginary else "NON_DISCRIMINATING")
    if result["status"]!=status or result["WIN"] is not False or result["old_bank_replays"]!=0 or result["old_output_inputs"]!=0:
        raise ValueError("scope/status/oracle violation")
    for key,value in (("CONTOUR_BOUNDARY","UNIMPLEMENTED"),("FINITE_ZERO_TRACE","OPEN"),
                      ("H1_FORMAL","OPEN"),("COEFFICIENT_N","OPEN"),("D_N","UNPAID")):
        if result[key]!=value:
            raise ValueError("unpaid scope promoted:"+key)
    return dict(structural_checker_PASS=True, numerical_decision=status,
                functional_nodes_verified=217088, arithmetic_integers_verified=999999,
                primitives_recomputed=False, analytic_remainders_formalized=False,
                H1_FORMAL=False,COEFFICIENT_N=False,D_N=False,WIN=False)
