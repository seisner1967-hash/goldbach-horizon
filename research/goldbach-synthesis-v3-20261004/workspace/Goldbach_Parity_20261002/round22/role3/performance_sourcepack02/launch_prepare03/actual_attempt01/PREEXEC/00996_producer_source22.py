"""Complete fixed thermal H1 producer DRAFT SOURCE; no invocation is authorized.

Distinct performance-sourcepack02 dependencies: dyadic/analytic/transport
preserve exact endpoints and envelopes. No closed result is imported.
The selected left-side route is direct EM of the true zeta and its derivative;
division must certify a nonzero denominator. No finite-difference derivative.
The horizontal rectangle is deliberately a separate unimplemented volet.
"""
import json
from pathlib import Path
from fractions import Fraction as F
from dyadic_r01 import (Box, CBox, Point, EPS, SCALE, pow2, pi_box,
                       exp_box, log_box, rational_json)
from dyadic_r01 import COUNTERS as PRIMITIVE_COUNTERS
from analytic_r01 import (COUNTERS, a_log_derivative, gamma_box,
                          arch_integrand, euler_constant_box, f1_box,
                          PERFORMANCE_COUNTERS)
from kernel_r01 import (kernel_catalogue, FourBudgets, grid_radius)
from arithmetic_catalogue_source22 import (new_finite_arithmetic_side,
                                           check_new_arithmetic_stream)
from transport_catalogue_source22 import (start_point, em_power_track,
                                         thermal_y_track)
from envelopes_source22 import (N, Y, T, X, Q, R, TAU, W, W_ARCH,
                                analytic_envelopes)


def _record_sample(write, key, value, point, function, position, weight, weight_radius):
    write(dict(key=key, point_real=str(point.real), point_imag=str(point.imag),
               weight_real=str(weight.real), weight_imag=str(weight.imag),
               evaluation_box=value.as_json(),
               E_function=rational_json(function), E_position=rational_json(position),
               E_weight=rational_json(weight_radius)))


def _add_sample(total, value, position, weight, weight_radius, key, write):
    point, function = Point.from_box(value)
    position = grid_radius(position)
    if function > pow2(-81) or position > pow2(-81):
        raise ArithmeticError("constructed nodal function/position efficiency guard failed")
    total.add(point, function, position, weight, weight_radius)
    _record_sample(write, key, value, point, function, position, weight, weight_radius)


def _catalogue_data(catalogue):
    return [dict(j=item["j"], circle_box=item["node"][2].as_json(),
                 weight_box=item["weight"][2].as_json()) for item in catalogue]


def _complete_budget_guard(total, count):
    if total.nodes != count:
        raise ArithmeticError("incomplete integrated node catalogue")
    if total.weights > pow2(-72) or total.accumulation > pow2(-72):
        raise ArithmeticError("actual weight/accumulation efficiency guard failed")


def new_vertical_trace(write_node, progress):
    catalogue = kernel_catalogue(128, F(3, 16), F(1, 8), 64, True)
    total = FourBudgets()
    seeds = transports = 0
    max_transport = F(0)
    for side, sign, label in ((F(3, 2), 1, "right"), (F(-1, 2), -1, "left")):
        for item in catalogue:
            j = item["j"]
            node, rho, _ = item["node"]
            weight, weight_error, _ = item["weight"]
            if sign < 0:
                weight = -weight
            s0 = start_point(side, node)
            tracks = {n: em_power_track(n, s0, label, j) for n in range(2, 129)}
            ytrack = thermal_y_track(s0, label, j)
            seeds += 128
            for k in range(800):
                s = s0+CBox.exact(0, F(k, 4))
                powers = {n: tracks[n].box() for n in range(2, 129)}
                factor = a_log_derivative(s, powers)
                value = ytrack.box()*gamma_box(s+CBox.exact(1))*factor
                # Cauchy derivative on the outer3/8 disc, inner3/16 plus
                # rho<2^-200 leaves more than1/8: norm derivative <=8W.
                _add_sample(total, value, 8*W*rho, weight, weight_error,
                            ["vertical", label, j, k], write_node)
                if k != 799:
                    for track in tracks.values():
                        track.advance()
                    ytrack.advance()
                    transports += 128
            if any(track.index != 799 for track in tracks.values()) or ytrack.index != 799:
                raise ArithmeticError("EM/Y transport endpoint not complete")
            max_transport = max(max_transport, ytrack.radius,
                                *(track.radius for track in tracks.values()))
            progress(dict(volet="vertical", side=label, circle=j,
                          nodes=total.nodes, catalogue_fraction=[total.nodes, 204800]))
    _complete_budget_guard(total, 204800)
    return total, dict(seed_tracks=seeds, actual_track_advances=transports,
                       max_transport_radius=rational_json(max_transport),
                       selected_left_route="DIRECT_EM_TRUE_ZETA", old_values_used=False,
                       radius_transport="INTEGER_GRID_EXACT_SAME_ENVELOPE"), _catalogue_data(catalogue)


def new_arch_integral(write_node, progress):
    length = log_box(Box.rational(R))
    if not 12 < length.lower() <= length.upper() < 16:
        raise ArithmeticError("constructed logR catalogue domain failed")
    midpoint = length.midpoint()
    rho_length = max(midpoint-length.lower(), length.upper()-midpoint)
    catalogue = kernel_catalogue(96, F(1, 8), midpoint/256, 32, False)
    total = FourBudgets()
    for k in range(128):
        centre = F(2*k+1, 256)*midpoint
        for item in catalogue:
            j = item["j"]
            node, rho, _ = item["node"]
            weight, weight_error, _ = item["weight"]
            u = node.box()+CBox.exact(centre)
            value = arch_integrand(u)
            # Exact centre is(2k+1)*logR/256. The true halfwidth islogR/256.
            # For the integrated real kernel, |dw_j/dlogR|<=1/(96*m), m=96,
            # from r/Rc<=1/2 and the sum of the even geometric series.
            actual_weight_error = grid_radius(weight_error+rho_length/F(96*96))
            position = 16*W_ARCH*(rho+F(2*k+1, 256)*rho_length)
            _add_sample(total, value, position, weight, actual_weight_error,
                        ["arch", k, j], write_node)
        progress(dict(volet="arch", cell=k, nodes=total.nodes,
                      catalogue_fraction=[total.nodes, 12288]))
    _complete_budget_guard(total, 12288)
    return total, dict(logR=length.as_json(), logR_midpoint=rational_json(midpoint),
                       logR_radius=rational_json(rho_length),
                       true_endpoint_and_width_paid=True, old_values_used=False), _catalogue_data(catalogue)


def _overlap(a, b):
    return max(a.lo, b.lo) <= min(a.hi, b.hi)


def new_global_thermal_source(output_dir, progress=None):
    """Future single invocation; no implicit run at import or file creation.

    Creates new certificate and node streams with exclusive-create mode.
    Caller must provide a new directory after byte-bound gate. Exceptions are
    source/evaluator failures, never a counterexample to Goldbach. A launcher,
    independent review, and finite-interval checker are still gate obligations.
    """
    if (type(N) is not int or N != 100000000 or type(Y) is not int
            or Y != 10000 or Y * Y != N):
        raise ArithmeticError("actual fixed N=10^8, Y^2=N thermal contract required")
    if (any(COUNTERS.values()) or any(PRIMITIVE_COUNTERS.values())
            or any(PERFORMANCE_COUNTERS.values())):
        raise ArithmeticError("fresh interpreter required; old analytic work detected")
    output_dir = Path(output_dir)
    if not output_dir.is_dir():
        raise ValueError("gate-created new output directory required")
    progress = progress or (lambda record: None)
    nodes_path = output_dir/"new_nodes.ndjson"
    certificates_path = output_dir/"new_arithmetic.ndjson"
    with nodes_path.open("x", encoding="utf-8") as nodes:
        def write_node(record):
            nodes.write(json.dumps(record, separators=(",", ":"))+"\n")
        trace, trace_diagnostics, trace_catalogue = new_vertical_trace(write_node, progress)
        arch, arch_diagnostics, arch_catalogue = new_arch_integral(write_node, progress)
    with certificates_path.open("x", encoding="utf-8") as certificates:
        def write_certificate(record):
            certificates.write(json.dumps(record, separators=(",", ":"))+"\n")
        arithmetic = new_finite_arithmetic_side(write_certificate, progress)
    with certificates_path.open(encoding="utf-8") as certificates:
        arithmetic_stream = check_new_arithmetic_stream(json.loads(line) for line in certificates)
    if arithmetic["combined"].width() > pow2(-50):
        raise ArithmeticError("actual arithmetic total width guard failed")
    # Explicitly primal4 from this new invocation; proper powers in the full
    # stream remain untouched. The old combined-four field is not the mutant.
    four_primal = arithmetic["primal_four"]
    if four_primal.lower() <= F(1, Y):
        raise ArithmeticError("primal4 mutation lower bound not constructed")
    f1 = f1_box(Y)
    constant = log_box(pi_box().scale(4))+euler_constant_box()
    constant_term = constant*f1
    expected_performance_counts = dict(half_log_two_pi_constructions=1,
                                      f1_constructions=1, gamma_value_only=204800)
    if PERFORMANCE_COUNTERS != expected_performance_counts:
        raise ArithmeticError("fresh fixed-catalogue cache/call guards failed")
    if constant_term.width() > pow2(-50):
        raise ArithmeticError("actual constant product width guard failed")
    errors = analytic_envelopes()
    # Positive arithmetic tails; signed contour and Arch tails.
    positive_tail = Box.rational(errors["E_prim"]+errors["E_dual"])
    lhs = arithmetic["combined"]+Box(0, positive_tail.hi)
    jt = trace.enclosure()
    arch_value = arch.enclosure()
    rhs = (Box.rational(1+Y)-jt.real.widen(errors["E_vert"]+errors["E_quad"])
           -constant_term-arch_value.real.widen(errors["E_arch"]+errors["E_quad_arch"]))
    errors.update(E_arithmetic_round=arithmetic["combined"].width(),
                  E_constants_round=constant_term.width(),
                  E_actual_trace=trace.error(), E_actual_arch=arch.error(),
                  E_final_grid=8*EPS)
    total_error = sum(errors.values(), F(0))
    if total_error >= F(1, 100000000):
        raise ArithmeticError("constructed total envelope is not informative")
    mutants = dict(omit_Y=(lhs, rhs-Box.rational(Y)),
                   omit_one=(lhs, rhs-Box.rational(1)),
                   remove_primal_four=(lhs-four_primal, rhs))
    disjoint = {name: not _overlap(a, b) for name, (a, b) in mutants.items()}
    residual = lhs-rhs
    agrees = _overlap(lhs, rhs) and residual.abs_upper() <= TAU
    imaginary_compatible = (jt.imag.lo <= 0 <= jt.imag.hi and
                            arch_value.imag.lo <= 0 <= arch_value.imag.hi)
    status = ("THERMAL_TRACE_NUMERIC_AGREEMENT" if agrees and imaginary_compatible and all(disjoint.values())
              else "ENCLOSURE_CONFLICT" if not _overlap(lhs, rhs) or not imaginary_compatible
              else "NON_DISCRIMINATING")
    result = dict(schema="GLOBAL_THERMAL_H1_SOURCE_22", parameters=dict(N=N,Y=Y,T=T,X=X,Q=Q,R=R),
                  status=status, lhs=lhs.as_json(), rhs=rhs.as_json(), residual=residual.as_json(),
                  finite_arithmetic=arithmetic["combined"].as_json(), primal_four=four_primal.as_json(),
                  trace=jt.as_json(), arch=arch_value.as_json(), constants_term=constant_term.as_json(),
                  errors={k:rational_json(v) for k,v in errors.items()}, E_total=rational_json(total_error),
                  tau=rational_json(TAU), four_budgets_trace=trace.as_json(), four_budgets_arch=arch.as_json(),
                  trace_diagnostics=trace_diagnostics, arch_diagnostics=arch_diagnostics,
                  catalogue=dict(vertical=trace_catalogue,arch=arch_catalogue),
                  arithmetic_stream=arithmetic_stream, analytic_counts=dict(COUNTERS),
                  primitive_counts=dict(PRIMITIVE_COUNTERS),
                  performance_counts=dict(PERFORMANCE_COUNTERS),
                  performance_source_packet="SOURCEPACK02_EXACT_ENDPOINTS_AND_ENVELOPES",
                  mutants={k:dict(lhs=a.as_json(),rhs=b.as_json(),disjoint=disjoint[k]) for k,(a,b) in mutants.items()},
                  complete_vertical_nodes=204800, complete_arch_nodes=12288,
                  CONTOUR_BOUNDARY="UNIMPLEMENTED", FINITE_ZERO_TRACE="OPEN",
                  H1_FORMAL="OPEN", COEFFICIENT_N="OPEN", D_N="UNPAID", WIN=False,
                  old_bank_replays=0, old_output_inputs=0)
    with (output_dir/"global_thermal_result.json").open("x", encoding="utf-8") as target:
        json.dump(result, target, indent=2, sort_keys=True)
    return result
