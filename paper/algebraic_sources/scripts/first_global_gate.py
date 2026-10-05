#!/usr/bin/env python3
"""Bounded first-even-N gate producer; independent Judge replay is required.

SOURCE ONLY until a separately reviewed authorization binds this exact source.
No generator/checker from an earlier gate is imported. All proof arithmetic is
integer Boolean evaluation, hence exact over Q. This does not search multipliers.
"""
import argparse
import datetime
import hashlib
import json
from math import isqrt, prod
from pathlib import Path
import sys
import time


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "evidence" / "first_global_gate_v1"
MIN_N, MAX_N, STEP = 4, 30, 2
FAMILIES = (
    "COARSE_PARITY", "SIEVE_ONLY", "SIEVE_DYADIC_BERTRAND",
    "BERTRAND_COARSE", "FULL_BERTRAND_SIEVE",
    "FACTOR_COVERAGE_BERTRAND_SIEVE", "PROPER_BERTRAND_ONLY",
)
LIMITS = {"wall_seconds": 180, "search_nodes": 250000,
          "RUP_additions": 250000, "clause_visits": 50000000}
AUTHORIZATION_MARKER = "EXECUTE_FIRST_GLOBAL_GATE_V1"


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def json_bytes(value):
    return (json.dumps(value, indent=2, allow_nan=False) + "\n").encode("utf-8")


def save_new(path, raw):
    # This exclusive mode never replaces old evidence or an earlier attempt.
    with path.open("xb") as stream:
        stream.write(raw)
    return {"path": path.relative_to(ROOT).as_posix(),
            "sha256": digest(raw), "bytes": len(raw)}


def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def family_spec(family, n):
    require(family in FAMILIES, "Unknown original family")
    require(MIN_N <= n <= MAX_N and n % 2 == 0, "Outside reviewed domain")
    sieve = family in ("SIEVE_ONLY", "SIEVE_DYADIC_BERTRAND",
                       "FULL_BERTRAND_SIEVE", "FACTOR_COVERAGE_BERTRAND_SIEVE")
    coarse = family in ("COARSE_PARITY", "BERTRAND_COARSE")
    constraints, zero_slots = [], []
    for i in range(n + 1):
        forbidden = (sieve and not prime(i)) or (coarse and
                     (i in (0, 1) or (i > 2 and i % 2 == 0)))
        if forbidden:
            constraints.append({"kind": "zero_coordinate", "coordinate": i})
        elif coarse:
            # The actual Lean coarseConstraint has an identically-zero slot here.
            zero_slots.append(i)
    if family == "SIEVE_DYADIC_BERTRAND":
        constraints.append({"kind": "one_coordinate", "coordinate": 2,
                            "guard": "DIRECT_PRIME_COORDINATE_PIN_X2"})
        j = 1
        while 2 ** (j + 1) <= n:
            constraints.append({"kind": "nonempty_product", "index_kind": "dyadic",
                                "index": j, "lower_open": 2 ** j,
                                "upper_open": 2 ** (j + 1),
                                "coordinates": list(range(2 ** j + 1, 2 ** (j + 1)))})
            j += 1
    if family in ("BERTRAND_COARSE", "FULL_BERTRAND_SIEVE",
                  "FACTOR_COVERAGE_BERTRAND_SIEVE", "PROPER_BERTRAND_ONLY"):
        first_m = 2 if family == "PROPER_BERTRAND_ONLY" else 1
        for m in range(first_m, n // 2 + 1):
            constraints.append({"kind": "nonempty_product", "index_kind": "Bertrand",
                                "index": m, "lower_open": m, "upper_closed": 2 * m,
                                "coordinates": list(range(m + 1, 2 * m + 1))})
    if family == "FACTOR_COVERAGE_BERTRAND_SIEVE":
        for m in range(2, n + 1):
            if not prime(m):
                constraints.append({"kind": "nonempty_product", "index_kind": "factor",
                                    "index": m,
                                    "coordinates": [d for d in range(2, m) if m % d == 0]})
    return {"family": family, "N": n, "SIEVE": sieve, "coarse": coarse,
            "constraints": constraints, "identically_zero_coarse_slots": zero_slots,
            "uniform_constants": [0, 1, -1],
            "guard_notes": {
                "explicit_X2_pin": family == "SIEVE_DYADIC_BERTRAND",
                "m1_interval_pins_X2": family in ("BERTRAND_COARSE", "FULL_BERTRAND_SIEVE",
                                                   "FACTOR_COVERAGE_BERTRAND_SIEVE"),
                "factor_square_instances_pin_small_prime_coordinates":
                    family == "FACTOR_COVERAGE_BERTRAND_SIEVE"}}


def family_clauses(spec):
    clauses = []
    for constraint in spec["constraints"]:
        kind = constraint["kind"]
        if kind == "zero_coordinate":
            clauses.append([-(constraint["coordinate"] + 1)])
        elif kind == "one_coordinate":
            clauses.append([constraint["coordinate"] + 1])
        elif kind == "nonempty_product":
            clauses.append([i + 1 for i in constraint["coordinates"]])
        else:
            raise RuntimeError("Unknown polynomial kind")
    return clauses


def ordered_g_clauses(n):
    # Keep N+1 ordered terms. Off-diagonal duplicate clauses are intentional.
    return [[-(i + 1)] if i == n - i else [-(i + 1), -(n - i + 1)]
            for i in range(n + 1)]


def dimacs(n, clauses, description):
    require(all(len(set(c)) == len(c) for c in clauses), "Duplicate literal in clause")
    require(all(1 <= abs(lit) <= n + 1 for c in clauses for lit in c), "Invalid variable")
    lines = ["c " + description, "c variable i+1 is coordinate X_i",
             f"p cnf {n + 1} {len(clauses)}"]
    lines.extend(" ".join(map(str, c)) + (" 0" if c else "0") for c in clauses)
    return ("\n".join(lines) + "\n").encode("ascii")


def cnf_model(clauses, bits):
    return all(any(bits[abs(lit) - 1] == int(lit > 0) for lit in c) for c in clauses)


def polynomial_replay(spec, bits):
    n = spec["N"]
    require(len(bits) == n + 1 and all(type(b) is int and b in (0, 1) for b in bits),
            "Invalid Boolean vector")
    booleans = [b * b - b for b in bits]
    family_values = []
    for constraint in spec["constraints"]:
        kind = constraint["kind"]
        if kind == "zero_coordinate":
            value = bits[constraint["coordinate"]]
        elif kind == "one_coordinate":
            value = bits[constraint["coordinate"]] - 1
        else:
            require(kind == "nonempty_product", "Unknown direct polynomial kind")
            value = prod(1 - bits[i] for i in constraint["coordinates"])
        family_values.append(value)
    require(all(v == 0 for v in booleans + family_values), "Nonzero family polynomial")
    ordered_terms = [bits[i] * bits[n - i] for i in range(n + 1)]
    return {"boolean_polynomial_values": booleans, "family_polynomial_values": family_values,
            "identically_zero_coarse_values": [0] * len(spec["identically_zero_coarse_slots"]),
            "ordered_g_terms": ordered_terms, "g_integer_over_Q": sum(ordered_terms)}


class BoundedStop(Exception):
    pass


class Budget:
    def __init__(self):
        self.start = time.monotonic()
        self.nodes = self.additions = self.visits = 0

    def poll(self):
        if time.monotonic() - self.start > LIMITS["wall_seconds"]:
            raise BoundedStop("wall_seconds")
        if self.nodes > LIMITS["search_nodes"]:
            raise BoundedStop("search_nodes")
        if self.additions > LIMITS["RUP_additions"]:
            raise BoundedStop("RUP_additions")
        if self.visits > LIMITS["clause_visits"]:
            raise BoundedStop("clause_visits")

    def snapshot(self):
        return {"elapsed_seconds_metadata_only": time.monotonic() - self.start,
                "search_nodes": self.nodes, "RUP_additions": self.additions,
                "clause_visits": self.visits}


def propagate(clauses, assumptions, budget):
    assignment = {}
    for lit in assumptions:
        var, value = abs(lit), lit > 0
        if var in assignment and assignment[var] != value:
            return None
        assignment[var] = value
    while True:
        changed = False
        for clause in clauses:
            budget.visits += 1
            budget.poll()
            if any(abs(lit) in assignment and assignment[abs(lit)] == (lit > 0)
                   for lit in clause):
                continue
            unknown = [lit for lit in clause if abs(lit) not in assignment]
            if not unknown:
                return None
            if len(unknown) == 1:
                lit = unknown[0]
                assignment[abs(lit)] = lit > 0
                changed = True
        if not changed:
            return assignment


def solve(n, original_clauses, budget):
    clauses = [c[:] for c in original_clauses]
    additions = []
    initial_nodes = budget.nodes

    def learn(decisions):
        addition = [-lit for lit in decisions]
        # The negation of this clause is exactly the branch's decisions.
        require(propagate(clauses, [-lit for lit in addition], budget) is None,
                "Producer failed to derive a literal RUP addition")
        budget.additions += 1
        budget.poll()
        clauses.append(addition)
        additions.append(addition)

    def visit(decisions):
        budget.nodes += 1
        budget.poll()
        assignment = propagate(clauses, decisions, budget)
        if assignment is None:
            learn(decisions)
            return None
        unresolved = [c for c in clauses if not any(abs(lit) in assignment and
                      assignment[abs(lit)] == (lit > 0) for lit in c)]
        if not unresolved:
            bits = [int(assignment.get(i + 1, False)) for i in range(n + 1)]
            require(cnf_model(original_clauses, bits), "Producer SAT model failed exact CNF replay")
            return bits
        clause = min(unresolved, key=lambda c: sum(abs(lit) not in assignment for lit in c))
        variable = next(abs(lit) for lit in clause if abs(lit) not in assignment)
        for decision in (-variable, variable):
            model = visit(decisions + [decision])
            if model is not None:
                return model
        learn(decisions)
        return None

    model = visit([])
    if model is None:
        require(bool(additions) and additions[-1] == [], "Missing terminal empty RUP clause")
    return {"result": "SAT" if model is not None else "UNSAT_WITH_LITERAL_RUP_DRAT",
            "model": model, "additions": additions, "search_nodes": budget.nodes - initial_nodes}


def proof_bytes(additions):
    return ("\n".join(" ".join(map(str, c)) + (" 0" if c else "0")
                     for c in additions) + "\n").encode("ascii")


def run_case(family, n, budget):
    spec = family_spec(family, n)
    f_clauses = family_clauses(spec)
    g_clauses = ordered_g_clauses(n)
    a = [int(prime(i)) for i in range(n + 1)]
    a_replay = polynomial_replay(spec, a)
    require(cnf_model(f_clauses, a), "True prime vector is not a family CNF model")
    stem = f"{family}_N{n}"
    full = f_clauses + g_clauses
    full_binding = save_new(OUT / (stem + ".cnf"), dimacs(n, full, "ordered g_N=0 gate"))
    gate = solve(n, full, budget)
    row = {"family": family, "N": n, "variables": n + 1,
           "family_constraint_count": len(f_clauses), "ordered_g_clause_count": n + 1,
           "full_clause_count": len(full), "full_CNF": full_binding,
           "specification": spec, "prime_indicator_a": a,
           "prime_point_replay_without_g": a_replay, "pseudo_gate_result": gate["result"],
           "pseudo_search_nodes": gate["search_nodes"], "pseudo_proof": None}
    if gate["model"] is None:
        row["pseudo_proof"] = {**save_new(OUT / (stem + ".drat"), proof_bytes(gate["additions"])),
                               "format": "DRAT additions, every addition RUP; no deletions",
                               "addition_count": len(gate["additions"])}
    else:
        b = gate["model"]
        replay = polynomial_replay(spec, b)
        require(replay["g_integer_over_Q"] == 0, "Pseudo model has nonzero ordered g_N")
        row.update({"pseudo_solution_b": b, "pseudo_support": [i for i, bit in enumerate(b) if bit],
                    "pseudo_polynomial_replay": replay, "pseudo_differs_from_a": b != a})
    # This extra clause belongs ONLY to the search predicate b != a for gate (ii).
    different_from_a = [-(i + 1) if a[i] else i + 1 for i in range(n + 1)]
    second_cnf = f_clauses + [different_from_a]
    row["second_model_search_CNF"] = save_new(OUT / (stem + "_second.cnf"),
                                               dimacs(n, second_cnf, "family without g_N, plus b != a"))
    second = solve(n, second_cnf, budget)
    row["second_model_search_nodes"] = second["search_nodes"]
    if second["model"] is None:
        row["pinning_test_result"] = "UNIQUE_PRIME_POINT_AT_THIS_N_WITH_LITERAL_RUP_DRAT"
        row["second_model_search_proof"] = {
            **save_new(OUT / (stem + "_second.drat"), proof_bytes(second["additions"])),
            "format": "DRAT additions, every addition RUP; no deletions",
            "addition_count": len(second["additions"])}
    else:
        b_second = second["model"]
        require(b_second != a, "Second model equals the true prime indicator")
        row.update({"pinning_test_result": "SECOND_BOOLEAN_MODEL_FOUND",
                    "second_boolean_solution_without_g": b_second,
                    "second_polynomial_replay_without_g": polynomial_replay(spec, b_second),
                    "Boolean_solution_count_lower_bound_without_g": 2,
                    "second_model_search_proof": None})
    return row


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--authorization", required=True)
    parser.add_argument("--expected-authorization-sha256", required=True)
    args = parser.parse_args()
    authorization_path = Path(args.authorization).resolve(strict=True)
    authorization_raw = authorization_path.read_bytes()
    source_sha = digest(Path(__file__).read_bytes())
    require(len(args.expected_authorization_sha256) == 64 and
            digest(authorization_raw) == args.expected_authorization_sha256,
            "Authorization SHA-256 mismatch")
    require(AUTHORIZATION_MARKER.encode("ascii") in authorization_raw and
            source_sha.encode("ascii") in authorization_raw,
            "Separate authorization must contain the action marker and this exact source SHA-256")
    # A source-only review cannot accidentally execute this main without authority.
    OUT.mkdir(parents=True, exist_ok=False)
    budget = Budget()
    result = {"schema": 1, "stage": "PRODUCER_CANDIDATES_PENDING_INDEPENDENT_JUDGE",
              "field": "Q; exact integer Boolean polynomial evaluations",
              "domain": "even N >= 4", "bounded_scan": {"minimum": MIN_N, "maximum": MAX_N, "step": STEP},
              "families_in_reviewed_order": list(FAMILIES), "limits": LIMITS,
              "source": {"path": Path(__file__).relative_to(ROOT).as_posix(), "sha256": source_sha},
              "authorization": {"path": str(authorization_path), "sha256": digest(authorization_raw)},
              "started_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
              "no_multiplier_search": True, "C1_used": False, "rows": [],
              "candidate_first_pseudo_solution_even_N_at_least_4": {},
              "no_candidate_by_maximum": [], "active_case_at_stop": None, "status": "ACTIVE"}
    return_code = 0
    try:
        for family in FAMILIES:
            found = False
            for n in range(MIN_N, MAX_N + 1, STEP):
                result["active_case_at_stop"] = {"family": family, "N": n,
                                               "stage": "CASE_STARTED_NOT_YET_A_COMPLETED_ROW"}
                row = run_case(family, n, budget)
                result["rows"].append(row)
                result["active_case_at_stop"] = None
                print(f"{family} N={n}: {row['pseudo_gate_result']}; {row['pinning_test_result']}", flush=True)
                if row["pseudo_gate_result"] == "SAT":
                    result["candidate_first_pseudo_solution_even_N_at_least_4"][family] = n
                    found = True
                    break
            if not found:
                result["no_candidate_by_maximum"].append(family)
        result["status"] = "COMPLETE_PENDING_INDEPENDENT_JUDGE"
    except BoundedStop as error:
        result["status"] = "BOUNDED_INCOMPLETE_NO_NEW_GLOBAL_MINIMUM_CREDIT"
        result["stop_reason"] = str(error)
        return_code = 2
    except Exception as error:
        result["status"] = "PRODUCER_ERROR_NO_NEW_GLOBAL_MINIMUM_CREDIT"
        result["error"] = {"type": type(error).__name__, "message": str(error)}
        return_code = 1
    result["terminal_utc"] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    result["budget_observation"] = budget.snapshot()
    # Retain bindings for partial-case files too; none is silently promoted to a row.
    result["all_saved_case_artifacts_before_manifest"] = [
        {"path": path.relative_to(ROOT).as_posix(), "sha256": digest(path.read_bytes()),
         "bytes": path.stat().st_size} for path in sorted(OUT.iterdir()) if path.is_file()]
    result["independent_review_obligation"] = (
        "Reconstruct every complete CNF and direct polynomial value without importing this source; "
        "replay every DRAT addition by independent RUP through the terminal empty clause; "
        "check the contiguous even-N prefix for each claimed first SAT and both sides of gate (ii).")
    binding = save_new(OUT / "producer_manifest.json", json_bytes(result))
    print(json.dumps({"status": result["status"], "manifest": binding}), flush=True)
    return return_code


if __name__ == "__main__":
    sys.stdout.reconfigure(encoding="utf-8")
    raise SystemExit(main())
