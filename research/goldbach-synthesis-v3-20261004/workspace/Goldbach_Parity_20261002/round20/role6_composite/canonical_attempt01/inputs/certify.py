"""NEW strict fixed-expression signs; exact prime-log reduction before a ZERO label."""
from fractions import Fraction

from arithmetic import factor, frac, map_json
from outward import iv_json


class StrictCertificates:
    def __init__(self, primes, oracle, store):
        self.primes = primes
        self.oracle = oracle
        self.store = store
        self.factor_cache = {}
        self.counts = {"POS": 0, "NEG": 0, "ZERO": 0}

    def interval(self, label, value, exact_zero=False, exact_expression=None):
        certificate = iv_json(value)
        if exact_zero:
            assert value == (0, 0), (label, certificate)
        elif certificate["sign"] not in ("POS", "NEG"):
            raise ArithmeticError({"label": label, "failure": "FIXED_NONZERO_SIGN_NOT_SEPARATED",
                                   "certificate": certificate, "exact_expression": exact_expression})
        self.counts[certificate["sign"]] += 1
        position = self.store.put({"scope": "STRICT_FIXED_EXPRESSION_NO_FREE_S_N_OR_PRINCIPAL",
                                   "label": label, "certificate": certificate,
                                   "exact_ZERO_proof": exact_zero,
                                   "exact_expression": exact_expression})
        return {**certificate, "stored_certificate_ref": position}

    def vector(self, label, original):
        reduced = {}
        factors = []
        for argument, coefficient in sorted(original.items()):
            if argument not in self.factor_cache:
                self.factor_cache[argument] = factor(argument, self.primes)
            pf = self.factor_cache[argument]
            factors.append([argument, [[p, e] for p, e in pf]])
            for p, exponent in pf:
                updated = reduced.get(p, Fraction(0)) + coefficient * exponent
                if updated:
                    reduced[p] = updated
                elif p in reduced:
                    del reduced[p]
        value = self.oracle.vector(reduced) if reduced else (Fraction(0), Fraction(0))
        certificate = self.interval(label, value, exact_zero=not reduced,
            exact_expression={"original_log_argument_map": map_json(original),
                              "all_actual_factorizations": factors,
                              "reduced_prime_log_map": map_json(reduced),
                              "reduction_identity": "log(product p^e)=sum e*log(p)",
                              "ZERO_iff_all_reduced_coefficients_vanish": not reduced})
        return value, certificate
