# ROLE4 distinct revision SOURCE ONLY, original arithmetic source untouched.
# Degree16 and explicit primal4 meet the fixed global catalogue contract.
# The readonly original UnitBoundTransport is used only for the primal heat
# sequence; its incompatible EM constructor is never imported by name/called.
"""New finite arithmetic side of H1, SOURCE ONLY, not imported or run.

All n=2..1000000 are visited before the prime-power mask. Individual trial
division supplies exact certificates; no sieve, Mobius inversion, or old prime
table is used. A future gate must bind both this source and dyadic_r01 plus the
new transport source. These routines do not run a bank or emit any verdict.
The analytic truncation tails of H1 are separate obligations of the future bank.
"""
from fractions import Fraction as F
from dyadic_r01 import Box, log_box
from unit_transport_source22 import primal_heat_sequence

Y = 10000
X = 1000000
Q = 1000000


def classify_integer(n):
    """Exact certificate n=p^e*r; prime p, and either r=1 or p does not divide r.

    The first divisor in increasing order is prime: a composite first divisor
    would have a smaller prime divisor of n. If no divisor d with d*d<=n exists,
    n is prime. The certificate checker below verifies primality independently.
    """
    if type(n) is not int or not 2 <= n <= X:
        raise ValueError("complete fixed arithmetic catalogue required")
    if n % 2 == 0:
        p, tested = 2, 1
    else:
        p, d, tested = n, 3, 1
        while d * d <= n:
            tested += 1
            if n % d == 0:
                p = d
                break
            d += 2
    r, exponent = n, 0
    while r % p == 0:
        r //= p
        exponent += 1
    if exponent < 1 or p ** exponent * r != n or r % p == 0:
        raise ArithmeticError("exact arithmetic factor certificate failed")
    return {"n": n, "p": p, "exponent": exponent, "cofactor": r,
            "is_prime_power": r == 1, "proper_prime_power": r == 1 and exponent >= 2,
            "trial_divisions": tested}


def independent_prime_certificate(p):
    if type(p) is not int or p < 2:
        return False
    if p == 2:
        return True
    if p % 2 == 0:
        return False
    d = 3
    while d * d <= p:
        if p % d == 0:
            return False
        d += 2
    return True


def check_new_arithmetic_stream(records):
    """Check the complete new stream, not an old output or a presumed prime list."""
    expected_n, verified_primes = 2, set()
    prime_power_count = proper_prime_power_count = ordinary_composite_count = 0
    for record in records:
        if record["n"] != expected_n or expected_n > X:
            raise ArithmeticError("missing, repeated, or reordered arithmetic integer")
        p, exponent, r = record["p"], record["exponent"], record["cofactor"]
        if any(type(k) is not int for k in (p, exponent, r)) or exponent < 1 or r < 1:
            raise ArithmeticError("invalid exact certificate fields")
        if p not in verified_primes:
            if not independent_prime_certificate(p):
                raise ArithmeticError("factor primality certificate failed")
            verified_primes.add(p)
        if p ** exponent * r != expected_n or r % p == 0:
            raise ArithmeticError("arithmetic product or coprimality witness failed")
        is_pp = r == 1
        if record["is_prime_power"] != is_pp:
            raise ArithmeticError("prime-power mask disagrees with exact certificate")
        if record["proper_prime_power"] != (is_pp and exponent >= 2):
            raise ArithmeticError("proper-prime-power mask disagrees with certificate")
        prime_power_count += is_pp
        proper_prime_power_count += is_pp and exponent >= 2
        ordinary_composite_count += not is_pp
        expected_n += 1
    if expected_n != X + 1:
        raise ArithmeticError("incomplete arithmetic stream")
    return {"all_integers_before_mask": X - 1,
            "prime_power_count": prime_power_count,
            "proper_prime_power_count": proper_prime_power_count,
            "ordinary_composite_count": ordinary_composite_count,
            "prime_certificates": len(verified_primes), "old_prime_table_used": False}


def dual_small_exponential(n):
    """Enclose exp(-1/(Y*n)) by the alternating degree-sixteen series.

    Here 0<a=1/(Y*n)<=1/20000. Terms decrease, so the even partial sum is an
    upper bound and subtracting a^17/17! gives a lower bound. All operations are
    exact rationals until outward conversion to the new dyadic grid.
    """
    if type(n) is not int or not 2 <= n <= Q:
        raise ValueError("fixed dual catalogue required")
    a = F(1, Y * n)
    term = value = F(1)
    for k in range(1, 17):
        term *= -a / k
        value += term
    error = abs(term * a / 17)
    # Bounding the whole interval by its two directed endpoint conversions
    # also accounts for rounding. No unspecified primitive error is injected.
    lower = Box.rational(value - error)
    upper = Box.rational(value)
    return Box(lower.lo, upper.hi)


def new_finite_arithmetic_side(write_certificate, progress=None):
    """Compute both true finite sums and preserve all prime powers, SOURCE ONLY.

    Certificate writer receives every integer, before either summation mask.
    Values are evaluated anew; cached log(p) boxes belong to this invocation.
    The n=4 contribution is retained for the proper-power mutation, once only.
    Returned boxes carry actual primitive/transport/summation rounding. The
    infinite primal/dual tails must be added separately by the future bank.
    """
    transport = primal_heat_sequence()
    primal = dual = Box.rational(0)
    four = four_primal = four_dual = None
    log_cache = {}
    pp_count = proper_count = divisions = 0
    for n in range(2, X + 1):
        certificate = classify_integer(n)
        write_certificate(certificate)
        divisions += certificate["trial_divisions"]
        if certificate["is_prime_power"]:
            p = certificate["p"]
            if p not in log_cache:
                log_cache[p] = log_box(Box.rational(p))
            logp = log_cache[p]
            primal_term = (logp * transport.box().real).scale(F(n, Y))
            dual_term = (logp * dual_small_exponential(n)).scale(F(1, Y * n * n))
            primal = primal + primal_term
            dual = dual + dual_term
            if n == 4:
                four = primal_term + dual_term
                four_primal, four_dual = primal_term, dual_term
            pp_count += 1
            proper_count += certificate["proper_prime_power"]
        if n < X:
            transport.advance()
        if progress is not None and n % 10000 == 0:
            progress({"last_integer": n, "all_visited": n - 1,
                      "prime_power_count": pp_count, "trial_divisions": divisions})
    if four is None or transport.index != X - 2:
        raise ArithmeticError("complete arithmetic endpoint or n=4 term missing")
    return {"primal": primal, "dual": dual, "combined": primal + dual,
            "proper_power_four": four, "primal_four": four_primal, "dual_four": four_dual, "all_integers_before_mask": X - 1,
            "prime_power_count": pp_count, "proper_prime_power_count": proper_count,
            "trial_divisions": divisions, "transport": transport.diagnostics(),
            "new_log_primitives": len(log_cache), "old_values_used": False,
            "analytic_tails_included": False, "H1_claim": False}

