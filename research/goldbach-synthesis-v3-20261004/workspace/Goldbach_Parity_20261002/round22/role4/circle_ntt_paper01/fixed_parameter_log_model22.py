"""SOURCE ONLY: no import/run yet; not an NTT producer or a prepared bank.

All primalities, root orders, tau comparisons and log boxes returned by these
functions must come from an actual future authorized invocation. This file
does not contain an observed PASS, a free epsilon input or a float primitive.
"""

N = 100000000
K = 134217728
S = 288230376151711744
MODULI = (
    (2013265921, 15, 31),
    (2281701377, 17, 3),
    (3221225473, 24, 5),
    (3489660929, 26, 3),
    (3892314113, 29, 3),
)


def require(ok, message):
    if not ok:
        raise ArithmeticError(message)


def checked_bits(x, cap):
    require(abs(x).bit_length() <= cap, "RATIONAL_WORKSPACE_OVERFLOW")
    return x


def pow_mod(base, exponent, modulus):
    require(exponent >= 0 and 1 < modulus < 2**32, "INVALID_POW_DOMAIN")
    acc = 1
    base %= modulus
    while exponent:
        if exponent & 1:
            product = acc * base
            require(product < 2**64, "MOD_PRODUCT_OVERFLOW")
            acc = product % modulus
        exponent //= 2
        if exponent:
            product = base * base
            require(product < 2**64, "MOD_PRODUCT_OVERFLOW")
            base = product % modulus
    return acc


def inverse_mod(a, p):
    require(0 < a < p, "INVALID_INVERSE_DOMAIN")
    r0, r1, x0, x1 = p, a, 0, 1
    while r1:
        q = r0 // r1
        r0, r1 = r1, r0 - q * r1
        x0, x1 = x1, x0 - q * x1
    require(r0 == 1, "NONUNIT_DIVISION")
    result = x0 % p
    require((a * result) % p == 1, "INVERSE_CHECK_FAILED")
    return result


def check_fixed_constants():
    require(N == 100000000 and K == 2**27 and S == 2**58, "WRONG_FIXED_INPUT")
    require(0 < N < K and N + 1 < K, "ALIAS_BOUND_FAILED")
    seen = set()
    rows = []
    product = 1
    for p, c, g in MODULI:
        require(p not in seen and p == c * K + 1, "WRONG_MODULUS")
        require(K < p < 2**32 and p % 2 == 1, "WRONG_MODULUS_DOMAIN")
        seen.add(p)
        d, divisions = 2, 0
        while d * d <= p:
            require(p % d != 0, "INVALID_MODULAR_PARAMETER_COMPOSITE")
            divisions += 1
            d += 1
        omega = pow_mod(g, c, p)
        require(0 < omega < p, "ZERO_ROOT")
        require(pow_mod(omega, K, p) == 1, "ROOT_PERIOD_FAILED")
        require(pow_mod(omega, K // 2, p) != 1, "ROOT_ORDER_FAILED")
        rows.append({"p": p, "c": c, "g": g, "omega": omega,
                     "omega_inverse": inverse_mod(omega, p),
                     "K_inverse": inverse_mod(K, p),
                     "trial_divisions": divisions})
        product *= p
    require(len(rows) == 5 and product > 2**154, "CRT_RANGE_FAILED")
    integer_bound = (N + 1) * (32 * S)**2
    require(integer_bound < 2**153 < product, "COEFFICIENT_RANGE_FAILED")
    tau_numerator = 2 * (N + 1) * (64 * S + 1) * 1000000
    require(tau_numerator <= S * S, "TAU_GUARD_FAILED")
    return {"status": "FIXED_PARAMETER_CHECKS_ONLY", "rows": rows,
            "CRT_product": product, "coefficient_upper": integer_bound,
            "joint_error_numerator": 2 * (N + 1) * (64 * S + 1),
            "error_denominator": S * S,
            "full_projection_computed": False,
            "catalogue_checked": False,
            "primitive_Lean_certified": False}


def _series_common(a, d, terms, cap):
    require(terms in (32, 40) and 0 <= 3 * a <= d and d > 0,
            "INVALID_LOG_SERIES_DOMAIN")
    H = 1
    for j in range(terms):
        H = checked_bits(H * (2 * j + 1), cap)
    denominator = checked_bits(d**(2 * terms - 1) * H, cap)
    numerator = 0
    for j in range(terms):
        odd = 2 * j + 1
        require(H % odd == 0, "COMMON_DENOMINATOR_FAILED")
        term = checked_bits(a**odd * d**(2 * terms - 2 - 2 * j) * (H // odd), cap)
        numerator = checked_bits(numerator + 2 * term, cap)
    return numerator, denominator


def log_box(p, terms):
    """Endpoints lo/d, hi/d, with closed positive remainder included."""
    require(2 <= p <= N and terms in (32, 40), "INVALID_LOG_INPUT")
    cap = 4096 if terms == 32 else 8192
    k = p.bit_length() - 1
    require(0 <= k <= 26 and 2**k <= p < 2**(k + 1), "LOG_REDUCTION_FAILED")
    a, d = p - 2**k, p + 2**k
    nz, dz = _series_common(a, d, terms, cap)
    n2, d2 = _series_common(1, 3, terms, cap)
    lower_n = checked_bits(k * n2 * dz + nz * d2, cap)
    lower_d = checked_bits(d2 * dz, cap)
    width_n = (k + 1) * 9
    width_d = 4 * (2 * terms + 1) * 3**(2 * terms + 1)
    common_d = checked_bits(lower_d * width_d, cap)
    lo = checked_bits(lower_n * width_d, cap)
    hi = checked_bits(lo + width_n * lower_d, cap)
    require(0 <= lo <= hi and common_d > 0, "INVALID_LOG_BOX")
    require(hi - lo == width_n * lower_d, "LOG_REMAINDER_LOST")
    require((hi - lo) * S < common_d, "LOG_WIDTH_GUARD_FAILED")
    return lo, hi, common_d, cap


def quantized_log_point(p, terms):
    lo, hi, d, cap = log_box(p, terms)
    numerator = checked_bits(S * (lo + hi), cap)
    denominator = checked_bits(2 * d, cap)
    q, r = divmod(numerator, denominator)
    if 2 * r > denominator or (2 * r == denominator and q % 2):
        q += 1
    point = max(0, min(32 * S, q))
    require(0 <= point <= 32 * S < 2**64, "POINT_STORAGE_OVERFLOW")
    require(abs(checked_bits(point * d - S * lo, cap)) <= d,
            "LOW_ENDPOINT_GUARD_FAILED")
    require(abs(checked_bits(point * d - S * hi, cap)) <= d,
            "HIGH_ENDPOINT_GUARD_FAILED")
    return point


def verify_record_log_point(p, point):
    """Fresh series40 endpoints; neither width nor radius is an input."""
    require(0 <= point <= 32 * S, "INVALID_POINT_RECORD")
    lo, hi, d, cap = log_box(p, 40)
    require(abs(checked_bits(point * d - S * lo, cap)) <= d,
            "RECORD_LOW_ENDPOINT_FAILED")
    require(abs(checked_bits(point * d - S * hi, cap)) <= d,
            "RECORD_HIGH_ENDPOINT_FAILED")
    return True

# No main, invocation, import, file I/O or PASS materialization in this source.
