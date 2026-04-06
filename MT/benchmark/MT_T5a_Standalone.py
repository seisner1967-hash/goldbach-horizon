"""
T5a — Theorem-Facing Benchmark (canonical B=7, A=2) — STANDALONE
=================================================================
Tests MT1/MT2/MT3 in their DECLARED parameter regime.
No adaptive B. Honest about degenerate points.

Upload this single file to Colab and run:
    !pip install sympy
    %run MT_T5a_Standalone.py
"""
import numpy as np
from sympy import primerange, factorint
import time
import json

# ══════════════════════════════════════════════════════════════
# CORE (inlined)
# ══════════════════════════════════════════════════════════════

EULER_GAMMA = 0.5772156649
C2_TWIN = 0.6601618

DICKMAN = {
    1.0: 1.0, 1.25: 0.4484, 1.5: 0.30685, 1.75: 0.2056,
    2.0: 0.12131, 2.5: 0.04856, 3.0: 0.01862, 3.5: 0.01537,
    4.0: 0.00491, 5.0: 0.000354
}

def dickman_rho(u):
    if u <= 1.0: return 1.0
    keys = sorted(DICKMAN.keys())
    if u >= keys[-1]: return DICKMAN[keys[-1]]
    for i in range(len(keys)-1):
        if keys[i] <= u <= keys[i+1]:
            t = (u - keys[i]) / (keys[i+1] - keys[i])
            return (1-t)*DICKMAN[keys[i]] + t*DICKMAN[keys[i+1]]
    return 0.0

def P_plus(n):
    if n <= 1: return 0
    f = factorint(n)
    return max(f.keys()) if f else 0

def S2_ratio(h, small_p):
    if h <= 0 or h % 2 != 0: return 0.0
    r = 1.0
    for p in small_p:
        if p <= 2: continue
        if h % p == 0: r *= (p-1)/(p-2)
    return r

def compute(N, B, A):
    logN = float(np.log(N))
    loglogN = float(np.log(logN)) if logN > 1 else 0.01
    Q = logN**B
    y = logN**A
    X = N / Q
    u = B / A
    t0 = time.time()

    primes = list(primerange(N//2, N+1))
    prime_set = set(primes)
    small_p = list(primerange(2, min(int(y)+10, 500)))

    max_gap = int(N/Q) + 1
    cluster = 0
    for i, p in enumerate(primes):
        for j in range(i+1, len(primes)):
            if primes[j] - p > max_gap: break
            cluster += 1

    C_gal = 2.0 * C2_TWIN * N**2 / (Q * logN**2)
    c_ratio = cluster / C_gal if C_gal > 0 else 0.0

    max_h = max(min(int(X)+2, max_gap+10), 20)
    var_sum, sm_var, ro_var, n_h = 0.0, 0.0, 0.0, 0
    for h in range(2, max_h+1, 2):
        pi2 = sum(1 for p in primes if p+h <= N and (p+h) in prime_set)
        exp_val = S2_ratio(h, small_p) * N / logN**2
        esq = (pi2 - exp_val)**2
        var_sum += esq
        if h > 1 and P_plus(h) <= y: sm_var += esq
        else: ro_var += esq
        n_h += 1

    V_bar = var_sum / max(n_h, 1)
    scale = N**2 / logN**4
    V_ratio = V_bar / scale if scale > 0 else 0.0
    sm_frac = sm_var / max(var_sum, 1e-30)

    rho_u = dickman_rho(u)
    smooth_main = rho_u * np.exp(EULER_GAMMA) * A * loglogN
    R_est = abs(c_ratio - 1.0) * smooth_main if cluster > 0 else smooth_main

    delta7 = float(np.sqrt(max(cluster, 1)) * logN)
    M_N = N / logN
    d7M = delta7 / M_N if M_N > 0 else 0.0
    mt3_norm = d7M * logN**(B/2 - 1) if B > 2 else d7M
    pcb_ratio = cluster / (N**2 / (Q * logN**2)) if cluster > 0 else 0.0

    elapsed = time.time() - t0
    return {
        "log10_N": float(round(np.log10(N), 1)),
        "N": int(N), "B": float(B), "A": float(A),
        "Q": float(round(Q, 2)), "X": float(round(X, 2)), "u": float(round(u, 3)),
        "primes": int(len(primes)),
        "rho_u": float(round(rho_u, 6)),
        "smooth_main_term": float(round(smooth_main, 6)),
        "R_smooth_est": float(round(R_est, 6)),
        "R_below_022": bool(R_est < 0.22),
        "MT1_margin": float(round(0.22 - R_est, 6)),
        "cluster_count": int(cluster),
        "C_gallagher": float(round(C_gal, 2)),
        "cluster_ratio": float(round(c_ratio, 6)),
        "V_bar_ratio": float(round(V_ratio, 6)),
        "smooth_frac": float(round(sm_frac, 6)),
        "delta7_over_M": float(round(d7M, 8)),
        "mt3_normalized": float(round(mt3_norm, 8)),
        "pcb_q1_ratio": float(round(pcb_ratio, 6)),
        "pcb_q1_holds": bool(pcb_ratio < 20),
        "elapsed_s": float(round(elapsed, 1)),
    }

# ══════════════════════════════════════════════════════════════
# T5a MAIN — CANONICAL B=7, A=2
# ══════════════════════════════════════════════════════════════

B_CANON = 7.0
A_CANON = 2.0
POINTS = [6, 7, 8, 9]

def main():
    print("╔══════════════════════════════════════════════════════════╗")
    print("║  T5a — THEOREM BENCHMARK (canonical B=7, A=2)          ║")
    print("╚══════════════════════════════════════════════════════════╝")
    print(f"  NOTE: At B=7, Q=(logN)^7 >> N for N < ~10^20.")
    print(f"  All points will be degenerate. This is EXPECTED.")
    print(f"  T5a tests that observables stay consistent, not that")
    print(f"  they show visible signal at these scales.")
    print(f"  Started: {time.strftime('%Y-%m-%d %H:%M:%S')}")

    results = []
    t0 = time.time()

    for log10N in POINTS:
        N = int(10**log10N)
        Q = np.log(N)**B_CANON
        X = N / Q
        regime = "degenerate" if X < 1 else ("marginal" if X < 100 else "asymptotic")

        print(f"\n  ▶ N=10^{log10N}  Q={Q:.0f}  X={X:.4f}  regime={regime}")

        r = compute(N, B_CANON, A_CANON)
        r["regime"] = regime
        results.append(r)

        print(f"    C={r['cluster_count']:,}  C/Gal={r['cluster_ratio']:.4f}  "
              f"V̄/sc={r['V_bar_ratio']:.6f}")
        print(f"    |R|={r['R_smooth_est']:.4f}  δ₇/M={r['delta7_over_M']:.8f}  "
              f"mt3n={r['mt3_normalized']:.6f}")
        print(f"    {r['elapsed_s']:.1f}s")

    total = time.time() - t0

    # Checks
    checks = {}
    r_vals = [r["R_smooth_est"] for r in results]
    checks["MT1_safety"] = "pass" if all(v < 0.22 for v in r_vals) else "warn"

    c_vals = [r["cluster_ratio"] for r in results if r["cluster_count"] > 0]
    checks["MT2_cluster"] = "pass" if (not c_vals or all(v < 5 for v in c_vals)) else "warn"
    if not c_vals: checks["MT2_cluster"] += " (degenerate: Q>>N, no clusters)"

    mt3_vals = [r["mt3_normalized"] for r in results if r["delta7_over_M"] > 0]
    checks["MT3_normalized"] = "pass" if (not mt3_vals or all(v < 10 for v in mt3_vals)) else "warn"
    if not mt3_vals: checks["MT3_normalized"] += " (degenerate: no signal)"

    print(f"\n{'═'*60}")
    print(f"  T5a SUMMARY — {total:.0f}s")
    print(f"{'═'*60}")
    for k, v in checks.items():
        icon = "✓" if "pass" in v else "⚠"
        print(f"  {icon} {k}: {v}")

    print(f"\n  INTERPRETATION:")
    print(f"  B=7 is the theoretical canonical choice for N → ∞.")
    print(f"  At N ≤ 10^9, Q >> N so the cluster regime is degenerate.")
    print(f"  The 'pass' verdicts mean: no contradiction detected.")
    print(f"  For visible signal, see T5b (adaptive B).")

    with open("t5a_results.json", "w") as f:
        json.dump({"benchmark": "T5a-theorem", "params": {"B": 7.0, "A": 2.0},
                   "data": results, "checks": checks,
                   "elapsed_s": float(round(total, 1))}, f, indent=2)
    print(f"\n  → t5a_results.json")

if __name__ == "__main__":
    main()
