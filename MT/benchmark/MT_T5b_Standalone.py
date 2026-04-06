"""
T5b — Exploratory Adaptive Benchmark — STANDALONE
===================================================
Explores MT-inspired observables with adaptive B.
NOT a direct validation of theorem statements.

Upload this single file to Colab and run:
    !pip install sympy
    %run MT_T5b_Standalone.py
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
# T5b — ADAPTIVE B
# ══════════════════════════════════════════════════════════════

POINTS = [
    (6,    1.5,  "degenerate"),
    (7,    2.0,  "degenerate"),
    (8,    2.5,  "transition"),
    (8.5,  3.0,  "transition"),
    (9,    3.0,  "meaningful"),
    (9.5,  3.5,  "meaningful"),
    (10,   3.5,  "meaningful"),
    (10.5, 3.5,  "meaningful"),
]

A = 2.0

def main():
    print("╔══════════════════════════════════════════════════════════╗")
    print("║  T5b — EXPLORATORY ADAPTIVE BENCHMARK (standalone)     ║")
    print("║  B varies with scale — signal visible but heuristic    ║")
    print("╚══════════════════════════════════════════════════════════╝")
    print(f"  NOTE: This uses adaptive B. Results should NOT be read")
    print(f"  as direct validation of MT1-MT3 theorem statements.")
    print(f"  Started: {time.strftime('%Y-%m-%d %H:%M:%S')}")

    results = []
    t_start = time.time()

    for log10N, B, regime in POINTS:
        print(f"\n  ▶ N=10^{log10N}, B={B}, regime={regime}")
        try:
            r = compute(int(10**log10N), B, A)
            r["regime"] = str(regime)
            results.append(r)

            print(f"    C={r['cluster_count']:,}  C/Gal={r['cluster_ratio']:.4f}  "
                  f"V̄/sc={r['V_bar_ratio']:.6f}")
            print(f"    |R|={r['R_smooth_est']:.4f}  δ₇/M={r['delta7_over_M']:.8f}  "
                  f"mt3n={r['mt3_normalized']:.6f}")
            print(f"    sm%={r['smooth_frac']*100:.0f}%  PCB={r['pcb_q1_ratio']:.4f}")
            print(f"    {r['elapsed_s']:.1f}s")

            with open("t5b_results.json", "w") as f:
                json.dump({"benchmark": "T5b-exploratory", "data": results,
                           "status": "running",
                           "elapsed_s": float(round(time.time()-t_start, 1))}, f, indent=2)
            print(f"    ✓ Saved ({len(results)}/{len(POINTS)})")

        except Exception as e:
            print(f"    ✗ Error: {e}")
            import traceback; traceback.print_exc()

    total = time.time() - t_start

    print(f"\n{'═'*60}")
    print(f"  T5b COMPLETE — {total/3600:.2f}h")
    print(f"{'═'*60}")

    print(f"\n  {'lgN':>5} {'B':>4} {'regime':>12} {'C/Gal':>7} {'V̄/sc':>8} "
          f"{'sm%':>5} {'δ₇/M':>10} {'mt3n':>8} {'PCB':>4}")
    print(f"  {'─'*70}")
    for r in results:
        print(f"  {r['log10_N']:5.1f} {r['B']:4.1f} {r['regime']:>12} "
              f"{r['cluster_ratio']:7.4f} {r['V_bar_ratio']:8.6f} "
              f"{r['smooth_frac']*100:4.0f}% "
              f"{r['delta7_over_M']:10.6f} "
              f"{r['mt3_normalized']:8.4f} "
              f"{'✓' if r['pcb_q1_holds'] else '✗':>4}")

    # MT3 normalized
    meaningful = [r for r in results if r["regime"] == "meaningful"]
    if meaningful:
        print(f"\n  MT3 NORMALIZED (meaningful only):")
        for r in meaningful:
            print(f"    N=10^{r['log10_N']:.1f}: (δ₇/M)·(logN)^(B/2-1) = {r['mt3_normalized']:.6f}")
        vals = [r["mt3_normalized"] for r in meaningful if r["mt3_normalized"] > 0]
        if vals:
            print(f"    Range: [{min(vals):.4f}, {max(vals):.4f}]")
            print(f"    Bounded: {'YES ✓' if max(vals) < 10*min(vals) else 'DIVERGING ✗'}")

    # V̄ trend
    vr = [r["V_bar_ratio"] for r in results if r["V_bar_ratio"] > 0]
    if len(vr) >= 2:
        mono = all(vr[i] >= vr[i+1] for i in range(len(vr)-1))
        print(f"\n  MT2 V̄/scale trend: {[f'{v:.4f}' for v in vr]}")
        print(f"    Monotone ↓: {'YES ✓' if mono else 'NO (B varies, expected)'}")

    pcb = [r for r in results if r["pcb_q1_holds"]]
    print(f"\n  PCB(Q¹) bounded: {len(pcb)}/{len(results)}")

    with open("t5b_results.json", "w") as f:
        json.dump({"benchmark": "T5b-exploratory", "data": results,
                   "status": "complete", "elapsed_h": float(round(total/3600, 2))}, f, indent=2)
    print(f"\n  → t5b_results.json  ({total/3600:.2f}h)")

if __name__ == "__main__":
    main()
