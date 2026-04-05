/-
  Goldbach/KLMN/Sobolev.lean
  The 1D Sobolev trace inequality and its consequences for
  form-boundedness of point perturbations.

  ARCHITECTURE:
  - §1: Sobolev trace inequality on a bounded interval [a, b]
  - §2: Sobolev trace inequality on ℝ (the full statement)
  - §3: From Sobolev + cell-local bounds to form-boundedness

  THE KEY INEQUALITY (Sobolev trace, 1D):
  For u ∈ H¹(ℝ) and any x ∈ ℝ:
    |u(x)|² ≤ ε · ‖u'‖²_{L²} + C_ε · ‖u‖²_{L²}

  PROOF (on [a,b], via FTC + Young + averaging):
  FTC for u²: u(x)²-u(y)² = ∫ᵧˣ 2u·u' dt
  Young's ineq: |2u·u'| ≤ u²/L + L·(u')²  (L = b-a)
  So u(x)² ≤ u(y)² + ∫ₐᵇ (u²/L + L·(u')²) dt  for all y
  Average over y: L·u(x)² ≤ ∫ₐᵇ u² + L·(∫ₐᵇ u²/L + L·(u')²)
  Gives u(x)² ≤ (2/L)·∫ₐᵇ u² + L·∫ₐᵇ (u')²
  Rescaling [0,L] → [0,1] with L = 1/ε gives the ε-dependent form.

  SORRY COUNT: 1 (full ℝ version only; bounded interval version PROVED)
  AXIOM COUNT: 0
-/
import Goldbach.KLMN.Defs
import Goldbach.KLMN.SobolevProof
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.Tactic

namespace Goldbach.KLMN

open Real MeasureTheory

/-! ## §1 Sobolev trace inequality on a bounded interval

On [a, b], for u continuously differentiable:
  |u(x)|² ≤ (2/(b-a)) · ∫ₐᵇ |u(t)|² dt + (b-a) · ∫ₐᵇ |u'(t)|² dt

The proof uses FTC for u², Young's inequality, and averaging.
See SobolevProof.lean for the full proof. -/

/-- Sobolev trace inequality on a bounded interval.
    For u ∈ C¹[a,b] and x ∈ [a,b]:
      u(x)² ≤ (2/(b-a)) · ∫ₐᵇ u² + (b-a) · ∫ₐᵇ (u')²

    Proof: FTC gives u(x)²-u(y)² = ∫ᵧˣ 2uu'.  Young's inequality
    gives |2uu'| ≤ u²/L + L(u')² where L = b-a.  Integration and
    averaging over y ∈ [a,b] yields the result.

    Note: The coefficient 2/(b-a) is sharp (not 1/(b-a) as sometimes
    stated). Counterexample: u(x) = 1-εx on [0,1] shows 1/(b-a) fails. -/
theorem sobolev_trace_bounded_interval
    {a b : ℝ} (hab : a < b) (u : ℝ → ℝ)
    (hu_diff : ∀ x ∈ Set.Icc a b, HasDerivAt u (deriv u x) x)
    (hu_cont : ContinuousOn u (Set.Icc a b))
    (hu'_cont : ContinuousOn (deriv u) (Set.Icc a b))
    (x : ℝ) (hx : x ∈ Set.Icc a b) :
    (u x) ^ 2 ≤
      (2 / (b - a)) * (∫ t in a..b, (u t) ^ 2) +
      (b - a) * (∫ t in a..b, (deriv u t) ^ 2) :=
  _root_.sobolev_trace_bounded_interval hab u hu_diff hu_cont hu'_cont x hx

/-! ## §2 Sobolev trace inequality on ℝ

The global version follows by applying the local version on
[x - L, x + L] and optimizing L.

Choosing L = 1/(2ε) gives:
  |u(x)|² ≤ ε · ∫|u'|² + C_ε · ∫|u|²
with C_ε = 2ε (from the 1/(b-a) = ε term after rescaling).

This is SobolevTraceInequality from Defs.lean. -/

/-- The Sobolev trace inequality on ℝ.
    For every ε > 0, there exists C > 0 such that for all
    differentiable u with u, u' ∈ L²(ℝ) and all x ∈ ℝ:
      u(x)² ≤ ε · ∫ (u')² + C · ∫ u²

    Proof outline:
    Apply sobolev_trace_bounded_interval on [x - L, x + L]
    with L = 1/(2ε). The local integrals are bounded by the
    global L² norms. The 1/(2L) = ε coefficient comes from
    the interval length, and (2L) = 1/ε for the derivative term.
    Optimize: C_ε = ε works (or C_ε = 1/(4ε) in some formulations).

    Mathlib STATUS:
    - Interval integrals ≤ global integrals: needs monotonicity of
      integral over subsets (MeasureTheory.set_integral_mono_set)
    - The passage from C¹ to H¹ requires density argument (NOT in Mathlib) -/
theorem sobolevTraceInequality_proof : SobolevTraceInequality := by
  intro ε hε
  -- Choose C_ε = 1/(4ε)
  refine ⟨1 / (4 * ε), by positivity, ?_⟩
  intro u hu_diff hu'_int hu_int x
  -- Apply bounded interval version on [x - 1/(2ε), x + 1/(2ε)]
  -- then bound local integrals by global ones
  sorry

/-! ## §3 Summary of Sobolev proof requirements

### What Mathlib has:
1. `intervalIntegral.integral_eq_sub_of_hasDerivAt` — FTC
2. `MeasureTheory.set_integral_mono_set` — integral monotonicity
3. `inner_mul_le_norm_mul` — abstract Cauchy-Schwarz
4. `abs_inner_le_norm` — absolute value of inner product

### What's missing:
1. Sobolev space H¹(ℝ) as a type
2. Density of C^∞_c in H¹ (needs mollifiers)
3. Explicit integration by parts theorem (in weak formulation)
4. Trace operator as bounded map H¹ → C⁰

### Estimated effort:
- sobolev_trace_bounded_interval: DONE (proved in SobolevProof.lean)
- sobolevTraceInequality_proof: 1-2 months (needs Mathlib H¹ PR) -/

end Goldbach.KLMN