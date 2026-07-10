import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Integrals
import TS.Goldbach.Strong.TS242.DirichletAbelSummationIdentityDischarge
import TS.Goldbach.Strong.TS238.AbelToCutoffBridgeFrontier

/-!
# TS243 - Dirichlet Cutoff Abel Final-Value Identification

TS242 established the finite Abel summation identity, and TS241 established
that the unit Dirichlet partial integral `F(T)` converges to the canonical
cutoff limit `dirichletCutoffLimit`.

This sprint begins the local final-value identification route.  It proves that,
for each fixed positive damping parameter, the finite Abel averages from TS242
tend to the already evaluated damped Dirichlet value.

The remaining final-value estimate, which sends `b -> 0+`, is kept as a named
local target rather than replaced by a general Tauberian theorem.
-/

namespace TS243
namespace Goldbach

open Filter MeasureTheory
open scoped Topology

/-- Fixed-damping Abel averages tend to the damped Dirichlet value. -/
def InfiniteAbelAverageStatement : Prop :=
  forall b : Real,
    0 < b ->
      Tendsto
        (fun T : Real => TS242.Goldbach.dirichletAbelAverage b T)
        atTop
        (nhds (Real.pi / 2 - Real.arctan b))

/--
The local final-value target.  Since TS241 already proves that the cutoff
partial integral converges, this is the only missing Abel identification
statement needed to identify the cutoff limit.
-/
def AbelAverageFinalValueStatement : Prop :=
  Tendsto
    (fun b : Real => Real.pi / 2 - Real.arctan b)
    (nhdsWithin (0 : Real) (Set.Ioi (0 : Real)))
    (nhds TS241.Goldbach.dirichletCutoffLimit)

/-- The fixed-damping Abel averages inherit their value from TS237 and TS242. -/
theorem infiniteAbelAverage :
    InfiniteAbelAverageStatement := by
  intro b hb
  have hDamped :
      Tendsto
        (fun T : Real => TS232.Goldbach.dampedPartialIntegral b T)
        atTop
        (nhds (Real.pi / 2 - Real.arctan b)) :=
    TS237.Goldbach.dampedDirichletEvaluationTarget b hb
  have hBoundary :
      Tendsto
        (fun T : Real =>
          Real.exp (-b * T) *
            TS228.Goldbach.dirichletUnitPartialIntegral T)
        atTop
        (nhds (0 : Real)) :=
    TS242.Goldbach.dampedCutoffBoundary_tendsto_zero b hb
  have hSub :
      Tendsto
        (fun T : Real =>
          TS232.Goldbach.dampedPartialIntegral b T -
            Real.exp (-b * T) *
              TS228.Goldbach.dirichletUnitPartialIntegral T)
        atTop
        (nhds (Real.pi / 2 - Real.arctan b)) := by
    simpa using hDamped.sub hBoundary
  apply hSub.congr'
  filter_upwards [eventually_ge_atTop (0 : Real)] with T hT
  have hIdentity :=
    TS242.Goldbach.dampedPartialIntegral_eq_boundary_add_abelAverage
      b T hb hT
  linarith

/-- The basic global bound `|F(x)| <= |x|` inherited from TS242. -/
theorem dirichletUnitPartialIntegral_abs_le
    (x : Real) :
    |TS228.Goldbach.dirichletUnitPartialIntegral x| <= |x| := by
  have h :=
    TS242.Goldbach.dirichletUnitPartialIntegral_sub_abs_le 0 x
  simpa [TS242.Goldbach.dirichletUnitPartialIntegral_zero] using h

/-- Exact finite integral of the exponential damping factor. -/
theorem expNegMul_intervalIntegral_eq
    (b a c : Real)
    (hb : Not (b = 0)) :
    intervalIntegral
        (fun x : Real => Real.exp (-b * x))
        a
        c
        volume =
      (Real.exp (-b * a) - Real.exp (-b * c)) / b := by
  have hderiv :
      forall x : Real,
        HasDerivAt
          (fun y : Real => Real.exp (-b * y) / (-b))
          (Real.exp (-b * x))
          x := by
    intro x
    have hlin :
        HasDerivAt (fun y : Real => -b * y) (-b) x := by
      simpa using (hasDerivAt_id x).const_mul (-b)
    have hExp := hlin.exp
    have hdiv := hExp.div_const (-b)
    convert hdiv using 1
    field_simp [hb]
  calc
    intervalIntegral
        (fun x : Real => Real.exp (-b * x))
        a
        c
        volume =
      Real.exp (-b * c) / (-b) -
        Real.exp (-b * a) / (-b) := by
          exact
            intervalIntegral.integral_eq_sub_of_hasDerivAt
              (fun x _hx => hderiv x)
              (by
                apply Continuous.intervalIntegrable
                fun_prop)
    _ = (Real.exp (-b * a) - Real.exp (-b * c)) / b := by
          field_simp [hb]
          ring

/-- The scaled exponential mass on a positive interval is bounded by one. -/
theorem scaled_expNegMul_intervalIntegral_le_one
    (b R T : Real)
    (hb : 0 < b)
    (hR : 0 <= R)
    (hRT : R <= T) :
    b *
        intervalIntegral
        (fun x : Real => Real.exp (-b * x))
        R
        T
        volume <=
      (1 : Real) := by
  have _hRT_used : R <= T := hRT
  rw [expNegMul_intervalIntegral_eq b R T hb.ne']
  have hexp_nonneg : 0 <= Real.exp (-b * T) :=
    (Real.exp_pos _).le
  have hdiff_le : Real.exp (-b * R) - Real.exp (-b * T) <=
      Real.exp (-b * R) := by
    linarith
  have hExpR_le_one : Real.exp (-b * R) <= 1 := by
    have hnonpos : -b * R <= 0 := by nlinarith
    simpa using (Real.exp_le_one_iff).mpr hnonpos
  calc
    b * ((Real.exp (-b * R) - Real.exp (-b * T)) / b)
        = Real.exp (-b * R) - Real.exp (-b * T) := by
          field_simp [hb.ne']
    _ <= Real.exp (-b * R) := hdiff_le
    _ <= 1 := hExpR_le_one

private theorem exp_times_partial_intervalIntegrable
    (b a c : Real) :
    IntervalIntegrable
      (fun x : Real =>
        Real.exp (-b * x) *
          TS228.Goldbach.dirichletUnitPartialIntegral x)
      volume
      a
      c := by
  have hcont :
      ContinuousOn
        (fun x : Real =>
          Real.exp (-b * x) *
            TS228.Goldbach.dirichletUnitPartialIntegral x)
        (Set.uIcc a c) := by
    exact
      ((by fun_prop :
        Continuous (fun x : Real => Real.exp (-b * x))).continuousOn).mul
        TS242.Goldbach.dirichletUnitPartialIntegral_continuous.continuousOn
  exact hcont.intervalIntegrable

private theorem exp_times_const_intervalIntegrable
    (b L a c : Real) :
    IntervalIntegrable
      (fun x : Real => Real.exp (-b * x) * L)
      volume
      a
      c := by
  apply Continuous.intervalIntegrable
  fun_prop

private theorem exp_times_centered_intervalIntegrable
    (b L a c : Real) :
    IntervalIntegrable
      (fun x : Real =>
        Real.exp (-b * x) *
          (TS228.Goldbach.dirichletUnitPartialIntegral x - L))
      volume
      a
      c := by
  have hcont :
      ContinuousOn
        (fun x : Real =>
          Real.exp (-b * x) *
            (TS228.Goldbach.dirichletUnitPartialIntegral x - L))
        (Set.uIcc a c) := by
    exact
      ((by fun_prop :
        Continuous (fun x : Real => Real.exp (-b * x))).continuousOn).mul
        (TS242.Goldbach.dirichletUnitPartialIntegral_continuous.continuousOn.sub
          continuousOn_const)
  exact hcont.intervalIntegrable

/-- Center the finite Abel average at the already constructed cutoff limit. -/
theorem dirichletAbelAverage_sub_cutoffLimit_mass
    (b T : Real)
    (hb : 0 < b) :
    TS242.Goldbach.dirichletAbelAverage b T -
        TS241.Goldbach.dirichletCutoffLimit *
          (1 - Real.exp (-b * T)) =
      b *
        intervalIntegral
          (fun x : Real =>
            Real.exp (-b * x) *
              (TS228.Goldbach.dirichletUnitPartialIntegral x -
                TS241.Goldbach.dirichletCutoffLimit))
          0
          T
          volume := by
  let L : Real := TS241.Goldbach.dirichletCutoffLimit
  let F : Real -> Real := TS228.Goldbach.dirichletUnitPartialIntegral
  have hExpInt :
      intervalIntegral
          (fun x : Real => Real.exp (-b * x))
          0
          T
          volume =
        (1 - Real.exp (-b * T)) / b := by
    simpa using expNegMul_intervalIntegral_eq b 0 T hb.ne'
  have hMass :
      b *
          intervalIntegral
            (fun x : Real => Real.exp (-b * x))
            0
            T
            volume =
        1 - Real.exp (-b * T) := by
    rw [hExpInt]
    field_simp [hb.ne']
  have hConst :
      intervalIntegral
          (fun x : Real => Real.exp (-b * x) * L)
          0
          T
          volume =
        L *
          intervalIntegral
            (fun x : Real => Real.exp (-b * x))
            0
            T
            volume := by
    calc
      intervalIntegral
          (fun x : Real => Real.exp (-b * x) * L)
          0
          T
          volume =
        intervalIntegral
          (fun x : Real => L * Real.exp (-b * x))
          0
          T
          volume := by
            congr 1
            ext x
            ring
      _ =
        L *
          intervalIntegral
            (fun x : Real => Real.exp (-b * x))
            0
            T
            volume := by
              rw [intervalIntegral.integral_const_mul]
  have hSub :
      intervalIntegral
          (fun x : Real =>
            Real.exp (-b * x) * F x -
              Real.exp (-b * x) * L)
          0
          T
          volume =
        intervalIntegral
            (fun x : Real => Real.exp (-b * x) * F x)
            0
            T
            volume -
          intervalIntegral
            (fun x : Real => Real.exp (-b * x) * L)
            0
            T
            volume := by
    exact
      intervalIntegral.integral_sub
        (exp_times_partial_intervalIntegrable b 0 T)
        (exp_times_const_intervalIntegrable b L 0 T)
  unfold TS242.Goldbach.dirichletAbelAverage
  calc
    b *
          intervalIntegral
            (fun x : Real =>
              Real.exp (-b * x) *
                TS228.Goldbach.dirichletUnitPartialIntegral x)
            0
            T
            volume -
        TS241.Goldbach.dirichletCutoffLimit *
          (1 - Real.exp (-b * T)) =
      b *
        (intervalIntegral
            (fun x : Real =>
              Real.exp (-b * x) *
                TS228.Goldbach.dirichletUnitPartialIntegral x)
            0
            T
            volume -
          TS241.Goldbach.dirichletCutoffLimit *
            intervalIntegral
              (fun x : Real => Real.exp (-b * x))
              0
              T
              volume) := by
        rw [<- hMass]
        ring
    _ =
      b *
        (intervalIntegral
            (fun x : Real =>
              Real.exp (-b * x) *
                TS228.Goldbach.dirichletUnitPartialIntegral x)
            0
            T
            volume -
          intervalIntegral
            (fun x : Real =>
              Real.exp (-b * x) *
                TS241.Goldbach.dirichletCutoffLimit)
            0
            T
            volume) := by
        rw [hConst]
    _ =
      b *
        intervalIntegral
          (fun x : Real =>
            Real.exp (-b * x) *
              TS228.Goldbach.dirichletUnitPartialIntegral x -
                Real.exp (-b * x) *
                  TS241.Goldbach.dirichletCutoffLimit)
          0
          T
          volume := by
        rw [hSub]
    _ =
      b *
        intervalIntegral
          (fun x : Real =>
            Real.exp (-b * x) *
              (TS228.Goldbach.dirichletUnitPartialIntegral x -
                TS241.Goldbach.dirichletCutoffLimit))
          0
          T
          volume := by
        congr 1
        apply intervalIntegral.integral_congr
        intro x _hx
        ring

/-- Compact pointwise bound for the centered Abel integrand. -/
theorem centered_abel_integrand_compact_bound
    (b R x : Real)
    (hb : 0 < b)
    (hR : 0 <= R)
    (hx0 : 0 <= x)
    (hxR : x <= R) :
    |Real.exp (-b * x) *
        (TS228.Goldbach.dirichletUnitPartialIntegral x -
          TS241.Goldbach.dirichletCutoffLimit)| <=
      R + |TS241.Goldbach.dirichletCutoffLimit| := by
  have _hR_used : 0 <= R := hR
  have hExp_le_one : |Real.exp (-b * x)| <= (1 : Real) := by
    have hnonpos : -b * x <= 0 := by nlinarith
    have hle : Real.exp (-b * x) <= 1 :=
      (Real.exp_le_one_iff).mpr hnonpos
    simpa [abs_of_pos (Real.exp_pos _)] using hle
  have hF_abs :
      |TS228.Goldbach.dirichletUnitPartialIntegral x| <= R := by
    have hFx := dirichletUnitPartialIntegral_abs_le x
    have hxabs : |x| <= R := by
      simpa [abs_of_nonneg hx0] using hxR
    exact hFx.trans hxabs
  have hcenter :
      |TS228.Goldbach.dirichletUnitPartialIntegral x -
          TS241.Goldbach.dirichletCutoffLimit| <=
        R + |TS241.Goldbach.dirichletCutoffLimit| := by
    calc
      |TS228.Goldbach.dirichletUnitPartialIntegral x -
          TS241.Goldbach.dirichletCutoffLimit| <=
        |TS228.Goldbach.dirichletUnitPartialIntegral x| +
          |TS241.Goldbach.dirichletCutoffLimit| := by
            simpa [sub_eq_add_neg] using
              abs_add
                (TS228.Goldbach.dirichletUnitPartialIntegral x)
                (-TS241.Goldbach.dirichletCutoffLimit)
      _ <= R + |TS241.Goldbach.dirichletCutoffLimit| := by
            exact add_le_add_right hF_abs _
  calc
    |Real.exp (-b * x) *
        (TS228.Goldbach.dirichletUnitPartialIntegral x -
          TS241.Goldbach.dirichletCutoffLimit)| =
      |Real.exp (-b * x)| *
        |TS228.Goldbach.dirichletUnitPartialIntegral x -
          TS241.Goldbach.dirichletCutoffLimit| := by
        rw [abs_mul]
    _ <= 1 * (R + |TS241.Goldbach.dirichletCutoffLimit|) := by
        exact mul_le_mul hExp_le_one hcenter (abs_nonneg _) (by norm_num)
    _ = R + |TS241.Goldbach.dirichletCutoffLimit| := by ring

/-- Tail pointwise bound for the centered Abel integrand. -/
theorem centered_abel_integrand_tail_bound
    (b eta x : Real)
    (heta : 0 <= eta)
    (htail :
      |TS228.Goldbach.dirichletUnitPartialIntegral x -
        TS241.Goldbach.dirichletCutoffLimit| <= eta) :
    |Real.exp (-b * x) *
        (TS228.Goldbach.dirichletUnitPartialIntegral x -
          TS241.Goldbach.dirichletCutoffLimit)| <=
      eta * Real.exp (-b * x) := by
  have _heta_used : 0 <= eta := heta
  have hExp_nonneg : 0 <= Real.exp (-b * x) :=
    (Real.exp_pos _).le
  calc
    |Real.exp (-b * x) *
        (TS228.Goldbach.dirichletUnitPartialIntegral x -
          TS241.Goldbach.dirichletCutoffLimit)| =
      Real.exp (-b * x) *
        |TS228.Goldbach.dirichletUnitPartialIntegral x -
          TS241.Goldbach.dirichletCutoffLimit| := by
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    _ <= Real.exp (-b * x) * eta := by
        exact mul_le_mul_of_nonneg_left htail hExp_nonneg
    _ = eta * Real.exp (-b * x) := by ring

/-- Compact integral bound for the centered Abel average. -/
theorem centered_abel_compact_integral_bound
    (b R : Real)
    (hb : 0 < b)
    (hR : 0 <= R) :
    |b *
        intervalIntegral
          (fun x : Real =>
            Real.exp (-b * x) *
              (TS228.Goldbach.dirichletUnitPartialIntegral x -
                TS241.Goldbach.dirichletCutoffLimit))
          0
          R
          volume| <=
      b * (R * (R + |TS241.Goldbach.dirichletCutoffLimit|)) := by
  let C : Real := R + |TS241.Goldbach.dirichletCutoffLimit|
  have hC_nonneg : 0 <= C := by
    dsimp [C]
    positivity
  have hbound :
      forall x : Real,
        Set.uIoc (0 : Real) R x ->
          norm
            (Real.exp (-b * x) *
              (TS228.Goldbach.dirichletUnitPartialIntegral x -
                TS241.Goldbach.dirichletCutoffLimit)) <= C := by
    intro x hx
    have hxIoc : Set.Mem (Set.Ioc (0 : Real) R) x := by
      simpa [Set.uIoc_of_le hR] using hx
    simpa [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), C] using
      centered_abel_integrand_compact_bound b R x hb hR hxIoc.1.le hxIoc.2
  have hnorm :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : Real))
      (b := R)
      (C := C)
      (f := fun x : Real =>
        Real.exp (-b * x) *
          (TS228.Goldbach.dirichletUnitPartialIntegral x -
            TS241.Goldbach.dirichletCutoffLimit))
      hbound
  have hnorm' :
      |intervalIntegral
          (fun x : Real =>
            Real.exp (-b * x) *
              (TS228.Goldbach.dirichletUnitPartialIntegral x -
                TS241.Goldbach.dirichletCutoffLimit))
          0
          R
          volume| <=
        C * R := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hR, C, mul_comm, mul_left_comm,
      mul_assoc] using hnorm
  calc
    |b *
        intervalIntegral
          (fun x : Real =>
            Real.exp (-b * x) *
              (TS228.Goldbach.dirichletUnitPartialIntegral x -
                TS241.Goldbach.dirichletCutoffLimit))
          0
          R
          volume| =
      b *
        |intervalIntegral
            (fun x : Real =>
              Real.exp (-b * x) *
                (TS228.Goldbach.dirichletUnitPartialIntegral x -
                  TS241.Goldbach.dirichletCutoffLimit))
            0
            R
            volume| := by
        rw [abs_mul, abs_of_pos hb]
    _ <= b * (C * R) := by
        exact mul_le_mul_of_nonneg_left hnorm' hb.le
    _ = b * (R * (R + |TS241.Goldbach.dirichletCutoffLimit|)) := by
        dsimp [C]
        ring

/-- Tail integral bound once the cutoff partial integral is close to its limit. -/
theorem centered_abel_tail_integral_bound
    (b eta R T : Real)
    (hb : 0 < b)
    (heta : 0 <= eta)
    (hR : 0 <= R)
    (hRT : R <= T)
    (hTail :
      forall x : Real,
        R <= x ->
          x <= T ->
            |TS228.Goldbach.dirichletUnitPartialIntegral x -
              TS241.Goldbach.dirichletCutoffLimit| <= eta) :
    |b *
        intervalIntegral
          (fun x : Real =>
            Real.exp (-b * x) *
              (TS228.Goldbach.dirichletUnitPartialIntegral x -
                TS241.Goldbach.dirichletCutoffLimit))
          R
          T
          volume| <=
      eta := by
  let f : Real -> Real := fun x =>
    Real.exp (-b * x) *
      (TS228.Goldbach.dirichletUnitPartialIntegral x -
        TS241.Goldbach.dirichletCutoffLimit)
  let g : Real -> Real := fun x => eta * Real.exp (-b * x)
  have hgInt : IntervalIntegrable g volume R T := by
    apply Continuous.intervalIntegrable
    dsimp [g]
    fun_prop
  have hbound :
      forall x : Real,
        Set.uIoc R T x ->
          norm (f x) <= g x := by
    intro x hx
    have hxIoc : Set.Mem (Set.Ioc R T) x := by
      simpa [Set.uIoc_of_le hRT] using hx
    have htailx :
        |TS228.Goldbach.dirichletUnitPartialIntegral x -
          TS241.Goldbach.dirichletCutoffLimit| <= eta :=
      hTail x hxIoc.1.le hxIoc.2
    simpa [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), f, g] using
      centered_abel_integrand_tail_bound b eta x heta htailx
  have hnorm :=
    intervalIntegral.norm_integral_le_of_norm_le
      (a := R)
      (b := T)
      (f := f)
      (g := g)
      ((ae_restrict_iff' measurableSet_uIoc).mpr
        (Eventually.of_forall hbound))
      hgInt
  have hExpInt_nonneg :
      0 <=
        intervalIntegral
          (fun x : Real => Real.exp (-b * x))
          R
          T
          volume := by
    exact
      intervalIntegral.integral_nonneg hRT
        (fun x _hx => (Real.exp_pos (-b * x)).le)
  have hgIntegral :
      intervalIntegral g R T volume =
        eta *
          intervalIntegral
            (fun x : Real => Real.exp (-b * x))
            R
            T
            volume := by
    dsimp [g]
    rw [intervalIntegral.integral_const_mul]
  have hnorm' :
      |intervalIntegral f R T volume| <=
        eta *
          intervalIntegral
            (fun x : Real => Real.exp (-b * x))
            R
            T
            volume := by
    have hg_nonneg :
        0 <=
          eta *
            intervalIntegral
              (fun x : Real => Real.exp (-b * x))
              R
              T
              volume := by
      exact mul_nonneg heta hExpInt_nonneg
    calc
      |intervalIntegral f R T volume| =
        norm (intervalIntegral f R T volume) := by
          simp [Real.norm_eq_abs]
      _ <= |intervalIntegral g R T volume| := hnorm
      _ = eta *
          intervalIntegral
            (fun x : Real => Real.exp (-b * x))
            R
            T
            volume := by
          rw [hgIntegral, abs_of_nonneg hg_nonneg]
  have hscaled :
      b *
          intervalIntegral
            (fun x : Real => Real.exp (-b * x))
            R
            T
            volume <=
        (1 : Real) :=
    scaled_expNegMul_intervalIntegral_le_one b R T hb hR hRT
  have hmain :
      b *
          |intervalIntegral f R T volume| <=
        eta := by
    calc
      b * |intervalIntegral f R T volume| <=
        b *
          (eta *
            intervalIntegral
              (fun x : Real => Real.exp (-b * x))
              R
              T
              volume) := by
          exact mul_le_mul_of_nonneg_left hnorm' hb.le
      _ = eta *
          (b *
            intervalIntegral
              (fun x : Real => Real.exp (-b * x))
              R
              T
              volume) := by ring
      _ <= eta * 1 := by
          exact mul_le_mul_of_nonneg_left hscaled heta
      _ = eta := by ring
  simpa [f, abs_mul, abs_of_pos hb] using hmain

/--
Finite centered Abel bound obtained by cutting the integral at a fixed `R`.
The compact part is paid for by the small factor `b`; the tail part is paid
for by the eventual closeness of the cutoff partial integral to its limit.
-/
theorem centered_abel_finite_bound
    (b eta R T : Real)
    (hb : 0 < b)
    (heta : 0 <= eta)
    (hR : 0 <= R)
    (hRT : R <= T)
    (hTail :
      forall x : Real,
        R <= x ->
          x <= T ->
            |TS228.Goldbach.dirichletUnitPartialIntegral x -
              TS241.Goldbach.dirichletCutoffLimit| <= eta) :
    |TS242.Goldbach.dirichletAbelAverage b T -
        TS241.Goldbach.dirichletCutoffLimit *
          (1 - Real.exp (-b * T))| <=
      b * (R * (R + |TS241.Goldbach.dirichletCutoffLimit|)) + eta := by
  let L : Real := TS241.Goldbach.dirichletCutoffLimit
  let f : Real -> Real := fun x =>
    Real.exp (-b * x) *
      (TS228.Goldbach.dirichletUnitPartialIntegral x - L)
  have hsplit :
      intervalIntegral f 0 T volume =
        intervalIntegral f 0 R volume +
          intervalIntegral f R T volume := by
    exact
      (intervalIntegral.integral_add_adjacent_intervals
        (exp_times_centered_intervalIntegrable b L 0 R)
        (exp_times_centered_intervalIntegrable b L R T)).symm
  have hcompact :
      |b * intervalIntegral f 0 R volume| <=
        b * (R * (R + |TS241.Goldbach.dirichletCutoffLimit|)) := by
    simpa [f, L] using
      centered_abel_compact_integral_bound b R hb hR
  have htail :
      |b * intervalIntegral f R T volume| <= eta := by
    simpa [f, L] using
      centered_abel_tail_integral_bound b eta R T hb heta hR hRT hTail
  have hcenter :=
    dirichletAbelAverage_sub_cutoffLimit_mass b T hb
  calc
    |TS242.Goldbach.dirichletAbelAverage b T -
        TS241.Goldbach.dirichletCutoffLimit *
          (1 - Real.exp (-b * T))| =
      |b * intervalIntegral f 0 T volume| := by
        rw [hcenter]
    _ = |b * intervalIntegral f 0 R volume +
          b * intervalIntegral f R T volume| := by
        rw [hsplit]
        ring_nf
    _ <= |b * intervalIntegral f 0 R volume| +
          |b * intervalIntegral f R T volume| := by
        exact abs_add _ _
    _ <= b * (R * (R + |TS241.Goldbach.dirichletCutoffLimit|)) + eta := by
        exact add_le_add hcompact htail

/--
The local Abel final-value theorem.  Since TS241 has already proved that
`F(T)` has a finite cutoff limit `L`, the Abel averages of `F` converge back to
`L` as the damping parameter tends to zero.  Comparing this with the evaluated
damped Dirichlet value identifies the final scalar limit.
-/
theorem abelAverageFinalValue :
    AbelAverageFinalValueStatement := by
  unfold AbelAverageFinalValueStatement
  let L : Real := TS241.Goldbach.dirichletCutoffLimit
  let scalar : Real -> Real := fun b => Real.pi / 2 - Real.arctan b
  change Tendsto scalar (nhdsWithin (0 : Real) (Set.Ioi (0 : Real))) (nhds L)
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro eps heps
  let eta : Real := eps / 5
  have heta : 0 < eta := by
    dsimp [eta]
    positivity
  have heta_nonneg : 0 <= eta := heta.le
  have hCutMetric :=
    Metric.tendsto_atTop.1
      TS241.Goldbach.tendsto_dirichletCutoffLimit
      eta
      heta
  let R0 : Real := Classical.choose hCutMetric
  have hR0 :
      forall n : Real, R0 <= n ->
        dist (TS228.Goldbach.dirichletUnitPartialIntegral n) L < eta := by
    simpa [L] using Classical.choose_spec hCutMetric
  let R : Real := max R0 1
  have hR0_le_R : R0 <= R := by
    dsimp [R]
    exact le_max_left _ _
  have hR_nonneg : 0 <= R := by
    dsimp [R]
    have hOne : (0 : Real) <= (1 : Real) := by norm_num
    exact le_trans hOne (le_max_right _ _)
  have hR_pos : 0 < R := by
    dsimp [R]
    have hOne : (1 : Real) <= max R0 (1 : Real) := le_max_right _ _
    linarith
  let K : Real := R * (R + |L|)
  have hK_nonneg : 0 <= K := by
    dsimp [K]
    positivity
  have hK_one_pos : 0 < K + 1 := by
    dsimp [K]
    positivity
  let delta : Real := eta / (K + 1)
  have hdelta_pos : 0 < delta := by
    dsimp [delta]
    positivity
  refine Exists.intro delta (And.intro hdelta_pos ?_)
  intro b hbWithin hbDist
  have hb : 0 < b := by
    simpa using hbWithin
  have hb_lt_delta : b < delta := by
    have hdist_abs : |b - 0| < delta := by
      simpa [Real.dist_eq] using hbDist
    simpa [abs_of_pos hb] using hdist_abs
  have hb_lt_eta_div : b < eta / (K + 1) := by
    simpa [delta] using hb_lt_delta
  have hbK_lt_eta : b * K < eta := by
    have hmul_le :
        b * K <= (eta / (K + 1)) * K := by
      exact mul_le_mul_of_nonneg_right (le_of_lt hb_lt_eta_div) hK_nonneg
    have hfrac_lt :
        (eta / (K + 1)) * K < eta := by
      have hK_ratio : K / (K + 1) < 1 := by
        rw [div_lt_one hK_one_pos]
        linarith
      have hrewrite :
          (eta / (K + 1)) * K = eta * (K / (K + 1)) := by
        field_simp [hK_one_pos.ne']
      calc
        (eta / (K + 1)) * K = eta * (K / (K + 1)) := hrewrite
        _ < eta * 1 := by
          exact mul_lt_mul_of_pos_left hK_ratio heta
        _ = eta := by ring
    exact lt_of_le_of_lt hmul_le hfrac_lt
  have hAvgTendsto :
      Tendsto
        (fun T : Real => TS242.Goldbach.dirichletAbelAverage b T)
        atTop
        (nhds (scalar b)) := by
    simpa [scalar] using infiniteAbelAverage b hb
  have hMassTendsto :
      Tendsto
        (fun T : Real => L * (1 - Real.exp (-b * T)))
        atTop
        (nhds L) := by
    have hscale :
        Tendsto (fun T : Real => -b * T) atTop atBot := by
      exact tendsto_id.const_mul_atTop_of_neg (by linarith)
    have hexp :
        Tendsto
          (fun T : Real => Real.exp (-b * T))
          atTop
          (nhds (0 : Real)) :=
      Real.tendsto_exp_atBot.comp hscale
    have hone :
        Tendsto
          (fun T : Real => 1 - Real.exp (-b * T))
          atTop
          (nhds (1 : Real)) := by
      simpa using (tendsto_const_nhds.sub hexp)
    have hmul := (tendsto_const_nhds (x := L)).mul hone
    simpa using hmul
  have hAvgMetric := Metric.tendsto_atTop.1 hAvgTendsto eta heta
  have hMassMetric := Metric.tendsto_atTop.1 hMassTendsto eta heta
  let Navg : Real := Classical.choose hAvgMetric
  have hNavg :
      forall n : Real, Navg <= n ->
        dist (TS242.Goldbach.dirichletAbelAverage b n) (scalar b) < eta :=
    Classical.choose_spec hAvgMetric
  let Nmass : Real := Classical.choose hMassMetric
  have hNmass :
      forall n : Real, Nmass <= n ->
        dist (L * (1 - Real.exp (-b * n))) L < eta :=
    Classical.choose_spec hMassMetric
  let T : Real := max R (max Navg Nmass)
  have hRT : R <= T := by
    dsimp [T]
    exact le_max_left _ _
  have hNavgT : Navg <= T := by
    dsimp [T]
    exact le_trans (le_max_left Navg Nmass) (le_max_right _ _)
  have hNmassT : Nmass <= T := by
    dsimp [T]
    exact le_trans (le_max_right Navg Nmass) (le_max_right _ _)
  have hTail :
      forall x : Real,
        R <= x ->
          x <= T ->
            |TS228.Goldbach.dirichletUnitPartialIntegral x - L| <= eta := by
    intro x hxR _hxT
    have hR0x : R0 <= x := le_trans hR0_le_R hxR
    have hx := hR0 x hR0x
    exact le_of_lt (by simpa [Real.dist_eq, L] using hx)
  have hCentered :
      |TS242.Goldbach.dirichletAbelAverage b T -
          L * (1 - Real.exp (-b * T))| <=
        b * K + eta := by
    simpa [K, L] using
      centered_abel_finite_bound b eta R T hb heta_nonneg hR_nonneg hRT hTail
  have hCentered_lt :
      |TS242.Goldbach.dirichletAbelAverage b T -
          L * (1 - Real.exp (-b * T))| < 2 * eta := by
    exact lt_of_le_of_lt hCentered (by nlinarith)
  have hAvg_abs :
      |scalar b - TS242.Goldbach.dirichletAbelAverage b T| < eta := by
    have hdist := hNavg T hNavgT
    simpa [Real.dist_eq, abs_sub_comm] using hdist
  have hMass_abs :
      |L * (1 - Real.exp (-b * T)) - L| < eta := by
    have hdist := hNmass T hNmassT
    simpa [Real.dist_eq] using hdist
  have hTri :
      |scalar b - L| <=
        |scalar b - TS242.Goldbach.dirichletAbelAverage b T| +
          |TS242.Goldbach.dirichletAbelAverage b T -
            L * (1 - Real.exp (-b * T))| +
          |L * (1 - Real.exp (-b * T)) - L| := by
    set S := scalar b
    set A := TS242.Goldbach.dirichletAbelAverage b T
    set M := L * (1 - Real.exp (-b * T))
    have hsplit : S - L = (S - A) + (A - M) + (M - L) := by ring
    calc
      |S - L| = |(S - A) + (A - M) + (M - L)| := by rw [hsplit]
      _ <= |(S - A) + (A - M)| + |M - L| := by
          exact abs_add _ _
      _ <= (|S - A| + |A - M|) + |M - L| := by
          exact add_le_add_right (abs_add _ _) _
      _ = |S - A| + |A - M| + |M - L| := by ring
  have hSum :
      |scalar b - TS242.Goldbach.dirichletAbelAverage b T| +
          |TS242.Goldbach.dirichletAbelAverage b T -
            L * (1 - Real.exp (-b * T))| +
          |L * (1 - Real.exp (-b * T)) - L| < eps := by
    have heta_eq : eps = 5 * eta := by
      dsimp [eta]
      ring
    nlinarith
  have hAbs : |scalar b - L| < eps :=
    lt_of_le_of_lt hTri hSum
  simpa [Real.dist_eq] using hAbs

/--
The final-value theorem, kept as the one local analytic target after the
fixed-damping Abel average has been evaluated.
-/
def LocalAbelFinalValueTheoremStatement : Prop :=
  AbelAverageFinalValueStatement

/-- TS243 discharges the local Abel final-value theorem. -/
theorem localAbelFinalValue :
    LocalAbelFinalValueTheoremStatement :=
  abelAverageFinalValue

/-- The cutoff limit extracted in TS241 is `pi/2`. -/
theorem dirichletCutoffLimit_eq_pi_div_two :
    TS241.Goldbach.dirichletCutoffLimit = Real.pi / 2 := by
  have hPi : TS229.Goldbach.DampedDirichletAbelLimitStatement :=
    TS229.Goldbach.dampedDirichletAbelLimit
  exact tendsto_nhds_unique localAbelFinalValue hPi

/-- Compatibility wrapper for older TS243 routing statements. -/
theorem dirichletCutoffLimit_eq_pi_div_two_of_finalValue
    (_hFinal : LocalAbelFinalValueTheoremStatement) :
    TS241.Goldbach.dirichletCutoffLimit = Real.pi / 2 :=
  dirichletCutoffLimit_eq_pi_div_two

/--
If the local final-value statement is supplied, the TS228 one-sided cutoff
target follows from the already constructed TS241 cutoff limit.
-/
theorem dirichletUnitPartialIntegralAtTop_of_finalValue
    (hFinal : LocalAbelFinalValueTheoremStatement) :
    TS228.Goldbach.DirichletUnitPartialIntegralAtTopStatement := by
  have hEq := dirichletCutoffLimit_eq_pi_div_two_of_finalValue hFinal
  simpa [TS228.Goldbach.DirichletUnitPartialIntegralAtTopStatement, hEq] using
    TS241.Goldbach.tendsto_dirichletCutoffLimit

/-- TS243 identifies the one-sided unit Dirichlet cutoff value. -/
theorem dirichletUnitPartialIntegralAtTop :
    TS228.Goldbach.DirichletUnitPartialIntegralAtTopStatement :=
  dirichletUnitPartialIntegralAtTop_of_finalValue localAbelFinalValue

/-- If the local final-value theorem is supplied, the TS229 Abel-to-cutoff bridge follows. -/
theorem abelToCutoffBridge_of_finalValue
    (hFinal : LocalAbelFinalValueTheoremStatement) :
    TS229.Goldbach.AbelToCutoffBridgeStatement := by
  intro _hDampedEvaluation _hAbelLimit
  exact dirichletUnitPartialIntegralAtTop_of_finalValue hFinal

/-- TS243 closes the TS229 Abel-to-cutoff bridge. -/
theorem abelToCutoffBridge :
    TS229.Goldbach.AbelToCutoffBridgeStatement :=
  abelToCutoffBridge_of_finalValue localAbelFinalValue

/-- If the local final-value theorem is supplied, the TS238 frontier is closed. -/
theorem abelToCutoffBridgeFrontier_of_finalValue
    (hFinal : LocalAbelFinalValueTheoremStatement) :
    TS238.Goldbach.AbelToCutoffBridgeFrontierStatement := by
  exact abelToCutoffBridge_of_finalValue hFinal

/-- TS243 closes the TS238 Abel-to-cutoff frontier. -/
theorem abelToCutoffBridgeFrontier :
    TS238.Goldbach.AbelToCutoffBridgeFrontierStatement :=
  abelToCutoffBridgeFrontier_of_finalValue localAbelFinalValue

/-- Ledger recording the TS243 final-value discharge. -/
structure DirichletCutoffAbelFinalValueIdentificationLedger where
  ts242_abel_identity :
    TS242.Goldbach.DirichletAbelSummationIdentityDischargeLedger

  infinite_abel_average_statement : Prop
  infinite_abel_average_statement_eq :
    infinite_abel_average_statement = InfiniteAbelAverageStatement
  infinite_abel_average_proved :
    infinite_abel_average_statement

  final_value_statement : Prop
  final_value_statement_eq :
    final_value_statement = LocalAbelFinalValueTheoremStatement
  final_value_proved :
    final_value_statement

  final_value_supplies_cutoff_limit :
    LocalAbelFinalValueTheoremStatement ->
      TS241.Goldbach.dirichletCutoffLimit = Real.pi / 2
  cutoff_value_pi_over_two_proved :
    TS241.Goldbach.dirichletCutoffLimit = Real.pi / 2

  final_value_supplies_ts228 :
    LocalAbelFinalValueTheoremStatement ->
      TS228.Goldbach.DirichletUnitPartialIntegralAtTopStatement
  ts228_atTop_proved :
    TS228.Goldbach.DirichletUnitPartialIntegralAtTopStatement

  final_value_supplies_abel_to_cutoff :
    LocalAbelFinalValueTheoremStatement ->
      TS229.Goldbach.AbelToCutoffBridgeStatement
  abel_to_cutoff_bridge_proved :
    TS229.Goldbach.AbelToCutoffBridgeStatement
  abel_to_cutoff_frontier_proved :
    TS238.Goldbach.AbelToCutoffBridgeFrontierStatement

  cos_square_integral_value_not_proved : True
  canonical_sinc_fourth_value_not_proved : True
  plancherel_not_proved : True
  explicit_formula_not_proved : True
  gallagher_not_proved : True
  goldbach_not_claimed : True

/-- Concrete TS243 final-value frontier ledger. -/
noncomputable def dirichletCutoffAbelFinalValueIdentificationLedger :
    DirichletCutoffAbelFinalValueIdentificationLedger where
  ts242_abel_identity :=
    TS242.Goldbach.dirichletAbelSummationIdentityDischargeLedger
  infinite_abel_average_statement :=
    InfiniteAbelAverageStatement
  infinite_abel_average_statement_eq := rfl
  infinite_abel_average_proved :=
    infiniteAbelAverage
  final_value_statement :=
    LocalAbelFinalValueTheoremStatement
  final_value_statement_eq := rfl
  final_value_proved :=
    localAbelFinalValue
  final_value_supplies_cutoff_limit :=
    dirichletCutoffLimit_eq_pi_div_two_of_finalValue
  cutoff_value_pi_over_two_proved :=
    dirichletCutoffLimit_eq_pi_div_two
  final_value_supplies_ts228 :=
    dirichletUnitPartialIntegralAtTop_of_finalValue
  ts228_atTop_proved :=
    dirichletUnitPartialIntegralAtTop
  final_value_supplies_abel_to_cutoff :=
    abelToCutoffBridge_of_finalValue
  abel_to_cutoff_bridge_proved :=
    abelToCutoffBridge
  abel_to_cutoff_frontier_proved :=
    abelToCutoffBridgeFrontier
  cos_square_integral_value_not_proved := True.intro
  canonical_sinc_fourth_value_not_proved := True.intro
  plancherel_not_proved := True.intro
  explicit_formula_not_proved := True.intro
  gallagher_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS243. -/
def DirichletCutoffAbelFinalValueIdentificationTarget : Prop :=
  Nonempty DirichletCutoffAbelFinalValueIdentificationLedger

/-- TS243 target: the local Abel final-value theorem identifies the cutoff limit. -/
theorem dirichletCutoffAbelFinalValueIdentificationTarget :
    DirichletCutoffAbelFinalValueIdentificationTarget :=
  Nonempty.intro dirichletCutoffAbelFinalValueIdentificationLedger

end Goldbach
end TS243
