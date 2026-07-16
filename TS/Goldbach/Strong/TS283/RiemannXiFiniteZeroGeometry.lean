import Mathlib.Topology.DiscreteSubset
import Mathlib.Tactic
import TS.Goldbach.Strong.TS282.RiemannXiCandidateBufferedSpec

/-!
# TS283 - Riemann Xi Finite Zero Geometry

TS282 defined an entire Riemann-xi candidate and isolated the exact finite
factorization data required by the buffered Jensen pipeline.  This sprint
constructs the geometric part of those data.

The global xi-zero set is closed and discrete because the candidate is entire
and is not identically zero.  Hence its intersection with every compact set is
finite.  For every prescribed positive inner radius `r`, the finitely many xi
zero radii below `T = r + 3` have a largest value strictly below `T`.  Two
explicit affine points between that barrier and `T` provide radii
`r < R < S < T`; the collar `R <= |z| <= S` contains no xi zero.

This module constructs exact inner and factor `Finset`s and the corresponding
three-radius Jensen geometry.  It does not construct analytic multiplicities,
local normal forms, the nonvanishing quotient, an effective boundary-growth
bound, a zero-counting estimate, the explicit formula, Gallagher, OTSA, or
Goldbach.
-/

noncomputable section

namespace TS283
namespace Goldbach

open Complex Metric Set Topology Filter

/-- The global zero set of the entire xi candidate from TS282. -/
def riemannXiCandidateZeroSet : Set Complex :=
  {z | TS282.Goldbach.riemannXiCandidate z = 0}

theorem riemannXiCandidate_not_eventually_zero
    (z : Complex) :
    Not (Filter.Eventually
      (fun w => TS282.Goldbach.riemannXiCandidate w = 0) (nhds z)) := by
  intro hLocal
  have hAnalyticOn :
      AnalyticOnNhd Complex TS282.Goldbach.riemannXiCandidate Set.univ :=
    TS282.Goldbach.riemannXiCandidate_analyticOnNhd Set.univ
  have hEqOn :
      Set.EqOn TS282.Goldbach.riemannXiCandidate 0 Set.univ :=
    hAnalyticOn.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ z) hLocal
  have hAtZero := hEqOn (Set.mem_univ (0 : Complex))
  rw [TS282.Goldbach.riemannXiCandidate_zero] at hAtZero
  norm_num at hAtZero

/-- Xi zeros form a closed discrete subset of the complex plane. -/
theorem riemannXiCandidateZeroSet_isClosed_and_discrete :
    IsClosed riemannXiCandidateZeroSet /\
      DiscreteTopology riemannXiCandidateZeroSet := by
  apply isClosed_and_discrete_iff.mpr
  intro z
  rw [disjoint_principal_right]
  change Filter.Eventually
    (fun w : Complex => Not (TS282.Goldbach.riemannXiCandidate w = 0))
    (nhdsWithin z (Set.compl (Set.singleton z)))
  let hf := TS282.Goldbach.riemannXiCandidate_analyticAt z
  exact hf.eventually_eq_zero_or_eventually_ne_zero.resolve_left
      (riemannXiCandidate_not_eventually_zero z)

/-- A compact set contains only finitely many xi zeros. -/
theorem compact_inter_riemannXiCandidateZeroSet_finite
    (K : Set Complex)
    (hK : IsCompact K) :
    Set.Finite (Set.inter K riemannXiCandidateZeroSet) := by
  have hClosed : IsClosed riemannXiCandidateZeroSet :=
    riemannXiCandidateZeroSet_isClosed_and_discrete.1
  letI : DiscreteTopology riemannXiCandidateZeroSet :=
    riemannXiCandidateZeroSet_isClosed_and_discrete.2
  have hTendsto :
      Tendsto ((fun z : riemannXiCandidateZeroSet => (z : Complex)))
        cofinite (cocompact Complex) :=
    hClosed.tendsto_coe_cofinite_of_discreteTopology inferInstance
  have hPreimage :
      Set.Finite
        {z : riemannXiCandidateZeroSet | K (z : Complex)} :=
    tendsto_cofinite_cocompact_iff.mp hTendsto K hK
  have hImage := hPreimage.image
    (fun z : riemannXiCandidateZeroSet => (z : Complex))
  have hImageEq :
      (fun z : riemannXiCandidateZeroSet => (z : Complex)) ''
          {z : riemannXiCandidateZeroSet | K (z : Complex)} =
        Set.inter K riemannXiCandidateZeroSet := by
    ext z
    constructor
    case mp =>
      intro hz
      let w : riemannXiCandidateZeroSet := Classical.choose hz
      have hw := Classical.choose_spec hz
      have hwEq : (w : Complex) = z := hw.2
      exact And.intro
        (Eq.mp (congrArg K hwEq) hw.1)
        (Eq.mp (congrArg riemannXiCandidateZeroSet hwEq) w.property)
    case mpr =>
      intro hz
      let w : riemannXiCandidateZeroSet :=
        { val := z, property := hz.2 }
      exact Exists.intro w (And.intro hz.1 rfl)
  rw [hImageEq] at hImage
  exact hImage

/-- Xi zeros in a closed ball form a finite set. -/
theorem riemannXiCandidateZerosInClosedBallSet_finite
    (T : Real) :
    Set.Finite
      (Set.inter (Metric.closedBall (0 : Complex) T)
        riemannXiCandidateZeroSet) :=
  compact_inter_riemannXiCandidateZeroSet_finite
    (Metric.closedBall (0 : Complex) T)
      (isCompact_closedBall (0 : Complex) T)

/-- Exact finite selection of xi zeros in the closed ball of radius `T`. -/
noncomputable def riemannXiCandidateZerosInClosedBall
    (T : Real) : Finset Complex :=
  (riemannXiCandidateZerosInClosedBallSet_finite T).toFinset

@[simp]
theorem mem_riemannXiCandidateZerosInClosedBall_iff
    (T : Real)
    (z : Complex) :
    Membership.mem (riemannXiCandidateZerosInClosedBall T) z <->
      Complex.abs z <= T /\
        TS282.Goldbach.riemannXiCandidate z = 0 := by
  rw [riemannXiCandidateZerosInClosedBall, Set.Finite.mem_toFinset]
  constructor
  case mp =>
    intro hz
    have hzAbs : Complex.abs z <= T := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hz.1
    exact And.intro hzAbs hz.2
  case mpr =>
    intro hz
    have hzBall : Membership.mem (Metric.closedBall (0 : Complex) T) z := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hz.1
    exact And.intro hzBall hz.2

/-- Radii strictly below `T` attained by xi zeros in the closed `T`-ball. -/
noncomputable def riemannXiCandidateZeroRadiiBelow
    (T : Real) : Finset Real :=
  (riemannXiCandidateZerosInClosedBall T).image Complex.abs |>.filter
    (fun radius => radius < T)

/-- The largest relevant zero radius below `T`, with `r` inserted as a floor. -/
noncomputable def xiZeroRadiusBarrier
    (r T : Real) : Real :=
  (insert r (riemannXiCandidateZeroRadiiBelow T)).max' (by simp)

theorem innerRadius_le_xiZeroRadiusBarrier
    (r T : Real) :
    r <= xiZeroRadiusBarrier r T := by
  apply Finset.le_max'
  simp [xiZeroRadiusBarrier]

theorem xiZeroRadiusBarrier_lt
    {r T : Real}
    (hrT : r < T) :
    xiZeroRadiusBarrier r T < T := by
  rw [xiZeroRadiusBarrier, Finset.max'_lt_iff]
  intro radius hRadius
  rw [Finset.mem_insert] at hRadius
  rcases hRadius with hEq | hBelow
  case inl => simpa [hEq] using hrT
  case inr => exact (Finset.mem_filter.mp hBelow).2

theorem xiZeroRadius_le_barrier
    {r T : Real}
    {z : Complex}
    (hz : Membership.mem (riemannXiCandidateZerosInClosedBall T) z)
    (hzT : Complex.abs z < T) :
    Complex.abs z <= xiZeroRadiusBarrier r T := by
  apply Finset.le_max'
  rw [Finset.mem_insert]
  right
  rw [riemannXiCandidateZeroRadiiBelow, Finset.mem_filter]
  constructor
  case left =>
    exact Finset.mem_image.mpr (Exists.intro z (And.intro hz rfl))
  case right => exact hzT

/-- Geometric part of a future concrete TS282 xi factorization. -/
structure XiFiniteZeroGeometryData where
  config : TS275.Goldbach.JensenDiskConfiguration
  innerZeros : Finset Complex
  factorZeros : Finset Complex

  center_eq_zero : config.center = 0

  innerZeros_subset_factorZeros : innerZeros <= factorZeros

  inner_zero_mem_disk :
    forall rho : Complex,
      Membership.mem innerZeros rho ->
        Complex.abs (rho - config.center) <= config.innerRadius

  factor_zero_mem_open_disk :
    forall rho : Complex,
      Membership.mem factorZeros rho ->
        Complex.abs (rho - config.center) < config.averagingRadius

  factor_zero_iff :
    forall z : Complex,
      Membership.mem
          (Metric.closedBall config.center config.analyticRadius) z ->
        (TS282.Goldbach.riemannXiCandidate z = 0 <->
          Membership.mem factorZeros z)

  zero_free_collar :
    forall z : Complex,
      config.averagingRadius <= Complex.abs (z - config.center) ->
      Complex.abs (z - config.center) <= config.analyticRadius ->
        Not (TS282.Goldbach.riemannXiCandidate z = 0)

/-- Concrete finite xi-zero geometry for every positive inner radius. -/
noncomputable def xiFiniteZeroGeometryData
    (r : Real)
    (hr : 0 < r) : XiFiniteZeroGeometryData := by
  let T : Real := r + 3
  let L : Real := xiZeroRadiusBarrier r T
  let R : Real := (2 * L + T) / 3
  let S : Real := (L + 2 * T) / 3
  have hrT : r < T := by
    dsimp [T]
    linarith
  have hrL : r <= L := by
    exact innerRadius_le_xiZeroRadiusBarrier r T
  have hLT : L < T := xiZeroRadiusBarrier_lt hrT
  have hGapPos : 0 < (T - L) / 3 := by
    exact div_pos (sub_pos.mpr hLT) (by norm_num)
  have hLR : L < R := by
    apply sub_pos.mp
    have hEq : R - L = (T - L) / 3 := by
      dsimp only [R]
      ring
    rw [hEq]
    exact hGapPos
  have hrR : r < R := by
    exact lt_of_le_of_lt hrL hLR
  have hRS : R < S := by
    apply sub_pos.mp
    have hEq : S - R = (T - L) / 3 := by
      dsimp only [R, S]
      ring
    rw [hEq]
    exact hGapPos
  have hST : S < T := by
    rw [sub_pos.symm]
    have hEq : T - S = (T - L) / 3 := by
      dsimp only [S]
      ring
    rw [hEq]
    exact hGapPos
  let C : TS275.Goldbach.JensenDiskConfiguration :=
    { center := 0
      innerRadius := r
      averagingRadius := R
      analyticRadius := S
      innerRadius_positive := hr
      innerRadius_lt_averagingRadius := hrR
      averagingRadius_lt_analyticRadius := hRS }
  exact
    { config := C
      innerZeros := riemannXiCandidateZerosInClosedBall r
      factorZeros := riemannXiCandidateZerosInClosedBall S
      center_eq_zero := rfl
      innerZeros_subset_factorZeros := by
        intro z hz
        rw [mem_riemannXiCandidateZerosInClosedBall_iff] at hz
        rw [mem_riemannXiCandidateZerosInClosedBall_iff]
        exact And.intro
          (hz.1.trans (le_of_lt (hrR.trans hRS))) hz.2
      inner_zero_mem_disk := by
        intro z hz
        rw [mem_riemannXiCandidateZerosInClosedBall_iff] at hz
        simpa [C] using hz.1
      factor_zero_mem_open_disk := by
        intro z hz
        rw [mem_riemannXiCandidateZerosInClosedBall_iff] at hz
        have hzT : Complex.abs z < T := hz.1.trans_lt hST
        have hzMemT :
            Membership.mem (riemannXiCandidateZerosInClosedBall T) z := by
          rw [mem_riemannXiCandidateZerosInClosedBall_iff]
          exact And.intro (hz.1.trans hST.le) hz.2
        have hzL : Complex.abs z <= L :=
          xiZeroRadius_le_barrier hzMemT hzT
        simpa [C] using hzL.trans_lt hLR
      factor_zero_iff := by
        intro z hzBall
        rw [mem_riemannXiCandidateZerosInClosedBall_iff]
        have hzAbs : Complex.abs z <= S := by
          simpa [C, Metric.mem_closedBall, dist_zero_right] using hzBall
        constructor
        case mp =>
          intro hzZero
          exact And.intro hzAbs hzZero
        case mpr => exact fun hz => hz.2
      zero_free_collar := by
        intro z hzR hzS hzZero
        have hzAbsS : Complex.abs z <= S := by
          simpa [C] using hzS
        have hzT : Complex.abs z < T := hzAbsS.trans_lt hST
        have hzMemT :
            Membership.mem (riemannXiCandidateZerosInClosedBall T) z := by
          rw [mem_riemannXiCandidateZerosInClosedBall_iff]
          exact And.intro (hzAbsS.trans hST.le) hzZero
        have hzL : Complex.abs z <= L :=
          xiZeroRadius_le_barrier hzMemT hzT
        have hzR' : R <= Complex.abs z := by
          simpa [C] using hzR
        exact (not_lt_of_ge hzR') (hzL.trans_lt hLR) }

@[simp]
theorem xiFiniteZeroGeometryData_innerRadius
    (r : Real)
    (hr : 0 < r) :
    (xiFiniteZeroGeometryData r hr).config.innerRadius = r :=
  rfl

/-- Existence facade for the concrete xi finite-zero geometry. -/
theorem exists_xiFiniteZeroGeometryData
    (r : Real)
    (hr : 0 < r) :
    Exists fun G : XiFiniteZeroGeometryData => G.config.innerRadius = r :=
  Exists.intro (xiFiniteZeroGeometryData r hr) rfl

structure RiemannXiFiniteZeroGeometryLedger where
  ts282_candidate : TS282.Goldbach.RiemannXiCandidateBufferedSpecLedger
  xi_zero_set_closed_and_discrete :
    IsClosed riemannXiCandidateZeroSet /\
      DiscreteTopology riemannXiCandidateZeroSet
  compact_zero_finiteness :
    forall K : Set Complex,
      IsCompact K -> Set.Finite (Set.inter K riemannXiCandidateZeroSet)
  positive_inner_radius_geometry :
    forall r : Real,
      0 < r ->
        Exists fun G : XiFiniteZeroGeometryData => G.config.innerRadius = r
  multiplicities_not_constructed : True
  local_normal_forms_not_constructed : True
  quotient_not_constructed : True
  effective_xi_growth_not_proved : True
  zero_counting_not_proved : True
  explicit_formula_not_proved : True
  gallagher_not_proved : True
  otsa_bridge_not_proved : True
  goldbach_not_claimed : True

noncomputable def riemannXiFiniteZeroGeometryLedger :
    RiemannXiFiniteZeroGeometryLedger where
  ts282_candidate := TS282.Goldbach.riemannXiCandidateBufferedSpecLedger
  xi_zero_set_closed_and_discrete :=
    riemannXiCandidateZeroSet_isClosed_and_discrete
  compact_zero_finiteness := compact_inter_riemannXiCandidateZeroSet_finite
  positive_inner_radius_geometry := exists_xiFiniteZeroGeometryData
  multiplicities_not_constructed := True.intro
  local_normal_forms_not_constructed := True.intro
  quotient_not_constructed := True.intro
  effective_xi_growth_not_proved := True.intro
  zero_counting_not_proved := True.intro
  explicit_formula_not_proved := True.intro
  gallagher_not_proved := True.intro
  otsa_bridge_not_proved := True.intro
  goldbach_not_claimed := True.intro

def RiemannXiFiniteZeroGeometryTarget : Prop :=
  Nonempty RiemannXiFiniteZeroGeometryLedger

theorem riemannXiFiniteZeroGeometryTarget :
    RiemannXiFiniteZeroGeometryTarget :=
  Nonempty.intro riemannXiFiniteZeroGeometryLedger

end Goldbach
end TS283
