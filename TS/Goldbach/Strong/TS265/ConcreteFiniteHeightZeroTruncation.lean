import Mathlib.Topology.DiscreteSubset
import Mathlib.Tactic
import TS.Goldbach.Strong.TS264.ConcreteRiemannZetaZeroFamilyRealization

/-!
# TS265 - Concrete Finite-Height Zero Truncation

TS264 constructed the actual nontrivial Riemann-zeta zero family and its
analytic multiplicities.  This sprint proves that the selected zeros below
every real height form a finite set and turns that set into an exact `Finset`.

The global zero set is shown closed and discrete.  Away from one this follows
from isolated zeros and analytic uniqueness; at one the zeta residue gives a
punctured neighborhood without zeros.  Closed discreteness implies finite
intersection with compact sets.  A simple norm bound then places every
height-truncated nontrivial zero in a compact closed ball.

The resulting noncomputable `Finset` instantiates the exact TS256 truncation
contract with height `X`.  TS264 then supplies reality, lossless real
projection, and exact absolute-value transport for the concrete finite sum.

No numerical enumeration algorithm, cardinality formula, zero-density bound,
global spectral summability, explicit formula, Gallagher estimate, or
Goldbach statement is proved.
-/

namespace TS265
namespace Goldbach

open Filter Set

def riemannZetaZeroSet : Set Complex :=
  {z | riemannZeta z = 0}

theorem riemannZeta_not_eventually_zero_of_ne_one
    (z : Complex)
    (hz : Not (z = 1)) :
    Not (Filter.Eventually (fun w => riemannZeta w = 0) (nhds z)) := by
  intro hLocal
  have hAnalyticOn :
      AnalyticOnNhd Complex riemannZeta TS263.Goldbach.zetaPuncturedDomain :=
    TS260.Goldbach.riemannZeta_differentiableOn_compl_one.analyticOnNhd
      isOpen_compl_singleton
  have hEqOn :
      Set.EqOn riemannZeta 0 TS263.Goldbach.zetaPuncturedDomain :=
    hAnalyticOn.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      TS263.Goldbach.zetaPuncturedDomain_isPreconnected
      (show TS263.Goldbach.zetaPuncturedDomain z by
        simpa [TS263.Goldbach.zetaPuncturedDomain] using hz)
      hLocal
  have hAtZero := hEqOn (show TS263.Goldbach.zetaPuncturedDomain 0 by
    change Not ((0 : Complex) = 1)
    norm_num)
  rw [riemannZeta_zero] at hAtZero
  norm_num at hAtZero

theorem riemannZeta_eventually_ne_zero_nhdsWithin_one :
    Filter.Eventually
      (fun z : Complex => Not (riemannZeta z = 0))
      (nhdsWithin (1 : Complex) (Set.compl (Set.singleton 1))) := by
  have hProduct := riemannZeta_residue_one.eventually_ne
    (show Not ((1 : Complex) = 0) by norm_num)
  filter_upwards [hProduct] with z hz
  intro hZeta
  apply hz
  rw [hZeta, mul_zero]

theorem riemannZetaZeroSet_isClosed_and_discrete :
    IsClosed riemannZetaZeroSet /\ DiscreteTopology riemannZetaZeroSet := by
  apply isClosed_and_discrete_iff.mpr
  intro z
  rw [disjoint_principal_right]
  change Filter.Eventually
    (fun w : Complex => Not (riemannZeta w = 0))
    (nhdsWithin z (Set.compl (Set.singleton z)))
  by_cases hz : z = 1
  case pos =>
    subst z
    exact riemannZeta_eventually_ne_zero_nhdsWithin_one
  case neg =>
    let hf := TS260.Goldbach.riemannZeta_analyticAt_of_ne_one z hz
    exact hf.eventually_eq_zero_or_eventually_ne_zero.resolve_left
      (riemannZeta_not_eventually_zero_of_ne_one z hz)

theorem compact_inter_riemannZetaZeroSet_finite
    (K : Set Complex)
    (hK : IsCompact K) :
    Set.Finite (Set.inter K riemannZetaZeroSet) := by
  have hClosed : IsClosed riemannZetaZeroSet :=
    riemannZetaZeroSet_isClosed_and_discrete.1
  letI : DiscreteTopology riemannZetaZeroSet :=
    riemannZetaZeroSet_isClosed_and_discrete.2
  have hTendsto :
      Tendsto ((fun z : riemannZetaZeroSet => (z : Complex)))
        cofinite (cocompact Complex) :=
    hClosed.tendsto_coe_cofinite_of_discreteTopology inferInstance
  have hPreimage :
      Set.Finite
        {z : riemannZetaZeroSet | K (z : Complex)} :=
    tendsto_cofinite_cocompact_iff.mp hTendsto K hK
  have hImage := hPreimage.image
    (fun z : riemannZetaZeroSet => (z : Complex))
  have hImageEq :
      (fun z : riemannZetaZeroSet => (z : Complex)) ''
          {z : riemannZetaZeroSet | K (z : Complex)} =
        Set.inter K riemannZetaZeroSet := by
    ext z
    constructor
    case mp =>
      intro hz
      let w : riemannZetaZeroSet := Classical.choose hz
      have hw := Classical.choose_spec hz
      have hwEq : (w : Complex) = z := hw.2
      exact And.intro
        (Eq.mp (congrArg K hwEq) hw.1)
        (Eq.mp (congrArg riemannZetaZeroSet hwEq) w.property)
    case mpr =>
      intro hz
      exact Exists.intro (Subtype.mk z hz.2) (And.intro hz.1 rfl)
  rw [hImageEq] at hImage
  exact hImage

def heightTruncatedZeroSet (T : Real) : Set Complex :=
  {rho |
    TS264.Goldbach.concreteNontrivialRiemannZetaZeroSet rho /\
      abs rho.im <= T}

theorem heightTruncatedZeroSet_subset_compact_inter
    (T : Real) :
    heightTruncatedZeroSet T <=
      Set.inter (Metric.closedBall (0 : Complex) (T + 1))
        riemannZetaZeroSet := by
  intro rho hRho
  have hStrip := TS264.Goldbach.concreteZero_in_critical_strip hRho.1
  have hReAbs : abs rho.re <= 1 := by
    rw [abs_of_pos hStrip.1]
    exact hStrip.2.le
  have hNorm : Complex.abs rho <= T + 1 := by
    calc
      Complex.abs rho <= abs rho.re + abs rho.im :=
        Complex.abs_le_abs_re_add_abs_im rho
      _ <= 1 + T := add_le_add hReAbs hRho.2
      _ = T + 1 := add_comm 1 T
  constructor
  case left =>
    rw [Metric.mem_closedBall, dist_zero_right]
    simpa using hNorm
  case right =>
    exact TS264.Goldbach.concreteZero_is_zeta_zero hRho.1

theorem heightTruncatedZeroSet_finite
    (T : Real) :
    Set.Finite (heightTruncatedZeroSet T) := by
  apply Set.Finite.subset
    (compact_inter_riemannZetaZeroSet_finite
      (Metric.closedBall (0 : Complex) (T + 1))
      (isCompact_closedBall (0 : Complex) (T + 1)))
  exact heightTruncatedZeroSet_subset_compact_inter T

noncomputable def zerosUpToHeight
    (T : Real) : Finset Complex :=
  (heightTruncatedZeroSet_finite T).toFinset

theorem mem_zerosUpToHeight_iff
    (T : Real)
    (rho : Complex) :
    Membership.mem (zerosUpToHeight T) rho <->
      TS264.Goldbach.concreteNontrivialRiemannZetaZeroSet rho /\
        abs rho.im <= T := by
  exact (heightTruncatedZeroSet_finite T).mem_toFinset

noncomputable def truncationDataOfHeight
    (height : TS256.Goldbach.ZeroTruncationHeightFunction)
    (hHeight : forall X : Nat, 0 <= height X) :
    TS256.Goldbach.RiemannZetaZeroTruncationData
      TS264.Goldbach.concreteRiemannZetaZeroFamilyContract where
  height := height
  zeros := fun X => zerosUpToHeight (height X)
  height_nonnegative := hHeight
  zeros_mem_zeroSet := by
    intro X rho hMem
    exact (mem_zerosUpToHeight_iff (height X) rho).mp hMem |>.1
  zeros_height_bounded := by
    intro X rho hMem
    exact (mem_zerosUpToHeight_iff (height X) rho).mp hMem |>.2
  zeros_complete_below_height := by
    intro X rho hZero hBound
    exact (mem_zerosUpToHeight_iff (height X) rho).mpr
      (And.intro hZero hBound)

noncomputable def concreteFiniteHeightTruncationData :
    TS256.Goldbach.RiemannZetaZeroTruncationData
      TS264.Goldbach.concreteRiemannZetaZeroFamilyContract :=
  truncationDataOfHeight
    (fun X : Nat => (X : Real))
    (fun X => Nat.cast_nonneg X)

theorem mem_concreteFiniteHeightTruncation_iff
    (X : Nat)
    (rho : Complex) :
    Membership.mem (concreteFiniteHeightTruncationData.zeros X) rho <->
      TS264.Goldbach.concreteNontrivialRiemannZetaZeroSet rho /\
        abs rho.im <= (X : Real) := by
  exact mem_zerosUpToHeight_iff (X : Real) rho

theorem concreteFiniteHeightTruncation_zeroSumReality :
    TS256.Goldbach.TruncatedZeroSumRealityStatement
      TS264.Goldbach.concreteRiemannZetaZeroFamilyContract
      concreteFiniteHeightTruncationData
      TS257.Goldbach.triangleSplineZeroSpectralSummand :=
  TS264.Goldbach.concreteTruncation_zeroSumReality
    concreteFiniteHeightTruncationData

theorem concreteFiniteHeightTruncation_realProjectionLossless
    (X : Nat) :
    ((TS257.Goldbach.triangleSplineZeroContributionFunction
      TS264.Goldbach.concreteRiemannZetaZeroFamilyContract
      concreteFiniteHeightTruncationData X : Real) : Complex) =
      TS257.Goldbach.triangleSplineZeroTruncatedComplexSum
        TS264.Goldbach.concreteRiemannZetaZeroFamilyContract
        concreteFiniteHeightTruncationData X :=
  TS264.Goldbach.concreteTruncation_realProjectionLossless
    concreteFiniteHeightTruncationData X

theorem concreteFiniteHeightTruncation_realAbs_eq_complexAbs
    (X : Nat) :
    abs
        (TS257.Goldbach.triangleSplineZeroContributionFunction
          TS264.Goldbach.concreteRiemannZetaZeroFamilyContract
          concreteFiniteHeightTruncationData X) =
      Complex.abs
        (TS257.Goldbach.triangleSplineZeroTruncatedComplexSum
          TS264.Goldbach.concreteRiemannZetaZeroFamilyContract
          concreteFiniteHeightTruncationData X) :=
  TS264.Goldbach.concreteTruncation_realAbs_eq_complexAbs
    concreteFiniteHeightTruncationData X

/-- Ledger recording the exact finite-height zero truncation. -/
structure ConcreteFiniteHeightZeroTruncationLedger where
  ts264_concrete_family :
    TS264.Goldbach.ConcreteRiemannZetaZeroFamilyRealizationLedger

  global_zero_set_closed :
    IsClosed riemannZetaZeroSet

  global_zero_set_discrete :
    DiscreteTopology riemannZetaZeroSet

  finite_below_every_height :
    forall T : Real,
      Set.Finite (heightTruncatedZeroSet T)

  exact_finite_selection :
    forall (T : Real) (rho : Complex),
      Membership.mem (zerosUpToHeight T) rho <->
        TS264.Goldbach.concreteNontrivialRiemannZetaZeroSet rho /\
          abs rho.im <= T

  concrete_ts256_truncation :
    TS256.Goldbach.RiemannZetaZeroTruncationData
      TS264.Goldbach.concreteRiemannZetaZeroFamilyContract

  concrete_zero_sum_reality :
    TS256.Goldbach.TruncatedZeroSumRealityStatement
      TS264.Goldbach.concreteRiemannZetaZeroFamilyContract
      concrete_ts256_truncation
      TS257.Goldbach.triangleSplineZeroSpectralSummand

  numerical_enumeration_algorithm_not_constructed : True
  zero_counting_bound_not_proved : True
  global_zero_summability_not_proved : True
  zero_contribution_bound_not_proved : True
  explicit_formula_identity_not_proved : True
  residual_bound_not_proved : True
  gallagher_not_proved : True
  goldbach_not_claimed : True

/-- Concrete TS265 ledger. -/
noncomputable def concreteFiniteHeightZeroTruncationLedger :
    ConcreteFiniteHeightZeroTruncationLedger where
  ts264_concrete_family :=
    TS264.Goldbach.concreteRiemannZetaZeroFamilyRealizationLedger
  global_zero_set_closed :=
    riemannZetaZeroSet_isClosed_and_discrete.1
  global_zero_set_discrete :=
    riemannZetaZeroSet_isClosed_and_discrete.2
  finite_below_every_height :=
    heightTruncatedZeroSet_finite
  exact_finite_selection :=
    mem_zerosUpToHeight_iff
  concrete_ts256_truncation :=
    concreteFiniteHeightTruncationData
  concrete_zero_sum_reality :=
    concreteFiniteHeightTruncation_zeroSumReality
  numerical_enumeration_algorithm_not_constructed := True.intro
  zero_counting_bound_not_proved := True.intro
  global_zero_summability_not_proved := True.intro
  zero_contribution_bound_not_proved := True.intro
  explicit_formula_identity_not_proved := True.intro
  residual_bound_not_proved := True.intro
  gallagher_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS265. -/
def ConcreteFiniteHeightZeroTruncationTarget : Prop :=
  Nonempty ConcreteFiniteHeightZeroTruncationLedger

/-- TS265 target: exact finite-height truncation is constructed and routed. -/
theorem concreteFiniteHeightZeroTruncationTarget :
    ConcreteFiniteHeightZeroTruncationTarget :=
  Nonempty.intro concreteFiniteHeightZeroTruncationLedger

end Goldbach
end TS265
