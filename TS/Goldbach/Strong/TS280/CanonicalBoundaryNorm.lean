import Mathlib.Tactic
import TS.Goldbach.Strong.TS279.BufferedQuotientHolomorphicLogConstruction

/-!
# TS280 - Canonical Boundary Norm

TS279 reduced the generic finite Jensen theorem to a pointwise norm bound for
`D.f` on the averaging sphere.  This sprint fills that final generic slot by
compactness.

The set of boundary norm values is the continuous image of a compact sphere.
Its supremum is therefore finite.  Taking `max 1` with this supremum gives a
positive canonical majorant, independent of any chosen maximizing witness.

The resulting theorem closes finite Jensen for every already-constructed
`BufferedJensenFactorizationData`.  The majorant is noncomputable and no
effective dependence on the radius is claimed.
-/

noncomputable section

namespace TS280
namespace Goldbach

open Complex Metric Set Topology

/-- Boundary values of the norm of the TS275 analytic function. -/
def boundaryNormValues
    (D : TS275.Goldbach.BufferedJensenFactorizationData) : Set Real :=
  (fun z : Complex => Complex.abs (D.f z)) ''
    Metric.sphere
      D.zeroData.config.center D.zeroData.config.averagingRadius

/-- The canonical compact boundary majorant. -/
noncomputable def canonicalBoundaryNorm
    (D : TS275.Goldbach.BufferedJensenFactorizationData) : Real :=
  max 1 (sSup (boundaryNormValues D))

theorem averagingSphere_compact
    (D : TS275.Goldbach.BufferedJensenFactorizationData) :
    IsCompact
      (Metric.sphere
        D.zeroData.config.center D.zeroData.config.averagingRadius) :=
  isCompact_sphere _ _

theorem averagingSphere_subset_analyticClosedBall
    (D : TS275.Goldbach.BufferedJensenFactorizationData) :
    Metric.sphere
        D.zeroData.config.center D.zeroData.config.averagingRadius <=
      Metric.closedBall
        D.zeroData.config.center D.zeroData.config.analyticRadius := by
  intro z hz
  have hAbs :
      Complex.abs (z - D.zeroData.config.center) =
        D.zeroData.config.averagingRadius := by
    rw [Metric.mem_sphere, dist_eq_norm, Complex.norm_eq_abs] at hz
    exact hz
  exact D.zeroData.config.averagingSphere_mem_analyticClosedBall z hAbs

theorem f_continuousOn_averagingSphere
    (D : TS275.Goldbach.BufferedJensenFactorizationData) :
    ContinuousOn D.f
      (Metric.sphere
        D.zeroData.config.center D.zeroData.config.averagingRadius) := by
  intro z hz
  exact (D.f_analytic z
    (averagingSphere_subset_analyticClosedBall D hz)).continuousAt.continuousWithinAt

theorem abs_f_continuousOn_averagingSphere
    (D : TS275.Goldbach.BufferedJensenFactorizationData) :
    ContinuousOn
      (fun z : Complex => Complex.abs (D.f z))
      (Metric.sphere
        D.zeroData.config.center D.zeroData.config.averagingRadius) :=
  Complex.continuous_abs.comp_continuousOn'
    (f_continuousOn_averagingSphere D)

theorem boundaryNormValues_compact
    (D : TS275.Goldbach.BufferedJensenFactorizationData) :
    IsCompact (boundaryNormValues D) := by
  unfold boundaryNormValues
  exact (averagingSphere_compact D).image_of_continuousOn
    (abs_f_continuousOn_averagingSphere D)

theorem boundaryNormValues_bddAbove
    (D : TS275.Goldbach.BufferedJensenFactorizationData) :
    BddAbove (boundaryNormValues D) :=
  (boundaryNormValues_compact D).bddAbove

theorem norm_mem_boundaryNormValues
    (D : TS275.Goldbach.BufferedJensenFactorizationData)
    (z : Complex)
    (hz :
      Complex.abs (z - D.zeroData.config.center) =
        D.zeroData.config.averagingRadius) :
    Membership.mem (boundaryNormValues D) (Complex.abs (D.f z)) := by
  unfold boundaryNormValues
  refine Exists.intro z (And.intro ?_ rfl)
  rw [Metric.mem_sphere, dist_eq_norm, Complex.norm_eq_abs]
  exact hz

theorem norm_le_boundarySup
    (D : TS275.Goldbach.BufferedJensenFactorizationData)
    (z : Complex)
    (hz :
      Complex.abs (z - D.zeroData.config.center) =
        D.zeroData.config.averagingRadius) :
    Complex.abs (D.f z) <= sSup (boundaryNormValues D) :=
  le_csSup (boundaryNormValues_bddAbove D)
    (norm_mem_boundaryNormValues D z hz)

theorem canonicalBoundaryNorm_positive
    (D : TS275.Goldbach.BufferedJensenFactorizationData) :
    0 < canonicalBoundaryNorm D := by
  unfold canonicalBoundaryNorm
  exact zero_lt_one.trans_le (le_max_left _ _)

theorem norm_le_canonicalBoundaryNorm
    (D : TS275.Goldbach.BufferedJensenFactorizationData)
    (z : Complex)
    (hz :
      Complex.abs (z - D.zeroData.config.center) =
        D.zeroData.config.averagingRadius) :
    Complex.abs (D.f z) <= canonicalBoundaryNorm D :=
  (norm_le_boundarySup D z hz).trans (le_max_right _ _)

/-- The canonical majorant fills the final TS275 boundary contract. -/
noncomputable def canonicalBoundaryNormStatement
    (D : TS275.Goldbach.BufferedJensenFactorizationData) :
    TS275.Goldbach.BoundaryNormOnAveragingSphereStatement
      D (canonicalBoundaryNorm D) where
  M_positive := canonicalBoundaryNorm_positive D
  norm_le := norm_le_canonicalBoundaryNorm D

/-- Generic finite Jensen with the canonical compact boundary majorant. -/
theorem finiteJensenBoundaryEstimate_canonical
    (D : TS275.Goldbach.BufferedJensenFactorizationData) :
    TS274.Goldbach.FiniteJensenBoundaryEstimateStatement
      D.zeroData.toJensenInnerZeroData.toFiniteJensenDiskData
      D.f (canonicalBoundaryNorm D) :=
  TS279.Goldbach.finiteJensenBoundaryEstimate_of_boundaryNorm
    D (canonicalBoundaryNorm D) (canonicalBoundaryNormStatement D)

/-- Direct multiplicity-count facade for downstream consumers. -/
theorem finiteJensenMultiplicityCount_le_canonical
    (D : TS275.Goldbach.BufferedJensenFactorizationData) :
    (TS274.Goldbach.finiteJensenMultiplicityCount
        D.zeroData.toJensenInnerZeroData.toFiniteJensenDiskData : Real) <=
      TS274.Goldbach.finiteJensenBoundaryLogBudget
          (canonicalBoundaryNorm D) (D.f D.zeroData.config.center) /
        Real.log
          (D.zeroData.config.averagingRadius /
            D.zeroData.config.innerRadius) :=
  TS274.Goldbach.finiteJensenMultiplicityCount_le_boundaryLogQuotient
    D.zeroData.toJensenInnerZeroData.toFiniteJensenDiskData
    D.f (canonicalBoundaryNorm D)
    (finiteJensenBoundaryEstimate_canonical D)

structure CanonicalBoundaryNormLedger where
  ts279_holomorphic_log :
    TS279.Goldbach.BufferedQuotientHolomorphicLogConstructionLedger

  canonical_norm :
    TS275.Goldbach.BufferedJensenFactorizationData -> Real

  canonical_norm_eq :
    canonical_norm = canonicalBoundaryNorm

  canonical_norm_positive :
    forall D : TS275.Goldbach.BufferedJensenFactorizationData,
      0 < canonical_norm D

  canonical_boundary_statement :
    forall D : TS275.Goldbach.BufferedJensenFactorizationData,
      TS275.Goldbach.BoundaryNormOnAveragingSphereStatement
        D (canonical_norm D)

  generic_jensen_boundary_estimate :
    forall D : TS275.Goldbach.BufferedJensenFactorizationData,
      TS274.Goldbach.FiniteJensenBoundaryEstimateStatement
        D.zeroData.toJensenInnerZeroData.toFiniteJensenDiskData
        D.f (canonical_norm D)

  generic_jensen_counting_inequality :
    forall D : TS275.Goldbach.BufferedJensenFactorizationData,
      (TS274.Goldbach.finiteJensenMultiplicityCount
          D.zeroData.toJensenInnerZeroData.toFiniteJensenDiskData : Real) <=
        TS274.Goldbach.finiteJensenBoundaryLogBudget
            (canonical_norm D) (D.f D.zeroData.config.center) /
          Real.log
            (D.zeroData.config.averagingRadius /
              D.zeroData.config.innerRadius)

  canonical_norm_noncomputable : True
  concrete_buffered_factorization_not_constructed : True
  effective_radius_growth_not_proved : True
  concrete_riemann_xi_not_defined : True
  effective_zero_count_not_proved : True
  explicit_formula_not_proved : True
  gallagher_not_proved : True
  otsa_bridge_not_proved : True
  goldbach_not_claimed : True

noncomputable def canonicalBoundaryNormLedger : CanonicalBoundaryNormLedger where
  ts279_holomorphic_log :=
    TS279.Goldbach.bufferedQuotientHolomorphicLogConstructionLedger
  canonical_norm := canonicalBoundaryNorm
  canonical_norm_eq := rfl
  canonical_norm_positive := canonicalBoundaryNorm_positive
  canonical_boundary_statement := canonicalBoundaryNormStatement
  generic_jensen_boundary_estimate := finiteJensenBoundaryEstimate_canonical
  generic_jensen_counting_inequality :=
    finiteJensenMultiplicityCount_le_canonical
  canonical_norm_noncomputable := True.intro
  concrete_buffered_factorization_not_constructed := True.intro
  effective_radius_growth_not_proved := True.intro
  concrete_riemann_xi_not_defined := True.intro
  effective_zero_count_not_proved := True.intro
  explicit_formula_not_proved := True.intro
  gallagher_not_proved := True.intro
  otsa_bridge_not_proved := True.intro
  goldbach_not_claimed := True.intro

def CanonicalBoundaryNormTarget : Prop :=
  Nonempty CanonicalBoundaryNormLedger

theorem canonicalBoundaryNormTarget : CanonicalBoundaryNormTarget :=
  Nonempty.intro canonicalBoundaryNormLedger

end Goldbach
end TS280
