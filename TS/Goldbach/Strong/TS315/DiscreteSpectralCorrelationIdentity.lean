import Mathlib.Tactic
import TS.Goldbach.Strong.TS314.FiniteQuadraticSpectralMomentGoodScale

namespace TS315
namespace Goldbach

noncomputable section

/-!
# Discrete spectral correlation identity

This module expands the exact TS314 finite quadratic moment as a finite double
sum over the concrete TS292 zero truncation.  All multiplicities, signs, and
Mellin denominators are inherited from `infiniteZeroSpectralTerm`; no manual
coefficient model and no reciprocal zeta derivative are introduced.

The total correlation is split into its diagonal and weighted off-diagonal
parts.  The aggregate off-diagonal estimate remains a named, uninhabited
contract.  A future discrete oscillatory argument must use the stored
height-scale compatibility and preserve the full project weights.
-/

abbrev ConcreteNontrivialZero := TS292.Goldbach.ConcreteNontrivialZero

/-- Exact finite zero set used at truncation height `T`. -/
noncomputable def truncatedZeroSet
    (T : Nat) : Finset ConcreteNontrivialZero :=
  TS292.Goldbach.concreteZerosUpToHeightSubtype T

/-- One exact normalized TS292 spectral term at arithmetic scale `x`. -/
noncomputable def normalizedTruncatedZeroTerm
    (x : Nat)
    (rho : ConcreteNontrivialZero) : Complex :=
  (TS313.Goldbach.canonicalTraceNormalizationFactor x : Complex) *
    TS292.Goldbach.infiniteZeroSpectralTerm x rho

/-- The TS314 truncated value is the sum of its exact normalized terms. -/
theorem normalizedTruncatedSpectralValue_eq_sum
    (x T : Nat) :
    TS314.Goldbach.normalizedTruncatedSpectralValue x T =
      Finset.sum (truncatedZeroSet T)
        (fun rho => normalizedTruncatedZeroTerm x rho) := by
  unfold TS314.Goldbach.normalizedTruncatedSpectralValue
    TS292.Goldbach.truncatedInfiniteZeroContribution
    truncatedZeroSet normalizedTruncatedZeroTerm
  rw [Finset.mul_sum]

/-- Finite algebraic expansion of a squared complex norm. -/
theorem norm_sum_sq_cast_eq_double_sum
    {alpha : Type*}
    [DecidableEq alpha]
    (s : Finset alpha)
    (f : alpha -> Complex) :
    ((norm (Finset.sum s f) ^ 2 : Real) : Complex) =
      Finset.sum s (fun rho =>
        Finset.sum s (fun sigma =>
          f rho * (starRingEnd Complex) (f sigma))) := by
  calc
    ((norm (Finset.sum s f) ^ 2 : Real) : Complex) =
        Finset.sum s f *
          (starRingEnd Complex) (Finset.sum s f) := by
      symm
      simpa only [Complex.ofReal_pow] using
        Complex.mul_conj' (Finset.sum s f)
    _ = Finset.sum s (fun rho =>
        Finset.sum s (fun sigma =>
          f rho * (starRingEnd Complex) (f sigma))) := by
      rw [map_sum, Finset.mul_sum]
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]

/-- Pointwise squared-size expansion for the exact truncated zero family. -/
theorem normalizedTruncatedSpectralSize_sq_cast_eq_double_sum
    (x T : Nat) :
    ((TS314.Goldbach.normalizedTruncatedSpectralSize x T ^ 2 : Real) :
        Complex) =
      Finset.sum (truncatedZeroSet T) (fun rho =>
        Finset.sum (truncatedZeroSet T) (fun sigma =>
          normalizedTruncatedZeroTerm x rho *
            (starRingEnd Complex)
              (normalizedTruncatedZeroTerm x sigma))) := by
  unfold TS314.Goldbach.normalizedTruncatedSpectralSize
  rw [normalizedTruncatedSpectralValue_eq_sum]
  exact norm_sum_sq_cast_eq_double_sum
    (truncatedZeroSet T)
    (fun rho => normalizedTruncatedZeroTerm x rho)

/-! ## Fubini-reordered pair kernel -/

/--
Exact normalized correlation kernel for one ordered pair of concrete zeros.
It already contains multiplicities, Mellin denominators, and the factor
`(2 / x)^2` inherited from TS314.
-/
noncomputable def normalizedZeroPairCorrelationKernel
    (X : Nat)
  (rho sigma : ConcreteNontrivialZero) : Complex :=
  Finset.sum (TS314.Goldbach.dyadicWindow X) (fun x =>
    normalizedTruncatedZeroTerm x rho *
      (starRingEnd Complex) (normalizedTruncatedZeroTerm x sigma))

/-- Complete ordered-pair correlation average below height `T`. -/
noncomputable def totalNormalizedZeroPairCorrelation
    (X T : Nat) : Complex :=
  (Finset.sum (truncatedZeroSet T) (fun rho =>
      Finset.sum (truncatedZeroSet T) (fun sigma =>
        normalizedZeroPairCorrelationKernel X rho sigma))) /
    (X : Complex)

/-- Finite Fubini identifies the TS314 moment with the pair correlation. -/
theorem finiteQuadraticSpectralMoment_cast_eq_pairCorrelation
    (X T : Nat) :
    (TS314.Goldbach.finiteQuadraticSpectralMoment X T : Complex) =
      totalNormalizedZeroPairCorrelation X T := by
  rw [TS314.Goldbach.finiteQuadraticSpectralMoment_eq_sum_div_scale]
  unfold totalNormalizedZeroPairCorrelation
    normalizedZeroPairCorrelationKernel
  push_cast
  apply congrArg (fun z : Complex => z / (X : Complex))
  calc
    Finset.sum (TS314.Goldbach.dyadicWindow X) (fun x =>
        (TS314.Goldbach.normalizedTruncatedSpectralSize x T : Complex) ^ 2) =
      Finset.sum (TS314.Goldbach.dyadicWindow X) (fun x =>
        Finset.sum (truncatedZeroSet T) (fun rho =>
          Finset.sum (truncatedZeroSet T) (fun sigma =>
            normalizedTruncatedZeroTerm x rho *
              (starRingEnd Complex)
                (normalizedTruncatedZeroTerm x sigma)))) := by
      apply Finset.sum_congr rfl
      intro x hx
      simpa only [Complex.ofReal_pow] using
        normalizedTruncatedSpectralSize_sq_cast_eq_double_sum x T
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro rho hRho
      rw [Finset.sum_comm]

/-! ## Diagonal and weighted off-diagonal separation -/

/-- Exact diagonal part of the ordered-pair correlation. -/
noncomputable def diagonalNormalizedZeroPairCorrelation
    (X T : Nat) : Complex :=
  (Finset.sum (truncatedZeroSet T) (fun rho =>
      normalizedZeroPairCorrelationKernel X rho rho)) /
    (X : Complex)

/-- Exact weighted off-diagonal part; each second index excludes the first. -/
noncomputable def offDiagonalNormalizedZeroPairCorrelation
    (X T : Nat) : Complex :=
  (Finset.sum (truncatedZeroSet T) (fun rho =>
      Finset.sum ((truncatedZeroSet T).erase rho) (fun sigma =>
        normalizedZeroPairCorrelationKernel X rho sigma))) /
    (X : Complex)

theorem totalNormalizedZeroPairCorrelation_eq_diagonal_add_offDiagonal
    (X T : Nat) :
    totalNormalizedZeroPairCorrelation X T =
      diagonalNormalizedZeroPairCorrelation X T +
        offDiagonalNormalizedZeroPairCorrelation X T := by
  unfold totalNormalizedZeroPairCorrelation
    diagonalNormalizedZeroPairCorrelation
    offDiagonalNormalizedZeroPairCorrelation
  rw [(add_div _ _ _).symm]
  apply congrArg (fun z : Complex => z / (X : Complex))
  calc
    Finset.sum (truncatedZeroSet T) (fun rho =>
        Finset.sum (truncatedZeroSet T) (fun sigma =>
          normalizedZeroPairCorrelationKernel X rho sigma)) =
      Finset.sum (truncatedZeroSet T) (fun rho =>
        normalizedZeroPairCorrelationKernel X rho rho +
          Finset.sum ((truncatedZeroSet T).erase rho) (fun sigma =>
            normalizedZeroPairCorrelationKernel X rho sigma)) := by
      apply Finset.sum_congr rfl
      intro rho hRho
      rw [add_comm]
      exact (Finset.sum_erase_add _ _ hRho).symm
    _ = _ := Finset.sum_add_distrib

/-- The diagonal is bounded by its explicit finite norm mass. -/
theorem diagonalNormalizedZeroPairCorrelation_norm_le
    (X T : Nat) :
    norm (diagonalNormalizedZeroPairCorrelation X T) <=
      Finset.sum (truncatedZeroSet T) (fun rho =>
        norm
          (normalizedZeroPairCorrelationKernel X rho rho /
            (X : Complex))) := by
  unfold diagonalNormalizedZeroPairCorrelation
  rw [Finset.sum_div]
  exact norm_sum_le _ _

/-- A real upper bound for the exact finite diagonal correlation. -/
def DiagonalZeroCorrelationBoundStatement
    (X T : Nat)
    (diagonalMajorant : Real) : Prop :=
  norm (diagonalNormalizedZeroPairCorrelation X T) <= diagonalMajorant

/--
Aggregate weighted off-diagonal correlation contract.

This is deliberately a bound on the complete project-weighted pair sum, not
a pointwise kernel estimate and not an unweighted count of close ordinates.
-/
def WeightedZeroOrdinatePairCorrelationWindowBoundStatement
    (X T : Nat)
    (offDiagonalMajorant : Real) : Prop :=
  4 * T <= X /\
    0 <= offDiagonalMajorant /\
      norm (offDiagonalNormalizedZeroPairCorrelation X T) <=
        offDiagonalMajorant

/-- Diagonal and weighted off-diagonal bounds control the full moment. -/
theorem finiteQuadraticSpectralMoment_le_of_pair_bounds
    (X T : Nat)
    (diagonalMajorant offDiagonalMajorant q : Real)
    (hDiagonal :
      DiagonalZeroCorrelationBoundStatement X T diagonalMajorant)
    (hOffDiagonal :
      WeightedZeroOrdinatePairCorrelationWindowBoundStatement
        X T offDiagonalMajorant)
    (hTotal : diagonalMajorant + offDiagonalMajorant <= q ^ 2) :
    TS314.Goldbach.FiniteQuadraticSpectralMomentBoundStatement X T q := by
  unfold TS314.Goldbach.FiniteQuadraticSpectralMomentBoundStatement
  have hCast := finiteQuadraticSpectralMoment_cast_eq_pairCorrelation X T
  have hReal :
      TS314.Goldbach.finiteQuadraticSpectralMoment X T =
        (totalNormalizedZeroPairCorrelation X T).re := by
    have := congrArg Complex.re hCast
    simpa using this
  calc
    TS314.Goldbach.finiteQuadraticSpectralMoment X T =
        (totalNormalizedZeroPairCorrelation X T).re := hReal
    _ <= norm (totalNormalizedZeroPairCorrelation X T) :=
      (by
        simpa [Complex.norm_eq_abs] using
          Complex.re_le_abs (totalNormalizedZeroPairCorrelation X T))
    _ = norm
        (diagonalNormalizedZeroPairCorrelation X T +
          offDiagonalNormalizedZeroPairCorrelation X T) := by
      rw [totalNormalizedZeroPairCorrelation_eq_diagonal_add_offDiagonal]
    _ <= norm (diagonalNormalizedZeroPairCorrelation X T) +
        norm (offDiagonalNormalizedZeroPairCorrelation X T) :=
      norm_add_le _ _
    _ <= diagonalMajorant + offDiagonalMajorant :=
      add_le_add hDiagonal hOffDiagonal.2.2
    _ <= q ^ 2 := hTotal

/-- TS315 audit ledger. -/
structure TS315Ledger where
  exact_ts292_coefficients_preserved : True
  reciprocal_zeta_derivative_not_introduced : True
  pointwise_norm_square_expanded : True
  finite_fubini_reordering_proved : True
  diagonal_off_diagonal_split_proved : True
  diagonal_norm_mass_reduction_proved : True
  weighted_pair_contract_named : True
  kusmin_landau_bound_not_proved : True
  weighted_pair_correlation_bound_not_proved : True
  finite_moment_bound_not_inhabited : True
  normalized_budget_not_constructed : True
  rh_not_assumed : True
  otsa_not_proved : True
  goldbach_not_claimed : True

def ts315Ledger : TS315Ledger where
  exact_ts292_coefficients_preserved := True.intro
  reciprocal_zeta_derivative_not_introduced := True.intro
  pointwise_norm_square_expanded := True.intro
  finite_fubini_reordering_proved := True.intro
  diagonal_off_diagonal_split_proved := True.intro
  diagonal_norm_mass_reduction_proved := True.intro
  weighted_pair_contract_named := True.intro
  kusmin_landau_bound_not_proved := True.intro
  weighted_pair_correlation_bound_not_proved := True.intro
  finite_moment_bound_not_inhabited := True.intro
  normalized_budget_not_constructed := True.intro
  rh_not_assumed := True.intro
  otsa_not_proved := True.intro
  goldbach_not_claimed := True.intro

end

end Goldbach
end TS315
