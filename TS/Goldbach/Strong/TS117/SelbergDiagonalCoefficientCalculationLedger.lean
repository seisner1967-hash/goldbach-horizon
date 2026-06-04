import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Tactic
import TS.Goldbach.Strong.TS116.SelbergGcdCoefficientKernelMatchLedger

namespace TS117
namespace Goldbach

/-!
# TS117 - Selberg Diagonal Coefficient Calculation Ledger

TS116 exposes the local compatibility obligation between the one-variable
gcd-indexed coefficient and the canonical dense `gcd/lcm` kernel.

This sprint performs the first calculation audit of that obligation. It records
a standard Mobius-square/totient coefficient candidate as a local arithmetic
slot, but more importantly proves a concrete obstruction for the current
TS109--TS116 shape: any coefficient depending only on `gcd(m,n)` cannot equal
the pair-dependent kernel `gcd(m,n)/lcm(m,n)` for all pairs.

Thus TS117 does not close the Selberg diagonal coefficient calculation. It
shows that the present diagonal interface must be refined before the
dense-to-diagonal identity can be discharged.
-/

/-- A standard Selberg-style Mobius-square/totient coefficient candidate. -/
def selbergMobiusSquareTotientCoefficient
    (d : Nat) :
    Rat :=
  if d = 0 then 0
  else ((ArithmeticFunction.moebius d : Rat) ^ (2 : Nat)) / (d.totient : Rat)

/-- The Mobius-square/totient candidate is normalized to `1` at `d = 1`. -/
theorem selbergMobiusSquareTotientCoefficient_one :
    selbergMobiusSquareTotientCoefficient 1 = 1 := by
  unfold selbergMobiusSquareTotientCoefficient
  norm_num

/--
The finite gcd coefficient obtained from the Mobius-square/totient candidate.

This is a calculation slot, not yet wired into TS109's canonical diagonal side.
-/
def selbergMobiusSquareTotientGcdCoefficient
    (level : Nat)
    (g : Nat) :
    Rat :=
  Finset.sum (TS115.Goldbach.selbergGcdCoefficientSupport level g) fun d =>
    selbergMobiusSquareTotientCoefficient d

/-- The candidate gcd coefficient is definitionally its filtered finite sum. -/
theorem selbergMobiusSquareTotientGcdCoefficient_eq_filter_sum
    (level : Nat)
    (g : Nat) :
    selbergMobiusSquareTotientGcdCoefficient level g =
      Finset.sum (TS115.Goldbach.selbergGcdCoefficientSupport level g) fun d =>
        selbergMobiusSquareTotientCoefficient d :=
  rfl

/-- Kernel value at `(2,4)` for the canonical dense gcd/lcm kernel. -/
theorem canonicalKernel_two_four :
    TS107.Goldbach.canonicalSelbergQuadraticKernel 2 4 = (1 / 2 : Rat) := by
  norm_num
    [TS107.Goldbach.canonicalSelbergQuadraticKernel,
      TS106.Goldbach.canonicalGcdKernel,
      TS106.Goldbach.canonicalLcmKernel]

/-- Kernel value at `(2,6)` for the canonical dense gcd/lcm kernel. -/
theorem canonicalKernel_two_six :
    TS107.Goldbach.canonicalSelbergQuadraticKernel 2 6 = (1 / 3 : Rat) := by
  norm_num
    [TS107.Goldbach.canonicalSelbergQuadraticKernel,
      TS106.Goldbach.canonicalGcdKernel,
      TS106.Goldbach.canonicalLcmKernel]

/-- The two displayed dense-kernel values are propositionally different. -/
theorem canonicalKernel_two_four_ne_two_six :
    (TS107.Goldbach.canonicalSelbergQuadraticKernel 2 4 =
      TS107.Goldbach.canonicalSelbergQuadraticKernel 2 6) -> False := by
  rw [canonicalKernel_two_four, canonicalKernel_two_six]
  norm_num

/--
No one-variable coefficient of `gcd(m,n)` can match the canonical dense
`gcd/lcm` kernel for all pairs.
-/
theorem no_gcd_only_coefficient_matches_canonicalKernel
    (coefficient : Nat -> Rat) :
    ((forall m n : Nat,
      coefficient (Nat.gcd m n) =
        TS107.Goldbach.canonicalSelbergQuadraticKernel m n) -> False) := by
  intro H
  have h24 := H 2 4
  have h26 := H 2 6
  have hEq :
      TS107.Goldbach.canonicalSelbergQuadraticKernel 2 4 =
        TS107.Goldbach.canonicalSelbergQuadraticKernel 2 6 := by
    rw [<- h24, <- h26]
    norm_num
  exact canonicalKernel_two_four_ne_two_six hEq

/--
The current TS116 compatibility obligation is impossible as stated.

The reason is structural: the TS115 coefficient depends only on
`Nat.gcd m n`, but the TS107 dense kernel depends on both `gcd` and `lcm`.
-/
theorem no_selbergGcdCoefficientKernelCompatibility
    (level : Nat)
    (weight : Nat -> Rat) :
    (TS116.Goldbach.SelbergGcdCoefficientKernelCompatibility level weight ->
      False) := by
  unfold TS116.Goldbach.SelbergGcdCoefficientKernelCompatibility
  unfold TS116.Goldbach.selbergCanonicalKernelFromGcd
  exact
    no_gcd_only_coefficient_matches_canonicalKernel
      (TS115.Goldbach.selbergGcdCoefficient level weight)

/--
Diagnostic package for the current diagonal coefficient calculation layer.

The positive fields expose the candidate arithmetic coefficient slot. The
obstruction field records that the present TS109--TS116 one-variable gcd shape
cannot close the canonical `gcd/lcm` kernel match.
-/
structure SelbergDiagonalCoefficientCalculation where
  candidateCoefficient :
    Nat -> Rat

  candidate_coefficient_eq :
    forall d : Nat,
      candidateCoefficient d = selbergMobiusSquareTotientCoefficient d

  candidate_normalized_at_one :
    candidateCoefficient 1 = 1

  candidateGcdCoefficient :
    Nat -> Nat -> Rat

  candidate_gcd_coefficient_eq :
    forall level g : Nat,
      candidateGcdCoefficient level g =
        selbergMobiusSquareTotientGcdCoefficient level g

  currentKernelObstruction :
    forall coefficient : Nat -> Rat,
      ((forall m n : Nat,
        coefficient (Nat.gcd m n) =
          TS107.Goldbach.canonicalSelbergQuadraticKernel m n) -> False)

  currentTS116CompatibilityObstruction :
    forall level : Nat,
      forall weight : Nat -> Rat,
        (TS116.Goldbach.SelbergGcdCoefficientKernelCompatibility
          level
          weight -> False)

  diagonal_slot_refinement_needed :
    True

  pair_or_lcm_sensitive_normalization_needed :
    True

  dense_to_diagonal_identity_still_open :
    True

/-- Concrete TS117 diagnostic package. -/
def selbergDiagonalCoefficientCalculation :
    SelbergDiagonalCoefficientCalculation where
  candidateCoefficient := selbergMobiusSquareTotientCoefficient
  candidate_coefficient_eq := by
    intro d
    rfl
  candidate_normalized_at_one :=
    selbergMobiusSquareTotientCoefficient_one
  candidateGcdCoefficient :=
    selbergMobiusSquareTotientGcdCoefficient
  candidate_gcd_coefficient_eq := by
    intro level g
    rfl
  currentKernelObstruction :=
    no_gcd_only_coefficient_matches_canonicalKernel
  currentTS116CompatibilityObstruction :=
    no_selbergGcdCoefficientKernelCompatibility
  diagonal_slot_refinement_needed := True.intro
  pair_or_lcm_sensitive_normalization_needed := True.intro
  dense_to_diagonal_identity_still_open := True.intro

/-- Target proposition for the TS117 coefficient calculation diagnostic. -/
def SelbergDiagonalCoefficientCalculationTarget : Prop :=
  Nonempty SelbergDiagonalCoefficientCalculation

/-- The TS117 diagnostic package is populated. -/
theorem selbergDiagonalCoefficientCalculationTarget :
    SelbergDiagonalCoefficientCalculationTarget :=
  Nonempty.intro selbergDiagonalCoefficientCalculation

/--
Compatibility with the already-built TS116 ledger: TS117 still exposes the
TS116 kernel-match layer, while proving that its current compatibility
obligation cannot be discharged without refining the diagonal normalization.
-/
theorem selbergGcdCoefficientKernelMatchTarget :
    TS116.Goldbach.SelbergGcdCoefficientKernelMatchTarget :=
  TS116.Goldbach.selbergGcdCoefficientKernelMatchTarget

end Goldbach
end TS117
