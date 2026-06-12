import Mathlib.Tactic
import TS.Goldbach.Strong.TS153.DependentSelbergBudgetFeasibilityProbe

namespace TS154
namespace Goldbach

/-!
# TS154 - Selberg Denominator Upper Bound and Obstruction Probe

TS153 extracts the exact lower threshold forced on the TS122 optimization
denominator by any successful refined Selberg/Brun-Titchmarsh comparison.
This sprint confronts that threshold with the arithmetic size of the actual
denominator.

The denominator is rewritten as a squarefree reciprocal-Jordan sum. Every
supported squarefree integer divides the product of the primes up to the
level, so the sum is dominated by a finite Euler product. Enlarging the prime
product to all integers gives the telescoping estimate

`D(level) <= product_{n=2}^level n^2 / (n^2 - 1)
          = 2 * level / (level + 1) < 2`.

Consequently any TS151 dependent scale comparison forces the exact TS153
threshold to be strictly below `2`. If the threshold is at least `2` at one
admissible pair `(x,Q)`, no choice of Selberg level can satisfy that scale
comparison there. No logarithmic growth of `D` is asserted.
-/

/-- A single summand of the TS122 optimization denominator. -/
def selbergDenominatorSummand (d : Nat) : Rat :=
  TS122.Goldbach.selbergMobiusRatCoefficient d ^ (2 : Nat) /
    TS122.Goldbach.selbergJordanTwoPenalty d



theorem squarefree_finset_prod_primes
    (s : Finset Nat)
    (hs : forall p : Nat, Membership.mem s p -> p.Prime) :
    Squarefree (Finset.prod s id) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
      rw [Finset.prod_insert hp]
      have hprime : p.Prime := hs p (Finset.mem_insert_self p s)
      have hrest : Squarefree (Finset.prod s id) := by
        apply ih
        intro q hq
        exact hs q (Finset.mem_insert_of_mem hq)
      have hcop : p.Coprime (Finset.prod s id) := by
        rw [hprime.coprime_iff_not_dvd]
        intro hpdvd
        have hex := (hprime.prime.dvd_finset_prod_iff id).1 hpdvd
        choose q hq hpq using hex
        have hqprime : q.Prime := hs q (Finset.mem_insert_of_mem hq)
        have hq_eq_p : q = p := (hqprime.dvd_iff_eq hprime.ne_one).1 hpq
        exact hp (by simpa [hq_eq_p] using hq)
      apply (Nat.squarefree_mul hcop).2
      exact And.intro hprime.squarefree hrest

/-- Primes at most the Selberg level. -/
def selbergPrimeSupport (level : Nat) : Finset Nat :=
  (Finset.range (level + 1)).filter Nat.Prime

/-- Product of all primes at most the Selberg level. -/
def selbergPrimorial (level : Nat) : Nat :=
  Finset.prod (selbergPrimeSupport level) id

theorem selbergPrimorial_squarefree
    (level : Nat) :
    Squarefree (selbergPrimorial level) := by
  apply squarefree_finset_prod_primes
  intro p hp
  exact (Finset.mem_filter.mp hp).2

theorem selbergPrimorial_pos
    (level : Nat) :
    0 < selbergPrimorial level := by
  unfold selbergPrimorial selbergPrimeSupport
  exact Finset.prod_pos fun p hp =>
    (Finset.mem_filter.mp hp).2.pos

theorem squarefree_dvd_selbergPrimorial
    {level d : Nat}
    (hdpos : 0 < d)
    (hdle : d <= level)
    (hdsq : Squarefree d) :
    Dvd.dvd d (selbergPrimorial level) := by
  rw [<- Nat.prod_primeFactors_of_squarefree hdsq]
  apply Finset.prod_dvd_prod_of_subset d.primeFactors
    (selbergPrimeSupport level) id
  intro p hp
  have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpdvd : Dvd.dvd p d := (Nat.mem_primeFactors.mp hp).2.1
  have hple : p <= level := (Nat.le_of_dvd hdpos hpdvd).trans hdle
  exact Finset.mem_filter.mpr
    (And.intro (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hple)) hpprime)

/-- Pointwise reciprocal of the positive Jordan-two arithmetic function. -/
def inverseJordanTwoFunction : ArithmeticFunction Rat :=
  ArithmeticFunction.pdiv
    (ArithmeticFunction.natToArithmeticFunction ArithmeticFunction.zeta :
      ArithmeticFunction Rat)
    TS119.Goldbach.selbergJordanTwoFunction

theorem inverseJordanTwoFunction_isMultiplicative :
    inverseJordanTwoFunction.IsMultiplicative := by
  unfold inverseJordanTwoFunction
  exact ArithmeticFunction.isMultiplicative_zeta.natCast.pdiv
    TS126.Goldbach.selbergJordanTwoFunction_isMultiplicative

theorem inverseJordanTwoFunction_apply_of_pos
    (d : Nat)
    (hd : 0 < d) :
    inverseJordanTwoFunction d =
      1 / TS122.Goldbach.selbergJordanTwoPenalty d := by
  unfold inverseJordanTwoFunction TS122.Goldbach.selbergJordanTwoPenalty
  rw [ArithmeticFunction.pdiv_apply]
  rw [ArithmeticFunction.natCoe_apply]
  rw [ArithmeticFunction.zeta_apply_ne (Nat.ne_of_gt hd)]
  simp [TS119.Goldbach.selbergJordanTwoCoefficient]

theorem selbergDenominatorSummand_eq_squarefree
    (d : Nat) :
    selbergDenominatorSummand d =
      if Squarefree d then inverseJordanTwoFunction d else 0 := by
  by_cases hdsq : Squarefree d
  case pos =>
    rw [if_pos hdsq]
    unfold selbergDenominatorSummand
    have hd0 : Not (d = 0) := by
      intro hd
      subst d
      norm_num [Nat.squarefree_iff_prime_squarefree] at hdsq
    have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
    rw [inverseJordanTwoFunction_apply_of_pos d hdpos]
    have hmu :
        TS122.Goldbach.selbergMobiusRatCoefficient d ^ (2 : Nat) = 1 := by
      unfold TS122.Goldbach.selbergMobiusRatCoefficient
      rw [show
        (ArithmeticFunction.moebius : ArithmeticFunction Rat) d =
          ((ArithmeticFunction.moebius d : Int) : Rat) by rfl]
      rw [<- Int.cast_pow]
      rw [ArithmeticFunction.moebius_sq_eq_one_of_squarefree hdsq]
      norm_num
    rw [hmu]
  case neg =>
    rw [if_neg hdsq]
    unfold selbergDenominatorSummand
    have hmu0 :
        TS122.Goldbach.selbergMobiusRatCoefficient d = 0 := by
      unfold TS122.Goldbach.selbergMobiusRatCoefficient
      rw [show
        (ArithmeticFunction.moebius : ArithmeticFunction Rat) d =
          ((ArithmeticFunction.moebius d : Int) : Rat) by rfl]
      rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hdsq]
      norm_num
    rw [hmu0]
    simp

theorem selbergOptimizationDenominator_eq_squarefreeSum
    (level : Nat) :
    TS122.Goldbach.selbergOptimizationDenominator level =
      Finset.sum
        ((TS122.Goldbach.selbergOptimizationSupport level).filter Squarefree)
        inverseJordanTwoFunction := by
  unfold TS122.Goldbach.selbergOptimizationDenominator
  change
    Finset.sum (TS122.Goldbach.selbergOptimizationSupport level)
        selbergDenominatorSummand = _
  calc
    Finset.sum (TS122.Goldbach.selbergOptimizationSupport level)
        selbergDenominatorSummand =
      Finset.sum (TS122.Goldbach.selbergOptimizationSupport level)
        (fun d => if Squarefree d then inverseJordanTwoFunction d else 0) := by
          apply Finset.sum_congr rfl
          intro d _hd
          exact selbergDenominatorSummand_eq_squarefree d
    _ = _ := by rw [Finset.sum_filter]

theorem selbergOptimizationDenominator_le_primorialDivisorSum
    (level : Nat) :
    TS122.Goldbach.selbergOptimizationDenominator level <=
      Finset.sum (selbergPrimorial level).divisors inverseJordanTwoFunction := by
  rw [selbergOptimizationDenominator_eq_squarefreeSum]
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (by
      intro d hd
      have hsupport := (Finset.mem_filter.mp hd).1
      have hdsq := (Finset.mem_filter.mp hd).2
      have hdpos := TS144.Goldbach.pos_of_mem_selbergOptimizationSupport hsupport
      have hdle : d <= level := by
        rw [TS148.Goldbach.selbergOptimizationSupport_eq_Icc] at hsupport
        exact (Finset.mem_Icc.mp hsupport).2
      exact Nat.mem_divisors.mpr
        (And.intro
          (squarefree_dvd_selbergPrimorial hdpos hdle hdsq)
          (selbergPrimorial_pos level).ne'))
    (by
      intro d hddiv _hdnot
      have hdvd : Dvd.dvd d (selbergPrimorial level) :=
        Nat.dvd_of_mem_divisors hddiv
      have hdpos : 0 < d :=
        Nat.pos_of_dvd_of_pos hdvd (selbergPrimorial_pos level)
      rw [inverseJordanTwoFunction_apply_of_pos d hdpos]
      have hJ := TS127.Goldbach.selbergJordanTwoCoefficient_pos_of_pos d hdpos
      exact div_nonneg zero_le_one hJ.le)

/-- Elementary Euler factor used to dominate the reciprocal Jordan sum. -/
def selbergEulerFactor (n : Nat) : Rat :=
  (n : Rat) ^ (2 : Nat) / ((n : Rat) ^ (2 : Nat) - 1)

theorem selbergEulerFactor_one_le
    (n : Nat)
    (hn : 2 <= n) :
    1 <= selbergEulerFactor n := by
  unfold selbergEulerFactor
  have hnrat : (2 : Rat) <= n := by exact_mod_cast hn
  have hden : 0 < (n : Rat) ^ (2 : Nat) - 1 := by nlinarith
  calc
    (1 : Rat) =
        ((n : Rat) ^ (2 : Nat) - 1) /
          ((n : Rat) ^ (2 : Nat) - 1) := by field_simp
    _ <= (n : Rat) ^ (2 : Nat) /
        ((n : Rat) ^ (2 : Nat) - 1) := by
      exact div_le_div_of_nonneg_right (by linarith) hden.le

theorem selbergEulerFactor_product_Icc
    (level : Nat)
    (hlevel : 1 <= level) :
    Finset.prod (Finset.Icc 2 level) selbergEulerFactor =
      (2 : Rat) * level / (level + 1) := by
  induction level, hlevel using Nat.le_induction with
  | base => norm_num [selbergEulerFactor]
  | succ n hn ih =>
      rw [Finset.prod_Icc_succ_top (by omega)]
      rw [ih]
      unfold selbergEulerFactor
      push_cast
      have hnrat : (1 : Rat) <= n := by exact_mod_cast hn
      have hnpos : (0 : Rat) < n := lt_of_lt_of_le zero_lt_one hnrat
      have hn1pos : (0 : Rat) < (n : Rat) + 1 := by positivity
      have hn2pos : (0 : Rat) < (n : Rat) + 2 := by positivity
      rw [show ((n : Rat) + 1) ^ 2 - 1 = n * (n + 2) by ring]
      field_simp [hnpos.ne', hn1pos.ne', hn2pos.ne']
      ring

theorem selbergPrimorial_primeFactors
    (level : Nat) :
    (selbergPrimorial level).primeFactors = selbergPrimeSupport level := by
  unfold selbergPrimorial
  apply Nat.primeFactors_prod
  intro p hp
  exact (Finset.mem_filter.mp hp).2

theorem one_add_inverseJordanTwo_prime_eq_eulerFactor
    {p : Nat}
    (hp : p.Prime) :
    1 + inverseJordanTwoFunction p = selbergEulerFactor p := by
  rw [inverseJordanTwoFunction_apply_of_pos p hp.pos]
  unfold TS122.Goldbach.selbergJordanTwoPenalty
  rw [TS124.Goldbach.selbergJordanTwoCoefficient_prime hp]
  unfold selbergEulerFactor
  have hden : (0 : Rat) < (p : Rat) ^ 2 - 1 := by
    have hpcast : (2 : Rat) <= p := by exact_mod_cast hp.two_le
    nlinarith
  field_simp [hden.ne']

theorem selbergPrimorialDivisorSum_eq_primeProduct
    (level : Nat) :
    Finset.sum (selbergPrimorial level).divisors inverseJordanTwoFunction =
      Finset.prod (selbergPrimeSupport level) selbergEulerFactor := by
  have h :=
    inverseJordanTwoFunction_isMultiplicative.prodPrimeFactors_one_add_of_squarefree
      (selbergPrimorial_squarefree level)
  rw [selbergPrimorial_primeFactors level] at h
  rw [<- h]
  apply Finset.prod_congr rfl
  intro p hp
  exact one_add_inverseJordanTwo_prime_eq_eulerFactor
    (Finset.mem_filter.mp hp).2

theorem selbergPrimeSupport_subset_Icc
    (level : Nat) :
    forall n : Nat,
      Membership.mem (selbergPrimeSupport level) n ->
        Membership.mem (Finset.Icc 2 level) n := by
  intro p hp
  have hpdata := Finset.mem_filter.mp hp
  exact Finset.mem_Icc.mpr
    (And.intro hpdata.2.two_le
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hpdata.1)))

theorem selbergPrimeProduct_le_eulerProduct
    (level : Nat) :
    Finset.prod (selbergPrimeSupport level) selbergEulerFactor <=
      Finset.prod (Finset.Icc 2 level) selbergEulerFactor := by
  let s := selbergPrimeSupport level
  let t := Finset.Icc 2 level
  have hsub := selbergPrimeSupport_subset_Icc level
  have hcomp_one :
      (1 : Rat) <= Finset.prod (t \ s) selbergEulerFactor := by
    calc
      (1 : Rat) = Finset.prod (t \ s) (fun _ => (1 : Rat)) := by simp
      _ <= Finset.prod (t \ s) selbergEulerFactor := by
        apply Finset.prod_le_prod
        case h0 =>
          intro _ _
          norm_num
        case h1 =>
          intro n hn
          exact selbergEulerFactor_one_le n
            (Finset.mem_Icc.mp (Finset.mem_sdiff.mp hn).1).1
  have hs_nonneg : 0 <= Finset.prod s selbergEulerFactor := by
    apply Finset.prod_nonneg
    intro n hn
    exact le_trans zero_le_one
      (selbergEulerFactor_one_le n (Finset.mem_Icc.mp (hsub n hn)).1)
  have hmul := mul_le_mul_of_nonneg_right hcomp_one hs_nonneg
  rw [one_mul] at hmul
  rw [Finset.prod_sdiff hsub] at hmul
  exact hmul

theorem selbergEulerFactor_product_Icc_le_two
    (level : Nat) :
    Finset.prod (Finset.Icc 2 level) selbergEulerFactor <= 2 := by
  by_cases hlevel : 0 < level
  case pos =>
    rw [selbergEulerFactor_product_Icc level hlevel]
    have hden : (0 : Rat) < (level : Rat) + 1 := by positivity
    calc
      (2 : Rat) * level / (level + 1) <=
          (2 : Rat) * (level + 1) / (level + 1) := by
        exact div_le_div_of_nonneg_right (by nlinarith) hden.le
      _ = 2 := by field_simp
  case neg =>
    have hlevel0 : level = 0 := Nat.eq_zero_of_not_pos hlevel
    subst level
    norm_num

/-- Uniform absolute upper bound for the TS122 denominator. -/
theorem selbergOptimizationDenominator_le_two
    (level : Nat) :
    TS122.Goldbach.selbergOptimizationDenominator level <= 2 := by
  calc
    TS122.Goldbach.selbergOptimizationDenominator level <=
        Finset.sum (selbergPrimorial level).divisors inverseJordanTwoFunction :=
      selbergOptimizationDenominator_le_primorialDivisorSum level
    _ = Finset.prod (selbergPrimeSupport level) selbergEulerFactor :=
      selbergPrimorialDivisorSum_eq_primeProduct level
    _ <= Finset.prod (Finset.Icc 2 level) selbergEulerFactor :=
      selbergPrimeProduct_le_eulerProduct level
    _ <= 2 := selbergEulerFactor_product_Icc_le_two level

/-- Sharper finite telescoping bound for every positive level. -/
theorem selbergOptimizationDenominator_le_telescopingBound
    (level : Nat)
    (hlevel : 0 < level) :
    TS122.Goldbach.selbergOptimizationDenominator level <=
      (2 : Rat) * level / (level + 1) := by
  calc
    TS122.Goldbach.selbergOptimizationDenominator level <=
        Finset.sum (selbergPrimorial level).divisors inverseJordanTwoFunction :=
      selbergOptimizationDenominator_le_primorialDivisorSum level
    _ = Finset.prod (selbergPrimeSupport level) selbergEulerFactor :=
      selbergPrimorialDivisorSum_eq_primeProduct level
    _ <= Finset.prod (Finset.Icc 2 level) selbergEulerFactor :=
      selbergPrimeProduct_le_eulerProduct level
    _ = (2 : Rat) * level / (level + 1) :=
      selbergEulerFactor_product_Icc level hlevel

/-- The TS122 denominator is strictly below two at every positive level. -/
theorem selbergOptimizationDenominator_lt_two
    (level : Nat)
    (hlevel : 0 < level) :
    TS122.Goldbach.selbergOptimizationDenominator level < 2 := by
  apply lt_of_le_of_lt
    (selbergOptimizationDenominator_le_telescopingBound level hlevel)
  have hden : (0 : Rat) < (level : Rat) + 1 := by positivity
  calc
    (2 : Rat) * level / (level + 1) <
        (2 : Rat) * (level + 1) / (level + 1) := by
      exact div_lt_div_of_pos_right (by nlinarith) hden
    _ = 2 := by field_simp

/-- Any successful TS150 comparison forces the TS153 threshold below two. -/
theorem necessarySelbergDenominatorLowerBoundRat_lt_two
    (level x Q : Nat)
    (hlevel : 0 < level)
    (hscale :
      TS150.Goldbach.RefinedSelbergBudgetLeBrunTitchmarsh level x Q) :
    TS153.Goldbach.necessarySelbergDenominatorLowerBoundRat x Q < 2 := by
  exact lt_of_le_of_lt
    (TS153.Goldbach.necessarySelbergDenominatorLowerBoundRat_le_denominator
      level x Q hlevel hscale)
    (selbergOptimizationDenominator_lt_two level hlevel)

/-- Dependent TS151 comparisons inherit the same absolute threshold cap. -/
theorem dependentRefinedComparison_forces_threshold_lt_two
    (level : TS151.Goldbach.SelbergLevelSelection)
    (scale :
      TS151.Goldbach.DependentRefinedSelbergBudgetScaleComparison level)
    (x Q : Nat)
    (hx : TS15.Goldbach.LargeX x)
    (hQ : Q = Nat.log 2 x * Nat.log 2 x) :
    TS153.Goldbach.necessarySelbergDenominatorLowerBoundRat x Q < 2 := by
  exact necessarySelbergDenominatorLowerBoundRat_lt_two
    (level x Q)
    x
    Q
    (scale.level_positive x Q hx hQ)
    (scale.refined_budget_le_brun_titchmarsh x Q hx hQ)

/-- A threshold at least two rules out every dependent level selection. -/
theorem no_dependentRefinedComparison_of_two_le_threshold
    (level : TS151.Goldbach.SelbergLevelSelection)
    (x Q : Nat)
    (hx : TS15.Goldbach.LargeX x)
    (hQ : Q = Nat.log 2 x * Nat.log 2 x)
    (hthreshold :
      (2 : Rat) <=
        TS153.Goldbach.necessarySelbergDenominatorLowerBoundRat x Q) :
    Not (TS151.Goldbach.DependentRefinedSelbergBudgetScaleComparison level) := by
  intro scale
  exact (not_lt_of_ge hthreshold)
    (dependentRefinedComparison_forces_threshold_lt_two
      level scale x Q hx hQ)

/-- TS154 package recording the proved denominator cap and its obstruction. -/
structure SelbergDenominatorUpperBoundObstructionProbe where
  denominator_le_two :
    forall level : Nat,
      TS122.Goldbach.selbergOptimizationDenominator level <= 2

  denominator_lt_two_of_pos :
    forall level : Nat,
      0 < level ->
        TS122.Goldbach.selbergOptimizationDenominator level < 2

  dependent_threshold_cap :
    forall level : TS151.Goldbach.SelbergLevelSelection,
      TS151.Goldbach.DependentRefinedSelbergBudgetScaleComparison level ->
        forall x Q : Nat,
          TS15.Goldbach.LargeX x ->
            Q = Nat.log 2 x * Nat.log 2 x ->
              TS153.Goldbach.necessarySelbergDenominatorLowerBoundRat x Q < 2

  cumulative_head_prime_count_obligation :
    True

/-- Concrete TS154 obstruction package. -/
def selbergDenominatorUpperBoundObstructionProbe :
    SelbergDenominatorUpperBoundObstructionProbe where
  denominator_le_two := selbergOptimizationDenominator_le_two
  denominator_lt_two_of_pos := selbergOptimizationDenominator_lt_two
  dependent_threshold_cap := by
    intro level scale x Q hx hQ
    exact dependentRefinedComparison_forces_threshold_lt_two
      level scale x Q hx hQ
  cumulative_head_prime_count_obligation := True.intro

theorem selbergDenominatorSummand_nonneg
    (d : Nat)
    (hd : 0 < d) :
    0 <= selbergDenominatorSummand d := by
  unfold selbergDenominatorSummand
  have hJ := TS127.Goldbach.selbergJordanTwoCoefficient_pos_of_pos d hd
  exact div_nonneg (sq_nonneg _) hJ.le

theorem selbergMobiusRatCoefficient_sq_le_one
    (d : Nat) :
    TS122.Goldbach.selbergMobiusRatCoefficient d ^ (2 : Nat) <= 1 := by
  rcases ArithmeticFunction.moebius_eq_or d with hzero | hone | hneg
  all_goals simp_all [TS122.Goldbach.selbergMobiusRatCoefficient]

theorem selbergDenominatorSummand_le_one
    (d : Nat)
    (hd : 0 < d) :
    selbergDenominatorSummand d <= 1 := by
  unfold selbergDenominatorSummand
  have hJ := TS148.Goldbach.one_le_selbergJordanTwoPenalty d hd
  have hmu := selbergMobiusRatCoefficient_sq_le_one d
  have hJpos : 0 < TS122.Goldbach.selbergJordanTwoPenalty d :=
    lt_of_lt_of_le zero_lt_one hJ
  calc
    TS122.Goldbach.selbergMobiusRatCoefficient d ^ (2 : Nat) /
          TS122.Goldbach.selbergJordanTwoPenalty d <=
        1 / TS122.Goldbach.selbergJordanTwoPenalty d :=
      div_le_div_of_nonneg_right hmu hJpos.le
    _ <= TS122.Goldbach.selbergJordanTwoPenalty d /
          TS122.Goldbach.selbergJordanTwoPenalty d :=
      div_le_div_of_nonneg_right hJ hJpos.le
    _ = 1 := by field_simp

theorem selbergOptimizationDenominator_le_level
    (level : Nat) :
    TS122.Goldbach.selbergOptimizationDenominator level <= (level : Rat) := by
  unfold TS122.Goldbach.selbergOptimizationDenominator
  change
    (Finset.sum (TS122.Goldbach.selbergOptimizationSupport level)
      selbergDenominatorSummand) <= (level : Rat)
  calc
    Finset.sum (TS122.Goldbach.selbergOptimizationSupport level)
        selbergDenominatorSummand <=
      Finset.sum (TS122.Goldbach.selbergOptimizationSupport level)
        (fun _ => (1 : Rat)) := by
          apply Finset.sum_le_sum
          intro d hd
          exact selbergDenominatorSummand_le_one d
            (TS144.Goldbach.pos_of_mem_selbergOptimizationSupport hd)
    _ = (level : Rat) := by
      simp [TS148.Goldbach.card_selbergOptimizationSupport]

/-- Target proposition for the TS154 denominator obstruction probe. -/
def SelbergDenominatorUpperBoundObstructionProbeTarget : Prop :=
  Nonempty SelbergDenominatorUpperBoundObstructionProbe

/-- The TS154 obstruction target is populated without external assumptions. -/
theorem selbergDenominatorUpperBoundObstructionProbeTarget :
    SelbergDenominatorUpperBoundObstructionProbeTarget :=
  Nonempty.intro selbergDenominatorUpperBoundObstructionProbe

end Goldbach
end TS154
