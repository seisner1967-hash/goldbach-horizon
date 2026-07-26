import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.Tactic
import TS.Goldbach.Strong.TS305.FixedLeftBoundaryConvergenceAndClosedResidual

/-!
# TS306 - Exceptional Residue Inventory

This module constructs the two exceptional local residue certificates for the
fixed Perron rectangle.  The pole at `s = 1` remains structurally separate as
the main term `x / 2`; the exceptional Finset is exactly `{0, -1}`.

The inventory certifies the listed local principal parts.  Exhaustiveness of
the singularity classification belongs to the later meromorphic rectangle
theorem and is not claimed here.
-/

noncomputable section

namespace TS306
namespace Goldbach

open Complex Filter Metric Set

/-! ## Generic simple-pole certificate -/

theorem analyticAt_dslope
    {H : Complex -> Complex}
    {p : Complex}
    (hH : AnalyticAt Complex H p) :
    AnalyticAt Complex (dslope H p) p := by
  cases' hH with q hq
  exact Exists.intro q.fslope hq.has_fpower_series_dslope_fslope

/-- Package an analytic numerator `H` as a certified simple pole
`H(z) / (z-p)`, using the analytic divided difference as regular part. -/
noncomputable def localSimplePoleData_of_analytic
    (x : Nat)
    (p : Complex)
    (H : Complex -> Complex)
    (hH : AnalyticAt Complex H p)
    (hIntegrand :
      Filter.Eventually
        (fun z =>
          TS293.Goldbach.triangleSplinePerronIntegrand x z =
            H z / (z - p))
        (nhdsWithin p (Set.compl {p}))) :
    TS293.Goldbach.PerronLocalResidueData x p where
  residue := H p
  regularPart := dslope H p
  regularPart_analytic := analyticAt_dslope hH
  principal_part := by
    filter_upwards [hIntegrand, self_mem_nhdsWithin] with z hz hzp
    have hne : Not (z = p) := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hzp
    rw [hz, dslope_of_ne H hne]
    unfold slope
    field_simp [sub_ne_zero.mpr hne]

/-! ## Analytic numerators at zero and minus one -/

/-- The holomorphic logarithmic derivative away from zeta zeros. -/
noncomputable def negZetaLogDerivative (z : Complex) : Complex :=
  -deriv riemannZeta z / riemannZeta z

theorem negZetaLogDerivative_analyticAt
    {p : Complex}
    (hpOne : Not (p = 1))
    (hpZero : Not (riemannZeta p = 0)) :
    AnalyticAt Complex negZetaLogDerivative p := by
  have hpMem : Membership.mem (Set.compl ({1} : Set Complex)) p := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hpOne
  have hZetaOn : AnalyticOnNhd Complex riemannZeta (Set.compl {1}) :=
    TS260.Goldbach.riemannZeta_differentiableOn_compl_one.analyticOnNhd
      isClosed_singleton.isOpen_compl
  exact (hZetaOn.deriv p hpMem).neg.div (hZetaOn p hpMem) hpZero

theorem riemannZeta_zero_ne_zero :
    Not (riemannZeta 0 = 0) := by
  rw [riemannZeta_zero]
  norm_num

theorem riemannZeta_neg_one_eq :
    riemannZeta (-1) = (-1 / 12 : Complex) := by
  rw [show (-1 : Complex) = -(1 : Nat) by norm_num,
    riemannZeta_neg_nat_eq_bernoulli]
  norm_num [bernoulli]

theorem riemannZeta_neg_one_ne_zero :
    Not (riemannZeta (-1) = 0) := by
  rw [riemannZeta_neg_one_eq]
  norm_num

theorem natCast_ne_zero_of_pos
    {x : Nat}
    (hx : 0 < x) :
    Not ((x : Complex) = 0) := by
  exact_mod_cast (ne_of_gt hx)

theorem natCpow_analyticAt
    {x : Nat}
    (hx : 0 < x)
    (p : Complex) :
    AnalyticAt Complex (fun z : Complex => (x : Complex) ^ z) p := by
  letI : NeZero (x : Complex) := { out := natCast_ne_zero_of_pos hx }
  exact
    (differentiable_const_cpow_of_neZero (x : Complex)).differentiableOn.analyticAt
      univ_mem

/-- Analytic numerator left after extracting the kernel pole at zero. -/
noncomputable def zeroPoleNumerator
    (x : Nat)
    (z : Complex) : Complex :=
  negZetaLogDerivative z * (x : Complex) ^ z / (z + 1)

/-- Analytic numerator left after extracting the kernel pole at minus one. -/
noncomputable def negOnePoleNumerator
    (x : Nat)
    (z : Complex) : Complex :=
  negZetaLogDerivative z * (x : Complex) ^ z / z

theorem zeroPoleNumerator_analyticAt
    (x : Nat)
    (hx : 0 < x) :
    AnalyticAt Complex (zeroPoleNumerator x) 0 := by
  unfold zeroPoleNumerator
  exact
    ((negZetaLogDerivative_analyticAt (by norm_num)
      riemannZeta_zero_ne_zero).mul (natCpow_analyticAt hx 0)).div
      (analyticAt_id.add analyticAt_const) (by norm_num)

theorem negOnePoleNumerator_analyticAt
    (x : Nat)
    (hx : 0 < x) :
    AnalyticAt Complex (negOnePoleNumerator x) (-1) := by
  unfold negOnePoleNumerator
  exact
    ((negZetaLogDerivative_analyticAt (by norm_num)
      riemannZeta_neg_one_ne_zero).mul (natCpow_analyticAt hx (-1))).div
      analyticAt_id (by norm_num)

theorem triangleSplinePerronIntegrand_eq_zeroPoleNumerator_div
    (x : Nat)
    (z : Complex) :
    TS293.Goldbach.triangleSplinePerronIntegrand x z =
      zeroPoleNumerator x z / z := by
  unfold TS293.Goldbach.triangleSplinePerronIntegrand
    TS257.Goldbach.triangleSplineMellinKernel
    zeroPoleNumerator negZetaLogDerivative
  simp only [div_eq_mul_inv, mul_inv]
  ring

theorem triangleSplinePerronIntegrand_eq_negOnePoleNumerator_div
    (x : Nat)
    (z : Complex) :
    TS293.Goldbach.triangleSplinePerronIntegrand x z =
      negOnePoleNumerator x z / (z - (-1)) := by
  unfold TS293.Goldbach.triangleSplinePerronIntegrand
    TS257.Goldbach.triangleSplineMellinKernel
    negOnePoleNumerator negZetaLogDerivative
  simp only [sub_neg_eq_add, div_eq_mul_inv, mul_inv]
  ring

/-- Local residue certificate at the Mellin-kernel pole `s = 0`. -/
noncomputable def zeroPerronLocalResidueData
    (x : Nat)
    (hx : 0 < x) :
    TS293.Goldbach.PerronLocalResidueData x 0 :=
  localSimplePoleData_of_analytic x 0 (zeroPoleNumerator x)
    (zeroPoleNumerator_analyticAt x hx)
    (Filter.Eventually.of_forall fun z => by
      simpa using triangleSplinePerronIntegrand_eq_zeroPoleNumerator_div x z)

/-- Local residue certificate at the Mellin-kernel pole `s = -1`. -/
noncomputable def negOnePerronLocalResidueData
    (x : Nat)
    (hx : 0 < x) :
    TS293.Goldbach.PerronLocalResidueData x (-1) :=
  localSimplePoleData_of_analytic x (-1) (negOnePoleNumerator x)
    (negOnePoleNumerator_analyticAt x hx)
    (Filter.Eventually.of_forall fun z =>
      triangleSplinePerronIntegrand_eq_negOnePoleNumerator_div x z)

theorem zeroPerronLocalResidueData_residue
    (x : Nat)
    (hx : 0 < x) :
    (zeroPerronLocalResidueData x hx).residue =
      -deriv riemannZeta 0 / riemannZeta 0 := by
  simp [zeroPerronLocalResidueData, localSimplePoleData_of_analytic,
    zeroPoleNumerator, negZetaLogDerivative]

theorem negOnePerronLocalResidueData_residue
    (x : Nat)
    (hx : 0 < x) :
    (negOnePerronLocalResidueData x hx).residue =
      ((x : Complex) ^ (-1 : Complex)) *
        (deriv riemannZeta (-1) / riemannZeta (-1)) := by
  simp [negOnePerronLocalResidueData, localSimplePoleData_of_analytic,
    negOnePoleNumerator, negZetaLogDerivative]
  ring

/-! ## Concrete exceptional inventory -/

/-- The exceptional poles inside every admissible TS293 rectangle. -/
def perronExceptionalPoles : Finset Complex :=
  {0, -1}

@[simp] theorem mem_perronExceptionalPoles_iff
    (p : Complex) :
    Membership.mem perronExceptionalPoles p <-> p = 0 \/ p = -1 := by
  simp [perronExceptionalPoles]

@[simp] theorem one_not_mem_perronExceptionalPoles :
    Not (Membership.mem perronExceptionalPoles (1 : Complex)) := by
  simp [perronExceptionalPoles]
  norm_num

/-- Residue value as a function of the pole, independent of membership proofs. -/
noncomputable def concreteExceptionalResidueValue
    (x : Nat)
    (p : Complex) : Complex :=
  if p = 0 then
    -deriv riemannZeta 0 / riemannZeta 0
  else
    ((x : Complex) ^ (-1 : Complex)) *
      (deriv riemannZeta (-1) / riemannZeta (-1))

noncomputable def concreteExceptionalResidueData
    (x : Nat)
    (hx : 0 < x)
    (p : {z : Complex // Membership.mem perronExceptionalPoles z}) :
    TS293.Goldbach.PerronLocalResidueData x p.1 := by
  by_cases hp : p.1 = 0
  case pos =>
    exact Eq.mp
      (congrArg (fun z => TS293.Goldbach.PerronLocalResidueData x z) hp.symm)
      (zeroPerronLocalResidueData x hx)
  case neg =>
    have hpNeg : p.1 = -1 :=
      (mem_perronExceptionalPoles_iff p.1).mp p.2 |>.resolve_left hp
    exact Eq.mp
      (congrArg (fun z => TS293.Goldbach.PerronLocalResidueData x z) hpNeg.symm)
      (negOnePerronLocalResidueData x hx)

theorem concreteExceptionalResidueData_residue
    (x : Nat)
    (hx : 0 < x)
    (p : {z : Complex // Membership.mem perronExceptionalPoles z}) :
    (concreteExceptionalResidueData x hx p).residue =
      concreteExceptionalResidueValue x p.1 := by
  cases' p with p hmem
  by_cases hp : p = 0
  case pos =>
    subst p
    simpa [concreteExceptionalResidueData,
      concreteExceptionalResidueValue] using
        zeroPerronLocalResidueData_residue x hx
  case neg =>
    have hpNeg : p = -1 :=
      (mem_perronExceptionalPoles_iff p).mp hmem |>.resolve_left hp
    subst p
    simpa [concreteExceptionalResidueData,
      concreteExceptionalResidueValue] using
        negOnePerronLocalResidueData_residue x hx

/-- The concrete TS293 inventory.  The Perron rectangle fields already imply
that both real points `0` and `-1` lie strictly inside it. -/
noncomputable def concreteExceptionalResidueInventory
    (x : Nat)
    (hx : 0 < x)
    (D : TS293.Goldbach.PerronRectangle) :
    TS293.Goldbach.PerronExceptionalResidueInventory x D where
  poles := perronExceptionalPoles
  residueData := concreteExceptionalResidueData x hx
  pole_in_open_rectangle := by
    intro p
    rcases (mem_perronExceptionalPoles_iff p.1).mp p.2 with hp | hp
    case inl =>
      have hpRe : p.1.re = 0 := by rw [hp]; simp
      have hpIm : p.1.im = 0 := by rw [hp]; simp
      rw [hpRe, hpIm]
      exact And.intro (by linarith [D.left_lt_neg_one])
        (And.intro (by linarith [D.one_lt_right])
          (And.intro (by linarith [D.tau_pos]) D.tau_pos))
    case inr =>
      have hpRe : p.1.re = -1 := by rw [hp]; norm_num
      have hpIm : p.1.im = 0 := by rw [hp]; norm_num
      rw [hpRe, hpIm]
      exact And.intro D.left_lt_neg_one
        (And.intro (by linarith [D.one_lt_right])
          (And.intro (by linarith [D.tau_pos]) D.tau_pos))

/-- Strengthened wrapper recording that the main pole `s = 1` is absent from
the exceptional inventory by construction. -/
structure MainTermSeparatedExceptionalInventory
    (x : Nat)
    (D : TS293.Goldbach.PerronRectangle) where
  inventory : TS293.Goldbach.PerronExceptionalResidueInventory x D
  poles_eq : inventory.poles = perronExceptionalPoles
  one_not_mem : Not (Membership.mem inventory.poles (1 : Complex))

/-- Concrete strengthened inventory with exact pole set `{0, -1}`. -/
noncomputable def mainTermSeparatedExceptionalInventory
    (x : Nat)
    (hx : 0 < x)
    (D : TS293.Goldbach.PerronRectangle) :
    MainTermSeparatedExceptionalInventory x D where
  inventory := concreteExceptionalResidueInventory x hx D
  poles_eq := rfl
  one_not_mem := one_not_mem_perronExceptionalPoles

theorem concreteExceptionalResidueInventory_poles
    (x : Nat)
    (hx : 0 < x)
    (D : TS293.Goldbach.PerronRectangle) :
    (concreteExceptionalResidueInventory x hx D).poles = {0, -1} := rfl

theorem concreteExceptionalResidueContribution_eq
    (x : Nat)
    (hx : 0 < x)
    (D : TS293.Goldbach.PerronRectangle) :
    TS293.Goldbach.exceptionalResidueContribution
        (concreteExceptionalResidueInventory x hx D) =
      -deriv riemannZeta 0 / riemannZeta 0 +
        ((x : Complex) ^ (-1 : Complex)) *
          (deriv riemannZeta (-1) / riemannZeta (-1)) := by
  classical
  unfold TS293.Goldbach.exceptionalResidueContribution
  change
    Finset.sum perronExceptionalPoles.attach
        (fun p => (concreteExceptionalResidueData x hx p).residue) = _
  calc
    Finset.sum perronExceptionalPoles.attach
        (fun p => (concreteExceptionalResidueData x hx p).residue) =
        Finset.sum perronExceptionalPoles.attach
          (fun p => concreteExceptionalResidueValue x p.1) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact concreteExceptionalResidueData_residue x hx p
    _ = Finset.sum perronExceptionalPoles
          (concreteExceptionalResidueValue x) :=
      Finset.sum_attach perronExceptionalPoles
        (concreteExceptionalResidueValue x)
    _ = _ := by
      simp [perronExceptionalPoles, concreteExceptionalResidueValue]

theorem concreteExceptionalResidueContribution_eq_inv
    (x : Nat)
    (hx : 0 < x)
    (D : TS293.Goldbach.PerronRectangle) :
    TS293.Goldbach.exceptionalResidueContribution
        (concreteExceptionalResidueInventory x hx D) =
      -deriv riemannZeta 0 / riemannZeta 0 +
        (1 / (x : Complex)) *
          (deriv riemannZeta (-1) / riemannZeta (-1)) := by
  rw [concreteExceptionalResidueContribution_eq]
  rw [Complex.cpow_neg_one, one_div]

/-- Height-independent norm envelope for the two concrete residues. -/
noncomputable def concreteExceptionalResidueBound
    (x : Nat) : Real :=
  norm (-deriv riemannZeta 0 / riemannZeta 0) +
    norm
      ((1 / (x : Complex)) *
        (deriv riemannZeta (-1) / riemannZeta (-1)))

theorem concreteExceptionalResidueBound_nonnegative
    (x : Nat) :
    0 <= concreteExceptionalResidueBound x := by
  unfold concreteExceptionalResidueBound
  positivity

/-- Concrete inventory on the canonical strong-height rectangle. -/
noncomputable def strongHeightExceptionalResidueInventory
    (x T : Nat)
    (hx : 0 < x)
    (hT : 1 <= T) :
    TS293.Goldbach.PerronExceptionalResidueInventory x
      (TS296.Goldbach.strongCleanPerronContourData T hT).toPerronRectangle :=
  concreteExceptionalResidueInventory x hx
    (TS296.Goldbach.strongCleanPerronContourData T hT).toPerronRectangle

/-- Discharge the TS298 exceptional-residue bound input for the concrete
inventory. -/
noncomputable def concreteExceptionalResidueBoundData
    (x T : Nat)
    (hx : 0 < x)
    (hT : 1 <= T) :
    TS298.Goldbach.ExceptionalResidueBoundData x T hT
      (strongHeightExceptionalResidueInventory x T hx hT) where
  bound := concreteExceptionalResidueBound x
  bound_nonnegative := concreteExceptionalResidueBound_nonnegative x
  norm_le := by
    unfold strongHeightExceptionalResidueInventory
    rw [concreteExceptionalResidueContribution_eq_inv]
    exact norm_add_le _ _

/-!
The TS293 inventory type certifies every listed principal part but does not
state that no other exceptional singularity occurs.  This named proposition
records exactly that later meromorphic-classification obligation while
excluding both the main pole and zeta zeros already handled elsewhere.
-/
def ExceptionalInventoryCompletenessStatement
    (x : Nat)
    (D : TS293.Goldbach.PerronRectangle)
    (E : TS293.Goldbach.PerronExceptionalResidueInventory x D) : Prop :=
  forall p : Complex,
    D.left < p.re -> p.re < D.right ->
    -D.tau < p.im -> p.im < D.tau ->
    Not (p = 1) -> Not (riemannZeta p = 0) ->
    Not (AnalyticAt Complex
      (TS293.Goldbach.triangleSplinePerronIntegrand x) p) ->
    Membership.mem E.poles p

structure ExceptionalResidueInventoryLedger where
  simple_pole_packaging_proved : True
  zeta_zero_value_proved : True
  zeta_neg_one_value_proved : True
  zero_local_residue_certified : True
  neg_one_local_residue_certified : True
  exact_pole_finset_proved : True
  main_pole_one_excluded : True
  exact_exceptional_contribution_proved : True
  ts298_exceptional_bound_routing_proved : True
  zero_residue_log_two_pi_evaluation_not_proved : True
  exhaustive_singularity_classification_not_proved : True
  archimedean_left_rate_not_proved : True
  perron_inversion_not_proved : True
  meromorphic_rectangle_residue_theorem_not_proved : True
  infinite_explicit_formula_not_proved : True
  gallagher_not_proved : True
  otsa_not_proved : True
  goldbach_not_claimed : True

def exceptionalResidueInventoryLedger : ExceptionalResidueInventoryLedger :=
  { simple_pole_packaging_proved := True.intro
    zeta_zero_value_proved := True.intro
    zeta_neg_one_value_proved := True.intro
    zero_local_residue_certified := True.intro
    neg_one_local_residue_certified := True.intro
    exact_pole_finset_proved := True.intro
    main_pole_one_excluded := True.intro
    exact_exceptional_contribution_proved := True.intro
    ts298_exceptional_bound_routing_proved := True.intro
    zero_residue_log_two_pi_evaluation_not_proved := True.intro
    exhaustive_singularity_classification_not_proved := True.intro
    archimedean_left_rate_not_proved := True.intro
    perron_inversion_not_proved := True.intro
    meromorphic_rectangle_residue_theorem_not_proved := True.intro
    infinite_explicit_formula_not_proved := True.intro
    gallagher_not_proved := True.intro
    otsa_not_proved := True.intro
    goldbach_not_claimed := True.intro }

end Goldbach
end TS306
