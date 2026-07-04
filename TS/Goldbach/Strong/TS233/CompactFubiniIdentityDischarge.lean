import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Prod
import TS.Goldbach.Strong.TS232.DampedDirichletFubiniBridgeReduction

/-!
# TS233 - Compact Fubini Identity Discharge

This sprint targets the first analytic obligation isolated by TS232:
the compact Fubini identity on the finite rectangle `[b, A] x [0, T]`.

The proof is kept local to finite interval integrals. It does not prove the
uniform Laplace-boundary limit, the damped difference limit, the auxiliary
high-damping bound, the corrected Fubini execution statement, or any
Abel-to-cutoff bridge.
-/

namespace TS233
namespace Goldbach

open MeasureTheory

/-- The continuous kernel used in the compact Fubini step. -/
noncomputable def compactFubiniKernel (s x : Real) : Real :=
  Real.exp ((-x) * s) * Real.sin x

/-- The compact Fubini kernel is continuous on the plane. -/
theorem compactFubiniKernel_continuous :
    Continuous (fun p : Prod Real Real => compactFubiniKernel p.1 p.2) := by
  unfold compactFubiniKernel
  fun_prop

/-- Primitive in the Laplace parameter for fixed nonzero `x`. -/
noncomputable def compactFubiniPrimitiveS (x s : Real) : Real :=
  (-Real.sin x / x) * Real.exp ((-x) * s)

/-- The parameter primitive differentiates to the compact Fubini kernel. -/
theorem hasDerivAt_compactFubiniPrimitiveS
    (x s : Real) (hx : x = 0 -> False) :
    HasDerivAt
      (fun u : Real => compactFubiniPrimitiveS x u)
      (compactFubiniKernel s x)
      s := by
  have hlin :
      HasDerivAt (fun u : Real => (-x) * u) (-x) s :=
    by simpa using ((hasDerivAt_id s).const_mul (-x))
  have hexp :
      HasDerivAt
        (fun u : Real => Real.exp ((-x) * u))
        (Real.exp ((-x) * s) * (-x))
        s := by
    simpa using hlin.exp
  have hscaled :
      HasDerivAt
        (fun u : Real =>
          (-Real.sin x / x) * Real.exp ((-x) * u))
        ((-Real.sin x / x) *
          (Real.exp ((-x) * s) * (-x)))
        s :=
    hexp.const_mul (-Real.sin x / x)
  have hderivEq :
      ((-Real.sin x / x) *
          (Real.exp ((-x) * s) * (-x))) =
        compactFubiniKernel s x := by
    unfold compactFubiniKernel
    field_simp [hx]
    ring
  rw [hderivEq] at hscaled
  simpa [compactFubiniPrimitiveS] using hscaled

/--
For each `x`, integrating the continuous kernel over the Laplace parameter
produces the damped-kernel difference.
-/
theorem parameterIntegral_eq_dampedDifferenceKernel
    (b A x : Real) :
    intervalIntegral
      (fun s : Real => compactFubiniKernel s x)
      b
      A
      volume =
      TS229.Goldbach.dampedDirichletKernel b x -
        TS229.Goldbach.dampedDirichletKernel A x := by
  by_cases hx : x = 0
  case pos =>
    simp [hx, compactFubiniKernel, TS229.Goldbach.dampedDirichletKernel,
      TS213.Goldbach.sineDirichletKernel]
  case neg =>
    have hcont :
        ContinuousOn
          (fun s : Real => compactFubiniKernel s x)
          (Set.uIcc b A) := by
      unfold compactFubiniKernel
      fun_prop
    have hderiv :
        forall s : Real, Set.Mem (Set.uIcc b A) s ->
          HasDerivAt
            (fun u : Real => compactFubiniPrimitiveS x u)
            (compactFubiniKernel s x)
            s := by
      intro s hs
      exact hasDerivAt_compactFubiniPrimitiveS x s hx
    have hFTC :
        intervalIntegral
          (fun s : Real => compactFubiniKernel s x)
          b
          A
          volume =
          compactFubiniPrimitiveS x A -
            compactFubiniPrimitiveS x b := by
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt
        hderiv hcont.intervalIntegrable
    rw [hFTC]
    unfold compactFubiniPrimitiveS
    unfold TS229.Goldbach.dampedDirichletKernel
    unfold TS213.Goldbach.sineDirichletKernel
    field_simp [hx]
    ring_nf

/-- Set-integral form of `parameterIntegral_eq_dampedDifferenceKernel`. -/
theorem parameterSetIntegral_eq_dampedDifferenceKernel
    (b A x : Real) (hA : b <= A) :
    integral (volume.restrict (Set.Ioc b A))
      (fun s : Real => compactFubiniKernel s x) =
      TS229.Goldbach.dampedDirichletKernel b x -
        TS229.Goldbach.dampedDirichletKernel A x := by
  rw [<- intervalIntegral.integral_of_le hA]
  exact parameterIntegral_eq_dampedDifferenceKernel b A x

/-- Set-integral form of the finite Laplace sine partial integral. -/
theorem laplaceSinePartialIntegral_eq_compactFubiniSetIntegral
    (s T : Real) (hT : 0 <= T) :
    TS230.Goldbach.laplaceSinePartialIntegral s T =
      integral (volume.restrict (Set.Ioc 0 T))
        (fun x : Real => compactFubiniKernel s x) := by
  unfold TS230.Goldbach.laplaceSinePartialIntegral
  unfold TS230.Goldbach.laplaceSineKernel
  rw [intervalIntegral.integral_of_le hT]
  apply integral_congr_ae
  filter_upwards with x
  unfold compactFubiniKernel
  have harg : -(s * x) = (-x) * s := by
    ring
  rw [harg]

/-- The damped Dirichlet kernel is interval-integrable on every compact interval. -/
theorem dampedDirichletKernel_intervalIntegrable
    (c a b : Real) :
    IntervalIntegrable
      (fun x : Real => TS229.Goldbach.dampedDirichletKernel c x)
      volume
      a
      b := by
  have hD :
      IntervalIntegrable
        (fun x : Real => TS213.Goldbach.sineDirichletKernel 1 x)
        volume
        a
        b :=
    TS228.Goldbach.sineDirichletKernel_one_intervalIntegrable a b
  have hExp :
      ContinuousOn
        (fun x : Real => Real.exp (-c * x))
        (Set.uIcc a b) := by
    fun_prop
  simpa [TS229.Goldbach.dampedDirichletKernel] using
    hD.continuousOn_mul hExp

/-- Integrability of the compact Fubini kernel on a restricted rectangle. -/
theorem compactFubiniKernel_integrable_restrictRectangle
    (b A T : Real) :
    Integrable
      (Function.uncurry compactFubiniKernel)
      ((volume.restrict (Set.Ioc b A)).prod
        (volume.restrict (Set.Ioc 0 T))) := by
  have hcont :
      ContinuousOn
        (Function.uncurry compactFubiniKernel)
        (Set.prod (Set.Icc b A) (Set.Icc 0 T)) := by
    simpa [Function.uncurry] using
      compactFubiniKernel_continuous.continuousOn
  have hcompact : IsCompact (Set.prod (Set.Icc b A) (Set.Icc 0 T)) :=
    isCompact_Icc.prod isCompact_Icc
  have hintCompact :
      IntegrableOn
        (Function.uncurry compactFubiniKernel)
        (Set.prod (Set.Icc b A) (Set.Icc 0 T))
        (volume.prod volume) :=
    hcont.integrableOn_compact hcompact
  have hsubset :
      Set.prod (Set.Ioc b A) (Set.Ioc 0 T) <=
        Set.prod (Set.Icc b A) (Set.Icc 0 T) :=
    Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self
  have hintIoc :
      IntegrableOn
        (Function.uncurry compactFubiniKernel)
        (Set.prod (Set.Ioc b A) (Set.Ioc 0 T))
        (volume.prod volume) :=
    hintCompact.mono_set hsubset
  simpa [IntegrableOn, Measure.prod_restrict] using hintIoc

/-- Swap the two compact integrals for the compact Fubini kernel. -/
theorem compactFubiniKernel_integral_swap
    (b A T : Real) :
    integral (volume.restrict (Set.Ioc b A))
        (fun s : Real =>
          integral (volume.restrict (Set.Ioc 0 T))
            (fun x : Real => compactFubiniKernel s x)) =
      integral (volume.restrict (Set.Ioc 0 T))
        (fun x : Real =>
          integral (volume.restrict (Set.Ioc b A))
            (fun s : Real => compactFubiniKernel s x)) := by
  exact integral_integral_swap
    (compactFubiniKernel_integrable_restrictRectangle b A T)

/-- The compact Fubini identity isolated in TS232. -/
theorem compactFubiniIdentity :
    TS232.Goldbach.CompactFubiniIdentityStatement := by
  intro b A T hb hA hT
  have hA_le : b <= A := hA.le
  have hbInt :
      IntervalIntegrable
        (fun x : Real => TS229.Goldbach.dampedDirichletKernel b x)
        volume
        0
        T :=
    dampedDirichletKernel_intervalIntegrable b 0 T
  have hAInt :
      IntervalIntegrable
        (fun x : Real => TS229.Goldbach.dampedDirichletKernel A x)
        volume
        0
        T :=
    dampedDirichletKernel_intervalIntegrable A 0 T
  calc
    TS232.Goldbach.dampedPartialIntegral b T -
        TS232.Goldbach.dampedPartialIntegral A T
        =
      intervalIntegral
        (fun x : Real =>
          TS229.Goldbach.dampedDirichletKernel b x -
            TS229.Goldbach.dampedDirichletKernel A x)
        0
        T
        volume := by
          unfold TS232.Goldbach.dampedPartialIntegral
          exact (intervalIntegral.integral_sub hbInt hAInt).symm
    _ =
      integral (volume.restrict (Set.Ioc 0 T))
        (fun x : Real =>
          TS229.Goldbach.dampedDirichletKernel b x -
            TS229.Goldbach.dampedDirichletKernel A x) := by
          exact intervalIntegral.integral_of_le hT
    _ =
      integral (volume.restrict (Set.Ioc 0 T))
        (fun x : Real =>
          integral (volume.restrict (Set.Ioc b A))
            (fun s : Real => compactFubiniKernel s x)) := by
          apply integral_congr_ae
          filter_upwards with x
          exact (parameterSetIntegral_eq_dampedDifferenceKernel b A x hA_le).symm
    _ =
      integral (volume.restrict (Set.Ioc b A))
        (fun s : Real =>
          integral (volume.restrict (Set.Ioc 0 T))
            (fun x : Real => compactFubiniKernel s x)) := by
          exact (compactFubiniKernel_integral_swap b A T).symm
    _ =
      integral (volume.restrict (Set.Ioc b A))
        (fun s : Real => TS230.Goldbach.laplaceSinePartialIntegral s T) := by
          apply integral_congr_ae
          filter_upwards with s
          exact (laplaceSinePartialIntegral_eq_compactFubiniSetIntegral s T hT).symm
    _ =
      intervalIntegral
        (fun s : Real => TS230.Goldbach.laplaceSinePartialIntegral s T)
        b
        A
        volume := by
          exact (intervalIntegral.integral_of_le hA_le).symm

/-- Ledger recording the TS233 compact Fubini discharge. -/
structure CompactFubiniIdentityDischargeLedger where
  ts232_fubini_reduction :
    TS232.Goldbach.DampedDirichletFubiniBridgeReductionLedger

  compact_fubini_identity_statement : Prop
  compact_fubini_identity_statement_eq :
    compact_fubini_identity_statement =
      TS232.Goldbach.CompactFubiniIdentityStatement
  compact_fubini_identity_proved :
    compact_fubini_identity_statement

  parameter_primitive_defined : True
  parameter_primitive_derivative_proved : True
  parameter_integral_difference_proved : True
  rectangle_integrability_proved : True
  compact_integral_swap_proved : True

  laplace_boundary_uniform_limit_not_proved : True
  damped_difference_atTop_not_proved : True
  auxiliary_damping_uniform_bound_not_proved : True
  corrected_fubini_execution_not_proved : True
  damped_dirichlet_evaluation_not_proved : True
  abel_to_cutoff_bridge_not_proved : True
  dirichlet_cutoff_value_not_proved : True
  cos_square_integral_value_not_proved : True
  canonical_sinc_fourth_value_not_proved : True
  plancherel_not_proved : True
  explicit_formula_not_proved : True
  gallagher_not_proved : True
  goldbach_not_claimed : True

/-- Concrete TS233 discharge ledger. -/
noncomputable def compactFubiniIdentityDischargeLedger :
    CompactFubiniIdentityDischargeLedger where
  ts232_fubini_reduction :=
    TS232.Goldbach.dampedDirichletFubiniBridgeReductionLedger
  compact_fubini_identity_statement :=
    TS232.Goldbach.CompactFubiniIdentityStatement
  compact_fubini_identity_statement_eq := rfl
  compact_fubini_identity_proved := compactFubiniIdentity
  parameter_primitive_defined := True.intro
  parameter_primitive_derivative_proved := True.intro
  parameter_integral_difference_proved := True.intro
  rectangle_integrability_proved := True.intro
  compact_integral_swap_proved := True.intro
  laplace_boundary_uniform_limit_not_proved := True.intro
  damped_difference_atTop_not_proved := True.intro
  auxiliary_damping_uniform_bound_not_proved := True.intro
  corrected_fubini_execution_not_proved := True.intro
  damped_dirichlet_evaluation_not_proved := True.intro
  abel_to_cutoff_bridge_not_proved := True.intro
  dirichlet_cutoff_value_not_proved := True.intro
  cos_square_integral_value_not_proved := True.intro
  canonical_sinc_fourth_value_not_proved := True.intro
  plancherel_not_proved := True.intro
  explicit_formula_not_proved := True.intro
  gallagher_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS233. -/
def CompactFubiniIdentityDischargeTarget : Prop :=
  Nonempty CompactFubiniIdentityDischargeLedger

/-- TS233 target: the compact Fubini identity is discharged. -/
theorem compactFubiniIdentityDischargeTarget :
    CompactFubiniIdentityDischargeTarget :=
  Nonempty.intro compactFubiniIdentityDischargeLedger

end Goldbach
end TS233
