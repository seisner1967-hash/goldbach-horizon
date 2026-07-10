import TS.Goldbach.Strong.TS245.CosSquareImproperCutoffAssembly

/-!
# TS246 - Canonical Sinc-Fourth Assembly

TS245 proved that the positive-half-line cos-square Haar integral is `pi/6`.
TS218 already proved the scaling from that integral to the positive-half-line
canonical sinc-fourth integral and the evenness reduction to the full line.

This sprint performs the final algebraic assembly and discharges the canonical
TS209 scalar statement.  The specialized triangle-spline Plancherel evidence
is left for the next packaging sprint.
-/

namespace TS246
namespace Goldbach

/-- The canonical full-line sinc-fourth integral has value `2*pi/3`. -/
theorem canonicalSincFourthIntegralValue :
    TS209.Goldbach.CanonicalSincFourthIntegralValueStatement :=
  TS213.Goldbach.canonicalSincFourthIntegral_of_cosSquareValue_scaling_evenness
    TS245.Goldbach.cosSquareImproperIntegralValue
    TS218.Goldbach.halfLineSincFourthScaling
    TS218.Goldbach.fullLineSincFourthEvenness

/-- Ledger recording the TS246 canonical sinc-fourth assembly. -/
structure CanonicalSincFourthAssemblyLedger where
  ts245_cos_square_assembly :
    TS245.Goldbach.CosSquareImproperCutoffAssemblyLedger

  ts218_scaling_evenness :
    TS218.Goldbach.SincFourthScalingEvennessDischargeLedger

  canonical_sinc_fourth_value_proved :
    TS209.Goldbach.CanonicalSincFourthIntegralValueStatement

  canonical_value_supplies_plancherel_evidence :
    TS209.Goldbach.CanonicalSincFourthIntegralValueStatement ->
      TS204.Goldbach.TriangleSplinePlancherelInputEvidence
        TS204.Goldbach.triangleSplinePlancherelInputContract

  plancherel_evidence_not_assembled : True
  explicit_formula_not_proved : True
  gallagher_not_proved : True
  goldbach_not_claimed : True

/-- Concrete TS246 discharge ledger. -/
noncomputable def canonicalSincFourthAssemblyLedger :
    CanonicalSincFourthAssemblyLedger where
  ts245_cos_square_assembly :=
    TS245.Goldbach.cosSquareImproperCutoffAssemblyLedger
  ts218_scaling_evenness :=
    TS218.Goldbach.sincFourthScalingEvennessDischargeLedger
  canonical_sinc_fourth_value_proved :=
    canonicalSincFourthIntegralValue
  canonical_value_supplies_plancherel_evidence :=
    TS209.Goldbach.triangleSplinePlancherelInputEvidence_of_canonicalSincFourthIntegral
  plancherel_evidence_not_assembled := True.intro
  explicit_formula_not_proved := True.intro
  gallagher_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS246. -/
def CanonicalSincFourthAssemblyTarget : Prop :=
  Nonempty CanonicalSincFourthAssemblyLedger

/-- TS246 target: the canonical full-line sinc-fourth value is proved. -/
theorem canonicalSincFourthAssemblyTarget :
    CanonicalSincFourthAssemblyTarget :=
  Nonempty.intro canonicalSincFourthAssemblyLedger

end Goldbach
end TS246
