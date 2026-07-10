import TS.Goldbach.Strong.TS246.CanonicalSincFourthAssembly

/-!
# TS247 - Triangle Spline Plancherel Evidence Assembly

TS246 proved the canonical full-line sinc-fourth value `2*pi/3`.  TS209 and
TS208 already proved that this scalar value supplies the concrete TS174
triangle-spline Plancherel isometry and the TS204 energy-transport contract.

This sprint constructs that evidence bundle unconditionally and exposes its
two usable consequences.  It does not claim a general Plancherel theorem.
-/

namespace TS247
namespace Goldbach

open scoped ENNReal

/-- Concrete Plancherel input evidence for the triangle spline. -/
noncomputable def triangleSplinePlancherelEvidence :
    TS204.Goldbach.TriangleSplinePlancherelInputEvidence
      TS204.Goldbach.triangleSplinePlancherelInputContract :=
  TS209.Goldbach.triangleSplinePlancherelInputEvidence_of_canonicalSincFourthIntegral
    TS246.Goldbach.canonicalSincFourthIntegralValue

/-- The specialized triangle-spline Plancherel isometry is proved. -/
theorem triangleSplinePlancherelIsometry :
    TS174.Goldbach.TriangleSplinePlancherelIsometryStatement :=
  triangleSplinePlancherelEvidence.plancherel

/-- The TS204 Plancherel-to-energy transport is available in the evidence. -/
theorem triangleSplinePlancherelEnergyTransport :
    TS204.Goldbach.triangleSplinePlancherelInputContract
      |>.spectral_energy_transport_statement :=
  triangleSplinePlancherelEvidence.spectral_energy_transport

/-- The pi-scaled squared-sinc candidate has its exact L2 energy. -/
theorem triangleSplineSincL2EnergyValue :
    TS174.Goldbach.triangleSplineSincL2Energy =
      ENNReal.ofReal (Real.sqrt (2 / 3)) :=
  triangleSplinePlancherelEnergyTransport triangleSplinePlancherelIsometry

/-- Ledger recording the terminal Wall 1 evidence assembly. -/
structure TriangleSplinePlancherelEvidenceAssemblyLedger where
  ts246_canonical_assembly :
    TS246.Goldbach.CanonicalSincFourthAssemblyLedger

  plancherel_evidence :
    TS204.Goldbach.TriangleSplinePlancherelInputEvidence
      TS204.Goldbach.triangleSplinePlancherelInputContract

  specialized_plancherel_isometry_proved :
    TS174.Goldbach.TriangleSplinePlancherelIsometryStatement

  spectral_energy_transport_available :
    TS204.Goldbach.triangleSplinePlancherelInputContract
      |>.spectral_energy_transport_statement

  spectral_energy_value_proved :
    TS174.Goldbach.triangleSplineSincL2Energy =
      ENNReal.ofReal (Real.sqrt (2 / 3))

  general_plancherel_not_proved : True
  explicit_formula_not_proved : True
  gallagher_not_proved : True
  goldbach_not_claimed : True

/-- Concrete TS247 Wall 1 evidence ledger. -/
noncomputable def triangleSplinePlancherelEvidenceAssemblyLedger :
    TriangleSplinePlancherelEvidenceAssemblyLedger where
  ts246_canonical_assembly :=
    TS246.Goldbach.canonicalSincFourthAssemblyLedger
  plancherel_evidence :=
    triangleSplinePlancherelEvidence
  specialized_plancherel_isometry_proved :=
    triangleSplinePlancherelIsometry
  spectral_energy_transport_available :=
    triangleSplinePlancherelEnergyTransport
  spectral_energy_value_proved :=
    triangleSplineSincL2EnergyValue
  general_plancherel_not_proved := True.intro
  explicit_formula_not_proved := True.intro
  gallagher_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS247. -/
def TriangleSplinePlancherelEvidenceAssemblyTarget : Prop :=
  Nonempty TriangleSplinePlancherelEvidenceAssemblyLedger

/-- TS247 target: the specialized Plancherel evidence is assembled. -/
theorem triangleSplinePlancherelEvidenceAssemblyTarget :
    TriangleSplinePlancherelEvidenceAssemblyTarget :=
  Nonempty.intro triangleSplinePlancherelEvidenceAssemblyLedger

end Goldbach
end TS247
