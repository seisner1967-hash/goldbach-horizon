import Mathlib.Tactic
import TS.Goldbach.Strong.TS95.ExplicitFormulaTraceBridgeLedger

namespace TS96
namespace Goldbach

/-!
# TS96 - Spectral Trace Majorant Discharge

TS92 isolates the `Ct <= 1/2` spectral trace majorant contract. TS93 records
the zeta-zero family ledger, TS94 records the kernel-data ledger, and TS95
records the explicit-formula bridge ledger with a rational trace budget.

This sprint assembles those pieces mechanically: a concrete TS95 explicit
formula ledger supplies the TS92 `SpectralTraceMajorantContract`. No
Riemann-von Mangoldt formula and no zeta-zero trace estimate is proved here;
the analytic content remains exactly the TS95 ledger.
-/

/--
A concrete explicit-formula trace ledger supplies the TS92 spectral trace
majorant contract, using its rational trace budget as `Ct_bound`.
-/
def spectralTraceMajorantContract_of_explicitFormulaLedger
    (H : TS95.Goldbach.ExplicitFormulaTraceBridgeLedger) :
    TS92.Goldbach.SpectralTraceMajorantContract where
  kernel :=
    TS94.Goldbach.traceKernelSpectralData_of_ledger
      H.kernelData
  zeros :=
    TS93.Goldbach.zetaZeroFamily_of_ledger
      H.zeroFamily
  explicitFormula :=
    TS95.Goldbach.explicitFormulaTraceBridge_of_ledger
      H
  Ct_bound :=
    H.traceBudget
  Ct_pos :=
    H.traceBudget_pos
  Ct_le_half :=
    H.traceBudget_le_half

/-- Target proposition for the TS96 spectral trace majorant assembly. -/
def SpectralTraceMajorantDischargeTarget : Prop :=
  TS92.Goldbach.SpectralTraceMajorantContractTarget

/-- A TS95 explicit-formula ledger target discharges the TS92 spectral target. -/
theorem spectralTraceMajorantContractTarget_of_explicitFormulaTraceBridgeLedgerTarget
    (H : TS95.Goldbach.ExplicitFormulaTraceBridgeLedgerTarget) :
    TS92.Goldbach.SpectralTraceMajorantContractTarget := by
  cases H with
  | intro h =>
      exact
        Nonempty.intro
          (spectralTraceMajorantContract_of_explicitFormulaLedger h)

/--
A TS95 explicit-formula ledger target supplies the TS32 trace majorant target
through the TS92 bridge.
-/
theorem traceMajorantContractTarget_of_explicitFormulaTraceBridgeLedgerTarget
    (H : TS95.Goldbach.ExplicitFormulaTraceBridgeLedgerTarget) :
    Nonempty TS32.Goldbach.TraceMajorantContract :=
  TS92.Goldbach.traceMajorantContractTarget_of_spectralTraceTarget
    (spectralTraceMajorantContractTarget_of_explicitFormulaTraceBridgeLedgerTarget
      H)

/--
TS95 explicit-formula plus TS83 Mellin-tail final contracts give the final
TS84 OTSA majorant API target, using the TS91 scale-transfer package.
-/
theorem OTSAFinalMajorantAPIContractsTarget_of_explicitFormulaTrace_mellin
    (Ht : TS95.Goldbach.ExplicitFormulaTraceBridgeLedgerTarget)
    (Hm : TS83.MellinJackson.MellinTailFinalAPIContractsTarget) :
    TS84.Goldbach.OTSAFinalMajorantAPIContractsTarget :=
  TS92.Goldbach.OTSAFinalMajorantAPIContractsTarget_of_spectralTrace_mellin
    (spectralTraceMajorantContractTarget_of_explicitFormulaTraceBridgeLedgerTarget
      Ht)
    Hm

/--
Adding Brun-Titchmarsh leaves TS95 explicit-formula and TS83 Mellin-tail final
contracts as the remaining inputs for the TS25 padded-scale infrastructure.
-/
theorem paddedScaleAnalyticInfrastructureTarget_of_BrunTitchmarsh_explicitFormulaTrace_mellin
    (HBT : Nonempty TS22.Goldbach.BrunTitchmarshNatIntervalBound)
    (Ht : TS95.Goldbach.ExplicitFormulaTraceBridgeLedgerTarget)
    (Hm : TS83.MellinJackson.MellinTailFinalAPIContractsTarget) :
    Nonempty TS25.Goldbach.PaddedScaleAnalyticInfrastructure :=
  TS92.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_BrunTitchmarsh_spectralTrace_mellin
    HBT
    (spectralTraceMajorantContractTarget_of_explicitFormulaTraceBridgeLedgerTarget
      Ht)
    Hm

/-- Local TS96 target, discharged from a TS95 explicit-formula ledger target. -/
theorem spectralTraceMajorantDischargeTarget_of_explicitFormulaTraceBridgeLedgerTarget
    (H : TS95.Goldbach.ExplicitFormulaTraceBridgeLedgerTarget) :
    SpectralTraceMajorantDischargeTarget :=
  spectralTraceMajorantContractTarget_of_explicitFormulaTraceBridgeLedgerTarget
    H

end Goldbach
end TS96
