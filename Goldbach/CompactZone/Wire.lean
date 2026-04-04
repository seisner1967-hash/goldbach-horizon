/-
  Goldbach/CompactZone/Wire.lean
  Wire the CompactZoneBound proof into the A2 framework.

  PROVED (0 sorry, 0 axiom, 0 opaque):
    - po_a2_stage1_proved : PO_A2_stage1
      (CompactZoneBound discharged, stage1 no longer an external hypothesis)
    - a2Interface_compact_discharged : KLMNHypothesis → A2Interface
      (CompactZoneBound is no longer needed as a parameter)
    - a2Interface_compact_holds : KLMNHypothesis → A2Interface.holds

  STATUS: CompactZoneBound is DISCHARGED. The A2 path now depends
  only on KLMNHypothesis (KLMN perturbation theory, absent from Mathlib).

  0 sorry.
-/
import Goldbach.CompactZone.Grid
import Goldbach.A2PureAnalytic

namespace Goldbach.CompactZone

/-! ## §1 Discharge PO_A2_stage1

CompactZoneBound → PO_A2_stage1 was proved in A2PureAnalytic.
CompactZoneBound is proved in Grid.lean. Combine. -/

/-- **PO_A2_stage1 is now a theorem, not a hypothesis.**
    The compact zone bound is discharged. -/
theorem po_a2_stage1_proved : Goldbach.Roadmap.PO_A2_stage1 :=
  Goldbach.stage1_of_compact_zone compactZoneBound_proved

/-! ## §2 Simplified A2 interface construction

With CompactZoneBound discharged, the A2Interface now depends
only on KLMNHypothesis (which requires Mathlib additions for
quadratic form domains and Friedrichs extension). -/

/-- A2Interface with CompactZoneBound already discharged. -/
noncomputable def a2Interface_compact_discharged
    (h_klmn : Goldbach.KLMNHypothesis) : Goldbach.A2Interface :=
  Goldbach.a2Interface_of_hypotheses compactZoneBound_proved h_klmn

/-- The A2Interface holds with only KLMN as external hypothesis. -/
theorem a2Interface_compact_holds
    (h_klmn : Goldbach.KLMNHypothesis) :
    (a2Interface_compact_discharged h_klmn).holds :=
  Goldbach.a2Interface_holds compactZoneBound_proved h_klmn

end Goldbach.CompactZone
