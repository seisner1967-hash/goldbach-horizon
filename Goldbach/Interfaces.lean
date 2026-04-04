/-
  Goldbach/Interfaces.lean
  Finer analytic interfaces sitting above `GoldbachFramework`.

  Goal:
  replace coarse assumptions (`Prop`) by small structured packets,
  one hypothesis at a time, without changing the theorem
  `goldbachStrong_of_framework`.
-/

import Goldbach.Framework

namespace Goldbach

/-! ## A2 interface -/

/-- A finer interface for the A2 (self-adjointness) input. -/
structure A2Interface where
  c0_lt_quarter : Prop
  klmn_step : Prop
  hc0_lt_quarter : c0_lt_quarter
  hklmn_step : klmn_step
  derive_a2 : c0_lt_quarter → klmn_step → Prop

/-- The coarse A2 statement extracted from the finer interface. -/
def A2Interface.holds (I : A2Interface) : Prop :=
  I.derive_a2 I.hc0_lt_quarter I.hklmn_step

/-! ## PCB / Gallagher interface -/

/-- A finer interface for the Gallagher / PCB input. -/
structure PCBInterface where
  gallagher_theorem : Prop
  brun_titchmarsh_step : Prop
  hgallagher_theorem : gallagher_theorem
  hbrun_titchmarsh_step : brun_titchmarsh_step
  derive_pcb : gallagher_theorem → brun_titchmarsh_step → Prop

/-- The coarse PCB statement extracted from the finer interface. -/
def PCBInterface.holds (I : PCBInterface) : Prop :=
  I.derive_pcb I.hgallagher_theorem I.hbrun_titchmarsh_step

/-! ## F1b / Herglotz interface -/

/-- A finer interface for the F1b (Herglotz positivity) input. -/
structure F1bInterface where
  self_adjoint_input : Prop
  resolvent_herglotz : Prop
  cauchy_schwarz_bridge : Prop
  hself_adjoint_input : self_adjoint_input
  hresolvent_herglotz : resolvent_herglotz
  hcauchy_schwarz_bridge : cauchy_schwarz_bridge
  derive_f1b : self_adjoint_input → resolvent_herglotz → cauchy_schwarz_bridge → Prop

/-- The coarse F1b statement extracted from the finer interface. -/
def F1bInterface.holds (I : F1bInterface) : Prop :=
  I.derive_f1b I.hself_adjoint_input I.hresolvent_herglotz I.hcauchy_schwarz_bridge

/-! ## F1a / OTSA interface -/

/-- A finer interface for the F1a (windowed OTSA / Fredholm) input. -/
structure F1aInterface where
  compact_window_fredholm : Prop
  otsa_trace_identity : Prop
  hcompact_window_fredholm : compact_window_fredholm
  hotsa_trace_identity : otsa_trace_identity
  derive_f1a : compact_window_fredholm → otsa_trace_identity → Prop

/-- The coarse F1a statement extracted from the finer interface. -/
def F1aInterface.holds (I : F1aInterface) : Prop :=
  I.derive_f1a I.hcompact_window_fredholm I.hotsa_trace_identity

/-! ## G2 / Mellin-Jackson interface -/

/-- A finer interface for the G2 (Mellin--Jackson approximation) input. -/
structure G2Interface where
  mellin_jackson_theorem : Prop
  bandwidth_choice : Prop
  error_absorption : Prop
  hmellin_jackson_theorem : mellin_jackson_theorem
  hbandwidth_choice : bandwidth_choice
  herror_absorption : error_absorption
  derive_g2 : mellin_jackson_theorem → bandwidth_choice → error_absorption → Prop

/-- The coarse G2 statement extracted from the finer interface. -/
def G2Interface.holds (I : G2Interface) : Prop :=
  I.derive_g2 I.hmellin_jackson_theorem I.hbandwidth_choice I.herror_absorption

/-! ## Full refined package -/

/--
A refined package of analytic interfaces.
This sits strictly above `GoldbachFramework` and can be collapsed back to it.
-/
structure AnalyticInterfaces (N0 AMSBound : ℕ) where
  a2I : A2Interface
  pcbI : PCBInterface
  f1bI : F1bInterface
  f1aI : F1aInterface
  g2I : G2Interface
  ha2 : a2I.holds
  hpcbGallagher : pcbI.holds
  hf1bHerglotz : f1bI.holds
  hf1aOTSA : f1aI.holds
  hg2MellinJackson : g2I.holds
  amsVerified : VerifiedUpTo AMSBound
  asymptoticOfInterfaces :
    a2I.holds →
    pcbI.holds →
    f1bI.holds →
    f1aI.holds →
    g2I.holds →
    HoldsAbove N0

/-- Collapse the refined package back to the coarse `GoldbachFramework`. -/
def AnalyticInterfaces.toFramework
    {N0 AMSBound : ℕ}
    (I : AnalyticInterfaces N0 AMSBound) :
    GoldbachFramework N0 AMSBound where
  a2 := I.a2I.holds
  pcbGallagher := I.pcbI.holds
  f1bHerglotz := I.f1bI.holds
  f1aOTSA := I.f1aI.holds
  g2MellinJackson := I.g2I.holds
  ha2 := I.ha2
  hpcbGallagher := I.hpcbGallagher
  hf1bHerglotz := I.hf1bHerglotz
  hf1aOTSA := I.hf1aOTSA
  hg2MellinJackson := I.hg2MellinJackson
  amsVerified := I.amsVerified
  asymptoticOfCore := I.asymptoticOfInterfaces

/-- Direct theorem from the refined package. -/
theorem goldbachStrong_of_interfaces
    {N0 AMSBound : ℕ}
    (I : AnalyticInterfaces N0 AMSBound)
    (hcover : N0 ≤ AMSBound) :
    GoldbachStrong := by
  exact goldbachStrong_of_framework I.toFramework hcover

end Goldbach
