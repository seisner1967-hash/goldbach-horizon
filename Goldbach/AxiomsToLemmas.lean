/-
  Goldbach/AxiomsToLemmas.lean
  One-hypothesis-at-a-time refinement lemmas.

  Each theorem shows how to replace one coarse `Prop` from `GoldbachFramework`
  by a finer interface, while keeping the other inputs coarse.
-/

import Goldbach.Interfaces

namespace Goldbach

/-! ## Replacing only A2 by a finer interface -/

/-- Build a coarse framework from a refined A2 input and coarse remaining inputs. -/
def frameworkOfA2Interface
    {N0 AMSBound : ℕ}
    (a2I : A2Interface)
    (pcb : Prop)
    (f1b : Prop)
    (f1a : Prop)
    (g2 : Prop)
    (hams : VerifiedUpTo AMSBound)
    (hasymp : a2I.holds → pcb → f1b → f1a → g2 → HoldsAbove N0) :
    GoldbachFramework N0 AMSBound where
  a2 := a2I.holds
  pcbGallagher := pcb
  f1bHerglotz := f1b
  f1aOTSA := f1a
  g2MellinJackson := g2
  amsVerified := hams
  asymptoticOfCore := hasymp

/-- Goldbach strong from a refined A2 input. -/
theorem goldbachStrong_of_A2Interface
    {N0 AMSBound : ℕ}
    (a2I : A2Interface)
    (pcb : Prop)
    (f1b : Prop)
    (f1a : Prop)
    (g2 : Prop)
    (hams : VerifiedUpTo AMSBound)
    (hasymp : a2I.holds → pcb → f1b → f1a → g2 → HoldsAbove N0)
    (hcover : N0 ≤ AMSBound) :
    GoldbachStrong := by
  exact goldbachStrong_of_framework
    (frameworkOfA2Interface a2I pcb f1b f1a g2 hams hasymp)
    hcover

/-! ## Replacing only PCB by a finer interface -/

/-- Build a coarse framework from a refined PCB input and coarse remaining inputs. -/
def frameworkOfPCBInterface
    {N0 AMSBound : ℕ}
    (a2 : Prop)
    (pcbI : PCBInterface)
    (f1b : Prop)
    (f1a : Prop)
    (g2 : Prop)
    (hams : VerifiedUpTo AMSBound)
    (hasymp : a2 → pcbI.holds → f1b → f1a → g2 → HoldsAbove N0) :
    GoldbachFramework N0 AMSBound where
  a2 := a2
  pcbGallagher := pcbI.holds
  f1bHerglotz := f1b
  f1aOTSA := f1a
  g2MellinJackson := g2
  amsVerified := hams
  asymptoticOfCore := hasymp

/-- Goldbach strong from a refined PCB input. -/
theorem goldbachStrong_of_PCBInterface
    {N0 AMSBound : ℕ}
    (a2 : Prop)
    (pcbI : PCBInterface)
    (f1b : Prop)
    (f1a : Prop)
    (g2 : Prop)
    (hams : VerifiedUpTo AMSBound)
    (hasymp : a2 → pcbI.holds → f1b → f1a → g2 → HoldsAbove N0)
    (hcover : N0 ≤ AMSBound) :
    GoldbachStrong := by
  exact goldbachStrong_of_framework
    (frameworkOfPCBInterface a2 pcbI f1b f1a g2 hams hasymp)
    hcover

/-! ## Replacing only F1b by a finer interface -/

/-- Build a coarse framework from a refined F1b input and coarse remaining inputs. -/
def frameworkOfF1bInterface
    {N0 AMSBound : ℕ}
    (a2 : Prop)
    (pcb : Prop)
    (f1bI : F1bInterface)
    (f1a : Prop)
    (g2 : Prop)
    (hams : VerifiedUpTo AMSBound)
    (hasymp : a2 → pcb → f1bI.holds → f1a → g2 → HoldsAbove N0) :
    GoldbachFramework N0 AMSBound where
  a2 := a2
  pcbGallagher := pcb
  f1bHerglotz := f1bI.holds
  f1aOTSA := f1a
  g2MellinJackson := g2
  amsVerified := hams
  asymptoticOfCore := hasymp

/-- Goldbach strong from a refined F1b input. -/
theorem goldbachStrong_of_F1bInterface
    {N0 AMSBound : ℕ}
    (a2 : Prop)
    (pcb : Prop)
    (f1bI : F1bInterface)
    (f1a : Prop)
    (g2 : Prop)
    (hams : VerifiedUpTo AMSBound)
    (hasymp : a2 → pcb → f1bI.holds → f1a → g2 → HoldsAbove N0)
    (hcover : N0 ≤ AMSBound) :
    GoldbachStrong := by
  exact goldbachStrong_of_framework
    (frameworkOfF1bInterface a2 pcb f1bI f1a g2 hams hasymp)
    hcover

/-! ## Replacing only F1a by a finer interface -/

/-- Build a coarse framework from a refined F1a input and coarse remaining inputs. -/
def frameworkOfF1aInterface
    {N0 AMSBound : ℕ}
    (a2 : Prop)
    (pcb : Prop)
    (f1b : Prop)
    (f1aI : F1aInterface)
    (g2 : Prop)
    (hams : VerifiedUpTo AMSBound)
    (hasymp : a2 → pcb → f1b → f1aI.holds → g2 → HoldsAbove N0) :
    GoldbachFramework N0 AMSBound where
  a2 := a2
  pcbGallagher := pcb
  f1bHerglotz := f1b
  f1aOTSA := f1aI.holds
  g2MellinJackson := g2
  amsVerified := hams
  asymptoticOfCore := hasymp

/-- Goldbach strong from a refined F1a input. -/
theorem goldbachStrong_of_F1aInterface
    {N0 AMSBound : ℕ}
    (a2 : Prop)
    (pcb : Prop)
    (f1b : Prop)
    (f1aI : F1aInterface)
    (g2 : Prop)
    (hams : VerifiedUpTo AMSBound)
    (hasymp : a2 → pcb → f1b → f1aI.holds → g2 → HoldsAbove N0)
    (hcover : N0 ≤ AMSBound) :
    GoldbachStrong := by
  exact goldbachStrong_of_framework
    (frameworkOfF1aInterface a2 pcb f1b f1aI g2 hams hasymp)
    hcover

/-! ## Replacing only G2 by a finer interface -/

/-- Build a coarse framework from a refined G2 input and coarse remaining inputs. -/
def frameworkOfG2Interface
    {N0 AMSBound : ℕ}
    (a2 : Prop)
    (pcb : Prop)
    (f1b : Prop)
    (f1a : Prop)
    (g2I : G2Interface)
    (hams : VerifiedUpTo AMSBound)
    (hasymp : a2 → pcb → f1b → f1a → g2I.holds → HoldsAbove N0) :
    GoldbachFramework N0 AMSBound where
  a2 := a2
  pcbGallagher := pcb
  f1bHerglotz := f1b
  f1aOTSA := f1a
  g2MellinJackson := g2I.holds
  amsVerified := hams
  asymptoticOfCore := hasymp

/-- Goldbach strong from a refined G2 input. -/
theorem goldbachStrong_of_G2Interface
    {N0 AMSBound : ℕ}
    (a2 : Prop)
    (pcb : Prop)
    (f1b : Prop)
    (f1a : Prop)
    (g2I : G2Interface)
    (hams : VerifiedUpTo AMSBound)
    (hasymp : a2 → pcb → f1b → f1a → g2I.holds → HoldsAbove N0)
    (hcover : N0 ≤ AMSBound) :
    GoldbachStrong := by
  exact goldbachStrong_of_framework
    (frameworkOfG2Interface a2 pcb f1b f1a g2I hams hasymp)
    hcover

/-! ## Fully refined route -/

/-- The cleanest bridge: all analytic inputs are refined simultaneously. -/
theorem goldbachStrong_of_refinedInterfaces
    {N0 AMSBound : ℕ}
    (I : AnalyticInterfaces N0 AMSBound)
    (hcover : N0 ≤ AMSBound) :
    GoldbachStrong := by
  exact goldbachStrong_of_interfaces I hcover

end Goldbach
