/-
  Goldbach/Framework.lean
  A clean interface isolating the analytic inputs of the Horizon programme.
-/

import Goldbach.Collage

namespace Goldbach

/--
A conservative interface for the analytic core of the programme.

The idea is:
* `amsVerified` handles the finite computation range,
* `asymptoticOfCore` packages the implication from the analytic hypotheses
  to the asymptotic Goldbach range above `N0`.
-/
structure GoldbachFramework (N0 AMSBound : ℕ) where
  a2 : Prop
  pcbGallagher : Prop
  f1bHerglotz : Prop
  f1aOTSA : Prop
  g2MellinJackson : Prop
  amsVerified : VerifiedUpTo AMSBound
  asymptoticOfCore :
    a2 →
    pcbGallagher →
    f1bHerglotz →
    f1aOTSA →
    g2MellinJackson →
    HoldsAbove N0

/--
Abstract theorem: if a framework supplies the asymptotic range above `N0`,
and if that range overlaps the verified finite range up to `AMSBound`,
then Goldbach strong follows.
-/
theorem goldbachStrong_of_framework
    {N0 AMSBound : ℕ}
    (F : GoldbachFramework N0 AMSBound)
    (hcover : N0 ≤ AMSBound) :
    GoldbachStrong := by
  apply goldbachStrong_from_two_ranges hcover F.amsVerified
  exact F.asymptoticOfCore
    F.a2
    F.pcbGallagher
    F.f1bHerglotz
    F.f1aOTSA
    F.g2MellinJackson

end Goldbach
