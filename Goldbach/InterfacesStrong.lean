import Goldbach.A2PureAnalytic
import Goldbach.HerglotzPositivity
import Goldbach.FredholmOTSA
import Goldbach.MellinJackson
import Goldbach.KLMN.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Topology.Algebra.Support
import Mathlib.Data.Complex.Module
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
  Goldbach/InterfacesStrong.lean
  Phase IX — semantic redesign layer for Horizon Goldbach.
  0 sorry, 0 axiom, definitions only.
-/

open scoped BigOperators Topology
open MeasureTheory Complex Real

namespace Goldbach

-- §1 Common analytic scaffolding

def StrongTestFn (u : ℝ → ℂ) : Prop :=
  ContDiff ℝ 1 u ∧ HasCompactSupport u

noncomputable def strongL2Mass (u : ℝ → ℂ) : ℝ :=
  ∫ x : ℝ, ‖u x‖^2 ∂ volume

noncomputable def strongQ0 (Vconf : ℝ → ℝ) (u : ℝ → ℂ) : ℝ :=
  ∫ x : ℝ, ‖deriv u x‖^2 + Vconf x * ‖u x‖^2 ∂ volume

noncomputable def strongQPert (mu : Measure ℝ) (u : ℝ → ℂ) : ℝ :=
  ∫ x : ℝ, ‖u x‖^2 ∂ mu

noncomputable def strongCauchyTransform (mu : Measure ℝ) (z : ℂ) : ℂ :=
  ∫ t : ℝ, (((t : ℂ) - z)⁻¹) ∂ mu

noncomputable def strongResolventScalar
    (G : ℂ → ℝ → ℝ → ℂ) (u : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ x : ℝ, ∫ y : ℝ, starRingEnd ℂ (u x) * G z x y * u y ∂ volume ∂ volume

noncomputable def supNormIcc (a b : ℝ) (f : ℝ → ℂ) : ℝ :=
  sSup {r : ℝ | ∃ x ∈ Set.Icc a b, r = ‖f x‖}

noncomputable def modulusOfContinuityIcc (a b : ℝ) (f : ℝ → ℂ) (δ : ℝ) : ℝ :=
  sSup {r : ℝ |
    ∃ x ∈ Set.Icc a b, ∃ y ∈ Set.Icc a b,
      ‖x - y‖ ≤ δ ∧ r = ‖f x - f y‖}

-- §2 Strong data structures

structure KLMNStrongData where
  Vconf : ℝ → ℝ
  muPC : Measure ℝ

structure SpectralPositivityStrongData where
  kernel : ℂ → ℝ → ℝ → ℂ

structure FredholmOTSAStrongData where
  kernel : ℝ → ℝ → ℂ
  grid : ∀ N : ℕ, Fin N → ℝ
  weight : ∀ N : ℕ, Fin N → ℝ

structure BandwidthSufficientStrongData where
  a : ℝ
  b : ℝ
  rho : ℝ → ℂ
  J : ℕ → (ℝ → ℂ) → (ℝ → ℂ)
  mellinErr : ℕ → ℝ

-- §3 Strong predicates

def KLMNHypothesisStrong (D : KLMNStrongData) : Prop :=
  (∀ u, StrongTestFn u →
      Integrable (fun x : ℝ => ‖deriv u x‖^2) ∧
      Integrable (fun x : ℝ => D.Vconf x * ‖u x‖^2) ∧
      Integrable (fun x : ℝ => ‖u x‖^2)) ∧
  ∃ a b : ℝ,
    0 ≤ a ∧ a < 1 ∧ 0 ≤ b ∧
    ∀ u, StrongTestFn u →
      strongQPert D.muPC u ≤ a * strongQ0 D.Vconf u + b * strongL2Mass u

def SpectralPositivityHypothesisStrong (D : SpectralPositivityStrongData) : Prop :=
  ∀ u, StrongTestFn u →
    ∃ mu_u : Measure ℝ,
      mu_u Set.univ < ⊤ ∧
      ∀ z : ℂ, 0 < z.im →
        strongResolventScalar D.kernel u z = strongCauchyTransform mu_u z

noncomputable def fredholmSection (D : FredholmOTSAStrongData) (N : ℕ) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j =>
    (if i = j then (1 : ℂ) else 0) +
      (D.weight N j : ℂ) * D.kernel (D.grid N i) (D.grid N j)

noncomputable def fredholmSectionMass (D : FredholmOTSAStrongData) (N : ℕ) : ℝ :=
  ∑ i : Fin N, ∑ j : Fin N,
    ‖(D.weight N j : ℂ) * D.kernel (D.grid N i) (D.grid N j)‖

def FredholmOTSAHypothesisStrong (D : FredholmOTSAStrongData) : Prop :=
  ∃ tau : ℕ → ℝ,
    Summable tau ∧
    (∀ N, 0 ≤ tau N) ∧
    (∀ N, fredholmSectionMass D N ≤ tau N) ∧
    (∀ N, 0 < Complex.re (Matrix.det (fredholmSection D N)))

def BandwidthSufficientStrong (D : BandwidthSufficientStrongData) (B : ℝ) : Prop :=
  D.a < D.b ∧ 4 < B ∧
  ContinuousOn D.rho (Set.Icc D.a D.b) ∧
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ N : ℕ, 2 ≤ N →
      D.mellinErr N ≤
        supNormIcc D.a D.b (fun x => D.rho x - D.J N D.rho x) ∧
      supNormIcc D.a D.b (fun x => D.rho x - D.J N D.rho x) ≤
        (Real.pi / 2) * modulusOfContinuityIcc D.a D.b D.rho (Real.pi / N) ∧
      modulusOfContinuityIcc D.a D.b D.rho (Real.pi / N) ≤
        C / (Real.log N) ^ (B / 2)

-- §4 Bridge targets Strong -> Weak

def KLMNBridge (D : KLMNStrongData) : Prop :=
  KLMNHypothesisStrong D → KLMNHypothesis

def SpectralBridge (D : SpectralPositivityStrongData) : Prop :=
  SpectralPositivityHypothesisStrong D → SpectralPositivityHypothesis

def FredholmBridge (D : FredholmOTSAStrongData) : Prop :=
  FredholmOTSAHypothesisStrong D → FredholmOTSAHypothesis

def BandwidthBridge (D : BandwidthSufficientStrongData) (B : ℝ) : Prop :=
  BandwidthSufficientStrong D B → BandwidthSufficient B

-- §5 Bundled package

structure StrongInterfacePackage where
  klmn : KLMNStrongData
  spectral : SpectralPositivityStrongData
  fredholm : FredholmOTSAStrongData
  jackson : BandwidthSufficientStrongData

def StrongInterfacePackage.Holds (P : StrongInterfacePackage) (B : ℝ) : Prop :=
  KLMNHypothesisStrong P.klmn ∧
  SpectralPositivityHypothesisStrong P.spectral ∧
  FredholmOTSAHypothesisStrong P.fredholm ∧
  BandwidthSufficientStrong P.jackson B

end Goldbach