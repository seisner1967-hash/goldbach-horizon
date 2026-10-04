import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Tactic

/-!
Exact integer determinant coordinates and their inverse, with canonical lambda
existence from gcd(B,N)=1. Concrete shears keep lambda but change the product
of four actual Moebius coefficients on a DEVELOPED tuple. This coefficient is
not the already aggregated HH coefficient H_y(a)H_y(r). No analytic estimate,
invariance of masks, or estimate of D_N is supplied by these coordinates.
-/

namespace GoldbachResearch.DeterminantCoordinates

def quotientA (N lambda u D : ℤ) : ℤ := (u + lambda * D) / N
def quotientC (N lambda s B : ℤ) : ℤ := (s - lambda * B) / N

theorem quotient_reconstruction {N lambda u s B D : ℤ}
    (hu : N ∣ u + lambda * D) (hs : N ∣ s - lambda * B) :
    N * quotientA N lambda u D - lambda * D = u ∧
      N * quotientC N lambda s B + lambda * B = s := by
  have hA : N * quotientA N lambda u D = u + lambda * D :=
    Int.mul_ediv_cancel' hu
  have hC : N * quotientC N lambda s B = s - lambda * B :=
    Int.mul_ediv_cancel' hs
  constructor <;> linarith

theorem quotient_unit_determinant {N lambda u s B D : ℤ}
    (hN : 0 < N) (hdet : u * B + s * D = N)
    (hu : N ∣ u + lambda * D) (hs : N ∣ s - lambda * B) :
    quotientA N lambda u D * B + quotientC N lambda s B * D = 1 := by
  have hA : N * quotientA N lambda u D = u + lambda * D :=
    Int.mul_ediv_cancel' hu
  have hC : N * quotientC N lambda s B = s - lambda * B :=
    Int.mul_ediv_cancel' hs
  have hmul : N * (quotientA N lambda u D * B + quotientC N lambda s B * D - 1) = 0 := by
    linear_combination B * hA + D * hC + hdet
  have hzero := (mul_eq_zero.mp hmul).resolve_left hN.ne'
  linarith

def originalMatrix (u s B D : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![u,s;-D,B]
def hnfMatrix (N lambda : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![N,lambda;0,1]
def basisMatrix (A C B D : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![A,C;-D,B]

theorem matrix_factorization {N lambda u s B D : ℤ}
    (hu : N ∣ u + lambda * D) (hs : N ∣ s - lambda * B) :
    hnfMatrix N lambda * basisMatrix (quotientA N lambda u D)
      (quotientC N lambda s B) B D = originalMatrix u s B D := by
  rcases quotient_reconstruction hu hs with ⟨hA,hC⟩
  unfold hnfMatrix basisMatrix originalMatrix
  rw [Matrix.mul_fin_two]
  simp only [zero_mul, one_mul, zero_add, mul_neg, ← sub_eq_add_neg, zero_sub]
  rw [hA,hC]

theorem basisMatrix_det_one {N lambda u s B D : ℤ}
    (hN : 0 < N) (hdet : u * B + s * D = N)
    (hu : N ∣ u + lambda * D) (hs : N ∣ s - lambda * B) :
    Matrix.det (basisMatrix (quotientA N lambda u D)
      (quotientC N lambda s B) B D) = 1 := by
  unfold basisMatrix
  rw [Matrix.det_fin_two_of]
  have h := quotient_unit_determinant hN hdet hu hs
  simpa [mul_neg, sub_neg_eq_add] using h

theorem inverse_determinant {N lambda A C B D : ℤ}
    (hunit : A * B + C * D = 1) :
    (N * A - lambda * D) * B + (N * C + lambda * B) * D = N := by
  calc
    _ = N * (A * B + C * D) := by ring
    _ = N := by rw [hunit, mul_one]

theorem inverse_divisibilities (N lambda A C B D : ℤ) :
    N ∣ (N * A - lambda * D) + lambda * D ∧
      N ∣ (N * C + lambda * B) - lambda * B := by
  constructor
  · exact ⟨A, by ring⟩
  · exact ⟨C, by ring⟩

theorem inverse_quotients {N lambda A C B D : ℤ} (hN : N ≠ 0) :
    quotientA N lambda (N * A - lambda * D) D = A ∧
      quotientC N lambda (N * C + lambda * B) B = C := by
  unfold quotientA quotientC
  constructor <;> simp [hN]

theorem exists_canonical_lambda_of_coprime {N u s B D : ℤ}
    (hN : 0 < N) (hdet : u * B + s * D = N) (hcop : Int.gcd N B = 1) :
    ∃ lambda : ℤ, 0 ≤ lambda ∧ lambda < N ∧
      N ∣ u + lambda * D ∧ N ∣ s - lambda * B := by
  let eta := Int.gcdA B N
  let zeta := Int.gcdB B N
  have hbez : B * eta + N * zeta = 1 := by
    have hh := Int.gcd_eq_gcd_ab B N
    rw [Int.gcd_comm, hcop] at hh
    exact hh.symm
  let lambda0 := s * eta
  have hc : N ∣ s - lambda0 * B := by
    refine ⟨s * zeta, ?_⟩
    dsimp [lambda0]
    linear_combination -s * hbez
  have hprod : N ∣ B * (u + lambda0 * D) := by
    have he : B * (u + lambda0 * D) = N - D * (s - lambda0 * B) := by
      linear_combination hdet
    rw [he]
    exact dvd_sub (dvd_refl N) (dvd_mul_of_dvd_right hc D)
  have ha := Int.dvd_of_dvd_mul_right_of_gcd_one hprod hcop
  rcases hc with ⟨c0,hc⟩
  rcases ha with ⟨a0,ha⟩
  have hmod := Int.emod_add_ediv lambda0 N
  refine ⟨lambda0 % N, Int.emod_nonneg _ hN.ne',
    Int.emod_lt_of_pos _ hN, ?_, ?_⟩
  · refine ⟨a0 - (lambda0 / N) * D, ?_⟩
    linear_combination ha + D * hmod
  · refine ⟨c0 + (lambda0 / N) * B, ?_⟩
    linear_combination hc - B * hmod

theorem tuple_quotient_reconstruction {b k x z B D : ℤ}
    (hB : b * x ∣ B) (hD : k * z ∣ D) :
    b * (B / (b * x)) * x = B ∧ k * (D / (k * z)) * z = D := by
  constructor
  · calc
      _ = (B / (b * x)) * (b * x) := by ring
      _ = B := Int.ediv_mul_cancel hB
  · calc
      _ = (D / (k * z)) * (k * z) := by ring
      _ = D := Int.ediv_mul_cancel hD

theorem tuple_quotient_inverse {b k x z v t : ℤ}
    (hb : 0 < b) (hk : 0 < k) (hx : 0 < x) (hz : 0 < z) :
    (b * v * x) / (b * x) = v ∧ (k * t * z) / (k * z) = t := by
  have hbx : b * x ≠ 0 := mul_ne_zero hb.ne' hx.ne'
  have hkz : k * z ≠ 0 := mul_ne_zero hk.ne' hz.ne'
  constructor
  · rw [show b * v * x = (b * x) * v by ring]
    exact Int.mul_ediv_cancel_left v hbx
  · rw [show k * t * z = (k * z) * t by ring]
    exact Int.mul_ediv_cancel_left t hkz

def shearMatrix (j : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![1,j;0,1]

theorem shear_determinant_one (j : ℤ) : Matrix.det (shearMatrix j) = 1 := by
  simp [shearMatrix, Matrix.det_fin_two_of]

theorem shear_coordinates (u s B D j : ℤ) :
    originalMatrix u s B D * shearMatrix j =
      originalMatrix u (s + j * u) (B - j * D) D := by
  unfold originalMatrix shearMatrix
  rw [Matrix.mul_fin_two]
  simp [mul_comm, add_comm, sub_eq_add_neg]

theorem concrete_hnf_and_shear :
    hnfMatrix 100000000 73626461 * basisMatrix 9260 (-67) 91 12577 =
      originalMatrix 3 7951 91 12577 ∧
    originalMatrix 3 7951 91 12577 * shearMatrix (-78) =
      originalMatrix 3 7717 981097 12577 ∧
    hnfMatrix 100000000 73626461 * basisMatrix 9260 (-722347) 981097 12577 =
      originalMatrix 3 7717 981097 12577 ∧
    quotientA 100000000 73626461 3 12577 = 9260 ∧
    quotientC 100000000 73626461 7951 91 = -67 ∧
    quotientC 100000000 73626461 7717 981097 = -722347 ∧
    (13 : ℤ) ∣ 981097 ∧ (981097 : ℤ) / 13 = 75469 := by
  norm_num [hnfMatrix, basisMatrix, originalMatrix, shearMatrix,
    Matrix.mul_fin_two, quotientA, quotientC]

theorem concrete_canonical_bases :
    (0 : ℤ) ≤ 73626461 ∧ (73626461 : ℤ) < 100000000 ∧
    Matrix.det (basisMatrix 9260 (-67) 91 12577) = 1 ∧
    Matrix.det (basisMatrix 9260 (-722347) 981097 12577) = 1 ∧
    (3 : ℤ) * 91 + 7951 * 12577 = 100000000 ∧
    (3 : ℤ) * 981097 + 7717 * 12577 = 100000000 := by
  norm_num [basisMatrix, Matrix.det_fin_two_of]

def expandedTupleSign (u v s t : ℕ) : ℤ :=
  ArithmeticFunction.moebius u * ArithmeticFunction.moebius v *
    ArithmeticFunction.moebius s * ArithmeticFunction.moebius t

theorem concrete_expanded_tuple_sign_change :
    expandedTupleSign 3 7 7951 12577 = 1 ∧
      expandedTupleSign 3 75469 7717 12577 = -1 := by
  have hp3 : Nat.Prime 3 := by norm_num
  have hp7 : Nat.Prime 7 := by norm_num
  have hp7951 : Nat.Prime 7951 := by norm_num
  have hp12577 : Nat.Prime 12577 := by norm_num
  have hp7717 : Nat.Prime 7717 := by norm_num
  have hp163 : Nat.Prime 163 := by norm_num
  have hp463 : Nat.Prime 463 := by norm_num
  have hm75469 : ArithmeticFunction.moebius 75469 = 1 := by
    have hh := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
      ((Nat.coprime_primes hp163 hp463).mpr (by norm_num))
    rw [ArithmeticFunction.moebius_apply_prime hp163,
      ArithmeticFunction.moebius_apply_prime hp463] at hh
    norm_num at hh
    exact hh
  unfold expandedTupleSign
  rw [ArithmeticFunction.moebius_apply_prime hp3,
    ArithmeticFunction.moebius_apply_prime hp7,
    ArithmeticFunction.moebius_apply_prime hp7951,
    ArithmeticFunction.moebius_apply_prime hp12577, hm75469,
    ArithmeticFunction.moebius_apply_prime hp7717]
  norm_num

#print axioms quotient_reconstruction
#print axioms quotient_unit_determinant
#print axioms matrix_factorization
#print axioms basisMatrix_det_one
#print axioms inverse_determinant
#print axioms inverse_divisibilities
#print axioms inverse_quotients
#print axioms exists_canonical_lambda_of_coprime
#print axioms tuple_quotient_reconstruction
#print axioms tuple_quotient_inverse
#print axioms shear_determinant_one
#print axioms shear_coordinates
#print axioms concrete_hnf_and_shear
#print axioms concrete_canonical_bases
#print axioms concrete_expanded_tuple_sign_change

end GoldbachResearch.DeterminantCoordinates
