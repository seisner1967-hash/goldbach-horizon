# Frozen rational D_pi lower-bound statements

These signatures are frozen for independent Judge review. The field is exactly
Q. A certificate is the actual MvPolynomial identity for the full-count system,
with Boolean equations, SIEVE nonprime zeros, and declared coarse X0=X1=0.
No Goldbach assumption, positive pair-count assumption, evenness assumption, or
N threshold is added to the certificate lower bound.

```lean
namespace AlgebraicGoldbach.LowerBound

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem inverse_count_fwdDiff (t k n : ℕ) (h : n + k < t) :
    (fwdDiff (1 : ℕ))^[k] (fun s : ℕ => 1 / ((s : ℚ) - t)) n =
      - (k.factorial : ℚ) / falling t n (k + 1)

theorem boolean_inverse_totalDegree_ge (A : MvPolynomial σ ℚ) (t : ℕ)
    (ht : Fintype.card σ < t)
    (hA : ∀ b : σ → Bool,
      MvPolynomial.eval (fun i => boolValue (b i)) A *
        ((∑ i, boolValue (b i)) - t) = 1) :
    Fintype.card σ ≤ A.totalDegree

namespace Restriction

noncomputable def countConstraint (N : ℕ) : R N ℚ :=
  (∑ i : Fin (N + 1), X i) - C (pi N : ℚ)

noncomputable def nonprimeConstraint (N : ℕ) (i : Fin (N + 1)) : R N ℚ :=
  if Nat.Prime i.val then 0 else X i

def DpiCertificate (N : ℕ) (A B : R N ℚ)
    (U C : Fin (N + 1) → R N ℚ) : Prop :=
  1 = A * countConstraint N +
    (∑ i, U i * booleanConstraint i) +
    (∑ i, C i * nonprimeConstraint N i) + B * AlgebraicGoldbach.g N ℚ

theorem Dpi_multiplier_degree_lower_bound (N : ℕ)
    (A B : R N ℚ) (U C : Fin (N + 1) → R N ℚ)
    (hcert : DpiCertificate N A B U C) :
    pi N - r N ≤ A.totalDegree

theorem Dpi_standard_degree_lower_bound (N : ℕ)
    (A B : R N ℚ) (U C : Fin (N + 1) → R N ℚ)
    (hcert : DpiCertificate N A B U C) :
    pi N - r N + 1 ≤ (A * countConstraint N).totalDegree

theorem Dpi_certificate_degree_bound (N d : ℕ)
    (A B : R N ℚ) (U C : Fin (N + 1) → R N ℚ)
    (hcert : DpiCertificate N A B U C)
    (hdegree : (A * countConstraint N).totalDegree ≤ d) :
    pi N - r N + 1 ≤ d

end Restriction
end AlgebraicGoldbach.LowerBound
```

`pi N` and `r N` are the C1 definitions; C1 bridges the former to standard
`Nat.primeCounting` and the latter to the count of unordered prime pairs,
including equal-prime loops. Any standard certificate-degree bound controls
every individual summand, and therefore controls the displayed count summand.
