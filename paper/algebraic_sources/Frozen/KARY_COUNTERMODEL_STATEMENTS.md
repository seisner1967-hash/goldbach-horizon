# Frozen KARY_COUNTERMODEL signatures

```lean
theorem modelAtFour_omittedPrimes :
    CoprimeDivisor.omittedPrimes 4 modelAtFour = {(2 : Fin 5)}

theorem modelAtFour_omitted_card :
    (CoprimeDivisor.omittedPrimes 4 modelAtFour).card = 1

theorem modelAtFour_family (k : ℕ) (hk : 2 ≤ k) (S : ArithmeticIndex 4 k) :
    eval modelAtFour (arithmeticFamily 4 k S) = 0

theorem modelAtFour_boolean (i : Fin 5) :
    eval modelAtFour (booleanConstraint i) = 0

theorem modelAtFour_g_zero : eval modelAtFour (g 4 ℚ) = 0

theorem family_no_certificate_at_four (k : ℕ) (hk : 2 ≤ k)
    (A : ArithmeticIndex 4 k → R 4 ℚ) (U : Fin 5 → R 4 ℚ) (B : R 4 ℚ) :
    ¬ Certificate (arithmeticFamily 4 k) A U B
```
