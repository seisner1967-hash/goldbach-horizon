# Frozen KARY_MODELS signatures

```lean
theorem family_iff_omitted_card_lt (N k : ℕ) (x : Fin (N + 1) → ℚ) :
    (∀ S : ArithmeticIndex N k, eval x (arithmeticFamily N k S) = 0) ↔
      (CoprimeDivisor.omittedPrimes N x).card < k
```
