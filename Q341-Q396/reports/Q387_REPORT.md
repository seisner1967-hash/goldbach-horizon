# Q387 / RS15H report

## Verdict

```text
Q387_REFLECTED_GAMMA_EXCEPTION_PASS
Q387_EXCEPTIONAL_PAIR_REDUCTION_PASS
Q387_NEGATIVE_EVEN_VALUE_REINDEX_PASS
Q387_EXCEPTIONAL_SEED_OBSTRUCTION_PASS

Q387_EXCEPTIONAL_THETA_VALUE_PASS       : NOT_OBTAINED
Q387_EXCEPTIONAL_NONZERO_VALUE_PASS     : NOT_OBTAINED
Q387_AUXILIARY_THETA_SEED_REPAIR_PASS   : NOT_OBTAINED
```

## What was proved

For `s = 1 + 2*n`, the reflected completed auxiliary term is zero because
`Gammaℝ (1-s)` is zero.  On the Mellin seed domain, the auxiliary pair
therefore equals the completed theta expression at `s`.

For `0 < n`, the reflected point `-2*n` is exactly Q386's point
`negativeEvenPoint (n-1)`.  Its completed theta value is consequently equal
to Q386's exact value
`sourceRThetaFullLineIntegral (negativeEvenPoint (n-1)) / 2`.

Finally, if that exact value is nonzero, the old positive-odd Gaussian seed
identity is impossible.  This is a formal obstruction, not a non-nullity
claim.

## Not obtained

No closed form, sign, or nonzero theorem for the Q386 full-line integral was
proved.  No equality with `sourceCompletedZeta` or `sourceGaussianMellin` was
introduced.  The old Q384 zero-based seed connector remains unused.

## Verification

```text
lake build Q387Probe : PASS
tasks replayed/built  : 3342/3342
axioms                : propext, Classical.choice, Quot.sound
forbidden scan        : EMPTY
Git                   : HEAD = origin/main = 433e29e
Lean/Lake processes   : 0 at closeout
```

Q387 is a structural analytic progress milestone.  `SourceAuxiliaryThetaSeed`
and `BRIDGE_A` remain open.
