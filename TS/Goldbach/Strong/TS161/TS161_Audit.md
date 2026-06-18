# TS161 Audit - Phi Premortem and Spectral Pivot Ledger

## Status

`repo_committed`

TS161 archives the TS160 phi denominator candidate as a useful probe rather
than a completed Selberg repair.  It proves the local obstruction that blocks
the reuse of the TS149 divisor-envelope refinement with `phi`, then opens the
spectral pivot by referencing the TS94 and TS95 roadmap ledgers.

## Formal obstruction

TS161 proves:

```lean
TS161.Goldbach.sigmaOne_two_eq_three
TS161.Goldbach.totient_two_eq_one_rat
TS161.Goldbach.sigmaOne_two_gt_totient_two
TS161.Goldbach.not_sigmaOne_le_totient_on_positive_levels
```

The decisive computation is:

```text
sigma_1(2) = 3
phi(2) = 1
```

Therefore the global inequality

```text
forall d > 0, sigma_1(d) <= phi(d)
```

is false.  This is exactly the obstruction to copying the TS149 mechanism,
where the proof used `sigma_1(d) <= J2(d)` to absorb the divisor mass.

## Pivot package

The main ledger is:

```lean
TS161.Goldbach.PhiPremortemSpectralPivotLedger
TS161.Goldbach.phiPremortemSpectralPivotLedger
TS161.Goldbach.PhiPremortemSpectralPivotTarget
TS161.Goldbach.phiPremortemSpectralPivotTarget
```

It records:

```text
the TS160 phi candidate,
the fact that D_phi(3) > 2,
the formal divisor-mass obstruction,
the dimension and scale issues as design obligations,
the TS94 trace-kernel roadmap,
the TS95 explicit-formula bridge roadmap.
```

## Scope

TS161 does not prove that every phi-based sieve is impossible.  It proves only
that the simple phi replacement cannot reuse the TS149 divisor-mass absorption
argument.  It also does not supply a concrete spectral kernel or explicit
formula theorem; it records the pivot front and its existing roadmap targets.

## Verification

```powershell
lake build TS.Goldbach.Strong.TS161.PhiPremortemSpectralPivotLedger
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS161
git diff --check -- README.md TS\Goldbach\Strong\TS161
```

Expected result: build succeeds, no audit matches, and no whitespace errors.
