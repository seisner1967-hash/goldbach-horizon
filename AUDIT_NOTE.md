# Interface Predicate Audit — Horizon Goldbach
# Internal Note — April 5, 2026

## Summary

An internal audit of the five external hypotheses in the Goldbach Horizon
framework revealed that **four out of five are trivially satisfiable** due
to weak interface definitions. Only `PCBAsymptotic` carries genuine
asymptotic arithmetic content.

This is a design discovery, not a proof breakthrough. It defines the
next phase of the project: strengthening the interface predicates to
capture the intended mathematical content.

## Audit Results

| Predicate | Lean status | Mathematical status | Trivial witness | Problem |
|-----------|-------------|--------------------|-----------------|---------| 
| `CompactZoneBound` | provable | **weak** | C0=1/5, μ=0 | No connection to actual domination ratio |
| `KLMNHypothesis` | provable | **weak** | FormBoundData(4C0, 0) | Witness not tied to actual quadratic form of H_PC |
| `SpectralPositivityHypothesis` | provable | **weak** | Dirac measure at 0 | Measure not tied to actual resolvent |
| `FredholmOTSAHypothesis` | provable | **weak** | traceNorm=0 | Not tied to actual Fredholm determinant |
| `BandwidthSufficient` | theorem | **weak** | Bound itself as witness | No Jackson approximation content |
| `PCBAsymptotic` | open | **genuine** | — | Asymptotic Goldbach conjecture |

## Why the predicates are weak

Each hypothesis uses an existential quantifier (`∃ witness, conditions(witness)`)
where the conditions do not constrain the witness to correspond to any real
mathematical object. For example:

- `KLMNHypothesis` asks for `FormBoundData` with `relativeBound < 1`, but
  the data need not come from the actual Prime-Crystal Hamiltonian
- `SpectralPositivityHypothesis` asks for a positive spectral measure, but
  any Dirac measure satisfies this regardless of the operator
- `FredholmOTSAHypothesis` asks for a trace norm < 1 and a positive Fredholm
  partial, but `traceNorm = 0` trivially satisfies everything

## What was already strengthened

`CompactZoneBound` was the first weak predicate identified. It was strengthened
to `CompactZoneBoundStrong` (in CompactZone/Bridge.lean), which connects the
bound to the actual arithmetic measure and confining weight via explicit
per-cell rational certificates verified by `native_decide`. This is the
model for strengthening the other predicates.

## PCBAsymptotic — the genuine hypothesis

```lean
def PCBAsymptotic : Prop :=
  ∃ N_pcb : ℕ, ∀ n : ℕ, N_pcb < n → Even n → 0 < goldbachRep n
```

This is essentially the asymptotic Goldbach conjecture: there exists N₀
such that every even integer > N₀ is a sum of two primes. The universal
quantifier over all n > N₀ prevents any finite computation from discharging
it. A proof would require the circle method (Hardy-Littlewood, Vinogradov)
or equivalent machinery.

## Strengthening plan

### Priority 1: CompactZoneBoundStrong (DONE)

Already strengthened and proved. The strong version connects to the actual
domination ratio R(Q) = μ(Q)/W(Q) via Taylor enclosures and native_decide.

### Priority 2: KLMNHypothesisStrong

Must connect `FormBoundData` to the actual quadratic form of H_PC:
- Reference form q₀ = kinetic + confinement
- Perturbation q₁ = arithmetic Dirac comb
- Form-boundedness with explicit Sobolev trace constants
- Requires: Sobolev trace on ℝ (1 sorry remaining)

### Priority 3: SpectralPositivityStrong

Must connect the spectral measure to the actual resolvent of H_PC:
- Green function G₀(z; x, y) from the confining Hamiltonian
- Krein resolvent formula connecting H and H₀
- Herglotz representation from the actual operator
- Requires: unbounded operator theory (not in Mathlib)

### Priority 4: FredholmOTSAStrong

Must connect trace norm and Fredholm partial to the actual operator:
- Trace-class perturbation from the arithmetic potential
- Fredholm determinant of (I + K) where K is the resolvent difference
- Windowed approximation with controlled error
- Requires: trace-class operators (not in Mathlib)

### Priority 5: BandwidthSufficient (strong version)

Must connect to actual Jackson/Sobolev approximation theory:
- Modulus of continuity of the spectral density
- Jackson kernel approximation with explicit error
- Bandwidth absorption in the Mellin domain
- Requires: Jackson's theorem (not in Mathlib)

## Impact on project narrative

The correct narrative is no longer:

> "The framework reduces Goldbach to five explicit analytic hypotheses."

The correct narrative is:

> "The framework formalizes a conditional logical skeleton. An internal
> audit revealed that four of the five interface predicates are too weak
> to capture the intended analytic content. One predicate (CompactZoneBound)
> has been successfully strengthened and proved. The remaining four require
> redesign. Only PCBAsymptotic currently carries genuine arithmetic content."

## Conclusion

This audit is the most important result of the current phase. It shows
that the real work is not proving more theorems in Lean, but redesigning
the interfaces to capture the mathematics they were intended to represent.
The CompactZone strengthening serves as the template for this redesign.
