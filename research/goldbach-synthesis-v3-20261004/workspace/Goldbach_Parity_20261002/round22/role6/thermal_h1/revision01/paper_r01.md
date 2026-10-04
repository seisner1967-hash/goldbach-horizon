# Source revision01 — new closed radius representation, no new execution

The original attempt is closed TECHNICAL_SERIALIZATION_FAILURE, receipt
2c7409087b6f4c18d9de616592d3c8b3274622bd05feb9fd12d54f93a0548f48,
closure3f4ca3b9c9f03ab4a08c6f4922252a78f91ca768ceeb9aa92f42f1b755eda027.
Its25bindings, gate,27copies and actual directory remain untouched. No
completed original result exists and no phase value or partial PASS is used.
This source revision is a new bank and requires its own root gate.

## Remedy, conservative recurrence and exported sizes

For polynomial powers at an exact dyadic point p, let v_j approximate p^j
with absolute norm error e_j. If U is the L1 upper bound of p, nearest
dyadic multiplication gives error r_j certified from exact Gaussian integer
products. Set c_j=U e_j+r_j and e_(j+1)=ceil(2^512 c_j)/2^512.
Then0<=e_(j+1)-c_j<2^-512, so the new e_(j+1) is still an enclosure.
Every supplement is checked exactly and its dyadic upper bound is accumulated;
the denominator bit length of each propagated radius is checked
<=513. This is outward rounding, not a truncation of uncertainty.

The polynomial node displacement error k(U+rho)^(k-1)rho is also rounded
outward onto the same grid. Otherwise that position term could independently
reproduce the very denominator growth being repaired. The four budgets
function/position/weights/accumulation are kept separate. Their factors are
dyadic points or512-bit grid radii; exported products have denominator bit
length <=1025. No runtime integer-string setting is changed. No float is
introduced. The exact large Gaussian integer reference is independently
computed with binary exponentiation and is enclosed on512bits before export;
its enormous intermediate numerator is never converted to decimal JSON.

The regression catalogue, before all other cases, has exact points
(3/4+EPS)+i(1/8+EPS), exponent512, and
(3/4-EPS)-i(1/8+EPS), exponent768, EPS=2^-512. Both have norm<1.
The independent integer-power reference uses no transported radius and no
kernel recurrence. Their agreement tests the new representation well beyond
the original failing polynomial degrees; it does not prove the recurrence.
The proof above and actual integer rounding certificates carry enclosure.

The unused future800-cell PowerTrack in the fresh primitive source is repaired
conservatively too: its rounded radius is included, product-round plus
radius-round is checked<=2EPS, and the existing finite closed bound remains.
This component bank does not exercise or certify the whole800-cell recurrence.

## New phase catalogue and inherited analytic source provenance

All analytic modules are local new source files, adapted explicitly from the
original authored sources and rehashed. They import no original producer,
kernel, bank result, log, cache or PASS. The genuine normalized M128/K64 EM
and Γshift64/order32 Stirling formulas and their remainders are preserved,
not defined from the desired thermal correlation. SOURCE adaptation alone
is not numerical validation; all reference values will be computed anew.

New Gamma phase cases: sigma={1,3/2,2}, gamma={0,-5,5,-19,19},15cases.
The independent nonturned Γ integral retains[-64,6],2240cells each,
degree24, radius1/4 and q1/16. On its disks
|g|<10 exp(19/4)<=10*3^5=2430<2^12.
Thus the new Cauchy remainder is70*2^12*(1/16)^25/(1-1/16), with unchanged
proven left and right tails(3/8)^64+257*2^-256. The actual rounding width
and phase-informativeness guards remain2^-120 and1/1024. M=2^12 has no
claim for the four Γ100 expanded-domain width cases.

The three zero-height Γ cases, known EM special values and polynomial DFT
prerequisites overlap the failed first catalogue. This is explicit overlap
of mathematical objects, not an old output replay. Other phase inputs are
new. EM width cases now use imag=±1597/16. The original DFT orientation and
paid-alias cases are needed to exercise the repaired high-degree radii; they
are all recalculated from newly constructed roots/weights, never copied.

## Fixed catalogue, checker and limits

46cases:2radius regressions+15phase+4Γwidth+2EMconstants+8EMwidth+
13polynomial+2alias.19mutations,15sqrt certificates,33600reference cells
and806400reference Horner products. The fixed polynomial catalogues imply
50720grid-radius updates and50944rounded point products, checked independently
from the emitted counters. These are source counts, not new
timings. Every point, root, weight, arithmetic remainder, phase integral
and error budget must be actually constructed under the future gate.

The checker imports only Fraction, verifies the new46/15catalogues,
independent overlap/disjointness, outward radius denominator bounds,
nonnegative supplement,19mutations and no-global-credit fields. Correctly
wide references/mutations are UNRESOLVED, not identity-false. Source-only
metadata may freeze bindings. Only the exact distinct authorization for
THERMAL_COMPONENT_R01_AUX22 permits its sole future attempt. GlobalH1,
Mellin/FE formal proofs, all204800thermal nodes, arithmeticΛtrace, Arch,
horizontal nonannulation, coefficientN, D_N and WIN remain OPEN here.
