# Candidate family table

All model counts refer to solutions before g_N is added. Uniformity concerns
the declared constraints, not the reporting of experimental prime counts.
Seven original candidates fail the pseudo-solution gate. The additional
coprime-divisor density control passes the literal quartet tests but has a
countermodel at4 and is rejected by the Judge as hidden near-full counting.
Its proof audit and all five independent numeric replays passed. No barrier break is claimed.
The general k-ary class is a structural extension of this rejected control,
not a new viable candidate: its actual Q ideal/model classification is verified,
and the Boolean support{3} atN4 excludes certificates for every k>=2 in Lean,
fresh Judge3f4d742. General model counts remain paper statements. No extra
quartet gate or multiplier search is claimed for arbitrary k.

| Family | N tested | Pseudo-solutions / first tested failure | Boolean solutions before g | Uniform constants | Status |
|---|---|---|---|---|---|
| Coarse parity |30,60,100,200|YES at all /30|2^(N/2)|YES|DEAD at all tested N|
| SIEVE only |30,60,100,200|YES at all /30|2^pi(N)|YES|DEAD at all tested N|
| SIEVE + dyadic Bertrand |30,60,100,200|YES at all /30|Exact disjoint-interval counts in evidence/gates.json; >1|YES|DEAD at all tested N|
| Full Bertrand coarse |30,60,100,200|YES at all /30; also every N>=24 in Lean|2605;85011864;89138673060348;100361220703408430148554030100|YES|Uniformly DEAD; m=1 directly pins X2, violates guard|
| Full Bertrand SIEVE |30,60,100,200|YES at all /30|40;4608;1169766;2451642922548|YES|DEAD at all tested N|
| Full Bertrand SIEVE + proper-divisor coverage |30,60,100,200|YES at all /30|At least2, explicit distinct models; full counts unmeasured|YES|DEAD at all tested N; small-prime coordinates pinned|
| Proper Bertrand ONLY, m>=2 |30,60,100,200|YES at all /30; every N>=24 Judge-verified in Lean|1360168984;1460447976571497408;1605779531254534169267479998816;2035567386629014189772777661745725556916470813194361691441184|YES|Uniformly DEAD; EVERY bit is free; L4/L5 verified21f199d|
| Coprime-divisor density control |4,30,60,100,200|NO at quartet, literal RUP/DRAT logs; YES at4 /4|(pi(N)+1)*2^(N+1-pi(N)), exact counts in evidence/coprime_density/gates.json|YES|Judge-rejected near-full density; uniform L8 DEAD at4; all checks verified37ee03e|
| D_pi(N), calibration only |10..60 even|Excluded research control|Exactly1, proved in Lean|NO, pi(N) is a prime sum|PINNING and NON-UNIFORM; measured only under section7|

The interval-family counts are independently checked by different dynamic
programs and by exhaustive enumeration at N30 for the coarse family, and
N4..14 for the proper interval family. SAT witnesses are evaluated
directly with exact integers. The seven original candidates make only SAT claims.
The additional density control has complete CNFs and literal three-addition
RUP/DRAT logs for all four UNSAT claims, separately replayed before Judge review.

For the coarse family let H=floor(N/2), h the least odd integer greater than H.
The uniform support is {2,h} plus all odd n with3<=n<H except N-h.
It meets every interval and avoids every complementary pair, but selects9.
For the SIEVE strengthening, the recorded sparse prime supports are separate.

Proper-divisor coverage has been independently checked by the Judge in a fresh
clone. It forces X_p=1 when p is prime and p^2<=N, an explicitly flagged
coordinate-pinning obstruction. Its unconditional prime truth is currently a
paper argument for the SIEVE extension; the broader actual-polynomial
factor-horizon classification is independently verified in Lean.
