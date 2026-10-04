# Precision of the generic period-width count

This note preserves all15 frozen Gamma bindings and the original preparation.
It is documentary, not a producer input, additional attempt or revised result.
Root was informed before the unique Gamma START07:28:40.526891UTC.

The paper states that period uncertainty contributes fewer than2^16 grid units.
For the entire generic sin/cos input domain[-4096,4096], a safe bound is2^18:
the integer period has absolute value below2^10, and the certified pi width
is at most128 grid units; subtraction of2*period*pi contributes at most
2^11*128=2^18 units. The actual sampled phases have a smaller range, but
the generic-domain statement should use the larger bound.

This does not alter the implemented width guard
2^48*(input_width+2^-768)+2^-300. It also does not alter any enclosure:
the code subtracts the entire certified pi interval, then checks the residual
domain[-4,4] and evaluates Taylor polynomials with explicit remainder intervals.
Series enclosures and outward arithmetic establish validity independently of
this conservative efficiency count. No old or new mathematical run is repeated.
