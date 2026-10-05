"""Publication inventory and tables from existing, saved algebraic artifacts only.

No Lean, solver, certificate checker, build, or research program is invoked.
Run with --source-root pointing to the existing source collection once to copy
small portable artifacts. Subsequent runs read the copies beside this script.
Git, when used, is read only (show); existing source files are never changed.
"""

from __future__ import annotations

import argparse
import collections
import csv
import hashlib
import io
import json
from pathlib import Path
import re
import subprocess

PAPER = Path(__file__).resolve().parent
SOURCES = PAPER / "algebraic_sources"
COLLECTION = "AlgebraicGoldbach_20261004"
PROOF = "e5c4e119473e0023b0f500e322b5ed1ac4013e00"
ACCEPTANCE = "6f7d181a5440ad9c7c94c362efa968892dcd17c3"
ROOT_ACCEPTANCE = "3d5f0ff4df4e88fa3579f604eb341487ecf7552f"
GATE_DATA = "d8b42190c5721f10ca2ef48a1e6b8577910b0179"
GATE_RECEIPT = "4a0573938a0d199e1373e6078e7a15f09c15264d"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = re.compile(r"(?i)(?:\b[a-z]:[\\/]|[\\/](?:Users|home)[\\/]|[A-Z0-9._%+-]+@[A-Z0-9.-]+\.[A-Z]{2,})")

MODULE_SUMMARIES = {
    "AlgebraicGoldbach": "Import collection for the accepted auxiliary modules; the frozen open target is excluded.",
    "AlgebraicGoldbach.Soundness": "Ordinary polynomial certificate soundness, ordered Goldbach count including loops, and explicit faithful-field bounds.",
    "AlgebraicGoldbach.UniformCountermodel": "A Boolean coarse/Bertrand common zero for every N>=24, with composite coordinates allowed.",
    "AlgebraicGoldbach.UniformNonpinning": "The uniform coarse model differs from the prime indicator and selects composite nine.",
    "AlgebraicGoldbach.BertrandFamily": "Actual rational Bertrand polynomial family, prime truth, and the N>=24 common-zero obstruction.",
    "AlgebraicGoldbach.PinnedControl": "Circular coordinate-pinning calibration and its certificate equivalence; multiplier and summand degrees are distinct.",
    "AlgebraicGoldbach.FactorCoverage": "Proper-divisor coverage at horizon M<=N^2 is equivalent to pins on primes with p^2<=M.",
    "AlgebraicGoldbach.ProperBertrand": "Interval-only family with m>=2, every-coordinate Boolean freedom, prime truth, and N>=24 obstruction.",
    "AlgebraicGoldbach.SignDefinite": "Canonical rational coefficients of one sign preserve every supplied prime-supported common zero.",
    "AlgebraicGoldbach.CoprimeDivisor": "Actual rational coprime-divisor equations are equivalent to at most one prime coordinate differing from one.",
    "AlgebraicGoldbach.CoprimeKaryIdeal": "Equality of the actual rational arithmetic k-ary divisor ideal and the prime k-subset ideal.",
    "AlgebraicGoldbach.CoprimeKaryModels": "Arbitrary rational models are classified by fewer than k prime coordinates differing from one.",
    "AlgebraicGoldbach.CoprimeKaryCountermodel": "An actual Boolean common zero at N=4 excludes a certificate for each k>=2 in this exact class.",
    "AlgebraicGoldbach.LiteralCube": "Actual Boolean/coarse/ordered-g cube and a strict finite weighted covering obstruction.",
    "AlgebraicGoldbach.LowerBound.BooleanLattice": "Rational Boolean-lattice adjoints, commutator, and strict low-layer raising injectivity.",
    "AlgebraicGoldbach.LowerBound.BooleanCoefficients": "Ordinary exponent-support aggregation and compatibility with genuine variable multiplication.",
    "AlgebraicGoldbach.LowerBound.BooleanCoefficientDegree": "Aggregated coefficients vanish on supports larger than ordinary total degree.",
    "AlgebraicGoldbach.LowerBound.BooleanMultiplierRigidity": "Top-layer rigidity for the actual count multiplier, arbitrary rational parameter and signed functions.",
    "AlgebraicGoldbach.LowerBound.BooleanCountBridge": "The genuine ordinary count polynomial maps to the actual count multiplier.",
    "AlgebraicGoldbach.LowerBound.BooleanAnnihilation": "Boolean-equation multiples have zero aggregated coefficient image, without asserting ordinary polynomial zero.",
    "AlgebraicGoldbach.LowerBound.CountVariableCommutation": "The actual variable and count actions commute on finite types for arbitrary rational parameters.",
    "Calibration.C1": "Full-count calibration, prime support, unordered pairs including loops, and the exact independence threshold.",
    "Calibration.LowerBound": "Universal ordinary-Q static-NS lower bound for the supplied full-count certificate, not an upper construction.",
    "Calibration.Growth": "The required ordinary-Q static-NS degree is unbounded along even N, without asserting existence of certificates.",
    "Calibration.PCRestriction": "Genuine ordinary-Q PC restriction preserves rules and line degree; the lower corollary retains an external hypothesis.",
}

# Each short description is a reading aid. The exact copied source header and
# source line, including its hypotheses and section context, remain authoritative.
SHORT_STATEMENTS = {
    "booleanConstraint_eval": "Evaluating a Boolean generator gives x_i^2-x_i.",
    "booleanConstraint_zero_iff": "Over a domain, a zero Boolean generator means x_i is zero or one.",
    "primePoint_boolean": "The prime indicator satisfies every Boolean generator.",
    "primePoint_zero": "The prime indicator is zero at coordinate zero.",
    "primePoint_one": "The prime indicator is zero at coordinate one.",
    "primePoint_even_gt_two": "Even coordinates greater than two vanish at the prime indicator.",
    "primePoint_coarse": "The prime indicator satisfies the declared coarse constraints.",
    "certificate_excludes_common_zero": "A supplied identity excludes a supplied common zero of all its generators.",
    "certificate_nonzero_at_primePoint": "A supplied certificate and genuine constraint truth force g to be nonzero at the prime point.",
    "eval_g_primePoint": "Prime-point evaluation is the original ordered Goldbach count, including the midpoint loop.",
    "goldbachCount_positive_iff": "Positive ordered count is equivalent to existence of a prime pair summing to N.",
    "goldbachCount_le": "The ordered count is at most N+1.",
    "certificate_goldbachCount_positive": "A supplied certificate and prime-truth premises imply positive ordered count.",
    "certificate_implies_goldbach": "A supplied certificate and prime-truth premises imply existence of the corresponding prime pair.",
    "eval_g_rat_nonzero_iff": "Rational prime-point g is nonzero exactly when the ordered count is positive.",
    "certificate_g_rat_positive": "The supplied rational certificate and prime-truth premises give positive prime-point g.",
    "bounded_zmod_cast_injective": "Reduction is injective on the explicitly bounded nonnegative integer interval.",
    "bounded_zmod_cast_zero_iff": "Within the stated strict field bound, reduction preserves zero.",
    "goldbachCount_le_momentBound": "The ordered count obeys the declared integer moment bound.",
    "bounded_sum_le_momentBound": "A bounded nonnegative finite sum obeys the declared moment bound.",
    "finiteFieldPolicy_g_nonzero_iff": "The explicit field policy makes prime-point nonzero equivalent to positive integer count.",
    "finiteFieldPolicy_g_zero_iff": "The explicit field policy makes prime-point zero equivalent to zero integer count.",
    "high_bounds": "The selected upper endpoint lies between floor(N/2)+1 and floor(N/2)+2.",
    "high_odd": "The selected upper endpoint is odd.",
    "bit_boolean": "The model's integer bit is idempotent.",
    "selected_coarse": "For N>=24 the selected support satisfies the coarse exclusions.",
    "selected_no_sum": "For N>=24 two selected coordinates cannot sum to N.",
    "selected_bertrand": "For N>=24 each declared Bertrand interval contains a selected coordinate.",
    "bit_goldbach_zero": "For N>=24 the model's full ordered complementary-pair sum is zero.",
    "prime_indicator_bertrand": "Each declared interval contains a prime, by the imported Bertrand theorem.",
    "bit_bertrand_product": "For N>=24 each interval product vanishes on the model.",
    "prime_bit_boolean": "The prime bit is idempotent.",
    "prime_bit_coarse": "The prime bit satisfies the coarse exclusions.",
    "prime_bit_bertrand_product": "Each declared interval product vanishes on the prime bit.",
    "bit_coarse": "For N>=24 the model bit satisfies the coarse exclusions.",
    "uniform_bertrand_countermodel": "For every N>=24 the explicit bit model satisfies Booleanity, coarse constraints, intervals and g=0.",
    "uniform_model_selects_composite_nine": "For N>=24 the model selects nine whereas the prime indicator does not.",
    "uniform_model_differs_from_primes": "For N>=24 the model is different from the prime indicator.",
    "primePoint_bertrandPolynomial": "The true prime point zeros the actual interval polynomial under its explicit interval hypotheses.",
    "primePoint_bertrandFamily": "The true prime point zeros every actual coarse/Bertrand family generator.",
    "modelPoint_boolean": "The explicit rational model satisfies every Boolean generator.",
    "modelPoint_coarse": "For N>=24 the explicit rational model satisfies the coarse generators.",
    "modelPoint_bertrandPolynomial": "For N>=24 the model zeros the actual interval polynomial under its explicit interval hypotheses.",
    "modelPoint_bertrandFamily": "For N>=24 the model zeros every actual coarse/Bertrand generator.",
    "modelPoint_g_zero": "For N>=24 the model zeros the original ordered g.",
    "modelPoint_differs_from_primePoint": "For N>=24 the explicit rational model differs from the prime point.",
    "bertrandFamily_common_zero": "For N>=24 an actual rational Boolean/coarse/Bertrand/g common zero is supplied.",
    "bertrandFamily_has_second_boolean_solution": "For N>=24 both prime and distinct model points satisfy the family without g.",
    "bertrandFamily_no_certificate": "For N>=24 this exact coarse/Bertrand family has no supplied certificate identity.",
    "complement_involutive": "The bounded complementary-coordinate map is an involution.",
    "pinned_cross_sum": "The complementary-coordinate cross sum can be reindexed.",
    "pinned_telescoping": "The pinned generators telescope to g minus the prime-point count.",
    "pinned_control_certificate": "A nonzero prime-count premise yields the explicit circular pinned-control certificate.",
    "pinned_family_pins": "The pinned family has exactly the prime-indicator common zero.",
    "pinned_certificate_iff_goldbach": "Existence of a pinned-control certificate is equivalent to positive ordered count.",
    "pinned_multiplier_degree_le_one": "The explicit pinned multipliers have ordinary degree at most one.",
    "pinned_B_degree_zero": "The explicit coefficient multiplying g is constant.",
    "pinned_summand_degree_le_two": "Each explicit pinned multiplier-generator summand has degree at most two.",
    "g_degree_le_two": "The original ordered g has ordinary degree at most two.",
    "pinned_g_summand_degree_le_two": "The explicit constant multiple of g has degree at most two.",
    "minFac_le_horizon": "For a composite below M<=N^2 its least factor is within the coordinate horizon.",
    "primePoint_factorPolynomial": "Under M<=N^2 the prime point zeros the specified composite's proper-divisor polynomial.",
    "primePoint_coverage": "Under M<=N^2 the prime point satisfies proper-divisor coverage.",
    "properDivisors_prime_square": "The proper-divisor set of a prime square consists of its prime root.",
    "coverage_implies_primePins": "Coverage forces the declared small-prime coordinate pins.",
    "primePins_implies_coverage": "Under M<=N^2 the small-prime pins imply coverage.",
    "coverage_iff_primePins": "Under M<=N^2 coverage is equivalent to prime pins for p^2<=M.",
    "square_horizon_pins_prime_coordinates": "Coverage through N^2 pins every prime coordinate to one.",
    "square_horizon_and_sieve_pin_vector": "Coverage through N^2 plus SIEVE pins the entire prime vector.",
    "modelPoint_small_prime": "The model selects primes within the explicit smaller horizon.",
    "modelPoint_coverage": "The model satisfies coverage when M<=(floor(N/2)-3)^2.",
    "primePoint_horizonFamily": "Under M<=N^2 the prime point satisfies the combined horizon family.",
    "modelPoint_horizonFamily": "Under N>=24 and the smaller-horizon bound the model satisfies the combined family.",
    "horizonFamily_common_zero": "The smaller-horizon hypotheses supply an actual family/Boolean/g common zero.",
    "horizonFamily_no_certificate": "The explicit smaller-horizon hypotheses exclude a certificate for this combined family.",
    "horizonFamily_has_second_boolean_solution": "Under the explicit horizon hypotheses a distinct second Boolean family point exists.",
    "primePoint_family": "The prime point satisfies this module's actual family under its declared index hypotheses.",
    "onePoint_boolean": "The all-one point satisfies Booleanity.",
    "exceptPoint_boolean": "The one-coordinate-flip point satisfies Booleanity.",
    "onePoint_family": "The all-one point satisfies this module's family.",
    "exceptPoint_family": "The one-coordinate-flip point satisfies this module's family.",
    "onePoint_differs_from_primePoint": "The all-one point differs from the prime indicator.",
    "family_has_second_boolean_solution": "A Boolean family model distinct from the prime point is supplied under the exact source hypotheses.",
    "family_does_not_pin_any_coordinate": "For every coordinate the family has a Boolean model taking each of zero and one there.",
    "modelPoint_family": "For N>=24 the explicit model satisfies the proper interval-only family.",
    "family_common_zero": "For N>=24 the proper interval-only family has an actual Boolean/g common zero.",
    "family_no_certificate": "For N>=24 the proper interval-only family has no certificate identity.",
    "coefficient_on_primes_eq_zero": "Nonnegative canonical coefficients and prime truth force each prime-supported monomial coefficient to vanish.",
    "nonnegative_equation_vanishes_on_sievePoint": "A nonnegative-coefficient prime-true equation vanishes on every prime-supported rational point.",
    "sign_definite_equation_vanishes_on_sievePoint": "A canonical same-sign prime-true equation vanishes on every prime-supported rational point.",
    "sign_definite_family_preserves_sieve_common_zero": "A same-sign prime-true strengthening preserves a supplied prime-supported family common zero.",
    "sign_definite_strengthening_has_no_certificate": "A supplied prime-supported Boolean/g common zero survives the same-sign strengthening and excludes its certificate.",
    "nearFullPrimeSelection_iff_omitted_card_le_one": "Near-full prime selection means at most one prime coordinate differs from one.",
    "pairDivisors_prime_pair": "The coprime-prime pair divisor set consists of those two primes.",
    "family_implies_ordered_prime_pair_selected": "The coprime family forces at least one coordinate of each ordered distinct prime pair to be one.",
    "family_implies_nearFullPrimeSelection": "The coprime-divisor family implies near-full prime selection.",
    "nearFullPrimeSelection_implies_family": "Near-full prime selection implies all coprime-divisor equations.",
    "family_iff_nearFullPrimeSelection": "The rational coprime-divisor equations are exactly near-full prime selection.",
    "family_iff_at_most_one_omitted_prime": "The rational coprime-divisor equations hold iff at most one prime coordinate differs from one.",
    "leastFactor_val": "The bounded least-factor coordinate has the expected natural value.",
    "leastFactor_prime": "Under the explicit lower bound the least-factor coordinate is prime.",
    "leastFactor_dvd": "The least-factor coordinate divides the original number.",
    "leastFactor_injective_on": "Least-factor selection is injective on the declared pairwise-coprime arithmetic index.",
    "leastFactor_image_primeAllowed": "The least-factor image is an allowed prime k-subset.",
    "leastFactor_image_subset_divisors": "The least-factor image lies in the arithmetic divisor set.",
    "primeAllowed_arithmeticAllowed": "An allowed prime k-subset is an allowed arithmetic index.",
    "prime_divisors_eq": "The divisor set of an allowed prime subset is that subset.",
    "arithmetic_factorization": "The actual arithmetic product factors through its selected least-prime-factor product.",
    "arithmeticIdeal_eq_primeIdeal": "The actual rational arithmetic k-ary ideal equals the prime k-subset ideal.",
    "family_iff_omitted_card_lt": "For arbitrary rational points, the k-ary family holds iff fewer than k prime coordinates differ from one.",
    "modelAtFour_omittedPrimes": "The N=4 model's omitted-prime set is the singleton containing two.",
    "modelAtFour_omitted_card": "The N=4 model omits exactly one prime coordinate.",
    "modelAtFour_family": "For k>=2 the N=4 model satisfies the actual arithmetic family.",
    "modelAtFour_boolean": "The N=4 model satisfies every Boolean generator.",
    "modelAtFour_g_zero": "The N=4 model zeros the original ordered g, including its midpoint loop.",
    "family_no_certificate_at_four": "For every k>=2 this exact k-ary family has no certificate at N=4.",
    "value_boolean": "Each effective cube factor has Boolean rational value.",
    "value_negate": "Factor negation evaluates to one minus the original factor value.",
    "cubePoint_boolean": "Every actual arithmetic cube point satisfies Booleanity.",
    "cubePoint_coarse_zero": "For even N>=6 every coarse-forbidden cube coordinate is zero.",
    "cubePoint_coarse": "For even N>=6 every cube point satisfies the actual coarse equations.",
    "cubePoint_complement_product": "For even N>=6 each cube complementary-coordinate product is zero.",
    "cubePoint_g_zero": "For even N>=6 every cube point zeros the original ordered g.",
    "literal_eval": "An ordinary literal evaluates to its effective cube factor.",
    "clause_eval": "An actual clause evaluates to its coefficient times its effective factors.",
    "automatic_eval_zero": "An automatic clause is zero everywhere on the cube.",
    "clause_nonzero_iff": "A nonautomatic clause is nonzero exactly on its declared Boolean-coordinate requirements.",
    "choices_mem_iff": "The clause's allowed Boolean coordinate values have the stated literal characterization.",
    "badSet_eq_piFinset": "A nonautomatic clause's bad set is the product of its coordinate choices.",
    "choices_card": "Each coordinate has one allowed choice on effective support and two off it.",
    "badSet_card": "The exact clause bad-set size equals its declared weight.",
    "cube_card": "The actual Boolean cube has cardinality two to its declared finite dimension.",
    "weighted_common_zero": "For even N>=6 strict total clause weight below cube size leaves a full family/Boolean/coarse/g common zero.",
    "falling_ne_zero": "The rational falling product is nonzero under its explicit natural-index bound.",
    "falling_back": "The falling product satisfies its back recurrence.",
    "falling_front": "The falling product satisfies its front recurrence.",
    "inverse_count_fwdDiff": "The reciprocal-count forward difference has the stated factorial/falling-product formula.",
    "inverse_count_fwdDiff_ne_zero": "The reciprocal-count forward difference is nonzero under its strict index bound.",
    "cubeContrast_monomial_zero": "An exponent missing a variable has zero alternating cube contrast.",
    "cubeContrast_eval_zero_of_totalDegree_lt": "Ordinary degree below the variable count gives zero alternating cube contrast.",
    "cubeWeight_indicator": "The indicator cube weight is the stated alternating cardinality sign.",
    "boolValue_indicator_sum": "The rational sum of an indicator equals its support cardinality.",
    "cubeContrast_cardinality": "The cardinality-weighted cube sum equals the corresponding forward difference.",
    "inverse_count_cubeContrast": "The reciprocal count's cube contrast is its highest forward difference.",
    "boolean_inverse_totalDegree_ge": "A supplied Boolean-cube inverse of count minus t has degree at least the variable count when t exceeds it.",
    "totalDegree_substitution_le": "Substitution by degree-at-most-one polynomials does not increase ordinary total degree.",
    "totalDegree_eq_degLex_degree": "Ordinary total degree agrees with the degree-lex leading-degree convention under the stated types.",
    "totalDegree_mul_eq": "For nonzero ordinary rational polynomials the degrees add under multiplication.",
    "vars_card": "The canonical restriction variable type has cardinality pi(N)-r(N).",
    "polynomial_degree_le": "The canonical restriction does not increase ordinary total degree.",
    "polynomial_eval": "The restricted polynomial evaluates as the original polynomial at the restriction point.",
    "point_boolean": "The restriction point is Boolean.",
    "point_nonprime_zero": "The restriction point is zero on nonprime coordinates.",
    "point_g_zero": "The restriction point zeros the original ordered g.",
    "point_sum": "The restriction point's full count equals the remaining-variable Boolean count.",
    "certificate_inverse": "The supplied full-count certificate restricts to a Boolean-cube inverse identity.",
    "certificate_count_gt_vars": "A supplied certificate implies strict prime-count versus remaining-variable-count separation.",
    "certificate_multiplier_ne_zero": "The count multiplier in a supplied full-count certificate is nonzero.",
    "Dpi_multiplier_degree_lower_bound": "The supplied ordinary-Q full-count certificate has count-multiplier degree at least pi-r.",
    "countConstraint_coeff": "The specified degree-one count coefficient is one.",
    "countConstraint_ne_zero": "The actual full-count polynomial is nonzero.",
    "countConstraint_totalDegree": "The actual full-count polynomial has ordinary total degree one.",
    "Dpi_standard_degree_lower_bound": "The count summand of a supplied ordinary-Q full-count certificate has degree at least pi-r+1.",
    "Dpi_certificate_degree_bound": "Any stated upper degree on that count summand is at least pi-r+1.",
    "mem_primes": "Prime-set membership has the declared prime-and-horizon characterization.",
    "mem_pairRepresentatives": "Pair-representative membership records the declared prime endpoints and ordering, including a loop.",
    "pair_sets_injective": "Distinct ordered representatives give distinct unordered prime-pair sets.",
    "mem_unorderedPrimePairs": "Unordered-pair membership is exactly a prime pair summing to N, including repeated endpoints.",
    "pi_eq_primeCounting": "The declared prime-set count agrees with Mathlib primeCounting.",
    "r_eq_card_representatives": "The unordered pair count equals the representative count.",
    "upperEndpoints_subset": "The removed upper endpoints are prime coordinates.",
    "upperEndpoints_card": "The removed upper-endpoint set has cardinality r(N).",
    "maximumSupport_card": "The canonical maximum independent support has cardinality pi(N)-r(N).",
    "maximumSupport_independent": "The canonical maximum support is independent of complementary prime pairs.",
    "independent_card_le": "Every declared independent prime support has at most pi(N)-r(N) elements.",
    "independent_exists_iff": "An independent prime support of size m exists iff m<=pi(N)-r(N).",
    "boolean_iff": "A rational Boolean equation holds iff the value is zero or one.",
    "mem_support": "Support membership has the declared horizon-and-value-one characterization.",
    "support_subset_primes": "Nonprime-zero hypotheses make the rational support a subset of the prime set.",
    "sum_eq_support_card": "Booleanity makes the rational coordinate sum equal to support cardinality.",
    "g_zero_iff_independent": "Under Booleanity and nonprime zeros, g=0 is equivalent to independent prime support.",
    "characteristic_boolean": "A finite-set characteristic function is Boolean.",
    "support_characteristic": "A prime-supported set is recovered as the support of its characteristic function.",
    "C1": "For natural m, a full D_m pseudo-model exists iff m<=pi(N)-r(N), including loop pairs.",
    "C1_primeCounting": "The same exact D_m threshold is expressed with Mathlib primeCounting.",
    "r_le_pi": "The unordered pair count is at most the prime count.",
    "no_pseudo_solution_at_full_count_iff": "Absence of a full-count pseudo-model is equivalent to a positive unordered representation count.",
    "r_positive_iff": "Positive unordered representation count is equivalent to a prime pair summing to N.",
    "D_true_prime_indicator": "The true prime indicator satisfies D at the full prime count.",
    "D_full_count_pins": "Every full-count D model agrees with the prime indicator within the horizon.",
    "representatives_subset_maximumSupport_insert": "All pair representatives lie in the maximum support plus the possible midpoint.",
    "pair_count_le_independence_plus_one": "The representation count is at most the independence count plus one.",
    "independence_ge_half_prime_count": "The independence count is at least half the prime count, with natural rounding.",
    "independence_unbounded_on_even": "The independence count is unbounded along even N>=4.",
    "Dpi_standard_degree_unbounded_on_even": "Necessary count-summand degree for supplied full-count certificates is unbounded along even N>=4.",
    "degree_le": "Every genuine bounded-PC derivation line obeys its declared ordinary degree bound.",
    "scalar": "A scalar multiple is derived by the genuine binary linear rule under its explicit degree guard.",
    "polynomial_nonprime": "The actual nonprime generator restricts to zero.",
    "polynomial_boolean": "A Boolean generator restricts to a remaining-variable Boolean generator or zero.",
    "polynomial_g_zero": "The original ordered g restricts to the zero polynomial.",
    "restrictedVariable_sum": "The original-variable sum restricts to the remaining-variable sum.",
    "polynomial_count": "The full-count generator restricts to the actual Boolean-knapsack count generator.",
    "generator_image": "Every actual D_pi generator restricts to zero or a genuine knapsack generator.",
    "derivation_restriction": "Genuine input, binary linear, and single-variable PC derivations restrict without increased ordinary degree.",
    "dpi_refutation_restricts": "A supplied D_pi refutation yields a same-degree genuine knapsack refutation.",
    "dpi_degree_lower_bound_conditional": "Conditional corollary retaining explicit KnapsackLowerBound, alpha>=1 and supplied-refutation premises; see Appendix B.",
    "toggle_involutive": "Toggling one support coordinate twice is the identity.",
    "up_eq_sum": "The actual raising operator is the sum of coordinate raising actions.",
    "down_eq_sum": "The actual lowering operator is the sum of coordinate lowering actions.",
    "raiseAt_sum": "Coordinate raising commutes with finite rational function sums.",
    "lowerAt_sum": "Coordinate lowering commutes with finite rational function sums.",
    "coordinate_adjoint": "Coordinate raising and lowering are adjoint for the declared finite rational pairing.",
    "coordinate_commute": "Distinct-coordinate lowering and raising commute.",
    "coordinate_diagonal": "The same-coordinate commutator is the declared signed diagonal action.",
    "adjoint": "The actual total raising and lowering actions are adjoint.",
    "commutator": "The actual commutator acts by variable count minus twice support size.",
    "up_injective_below_middle": "On a pure k layer with strict 2k<card sigma, a zero raising image forces the signed function to vanish.",
    "support_single_one_add": "Adding a positive single-coordinate exponent inserts that coordinate into the exponent support.",
    "coefficientAtom_single_one_add": "The actual support atom obeys the variable-action identity.",
    "coefficients_monomial": "Ordinary monomial coefficients map to the corresponding scaled support atom.",
    "coefficients_X_mul": "Genuine ordinary variable multiplication maps to the actual finite-support bit action.",
    "support_card_le_exponent_sum": "Finite exponent-support cardinality is at most the total exponent sum.",
    "coefficients_eq_zero_of_totalDegree_lt_card": "Aggregated coefficients vanish when support size exceeds ordinary polynomial degree.",
    "countMul_eq_diagonal_add_up": "The actual count multiplier equals its signed diagonal action plus raising.",
    "top_layer_vanishes_of_countMul_degree_le": "With strict 2k<card sigma, function and count image zero above k force the function zero at and above k.",
    "coefficients_count_mul": "The genuine ordinary count-polynomial multiple maps to the actual count multiplier.",
    "coefficients_boolean_mul": "An ordinary Boolean-generator multiple has zero support-coefficient image, including infinite variable types.",
    "bitMul_countMul": "On finite types the actual bit and count actions commute for arbitrary rational parameter and signed functions.",
}

DEFINITION_DESCRIPTIONS = {
    "R": "Ordinary multivariate polynomial ring on the declared bounded coordinate type.",
    "g": "The declared full ordered complementary-coordinate polynomial or its explicitly separate calibration evaluation.",
    "Certificate": "A supplied ordinary identity with family, Boolean and ordered-g summands.",
    "primePoint": "The genuine prime-indicator point on the bounded coordinate type.",
    "goldbachCount": "The original ordered prime-indicator pair count, with a midpoint loop.",
    "KnapsackLowerBound": "An explicit unproved lower-bound predicate retained as a hypothesis; no new axiom is installed.",
    "Derives": "Genuine bounded ordinary-Q PC using input, binary linear combination and one-variable multiplication.",
    "Refutation": "A genuine derivation of the unit under the declared degree bound.",
    "dpiGenerators": "Actual full-count, SIEVE, Boolean and original ordered-g generators.",
    "knapsackCount": "The ordinary all-one-coefficient Boolean-knapsack count polynomial.",
    "knapsackGenerators": "Actual Boolean generators and the ordinary knapsack count polynomial.",
    "coefficients": "Linear aggregation of genuine ordinary exponent coefficients by their finite supports.",
    "coefficientAtom": "The finite-support atom associated to an ordinary exponent vector.",
    "bitMul": "The actual finite-support action representing genuine variable multiplication.",
    "countMul": "The actual signed count action, with rational subtraction outside the finite sum.",
    "up": "Actual Boolean-lattice raising action on signed rational support functions.",
    "down": "Actual Boolean-lattice lowering action on signed rational support functions.",
    "arithmeticIndexFintype": "The separately printed finite-index instance used by the actual k-ary N=4 family.",
}

def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()

def portable(data: bytes, path: str) -> None:
    text = data.decode("utf-8")
    if FORBIDDEN.search(text):
        raise ValueError("Nonportable or email-bearing artifact cannot be copied: " + path)
    if len(data) > 2_000_000:
        raise ValueError("Artifact is outside the small-copy publication scope: " + path)

def dump(path: Path, value) -> None:
    data = (json.dumps(value, indent=2, ensure_ascii=False) + "\n").encode("utf-8")
    portable(data, path.name)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(data)

def initialize_sources(origin: Path) -> None:
    references = {}
    def take(relative: str, commit: str, *, live=False):
        if live:
            data = (origin / relative).read_bytes()
        else:
            data = subprocess.check_output(["git", "-c", "safe.directory=" + origin.as_posix(),
                                           "-C", str(origin), "show", commit + ":" + relative])
        portable(data, relative)
        destination = SOURCES / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(data)
        references[relative] = {"path": "paper/algebraic_sources/" + relative,
                                "source_collection": COLLECTION,
                                "source_path": relative, "source_commit": commit, "commit": commit,
                                "original_collection": COLLECTION, "original_commit": commit,
                                "sha256": digest(data), "bytes": len(data),
                                "copy": "exact existing bytes" if live else "exact immutable Git artifact bytes"}
        return data
    coverage = json.loads(take("judge/axiom_coverage_audit_e5c4e11.json", ACCEPTANCE))
    for module in coverage["imported_project_modules"]:
        take(module.replace(".", "/") + ".lean", PROOF)
    for relative in ["AXIOMS.md", "audit/Axioms.lean", "lakefile.lean", "lean-toolchain",
                     "Target/Goldbach.lean", "TARGET.sha256", "evidence/degrees.csv",
                     "evidence/pc_curve.csv", "evidence/pc_rational_curve.csv",
                     "evidence/pc_heap/verified_increment_curve.csv",
                     "evidence/pc_heap/verified_increment_36_curve.csv",
                     "evidence/lower_bound_checks.json", "evidence/rational_curve_comparison.json",
                     "evidence/gates.json", "results/full_bertrand_gate.json",
                     "results/bertrand_model_counts.json", "results/proper_bertrand_gate.json",
                     "evidence/factor_coverage_gate.json", "evidence/coprime_density/gates.json",
                     "evidence/UPPER_LOOP_BLOCKED.md", "evidence/UPPER_NO_LOOP.md", "FAMILY_TABLE.md"]:
        take(relative, PROOF)
    for relative in ["TROPHY_RESULTS.json", "TROPHY_L1_L5.json",
                     "judge/count_variable_commutation_complete_header_audit_e5c4e11.json"]:
        take(relative, ACCEPTANCE)
    for relative, commit in [
        ("judge/boolean_lattice_complete_header_audit_4f8724d.json", "a51973ba44f84221a3d139d6288faad5a83f95a6"),
        ("judge/boolean_coefficients_complete_header_audit_d9a7e29.json", "46b43e426f66d8ac5c238c93548bc88958d3937c"),
        ("judge/boolean_multiplier_rigidity_complete_header_audit_00616e7.json", "6d1d9fbad18fd6b6dead4c1d3bade25241169f55"),
        ("audit/post_commit_integrity_e5c4e11.json", ROOT_ACCEPTANCE),
        ("audit/FIRST_GLOBAL_GATE_ROOT_A6_SAVED_DATA_REVIEW.json", GATE_RECEIPT),
        ("scripts/first_global_gate.py", GATE_DATA)]:
        take(relative, commit)
    headers = json.loads((SOURCES / "judge/count_variable_commutation_complete_header_audit_e5c4e11.json").read_text(encoding="utf-8"))
    for relative in headers["frozen_hashes"]:
        if relative.endswith(".md"):
            take(relative, PROOF)
    report = take("judge/first_global_gate_d8b4219_audit.json", GATE_DATA, live=True)
    receipt = json.loads((SOURCES / "audit/FIRST_GLOBAL_GATE_ROOT_A6_SAVED_DATA_REVIEW.json").read_text(encoding="utf-8"))
    if digest(report) != receipt["audit_binding"]["sha256"]:
        raise ValueError("Existing saved-data report is not the artifact identified by the existing root receipt")
    references["judge/first_global_gate_d8b4219_audit.json"].update({
        "artifact_commit": None,
        "source_commit_meaning": "audited data pin; report was not committed or Trophy-promoted before stop",
        "existing_receipt_commit": GATE_RECEIPT,
        "credit_level": "EVIDENCE"})
    # The original audit contains a local clone path. Only portable selected fields
    # are transcribed; its original artifact hash and commit remain explicit.
    original = subprocess.check_output(["git", "-c", "safe.directory=" + origin.as_posix(),
                                        "-C", str(origin), "show", ACCEPTANCE + ":judge/lean_audit_e5c4e11.json"])
    audit = json.loads(original)
    excerpt_name = "judge/lean_audit_e5c4e11_portable_excerpt.json"
    excerpt = {"transcription": "Selected existing audit fields; local clone path and unrelated inventory omitted, no fresh verification",
               "original_artifact": {"source_collection": COLLECTION, "path": "judge/lean_audit_e5c4e11.json",
                                     "source_commit": ACCEPTANCE, "sha256": digest(original)},
               **{k: audit[k] for k in ["role", "source_commit", "project_build_artifacts_inherited", "build",
                                       "pinned_lake_version", "frozen_target_sha256", "axioms_independently_reprinted", "scope"]}}
    dump(SOURCES / excerpt_name, excerpt)
    data = (SOURCES / excerpt_name).read_bytes()
    references[excerpt_name] = {"path": "paper/algebraic_sources/" + excerpt_name, "source_collection": COLLECTION,
                               "source_path": "judge/lean_audit_e5c4e11.json", "source_commit": ACCEPTANCE, "commit": ACCEPTANCE,
                               "original_collection": COLLECTION, "original_commit": ACCEPTANCE,
                               "sha256": digest(data), "original_sha256": digest(original), "bytes": len(data),
                               "copy": "labeled portable transcription of selected existing fields"}
    figure = (origin / "output/pdf/degree_curve.pdf").read_bytes()
    expected_figure = "613fb6898ed3dfd1226e7c07c345c297fab46c24e515dc0487962e6587aa816b"
    if digest(figure) != expected_figure:
        raise ValueError("Existing figure differs from the publication's cited original figure hash")
    (PAPER / "figures").mkdir(exist_ok=True)
    (PAPER / "figures/degree_curve.pdf").write_bytes(figure)
    references["output/pdf/degree_curve.pdf"] = {
        "path": "paper/figures/degree_curve.pdf", "commit": PROOF,
        "source_collection": COLLECTION, "original_collection": COLLECTION,
        "source_path": "output/pdf/degree_curve.pdf", "original_commit": PROOF,
        "source_commit_meaning": "accepted data snapshot; source figure has separately recorded existing hash",
        "sha256": digest(figure), "bytes": len(figure), "copy": "exact existing binary figure bytes"}
    dump(SOURCES / "sources.json", references)

def load(relative: str):
    return json.loads((SOURCES / relative).read_text(encoding="utf-8"))

def csv_rows(relative: str):
    return list(csv.DictReader(io.StringIO((SOURCES / relative).read_text(encoding="utf-8"))))

def strip_comments(text: str) -> str:
    chars = list(text); i = 0; depth = 0; quoted = False
    while i < len(text):
        if depth:
            if text.startswith("/-", i): depth += 1; chars[i:i+2] = "  "; i += 2; continue
            if text.startswith("-/", i): depth -= 1; chars[i:i+2] = "  "; i += 2; continue
            if text[i] != "\n": chars[i] = " "
            i += 1; continue
        if text[i] == '"' and (i == 0 or text[i-1] != "\\"): quoted = not quoted
        if not quoted and text.startswith("/-", i): depth = 1; chars[i:i+2] = "  "; i += 2; continue
        if not quoted and text.startswith("--", i):
            j = text.find("\n", i); j = len(text) if j < 0 else j
            chars[i:j] = " " * (j-i); i = j; continue
        i += 1
    return "".join(chars)

DECLARATION = re.compile(r"^(?:@\[[^\n]*?\]\s*)*(?:(private|protected)\s+)?(?:noncomputable\s+)?"
                         r"(theorem|lemma|def|abbrev|inductive|structure|instance)\s+([A-Za-z_][A-Za-z0-9_'.]*)")

def header_before_body(block: str) -> str:
    stack = []; pairs = {"(": ")", "[": "]", "{": "}"}; quoted = False; i = 0
    while i < len(block):
        char = block[i]
        if char == '"' and (i == 0 or block[i-1] != "\\"): quoted = not quoted
        if not quoted:
            if not stack and (block.startswith(":=", i) or re.match(r"\bwhere\b", block[i:])):
                return block[:i].strip()
            if not stack and char == "\n" and re.match(r"\n\s*\|", block[i:]):
                return block[:i].strip()
            if char in pairs: stack.append(pairs[char])
            elif stack and char == stack[-1]: stack.pop()
        i += 1
    return block.strip()

def declarations(module: str, text: str):
    clean = strip_comments(text); lines = clean.splitlines(keepends=True)
    scopes = []; records = []; positions = []; pos = 0
    for line in lines: positions.append(pos); pos += len(line)
    starts = []
    for number, line in enumerate(lines):
        namespace = re.match(r"^namespace\s+([A-Za-z0-9_'.]+)", line)
        section = re.match(r"^(?:noncomputable\s+)?section(?:\s+([A-Za-z0-9_']+))?\s*$", line)
        end = re.match(r"^end(?:\s+([A-Za-z0-9_'.]+))?\s*$", line)
        if namespace: scopes.append(("namespace", namespace.group(1))); continue
        if section: scopes.append(("section", section.group(1) or "")); continue
        if end:
            if scopes: scopes.pop()
            continue
        match = DECLARATION.match(line)
        if match:
            if match.group(1) == "private": continue
            kind, name = match.group(2), match.group(3)
            # Unnamed instance headers begin with a binder and do not match.
            prefix = ".".join(s[1] for s in scopes if s[0] == "namespace")
            full = prefix + "." + name if prefix else name
            starts.append((number, positions[number], kind, name, full))
    for index, (number, start, kind, name, full) in enumerate(starts):
        stop = starts[index+1][1] if index+1 < len(starts) else len(clean)
        header = header_before_body(clean[start:stop])
        records.append({"module": module, "name": full, "short_name": name,
                        "declaration_kind": kind, "source_line": number+1,
                        "source_header": " ".join(header.split())})
    return records

def axiom_dictionary_walk(value, found):
    if isinstance(value, dict):
        for key, item in value.items():
            if key.startswith("AlgebraicGoldbach.") and isinstance(item, list) and set(item) <= ALLOWED_AXIOMS:
                found[key] = item
            else: axiom_dictionary_walk(item, found)
    elif isinstance(value, list):
        for item in value: axiom_dictionary_walk(item, found)

def humanize(name: str) -> str:
    text = re.sub(r"([a-z])([A-Z])", r"\1 \2", name.replace("_", " "))
    return text.strip()

def inventory(source_refs):
    coverage = load("judge/axiom_coverage_audit_e5c4e11.json")
    audited = load("judge/lean_audit_e5c4e11_portable_excerpt.json")["axioms_independently_reprinted"]
    printed = dict(audited)
    for path in ["TROPHY_L1_L5.json", "TROPHY_RESULTS.json",
                 "judge/boolean_lattice_complete_header_audit_4f8724d.json",
                 "judge/boolean_coefficients_complete_header_audit_d9a7e29.json",
                 "judge/boolean_multiplier_rigidity_complete_header_audit_00616e7.json"]:
        axiom_dictionary_walk(load(path), printed)
    rows = []
    for module in coverage["imported_project_modules"]:
        path = module.replace(".", "/") + ".lean"
        for row in declarations(module, (SOURCES / path).read_text(encoding="utf-8")):
            name, short, kind = row["name"], row["short_name"], row["declaration_kind"]
            leaf = short.split(".")[-1]
            is_result = kind in ("theorem", "lemma")
            if is_result and name not in audited:
                raise ValueError("Publication parser found a result not in the existing accepted axiom list: " + name)
            if is_result and leaf not in SHORT_STATEMENTS:
                raise ValueError("Missing reviewed informal statement: " + name)
            description = SHORT_STATEMENTS[leaf] if is_result else DEFINITION_DESCRIPTIONS.get(leaf, "Defines " + humanize(short) + " in the declared module context; exact source is authoritative.")
            conditional = leaf in ("dpi_degree_lower_bound_conditional", "KnapsackLowerBound")
            row.update({"informal_statement": description,
                        "source_path": source_refs[path]["path"], "source_sha256": source_refs[path]["sha256"],
                        "source_collection": COLLECTION, "original_source_path": path,
                        "proof_commit": PROOF, "accepted_judge_batch": ACCEPTANCE,
                        "axioms_used": sorted(printed[name]) if name in printed else None,
                        "axiom_observation": "Existing separately reprinted entry" if name in printed else "Not separately reprinted in selected existing artifacts; no zero-axiom claim",
                        "credit_level": "Compiled Lean (conditional; Appendix B)" if conditional else "Compiled Lean" if is_result else "Compiled Lean definition/type",
                        "external_hypothesis_retained": conditional,
                        "claim_id": "ALG-LEAN-" + name})
            rows.append(row)
    result_names = {r["name"] for r in rows if r["declaration_kind"] in ("theorem", "lemma")}
    if result_names != set(audited):
        raise ValueError("Existing axiom-list entries missing from source extraction: " + ", ".join(sorted(set(audited)-result_names)))
    # These three constructor names are separately present in an existing accepted
    # axiom record; record them without pretending they are new theorem results.
    pc_source = source_refs["Calibration/PCRestriction.lean"]
    for ctor in ("input", "linear", "mulVar"):
        name = "AlgebraicGoldbach.PCRestriction.Derives." + ctor
        rows.append({"module": "Calibration.PCRestriction", "name": name, "short_name": "Derives."+ctor,
                     "declaration_kind": "constructor", "source_line": {"input":20,"linear":21,"mulVar":24}[ctor],
                     "source_header": "Existing source inductive constructor; see the copied Derives declaration.",
                     "informal_statement": {"input":"Input rule with membership and ordinary degree guard.",
                                             "linear":"Binary rational linear-combination rule with ordinary degree guard.",
                                             "mulVar":"Single genuine variable-multiplication rule with ordinary degree guard."}[ctor],
                     "source_path": pc_source["path"], "source_sha256": pc_source["sha256"],
                     "source_collection": COLLECTION, "original_source_path": "Calibration/PCRestriction.lean",
                     "proof_commit": PROOF, "accepted_judge_batch": ACCEPTANCE,
                     "axioms_used": sorted(printed[name]), "axiom_observation":"Existing separately reprinted constructor entry",
                     "credit_level":"Compiled Lean constructor", "external_hypothesis_retained":False,
                     "claim_id":"ALG-LEAN-"+name})
    return rows, coverage

def degree_data():
    ns = {int(r["N"]): r for r in csv_rows("evidence/degrees.csv")}
    lower = {int(r["N"]): r for r in load("evidence/lower_bound_checks.json")["rows"]}
    rational = {int(r["N"]): r for r in load("evidence/rational_curve_comparison.json")["rows"]}
    fp = {int(r["N"]): int(r["minimal_standard_PC_degree_Fp"]) for r in csv_rows("evidence/pc_curve.csv")}
    fp_sources = {n:"evidence/pc_curve.csv" for n in fp}
    for path in ("evidence/pc_heap/verified_increment_curve.csv", "evidence/pc_heap/verified_increment_36_curve.csv"):
        for row in csv_rows(path):
            n = int(row["N"]); fp[n] = int(row["minimal_standard_PC_degree_Fp"]); fp_sources[n] = path
    q = {int(r["N"]):int(r["minimal_standard_PC_degree_Q"]) for r in csv_rows("evidence/pc_rational_curve.csv")}
    rows = []
    for n, row in sorted(ns.items()):
        l, rat = lower[n], rational[n]
        rows.append({"N":n, "pi_N":int(row["pi_N"]), "unordered_pairs_including_loop_r":l["unordered_pairs_including_loop_r"],
                     "alpha":l["alpha"], "NS_minimum_Fp":int(row["minimal_standard_total_degree_Fp"]),
                     "NS_minimum_Q":rat["rational_upper_degree"], "PC_minimum_Fp":fp.get(n), "PC_minimum_Q":q.get(n),
                     "PC_Fp_source":fp_sources.get(n), "level":"EVIDENCE (existing exact finite arithmetic; not a Lean computation)",
                     "claim_id":"ALG-DEGREE-N"+str(n)})
    grouping = collections.defaultdict(list)
    for row in rows:
        if row["PC_minimum_Fp"] is not None: grouping[row["alpha"]].append({"N":row["N"],"degree":row["PC_minimum_Fp"]})
    groups = [{"alpha":a, "N":[r["N"] for r in group], "PC_degrees":sorted({r["degree"] for r in group})}
              for a, group in sorted(grouping.items())]
    consistent = all(len(group["PC_degrees"]) == 1 for group in groups)
    return rows, {"scope":"Existing fourteen finite-field points only; repeated alpha groups, not a universal functional-dependence or degree formula",
                  "same_alpha_same_PC_degree_in_saved_points":consistent, "groups":groups,
                  "formula_not_claimed":"A generic closed formula is not inferred from these data; the external KnapsackLowerBound remains explicit."}

FAMILY_NAMES = [
    ("COARSE_PARITY","Coarse parity","No additional prime-coordinate pin",32768),
    ("SIEVE_ONLY","SIEVE only","Nonprime zeros; no prime-coordinate pin",1024),
    ("SIEVE_DYADIC_BERTRAND","SIEVE + dyadic intervals","Direct X2-1 pin",144),
    ("BERTRAND_COARSE","Full Bertrand coarse","m=1 interval pins X2",2605),
    ("FULL_BERTRAND_SIEVE","Full Bertrand SIEVE","m=1 interval pins X2",40),
    ("FACTOR_COVERAGE_BERTRAND_SIEVE","Bertrand SIEVE + factors","m=1 X2 pin; small-prime factor pins",None),
    ("PROPER_BERTRAND_ONLY","Proper Bertrand only, m>=2","Every coordinate free in Lean",1360168984),
]

def family_data():
    saved = load("judge/first_global_gate_d8b4219_audit.json")["valid_saved_data_replay"]
    first = saved["first_even_pseudo_solution_N"]
    rows = []
    for key, label, pin, models in FAMILY_NAMES:
        rows.append({"family":key,"label":label,"mandatory_quartet_N":[30,60,100,200],
                     "pseudo_models_at_all_mandatory_quartet_N":True,"first_failure_among_quartet":30,
                     "first_even_pseudo_solution_N_at_least_4":first[key],
                     "first_even_status":"EVIDENCE: existing saved-data audit PASS and root serialized review; no new scoped Judge/Trophy credit",
                     "coordinate_pinning":pin,"Boolean_models_without_g_at_N30":models,
                     "Boolean_models_without_g_at_N30_lower_bound":2,"uniform_constants":True,
                     "status":"Rejected at all mandatory quartet cases; no viable L6 family",
                     "claim_id":"ALG-FAMILY-"+key})
    return rows

def tex_escape(text):
    table={"\\":r"\textbackslash{}","&":r"\&","%":r"\%","$":r"\$","#":r"\#","_":r"\_","{":r"\{","}":r"\}","~":r"\textasciitilde{}","^":r"\textasciicircum{}"}
    return "".join(table.get(char,char) for char in str(text))

def tex_name(text):
    displayed = re.sub(r"([a-z0-9])([A-Z])", r"\1\\allowbreak \2", tex_escape(text))
    return r"\texttt{" + displayed.replace(r"\_",r"\_\allowbreak ").replace(".",r".\allowbreak ") + "}"

REPRESENTATIVE_NAMES = {
    "AlgebraicGoldbach.Soundness": ["certificate_excludes_common_zero", "certificate_implies_goldbach", "finiteFieldPolicy_g_nonzero_iff"],
    "AlgebraicGoldbach.UniformCountermodel": ["bit_boolean", "uniform_bertrand_countermodel"],
    "AlgebraicGoldbach.UniformNonpinning": ["uniform_model_selects_composite_nine"],
    "AlgebraicGoldbach.BertrandFamily": ["bertrandFamily_no_certificate"],
    "AlgebraicGoldbach.PinnedControl": ["pinned_certificate_iff_goldbach", "pinned_multiplier_degree_le_one", "pinned_summand_degree_le_two"],
    "AlgebraicGoldbach.FactorCoverage": ["coverage_iff_primePins", "horizonFamily_no_certificate"],
    "AlgebraicGoldbach.ProperBertrand": ["family_does_not_pin_any_coordinate", "family_no_certificate"],
    "AlgebraicGoldbach.SignDefinite": ["sign_definite_strengthening_has_no_certificate"],
    "AlgebraicGoldbach.CoprimeDivisor": ["family_iff_at_most_one_omitted_prime", "family_does_not_pin_any_coordinate"],
    "AlgebraicGoldbach.CoprimeKaryIdeal": ["arithmeticIdeal_eq_primeIdeal"],
    "AlgebraicGoldbach.CoprimeKaryModels": ["family_iff_omitted_card_lt"],
    "AlgebraicGoldbach.CoprimeKaryCountermodel": ["family_no_certificate_at_four"],
    "AlgebraicGoldbach.LiteralCube": ["weighted_common_zero"],
    "AlgebraicGoldbach.LowerBound.BooleanLattice": ["adjoint", "commutator", "up_injective_below_middle"],
    "AlgebraicGoldbach.LowerBound.BooleanCoefficients": ["coefficients_X_mul"],
    "AlgebraicGoldbach.LowerBound.BooleanCoefficientDegree": ["coefficients_eq_zero_of_totalDegree_lt_card"],
    "AlgebraicGoldbach.LowerBound.BooleanMultiplierRigidity": ["top_layer_vanishes_of_countMul_degree_le"],
    "AlgebraicGoldbach.LowerBound.BooleanCountBridge": ["coefficients_count_mul"],
    "AlgebraicGoldbach.LowerBound.BooleanAnnihilation": ["coefficients_boolean_mul"],
    "AlgebraicGoldbach.LowerBound.CountVariableCommutation": ["bitMul_countMul"],
    "Calibration.C1": ["C1", "D_full_count_pins"],
    "Calibration.LowerBound": ["Dpi_multiplier_degree_lower_bound", "Dpi_standard_degree_lower_bound"],
    "Calibration.Growth": ["Dpi_standard_degree_unbounded_on_even"],
    "Calibration.PCRestriction": ["dpi_refutation_restricts"],
}

def representative_rows(rows):
    selected=[]
    for module, names in REPRESENTATIVE_NAMES.items():
        for name in names:
            matches=[r for r in rows if r["module"] == module and r["short_name"] == name]
            assert len(matches)==1, (module,name)
            selected.append({**matches[0], "representative_claim_id":"ALG-REP-%02d" % (len(selected)+1)})
    return selected

def obstruction_catalogue():
    return [
        {"class":"Pinned/full-count calibration", "result":"Exclusion is equivalent to a positive prime representation count; full count pins the prime vector.", "scope":"Declared calibration, not a weaker candidate family.", "level":"Compiled Lean", "claim_id":"ALG-C0-C1"},
        {"class":"Seven finite family gates", "result":"Every original family has a pseudo-model at every mandatory quartet input.", "scope":"N=30,60,100,200; last first-even data are EVIDENCE only.", "level":"Existing finite evidence", "claim_id":"ALG-NO-ELIGIBLE-FAMILY"},
        {"class":"Coarse/full and proper Bertrand", "result":"Actual rational Boolean/g common zeros forbid a supplied identity.", "scope":"N>=24; the coarse model is not asserted to satisfy SIEVE.", "level":"Compiled Lean", "claim_id":"ALG-UNIFORM-BERTRAND"},
        {"class":"Proper-divisor coverage", "result":"Coverage is exactly small-prime coordinate pinning; a smaller horizon preserves the coarse common zero.", "scope":"M<=N^2 for equivalence; N>=24 and M<=(floor(N/2)-3)^2 for the common zero.", "level":"Compiled Lean", "claim_id":"ALG-FACTOR-HORIZON"},
        {"class":"Same-sign canonical coefficients", "result":"Such true equations preserve a supplied prime-supported common zero.", "scope":"Ordinary rational coefficients all nonnegative or all nonpositive; prime truth and supplied sieve common zero required.", "level":"Compiled Lean", "claim_id":"ALG-SIGN-DEFINITE"},
        {"class":"Coprime-divisor density", "result":"The exact family is near-full prime selection, so finite quartet UNSAT does not qualify a weaker candidate.", "scope":"Actual rational family; at most one prime coordinate differs from one.", "level":"Compiled Lean / finite evidence", "claim_id":"ALG-COPRIME-GATE"},
        {"class":"k-ary coprime arithmetic ideal", "result":"Actual arithmetic and prime-subset ideals coincide; N=4 supplies a Boolean/g common zero.", "scope":"Arbitrary rational model classification; k>=2 at N=4.", "level":"Compiled Lean", "claim_id":"ALG-KARY-CLASSIFICATION"},
        {"class":"Literal-product cube covering", "result":"A strict exact total clause-weight bound leaves a common zero.", "scope":"Even N>=6, actual finite cube cardinality; no substituted floor formula.", "level":"Compiled Lean", "claim_id":"ALG-LITERAL-CUBE"},
        {"class":"Static NS degree", "result":"Every supplied ordinary-Q full-count identity has count-summand degree at least pi-r+1, unbounded along even N.", "scope":"A universal necessary lower bound; finite equality does not provide a universal upper construction.", "level":"Compiled Lean", "claim_id":"ALG-NS-LOWER"},
        {"class":"Ordinary polynomial calculus", "result":"A compiled degree-preserving restriction retains an external lower-bound predicate.", "scope":"The lower corollary is conditional; coefficient/lattice lemmas do not discharge it.", "level":"Compiled restriction / conditional corollary", "claim_id":"ALG-PC-HYPOTHESIS"},
    ]

def write_text(path, value):
    data = value.encode("utf-8"); portable(data, path.name); path.write_bytes(data)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-root",type=Path,help="Read-only existing source collection; omit to use copied publication inputs")
    args = parser.parse_args()
    if args.source_root is not None: initialize_sources(args.source_root)
    refs = load("sources.json")
    rows, coverage = inventory(refs)
    degrees, dependence = degree_data(); families = family_data()
    inv = {"schema":1,"collection":COLLECTION,"author":"Durand Serge","accepted_proof_snapshot":PROOF,
           "existing_judge_batch":ACCEPTANCE,"existing_root_acceptance":ROOT_ACCEPTANCE,
           "scope":"Inventory derived from existing source and accepted saved axiom artifacts; no new build or verification",
           "allowed_standard_axioms":sorted(ALLOWED_AXIOMS),"audited_result_count":len(coverage["public_theorems_and_lemmas_independently_enumerated"]),
           "frozen_header_count":204,"imported_module_count":len(coverage["imported_project_modules"]),
           "declaration_row_count":len(rows),"modules":MODULE_SUMMARIES,"declarations":rows,
           "degree_data":degrees,"PC_alpha_grouping":dependence,"families":families,
           "obstruction_catalogue":obstruction_catalogue(),
           "limitations":["Single-vendor agent Judge; no external validation implied.",
                          "Source headers may use surrounding section binders; the copied complete source is authoritative.",
                          "Not separately printed definition axioms are unknown, not asserted empty.",
                          "The frozen proofless target is excluded from the auxiliary build.",
                          "No universal NS upper construction or unconditional generic PC lower theorem follows.",
                          "The last global-first saved-data result was not Trophy-promoted before the stop instruction."]}
    dump(PAPER/"algebraic_inventory.json",inv)
    fields=["module","name","declaration_kind","informal_statement","axioms_used","credit_level","proof_commit",
            "source_path","source_sha256","source_line","source_header","external_hypothesis_retained","claim_id"]
    csv_stream=io.StringIO(newline=""); writer=csv.DictWriter(csv_stream,fieldnames=fields,lineterminator="\n")
    writer.writeheader()
    for row in rows:
        record={k:row[k] for k in fields}; record["axioms_used"]="NOT SEPARATELY REPRINTED" if row["axioms_used"] is None else ";".join(row["axioms_used"])
        writer.writerow(record)
    write_text(PAPER/"algebraic_lean_inventory.csv",csv_stream.getvalue())
    claims=[]
    def add(cid, statement, level, paths, **extra):
        if not isinstance(statement,str):
            extra={"details":statement,**extra}
            statement=extra.pop("statement_text",json.dumps(statement,ensure_ascii=False,sort_keys=True))
        claims.append({"id":cid,"statement":statement,"status":level,"evidence":[refs[p] for p in paths],**extra})
    for row in rows:
        add(row["claim_id"],row["informal_statement"],row["credit_level"],
            [row["original_source_path"],"judge/axiom_coverage_audit_e5c4e11.json","judge/lean_audit_e5c4e11_portable_excerpt.json"],
            theorem_or_declaration_name=row["name"],source_line=row["source_line"],axioms=row["axioms_used"],
            exact_source_header=row["source_header"],proof_commit=PROOF,external_hypothesis_retained=row["external_hypothesis_retained"])
    add("ALG-INVENTORY-SCOPE",{"axiom_manifest_entries":len(coverage["public_theorems_and_lemmas_independently_enumerated"]),"complete_frozen_headers":204,"imported_modules":25},
        "Existing Compiled Lean audit scope",["judge/axiom_coverage_audit_e5c4e11.json","judge/count_variable_commutation_complete_header_audit_e5c4e11.json","AXIOMS.md"],
        statement_text="The existing accepted audit enumerates 233 actual public theorem/lemma names, 204 frozen complete headers and 25 imported modules. The electronic inventory has 356 rows: those 233 results, 120 other named declarations and 3 constructors.")
    add("ALG-SETUP", "Ordinary variables X0..XN, Boolean equations, actual ordered g with midpoint loop and a supplied identity; certificate soundness does not supply an identity.",
        "Compiled Lean",["AlgebraicGoldbach/Soundness.lean"])
    add("ALG-FROZEN-TARGET", "The supplied frozen target contains an unfinished theorem declaration, is excluded from the auxiliary import/build, and cannot receive a proof without changing its frozen bytes.",
        "SOURCE/design limitation",["Target/Goldbach.lean","TARGET.sha256","AlgebraicGoldbach.lean","lakefile.lean","TROPHY_L1_L5.json"])
    add("ALG-C0-C1", "Pinned control is circular; for natural m the exact full D_m pseudo-model threshold is m<=pi-r, including loops. Full count pins the prime vector.",
        "Compiled Lean",["AlgebraicGoldbach/PinnedControl.lean","Calibration/C1.lean"])
    add("ALG-NS-LOWER", "For every supplied actual ordinary-Q D_pi certificate the count-multiplier degree is >=pi-r and its count-summand degree is >=pi-r+1; necessary degree is unbounded along even N.",
        "Compiled Lean",["Calibration/LowerBound.lean","Calibration/Growth.lean"])
    add("ALG-NS-UPPER-LIMIT", "Universal loop upper construction remains BLOCKED; the no-loop construction is PAPER, not a compiled universal upper theorem.",
        "Existing PAPER/status",["evidence/UPPER_LOOP_BLOCKED.md","evidence/UPPER_NO_LOOP.md"])
    add("ALG-PC-HYPOTHESIS", "The genuine ordinary-Q PC restriction is compiled; KnapsackLowerBound remains an explicit external hypothesis and the lower corollary is conditional.",
        "Compiled restriction / conditional corollary out of scope",["Calibration/PCRestriction.lean","TROPHY_RESULTS.json"])
    for row in degrees:
        paths=["evidence/degrees.csv","evidence/lower_bound_checks.json","evidence/rational_curve_comparison.json","TROPHY_RESULTS.json"]
        if row["PC_minimum_Fp"] is not None: paths.append(row["PC_Fp_source"])
        if row["PC_minimum_Q"] is not None: paths.append("evidence/pc_rational_curve.csv")
        add(row["claim_id"],row,row["level"],paths,statement_text="Existing finite degree row at N=%d; exact values and field scopes are retained in details." % row["N"])
    add("ALG-PC-ALPHA-GROUPING",dependence,"EVIDENCE: simple grouping of existing CSV/JSON rows",
        ["evidence/lower_bound_checks.json","evidence/pc_curve.csv","evidence/pc_heap/verified_increment_curve.csv","evidence/pc_heap/verified_increment_36_curve.csv"],
        statement_text="Among the 14 saved finite-field PC points, equal alpha values have equal measured PC degree. This is finite grouping consistency, not a universal dependence theorem.")
    add("ALG-DEGREE-CURVES",{"NS_Q_Fp_points":len(degrees),"NS_domain":"even N10..60","NS_min":min(r["NS_minimum_Q"] for r in degrees),
                              "NS_max":max(r["NS_minimum_Q"] for r in degrees),"PC_Q_points":sum(r["PC_minimum_Q"] is not None for r in degrees),
                              "PC_Fp_points":sum(r["PC_minimum_Fp"] is not None for r in degrees),"field_prime":1000000007},
        "EVIDENCE: existing exact finite measurements",["evidence/degrees.csv","evidence/rational_curve_comparison.json","evidence/pc_curve.csv","evidence/pc_rational_curve.csv","evidence/pc_heap/verified_increment_curve.csv","evidence/pc_heap/verified_increment_36_curve.csv","TROPHY_RESULTS.json"],
        statement_text="There are 26 NS equality points over Q and Fp at even N=10..60, with degrees 3..14; PC has 11 agreeing Q/Fp points at even N=10..30 and only Fp measurements at N=32,34,36, where p=1000000007.")
    add("ALG-DEGREE-FIGURE", "Exact copy of the existing degree plot; NS and PC have different measured domains, with the N32/34/36 PC points explicitly finite-field-only.",
        "EVIDENCE/existing figure",["output/pdf/degree_curve.pdf","evidence/degrees.csv","evidence/pc_curve.csv","evidence/pc_rational_curve.csv","evidence/pc_heap/verified_increment_curve.csv","evidence/pc_heap/verified_increment_36_curve.csv"])
    for row in families:
        add(row["claim_id"],row,"Established quartet evidence; last global-first values EVIDENCE only",
            ["FAMILY_TABLE.md","AlgebraicGoldbach/BertrandFamily.lean","AlgebraicGoldbach/ProperBertrand.lean","AlgebraicGoldbach/FactorCoverage.lean","evidence/gates.json","results/full_bertrand_gate.json","results/bertrand_model_counts.json","results/proper_bertrand_gate.json","evidence/factor_coverage_gate.json","judge/first_global_gate_d8b4219_audit.json","audit/FIRST_GLOBAL_GATE_ROOT_A6_SAVED_DATA_REVIEW.json"],
            statement_text="%s is uniform and has a Boolean pseudo-model at each mandatory quartet input; its first even input >=4 is %d in existing saved data only, without new scoped Judge/Trophy credit. Pinning and the N30 count are retained in details." % (row["family"],row["first_even_pseudo_solution_N_at_least_4"]))
    add("ALG-COORDINATE-GUARDS", "Whole-vector multiplicity does not remove a direct prime-coordinate pin: dyadic X2-1, m=1 interval, and factor small-prime pins are separately flagged.",
        "SOURCE and existing guard review",["scripts/first_global_gate.py","AlgebraicGoldbach/BertrandFamily.lean","AlgebraicGoldbach/FactorCoverage.lean","TROPHY_L1_L5.json"])
    add("ALG-COPRIME-GATE", "Coprime-divisor density control has N=4 Boolean/g common zero and literal quartet UNSAT evidence, but exact near-full counting rejects candidate promotion.",
        "Compiled classification plus existing finite gate evidence",["AlgebraicGoldbach/CoprimeDivisor.lean","AlgebraicGoldbach/CoprimeKaryCountermodel.lean","evidence/coprime_density/gates.json","TROPHY_L1_L5.json"])
    add("ALG-NO-ELIGIBLE-FAMILY", "The seven original families fail the quartet; the density control is rejected; highest candidate rung is L5 for proper Bertrand m>=2, with no eligible L6 or target proof.",
        "Existing Judge status",["TROPHY_L1_L5.json","TROPHY_RESULTS.json"])
    add("ALG-UNIFORM-BERTRAND", "For every N>=24 the actual coarse/Bertrand and proper interval-only rational families have Boolean/g common zeros and hence no supplied certificate; the coarse construction selects composite nine and is not a SIEVE model.",
        "Compiled Lean",["AlgebraicGoldbach/UniformCountermodel.lean","AlgebraicGoldbach/UniformNonpinning.lean","AlgebraicGoldbach/BertrandFamily.lean","AlgebraicGoldbach/ProperBertrand.lean"])
    add("ALG-FACTOR-HORIZON", "Over arbitrary Q points, coverage through M<=N^2 is equivalent to pins Xp=1 for primes p with p^2<=M. For N>=24 and M<=(floor(N/2)-3)^2, the combined coarse/Bertrand family retains its explicit Boolean/g common zero.",
        "Compiled Lean",["AlgebraicGoldbach/FactorCoverage.lean"])
    add("ALG-SIGN-DEFINITE", "An ordinary rational polynomial whose canonical coefficients all have one sign and which vanishes at the prime point also vanishes at every prime-supported point. Such strengthenings preserve every supplied prime-supported Boolean/g common zero of the original family.",
        "Compiled Lean",["AlgebraicGoldbach/SignDefinite.lean"])
    add("ALG-KARY-CLASSIFICATION", "The actual rational k-ary arithmetic divisor ideal equals the prime k-subset ideal, its rational models have fewer than k prime coordinates different from one, and for each k>=2 an N=4 Boolean/g common zero excludes a certificate for this exact class.",
        "Compiled Lean",["AlgebraicGoldbach/CoprimeKaryIdeal.lean","AlgebraicGoldbach/CoprimeKaryModels.lean","AlgebraicGoldbach/CoprimeKaryCountermodel.lean"])
    add("ALG-LITERAL-CUBE", "For even N>=6, a literal-product family on the actual complement-pair Boolean cube has a common zero when its exact total clause weight is strictly less than 2 raised to the actual finite cube-variable cardinality. No closed floor formula is asserted.",
        "Compiled Lean",["AlgebraicGoldbach/LiteralCube.lean"])
    for number,module in enumerate(coverage["imported_project_modules"],1):
        group=[r for r in rows if r["module"]==module]
        add("ALG-MODULE-%02d" % number, MODULE_SUMMARIES[module], "Compiled Lean module inventory",
            [module.replace(".","/")+".lean","judge/axiom_coverage_audit_e5c4e11.json"],
            module=module, theorem_lemma_rows=sum(r["declaration_kind"] in ("theorem","lemma") for r in group),
            other_named_rows=sum(r["declaration_kind"] not in ("theorem","lemma") for r in group),proof_commit=PROOF)
    selected=representative_rows(rows)
    for row in selected:
        add(row["representative_claim_id"],row["informal_statement"],row["credit_level"],
            [row["original_source_path"],"judge/axiom_coverage_audit_e5c4e11.json","judge/lean_audit_e5c4e11_portable_excerpt.json"],
            theorem_or_declaration_name=row["name"],axioms=row["axioms_used"],exact_source_header=row["source_header"],
            source_line=row["source_line"],proof_commit=PROOF,external_hypothesis_retained=row["external_hypothesis_retained"],
            inventory_claim_id=row["claim_id"])
    dump(PAPER/"algebraic_claims.json",{"schema":1,"collection":COLLECTION,"author":"Durand Serge","source_files":refs,"claims":claims})
    write_text(PAPER/"algebraic_tables.tex",algebraic_section(families))
    write_text(PAPER/"degree_section.tex",degree_section(degrees,dependence))
    write_text(PAPER/"algebraic_appendix.tex",appendix(rows,coverage,degrees))
    print(json.dumps({"declaration_rows":len(rows),"existing_audited_results":len(coverage["public_theorems_and_lemmas_independently_enumerated"]),
                      "NS_points":len(degrees),"PC_Fp_points":sum(r["PC_minimum_Fp"] is not None for r in degrees),
                      "same_alpha_same_PC_degree_in_saved_points":dependence["same_alpha_same_PC_degree_in_saved_points"],
                      "claims":len(claims),"research_or_solver_or_Lean_execution":False}))

def algebraic_section(families):
    header=r"""% Generated from existing artifacts; claim identifiers refer to algebraic_claims.json.
\section{Algebraic certificate setting and family obstructions}
\label{sec:algebraic}
We record an auxiliary formalization in the ordinary polynomial ring
$\mathbb Q[X_0,\ldots,X_N]$. Let $a_i$ be the prime indicator and retain
the original ordered polynomial, including a square term at the midpoint,
\[
 g_N(X)=\sum_{i=0}^{N}X_iX_{N-i}.
\]
A supplied certificate has the literal form
\[
 1=\sum_j A_jF_j+\sum_{i=0}^{N}U_i(X_i^2-X_i)+Bg_N.
\]
The compiled soundness theorem excludes a common zero of these actual
generators. Applied to the prime point it still requires both the identity
and genuine prime truth of the supplied family. It constructs neither.
This is a certificate meta-theorem, not a proof of binary Goldbach
\ev{ALG-SETUP}

\subsection{Calibration and circularity}
The pinned control $F_i=X_i-a_i$ has an identity exactly when the ordered
prime count is positive. Its explicit multipliers have degree at most one;
their ordinary multiplier--generator summands have degree at most two.
These are different conventions. For the calibration $D_m$, consisting of
Booleanity, nonprime zeros and total selected count $m\in\mathbb N$, the
compiled C1 equivalence is
\[
 \exists x\;(D_m(x)\ \wedge\ g_N(x)=0)
 \quad\Longleftrightarrow\quad m\leq\pi(N)-r(N),
\]
where $r(N)$ counts unordered prime representations, including a central
loop. At $m=\pi(N)$ the family pins the prime vector. Thus exclusion of
its pseudo-model is equivalent to positive prime representation count;
it supplies a circular calibration control.\ev{ALG-C0-C1}

\subsection{Family evidence and coordinate guards}
Every original family has recorded Boolean pseudo-models at each mandatory
test value $N\in\{30,60,100,200\}$. The first failure \emph{among that quartet}
is therefore $30$. The ``first even'' column below has a different, explicit
scope: even $N\geq4$, with every earlier even case covered by saved finite
data. Its existing saved-data audit passed and its serialized result was
reviewed before consolidation, but no scoped Judge/Trophy promotion was
completed. Those entries are \textsc{Evidence}, not new formal credit.
No statement about smaller or odd $N$ is implied.

\begin{center}
\small\setlength{\tabcolsep}{3pt}
\begin{tabular}{@{}p{.22\linewidth}p{.09\linewidth}p{.07\linewidth}p{.34\linewidth}p{.17\linewidth}@{}}
\toprule
Family & Uniform & First even & Coordinate guard & Models without $g$, $N=30$\\
\midrule
"""
    lines=[]
    for row in families:
        model=r"$\geq2$" if row["Boolean_models_without_g_at_N30"] is None else "$"+str(row["Boolean_models_without_g_at_N30"])+"$"
        lines.append(tex_escape(row["label"]).replace("m>=2",r"$m\geq2$")+r"\ev{"+row["claim_id"]+"} & Yes & $"+str(row["first_even_pseudo_solution_N_at_least_4"])+"$ & "+tex_escape(row["coordinate_pinning"]).replace("X2-1",r"$X_2-1$").replace("X2",r"$X_2$").replace("m=1",r"$m=1$")+" & "+model+r" \\")
    footer=r"""
\bottomrule
\end{tabular}
\end{center}
All seven rows have closed-form constants and more than one Boolean model
without $g$ at the quartet values; the displayed counts concern $N=30$ only.
All seven fail at every quartet value. Whole-vector multiplicity does not
excuse an equation that fixes a prime coordinate. The dyadic family explicitly
contains $X_2-1$; the $m=1$ full Bertrand interval also fixes $X_2$.
Proper-divisor coverage separately fixes small prime coordinates.
The proper interval-only family starts at $m=2$, contains no coarse or SIEVE
equations, and has compiled every-coordinate Boolean freedom. Its existing
candidate credit stops at L5; no eligible family receives L6.
\ev{ALG-COORDINATE-GUARDS}\ev{ALG-NO-ELIGIBLE-FAMILY}

The calibration and the later density control have a different status:
\begin{center}\small
\begin{tabular}{@{}p{.21\linewidth}p{.09\linewidth}p{.20\linewidth}p{.20\linewidth}p{.19\linewidth}@{}}
\toprule
Control & Uniform & Coordinate status & Quartet status & First even $N\geq4$\\
\midrule
$D_{\pi(N)}$\ev{ALG-C0-C1} & No & Pins full prime vector & Exclusion iff $r(N)>0$ & Not a first-input survey\\
Coprime-divisor density\ev{ALG-COPRIME-GATE} & Yes & Each coordinate free, all $N$ & Recorded UNSAT at all four & $4$, Boolean common zero\\
\bottomrule
\end{tabular}
\end{center}
The second control is rejected by its exact near-full-count classification;
its quartet UNSAT records do not promote it to an eligible candidate.

\subsection{Uniform and structural obstructions}
The actual coarse/Bertrand and proper interval-only families have compiled
rational Boolean common zeros with $g_N=0$ for every $N\geq24$.
The coarse construction selects composite $9$; it must not be silently used
as a SIEVE model. Prime-supported finite witnesses are separate.
\ev{ALG-UNIFORM-BERTRAND}
Proper-divisor coverage through $M\leq N^2$ is equivalent, over arbitrary
rational points, to $X_p=1$ for the prime coordinates with $p^2\leq M$.
The combined coarse/Bertrand family retains the explicit common zero under
$N\geq24$ and $M\leq(\lfloor N/2\rfloor-3)^2$.\ev{ALG-FACTOR-HORIZON}
Canonical rational equations whose coefficients all have one sign and which
vanish at the prime point preserve every supplied prime-supported common
zero. This statement does not cover arbitrary mixed-sign equations.
\ev{ALG-SIGN-DEFINITE}

The rational coprime-divisor family is exactly near-full prime selection:
at most one prime coordinate may differ from one. Its literal quartet UNSAT
data do not make it an eligible weaker family.\ev{ALG-COPRIME-GATE}
The actual $k$-ary arithmetic
ideal equals the prime $k$-subset ideal, and its arbitrary rational models
have fewer than $k$ prime coordinates different from one. For every $k\geq2$
the compiled $N=4$ Boolean common zero excludes a certificate for that exact
class. It is not a counterexample to Goldbach.\ev{ALG-KARY-CLASSIFICATION}

Finally, on the actual complement-pair Boolean cube, a literal-product
family has a common zero when its exact total clause weight is strictly
smaller than $2^{\dim\mathcal C_N}$, for even $N\geq6$.
The formalized dimension is the actual finite cube-variable cardinality;
no closed floor formula is substituted for it.\ev{ALG-LITERAL-CUBE}
These statements exclude
certificates for their declared classes and hypotheses only. They do not
exclude the whole algebraic route. Exact theorem names and source hypotheses
are catalogued in Appendix A.
"""
    return header+"\n".join(lines)+"\n"+footer

def degree_section(degrees,dependence):
    text=r"""% Generated from existing finite data; ALG-NS-LOWER, ALG-DEGREE-CURVES, ALG-PC-ALPHA-GROUPING.
\section{Degree results and finite computation evidence}
\label{sec:degrees}
For the actual full-count calibration over $\mathbb Q$, the compiled lower
theorem applies to every supplied ordinary certificate. Here $A$ is the
multiplier of the single count constraint $\sum_iX_i-\pi(N)$, not an arbitrary
family multiplier $A_j$:
\[
 \deg A\geq\alpha(N),\qquad
 \deg\bigl(A(\textstyle\sum_i X_i-\pi(N))\bigr)\geq\alpha(N)+1,
 \qquad \alpha(N)=\pi(N)-r(N).
\]
The required degree is unbounded along even $N$. Neither theorem asserts
the existence of a certificate. Equality is established by existing exact
finite arithmetic only at the $26$ measured even points $N=10,12,\ldots,60$:
the rational identities and the finite-field minima both equal $\alpha+1$,
with degrees between $3$ and $14$. This finite tightness is not a compiled
universal upper theorem. The universal upper construction with midpoint
loops remains blocked; its no-loop counterpart has only paper status.
\ev{ALG-NS-LOWER}\ev{ALG-NS-UPPER-LIMIT}\ev{ALG-DEGREE-CURVES}

Polynomial calculus is measured separately, with genuine ordinary powers,
input rules, binary linear combinations and single-variable multiplication.
The saved measurements over $\mathbb F_{1000000007}$ have exact degrees
$3,3,3,3,4,4,4,4,4,5,5$ for even $N=10,\ldots,30$;
the rational measurements agree at those $11$ points.
The additional finite-field-only points $N=32,34,36$ have degrees $6,5,5$.
All these computations are labeled \textsc{Evidence}; they are not Lean
computations, rational transfers from the larger points, or asymptotic bounds.
The full degree rows are recorded in the publication JSON and Appendix A.
\ev{ALG-DEGREE-CURVES}

\begin{figure}[htbp]
\centering\includegraphics[width=.88\linewidth]{figures/degree_curve.pdf}
\caption{Existing finite degree plot. Static NS equality is measured over
$\mathbb Q$ and $\mathbb F_{1000000007}$ at even $N=10,\ldots,60$.
PC degrees agree over both fields at even $N=10,\ldots,30$; the points
$N=32,34,36$ are finite-field-only. The plot is evidence at these inputs,
not a universal upper bound or a rational transfer.\ev{ALG-DEGREE-FIGURE}}
\label{fig:degree}
\end{figure}

"""
    if dependence["same_alpha_same_PC_degree_in_saved_points"]:
        text+=r"""Grouping the existing CSV rows using $\alpha$ from the saved lower-bound
JSON finds the same PC degree whenever $\alpha$ repeats in these $14$
finite-field points. The complete observed groups are:
\begin{center}
\begin{tabular}{@{}lll@{}}
\toprule
$\alpha$ & $N$ & Observed PC degree\\
\midrule
"""
        for group in dependence["groups"]:
            text+="$"+str(group["alpha"])+"$ & $"+",".join(map(str,group["N"]))+"$ & $"+str(group["PC_degrees"][0])+r"$ \\"+"\n"
        text+=r"""\bottomrule
\end{tabular}
\end{center}
This is finite group consistency, not a universal dependence theorem or a
closed PC degree formula.\ev{ALG-PC-ALPHA-GROUPING}

"""
    text+=r"""The compiled ordinary-Q restriction sends a supplied $D_\pi$ PC refutation
to a genuine Boolean-knapsack refutation on $\alpha$ variables without
increasing ordinary line degree. The explicit external predicate
\texttt{KnapsackLowerBound} remains a hypothesis of its lower corollary.
That conditional corollary is out of scope and is recorded in Appendix B;
the partial lattice, coefficient and count-action lemmas do not remove
the hypothesis.\ev{ALG-PC-HYPOTHESIS}
"""
    return text

def appendix(rows,coverage,degrees):
    text=r"""% Existing accepted algebraic source inventory. No new compile or theorem audit.
\subsection{Algebraic corpus inventory}
The accepted algebraic proof snapshot is \texttt{e5c4e119}; its existing
Judge batch is \texttt{6f7d181a} and root acceptance is \texttt{3d5f0ff4}.
The saved audit lists $233$ theorem/lemma axiom entries, $204$ complete frozen
headers and $25$ imported modules. The electronic inventory contains $356$
named rows: those $233$ theorems/lemmas, $120$ other named declarations and
$3$ constructors. Definitions and constructors are not added to the
theorem/lemma count.\ev{ALG-INVENTORY-SCOPE}
The full inventory is supplied as \nolinkurl{paper/algebraic_lean_inventory.csv}
and \nolinkurl{paper/algebraic_inventory.json}; the table below is a compact
module catalogue followed by a \emph{representative} theorem excerpt.
The complete CSV records every row's module, exact name, informal reading,
source line and hash, source header, observed axiom list, credit and proof pin.
Copied full source modules and original frozen headers are retained in
\nolinkurl{paper/algebraic_sources/}; this catalogue does not replace their
typeclass, index, inequality, signed-function or certificate hypotheses.

In the tables, A3 means the existing print contains exactly
\texttt{propext}, \texttt{Classical.choice}, \texttt{Quot.sound}; A2 means
\texttt{propext}, \texttt{Quot.sound}; A0 means an explicitly empty print.
P means \texttt{propext} alone.
NR means no separately reprinted entry in the selected artifacts; it does
not mean no axioms. CL denotes a compiled theorem/lemma, D a definition/type,
and C a constructor in an accepted module. CL-C marks the conditional
corollary whose retained hypothesis is discussed in Appendix B.
All rows use accepted proof snapshot \texttt{e5c4e119}.
Module names below omit the common \texttt{AlgebraicGoldbach.} prefix;
\texttt{Calibration.} is retained. Exact full names are in the CSV/JSON.

"""
    modules=coverage["imported_project_modules"]
    for start in range(0,len(modules),8):
        text+=r"\begin{center}\scriptsize\setlength{\tabcolsep}{3pt}"+"\n"+r"\begin{tabular}{@{}p{.29\linewidth}p{.05\linewidth}p{.05\linewidth}p{.53\linewidth}@{}}"+"\n"+r"\toprule Module & CL & Other & Scope of accepted module\\\midrule"+"\n"
        for number in range(start,min(start+8,len(modules))):
            module=modules[number]; group=[r for r in rows if r["module"]==module]
            count=sum(r["declaration_kind"] in ("theorem","lemma") for r in group)
            label=module.removeprefix("AlgebraicGoldbach.")
            text+=tex_name(label)+r"\ev{ALG-MODULE-"+("%02d" % (number+1))+"} & "+str(count)+" & "+str(len(group)-count)+" & "+tex_escape(MODULE_SUMMARIES[module])+r" \\"+"\n"
        text+=r"\bottomrule\end{tabular}\end{center}"+"\n\n"
    text+=r"\subsection{Representative algebraic theorem excerpt}"+"\n"
    text+=r"This selection is not the exhaustive theorem inventory. The electronic rows retain all actual audited names and their exact source headers. Displayed names omit only the common project prefix described above."+"\n\n"
    selected=representative_rows(rows)
    for start in range(0,len(selected),8):
        text+=r"\begin{center}\scriptsize\setlength{\tabcolsep}{3pt}"+"\n"+r"\begin{tabular}{@{}p{.39\linewidth}p{.43\linewidth}p{.05\linewidth}p{.06\linewidth}@{}}"+"\n"+r"\toprule Declaration & Informal reading (source hypotheses retained) & Ax. & Level\\\midrule"+"\n"
        for row in selected[start:start+8]:
            ax=row["axioms_used"]
            axcode="NR" if ax is None else "A0" if not ax else "A3" if set(ax)==ALLOWED_AXIOMS else "A2" if set(ax)=={"propext","Quot.sound"} else "P" if set(ax)=={"propext"} else ";".join(ax)
            level="CL-C" if row["external_hypothesis_retained"] else "CL"
            label=row["name"].removeprefix("AlgebraicGoldbach.")
            text+=tex_name(label)+r"\ev{"+row["representative_claim_id"]+"} & "+tex_escape(row["informal_statement"])+" & "+axcode+" & "+level+r" \\"+"\n"
        text+=r"\bottomrule\end{tabular}\end{center}"+"\n\n"
    text+=r"\subsection{Complete finite degree rows (Evidence)}"+"\n"+r"\begin{center}\small\begin{tabular}{@{}rrrrrrr@{}}"+"\n"+r"\toprule $N$ & $\pi$ & $r$ & $\alpha$ & NS $\mathbb Q/\mathbb F_p$ & PC $\mathbb F_p$ & PC $\mathbb Q$\\\midrule"+"\n"
    for row in degrees:
        vals=[row["N"],row["pi_N"],row["unordered_pairs_including_loop_r"],row["alpha"],row["NS_minimum_Q"],row["PC_minimum_Fp"],row["PC_minimum_Q"]]
        text+=str(vals[0])+r"\ev{"+row["claim_id"]+"} & "+" & ".join("--" if x is None else str(x) for x in vals[1:])+r" \\"+"\n"
    text+=r"\bottomrule\end{tabular}\end{center}"+"\n"+r"Here $p=1000000007$; a dash denotes an absent measurement, not a bound."+"\n"
    return text

if __name__ == "__main__":
    main()
