"""Derive publication tables from existing Judge JSON, logs and Lean text only.

No Lean, solver, native computation, audit or Git mutation is performed.
The historical official counter is retained separately from the extracted rows.
Run from any directory: python paper/generate_analytic_inventory.py
"""
import csv
import hashlib
import json
import math
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
BASE = Path("research/goldbach-synthesis-v3-20261004/workspace/Goldbach_Parity_20261002")
PUBLICATION = Path("publications/2026-10-goldbach-synthesis-v3-1")
COMMIT = "f7e1fda19a9781b6f4ae6ebcae1dfc81b1b41460"
STANDARD = {"propext", "Classical.choice", "Quot.sound"}

# Human paraphrases of selected existing declarations, read with their pinned
# source context. These are summaries, not replacement Lean specifications.
REPRESENTATIVES = {
    "ParityWeights": ("concrete_prime_triprime_same_parity", "The prime 101 and the composite 101*103*107 have the same odd parity weight; the composite lies between 100 and 100000000 and has no prime divisor at most 100."),
    "QuarticMobius": ("weighted_boundary_identity_real", "For arguments between alpha and N with N at most alpha^4, the weighted Mobius sum equals the stated combination of short double, cubic and quartic divisor sums."),
    "ChenWeight": ("weighted_prime_identity_real", "Under the quartic cap and the absence of prime factors at most alpha, the finite weighted Chen expression equals the corresponding prime-indicator sum."),
    "MultifibreObstruction": ("literalFourSiteBlock_neg", "The explicitly defined four-site block is negative."),
    "QuotientGauss": ("weighted_transform_real_part", "Under the finite-ring character assumptions in the source, the weighted real part of the quotient Kloosterman transform equals the squared Gauss-sum expression."),
    "AffineHHObstruction": ("concrete_mixed_level_displacement", "The displayed mixed difference of four concrete rational hhLevel values equals 1040."),
    "CompositeCompletion": ("zero_frequency_is_nonunit", "In a nontrivial ZMod ring, zero belongs to the set of nonunits."),
    "DeterminantCoordinates": ("concrete_expanded_tuple_sign_change", "The two displayed expanded determinant tuples have signs +1 and -1 respectively."),
    "UnitSupportedCompletion": ("double_unit_supported_completion", "For two functions vanishing on nonunits, the product of their unit-frequency moments satisfies the stated Gauss-normalized completion identity."),
    "PrimeCofactorIdentity": ("source_prime_bracket_cofactor", "For an admissible prime/cofactor representation with the original quotient cap and unit condition, the source prime bracket has the explicit Mobius-logarithm factorization."),
    "ShortDivisorComplement": ("at_one", "At argument one, the capped divisor kernel satisfies the displayed complementary short-divisor identity, for arbitrary natural caps."),
    "SquarefreeLcmCoefficient": ("squarefree_lcm_coefficient_unit", "For squarefree P coprime to N and r dividing P, the unit-masked lcm/totient sum equals the explicit finite Euler product divided by r."),
    "ThreeAdicPrimePairing": ("actual_principal_partition", "Under the recorded prime, ordering, coprimality and cap assumptions, the actual principal sum splits exactly into entropy, paired, singleton and geometric-face terms."),
    "PrimeSemiprimeSwitch": ("actual_admissible_switch", "For the specified admissible prime-to-semiprime switch, the two source brackets satisfy an exact logarithmic difference identity retaining both harmonic kernels."),
    "HarmonicKernelVariation": ("actual_kernel_abs_variation", "For positive front and arguments, ordered cofactors and prime complements beyond Q, harmonic-kernel variation is bounded by the two explicit finite logarithm/totient sums."),
    "LeastMissingPrimeMargin": ("large_prime_margin", "For every natural p at least 13, the displayed harmonic-minus-logarithm expression is at least 1/144; primality is not required."),
    "EulerAnchor": ("canonical_least_missing_prime_margin", "For nonzero even N and the stated lower bound on the twin constant, the singular series exceeds the logarithm of the least missing odd prime by at least 1/144."),
    "FourFormRoots": ("zero_mem_actualRoots", "Zero is a root of the actual four-form product over ZMod, with the source parameters retained."),
    "PowersetMoment": ("weighted_moment", "For nonnegative finite subset weights, the first weighted powerset moment factors as a product times the sum of h/(1+h) contributions."),
    "SelbergFourForms": ("weight_zero_outside", "If every element of P is at least one, a divisor subset outside the defined Selberg support has zero weight."),
    "FourFormTruncation": ("primeSupport_mono", "The prime support at cutoff y is contained in that at cutoff z whenever y is at most z."),
    "FourFormCollisionLoss": ("primeBase_positive", "The defined collision base is strictly positive at every prime."),
    "SeparatedTypeII": ("xi_bound", "The defined finite coefficient xi has absolute value at most one for every finite E and natural v."),
    "SeparatedTypeIIPrice": ("weighted_one_is_adversarial", "The separated bilinear sum with constant weight one equals the defined adversarial sum."),
    "SeparatedTypeIICount": ("units_inclusion", "For nonzero H, the count of elements coprime to H equals its Mobius divisor inclusion-exclusion sum."),
    "SeparatedTypeIILower": ("omitted_ratio_lower_R5", "Under the explicit conductor, interval, unit-count and three front/density guards, the omitted-to-unit ratio is at least density(H*ell)/(16*ell)."),
    "DoubleExtractionArithmetic": ("witnesses_distinct", "The two constructed witnesses of an admissible Cell are distinct."),
    "DividedFourForms": ("slopeProduct_eq", "The product of the divided-form slopes equals minus e times the anchor times the cube of the modulus."),
    "DividedRootCounts": ("witness1_q_cast_ne_zero", "For an admissible Cell, q is nonzero modulo the second constructed witness."),
    "DividedSelbergBridge": ("switch_weighted_moment", "For an admissible Cell and nonsaturated local root counts, the switched powerset logarithmic moment equals its Euler product times the local-density sum."),
    "RankCalibrationFace": ("three_small_primes_face_excludes_physicalMask", "Three distinct prime divisors whose squares are at most the front exclude the defined arithmetic mask when their product divides the conductor-weighted argument."),
    "RankCalibrationPrice": ("weighted_rank_price_decomposition", "The finite aggregate rank quantity decomposes exactly through an intermediate set into the remaining quantity and two price terms."),
    "RankCalibrationArithmetic": ("squarefree_subdivisor_reconstruction", "If d and d' are squarefree, k divides d and k' divides d', equality d*k=d'*k' forces equality of both pairs."),
    "RankCalibrationUnitLoss": ("small_prime_dvd_small_conductor", "Either designated prime c or r divides the defined small conductor whenever it is at most the cutoff R."),
    "RankCalibrationEuler": ("weighted_unit_inclusion", "For nonzero K, a finite sum over units modulo K equals its Mobius-weighted divisor inclusion-exclusion sum."),
    "RankCalibrationEstimator": ("normalized_density_error_bound", "For A at most J and positive ideal denominator, the difference of normalized A/J and A/ideal is bounded by the denominator discrepancy divided by ideal."),
    "TerminalPrimeExtraction": ("terminal_factorization", "For n at least two, the constructed cofactor multiplied by the terminal prime equals n."),
    "BalancedResourceSwitch": ("three_strata", "Every factor tuple falls into one of the three stated conductor ranges, separated by B and the square comparison with N."),
    "SignedHyperbolicCRT": ("unpack_encode", "For an admissible resource cell, unpacking the signed encoding recovers the original encoding."),
    "NonSSBracketSwitch": ("theta_coordinate_reindex", "The finite theta-bracket sum on the defined admissible domain equals its factor-coordinate reindexing."),
    "RankTwoHarmonic": ("unordered_pair_moment", "The ordered half of a symmetric weighted pair sum equals one half of the sum of the squared total and the diagonal square sum."),
    "OddBonferroniArithmetic": ("truncated_choose_zero", "For every truncation order, the alternating binomial sum at zero equals one."),
    "LeastFactorComposite": ("square_quotient", "For prime p, the least-prime quotient of p squared equals p."),
    "SwitchedSelbergWeight": ("totientDensity_properties", "For even N, the totient density at every prime in the switched support is strictly between zero and one."),
    "PhysicalCompositeSubtraction": ("physicalRaw_theta_difference", "The defined raw arithmetic mass equals its prime mass plus the proper-prime-power difference."),
    "CompositeAPConductor": ("totient_product_kernel", "For a finite set of primes, the Selberg product of totient densities equals the reciprocal totient of the prime product."),
    "SwitchedIncidenceEstimator": ("switchedIncidence_reference_price", "For even N and positive cutoff, the prime incidence minus its reference is bounded by the constructed main terms, both absolute remainders and the retained large-composite subtraction."),
    "FriablePhysicalPrefix": ("smooth_large_has_actual_band_divisor", "A Y-smooth integer n at least D has a divisor in the defined divisor band when D>1 and Y>0."),
    "FriableEulerRankin": ("tau_prime_pow", "At a prime power p^k, the divisor-counting function tau equals k+1."),
    "FriableKernelEnvelope": ("totientInverseSum_mono", "The finite reciprocal-totient sum is monotone in its natural cutoff."),
    "FriablePrimeHarmonic": ("pseries_tsum_le_one_add_inv", "For positive sigma, the nonnegative p-series with exponent 1+sigma is at most 1+1/sigma."),
    "FriableTotientEnvelope": ("weightedInverseTotient_multiplicative", "The defined weighted inverse-totient arithmetic function is multiplicative."),
    "FriablePhysicalPayment": ("uniqueResources1_subset_smoothInterval", "The second set of unique smooth resources is contained in the defined smooth interval."),
    "FriablePhysicalDemand": ("actual_theta_demand_abs_le_seven_log_cube", "Under the recorded structural support and front guards with log N at least one, the theta bracket has absolute value at most 7(log N)^3."),
    "FriableDemandAggregation": ("friableRank_support", "Membership in the defined friable rank implies structural support and smoothness of at least one of its two resources."),
    "FriableSourceGeometry": ("source_u_pos", "Under the defined source-onset condition, sourceU is positive."),
    "FriableSourceBudget": ("source_rank_front_le_two_N", "Under the source-onset condition, the product of the defined three source fronts is at most 2N."),
    "EpsteinKernel22": ("boundary_deficit_bounds", "For positive a and u, the defined boundary deficit lies between zero and a^2/(2u^2)."),
    "EpsteinFinite22": ("finiteShiftIntegral_formula", "For positive y and nonzero integer m, the finite shifted integral equals the stated weight-scaled endpoint sum."),
    "EpsteinUnfold22": ("unfoldFullRealThreeHalves_natAbs", "For positive y and nonzero integer m, the infinite shifted integral equals 2/(|m|^2 sqrt(y))."),
    "EpsteinTail22": ("continuousOn_truncationEnvelopeReal", "The defined real truncation envelope is continuous on the parameter domain where its second coordinate exceeds the fixed cutoff q."),
    "GammaPrerequisites22": ("Gamma_strip_exponential_bound", "The actual Gamma function has norm at most 2 exp(-pi|Im s|/4) throughout the closed strip 1<=Re s<=2."),
    "GammaDerivative22": ("Gamma_derivative_strip_exponential_bound", "The actual derivative of Gamma has norm at most 19 exp(-pi|Im s|/4) throughout the same closed strip."),
    "GammaPsiCore22": ("betaDifference_eq_integral", "For Re z>0 and real w>0, the beta-integral difference equals the integral of the defined difference integrand on (0,1)."),
    "GammaPsiBetaLimit22": ("gammaPsi_eq_beta_integral", "For Re z>0, the actual logarithmic derivative of Gamma equals minus Euler's constant plus its beta-integrand integral on (0,1)."),
    "GammaPsiIntegral22": ("gammaPsi_eq_exp_integral", "For Re z>0, the logarithmic derivative of Gamma equals minus Euler's constant plus the defined exponential integral over positive reals."),
    "GammaBoxBounds22": ("gammaBoxRadius_continuousAt", "The defined four-parameter Gamma-box radius is jointly continuous at every point whose Y coordinate is positive."),
    "GammaContourComponent22": ("gammaContourEnvelope_continuous", "The defined two-parameter Gamma contour envelope is continuous."),
    "ZetaEulerDirect22": ("contourZeta_ne_zero_on_right", "The actual Riemann zeta function is nonzero for Re s>1."),
    "ZetaReflection22": ("contourZeta_logDeriv_reflection", "On -1<Re s<0, the zeta logarithmic derivative equals the contour-chi logarithmic derivative minus the reflected zeta logarithmic derivative."),
    "GammaPsiDuplication22": ("gammaPsi_duplication", "For Re z>0, the Gamma logarithmic derivative satisfies psi(z)+psi(z+1/2)=2psi(2z)-2log 2."),
    "GammaPsiReflection22": ("gammaPsi_shift_reflection", "On -1<Re s<0, the indicated shifted Gamma-logarithmic-derivative difference equals 1/s minus the cotangent term."),
    "ContourChiPsi22": ("contourChi_logDeriv_eq_pair_integral", "On -1<Re s<0, the contour-chi logarithmic derivative equals log pi plus Euler's constant, 1/s and the actual paired integral."),
    "ThermalProjectionEnvelope22": ("thermalContinuousProjection_error_le", "For a>0 and natural N,M, the full-versus-partial circle projection error is bounded by the constructed projectionErrorEnvelope."),
    "ThermalProjectionIdentity22": ("thermalContinuousProjection_eq_vonMangoldt_sum", "For a>0 and natural N, the continuous circle projection equals the genuine von Mangoldt additive coefficient, including prime powers."),
    "DiscreteThermalProjection22": ("sampled_trueCircle_eq_coefficient", "For N<=M and K>max(N,2M-N), the finite sampled projector equals the genuine coefficient for every real damping parameter a."),
    "RationalLogQuantization22": ("quantizedLog_precision", "For 2<=p<=100000000, the fixed rational log constructor has absolute error at most 1/gridScale."),
    "QuantizedLambdaEnvelope22": ("coefficient_error_bound", "For N<=100000000, the genuine coefficient differs from the scaled canonical integer coefficient by at most the explicit errorEnvelope."),
    "FiniteFieldProjection22": ("fixed_A32_projection", "Over a prime field larger than 2^27, a root of order 2^27 gives the fixed canonical integer coefficient modulo that prime."),
    "ThermalGammaMellinInverse22": ("real_exp_eq_Gamma_integral", "For real x>0, exp(-x) equals the normalized actual Gamma inversion integral on Re s=2."),
    "ConcreteNTTRoots22": ("primitive_3892314113", "The specified bank root modulo the certified prime 3892314113 has exact multiplicative order 2^27."),
    "ConcreteNTTA32Projection22": ("projection_3892314113", "The specified finite-field projector modulo 3892314113 returns the canonical integer coefficient at N=100000000."),
    "AngularMellinBorder22": ("angularBorder_one_ne_zero", "For a>0 and natural N>0, the explicit angular boundary term at q=1 is nonzero."),
    "ComplexGammaMellinLocal22": ("complexGammaInverse_real", "The defined complex Gamma inverse agrees with exp(-x) on every positive real x."),
    "ComplexGammaMellinHolomorphy22": ("complex_exp_eq_Gamma_integral", "For Re w>0, exp(-w) equals the normalized actual Gamma integral with principal complex powers."),
    "ComplexGammaMellinTail22": ("exists_local_uniform_Gamma_tail", "For Re w>0 and H>=0, a constructed neighborhood has Gamma tails bounded by twice the center radius uniformly for all cutoffs T>=H."),
    "ComplexGammaMellinExpTailBridge22": ("complex_exp_truncation_error_le", "For Re w>0 and H>=0, the truncated Gamma inverse approximates exp(-w) within the explicit Gamma-tail radius."),
    "ComplexGammaMellinLambda22": ("lambdaMellinThermal_eq_integral", "For Re w>0, the genuine infinite von Mangoldt exponential series equals its normalized Dirichlet-series/Gamma integral; the norm-summable interchange is derived."),
}


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def binding(path):
    rel = path.relative_to(ROOT).as_posix()
    raw = path.read_bytes()
    return {"path": rel, "commit": COMMIT, "sha256": sha(raw), "bytes": len(raw)}


def load(path):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError("Duplicate JSON key")
            result[key] = value
        return result
    def reject(value):
        raise ValueError("Nonfinite JSON constant")
    def finite(value):
        if isinstance(value, float) and not math.isfinite(value):
            raise ValueError("Nonfinite JSON float")
        if isinstance(value, dict):
            for child in value.values():
                finite(child)
        elif isinstance(value, list):
            for child in value:
                finite(child)
    result = json.loads(path.read_text(encoding="utf-8-sig"),
                        object_pairs_hook=unique, parse_constant=reject)
    finite(result)
    return result


def portable(value):
    normalized = value.replace("\\", "/")
    marker = "Goldbach_Parity_20261002/"
    if marker not in normalized:
        return None
    return ROOT / BASE / normalized.split(marker, 1)[1]


def axiom_map(row):
    value = row.get("axioms", row.get("axiom_rows", row.get("theorem_axioms")))
    if isinstance(value, dict):
        return value
    if isinstance(value, list):
        return {item.get("declaration", item.get("theorem")): item["axioms"] for item in value}
    return {}


def records(value, origin, selected):
    if isinstance(value, dict):
        name = value.get("module")
        if (name in selected and value.get("exit_code", value.get("actual_exit_code")) == 0
                and axiom_map(value)):
            selected[name].append((origin, value))
        for child in value.values():
            records(child, origin, selected)
    elif isinstance(value, list):
        for child in value:
            records(child, origin, selected)


def source_for(row, origin):
    expected = row.get("original_source_sha256", row.get("source_sha256"))
    paths = []
    for key in ("source_snapshot", "source", "source_original", "instrumented_source"):
        if isinstance(row.get(key), str):
            path = portable(row[key])
            if path:
                paths.append(path)
    command = row.get("command", row.get("command_argv", []))
    if command and isinstance(command[-1], str):
        path = portable(command[-1])
        if path:
            paths.append(path)
    module = row["module"]
    if not any(p.exists() and sha(p.read_bytes()) == expected for p in paths):
        paths.extend((ROOT / BASE).rglob(module + ".lean"))
        paths.extend((ROOT / BASE).rglob(module + "_source.lean.txt"))
        paths.extend((ROOT / BASE).rglob(module + "_original_source.txt"))
    valid = [p for p in dict.fromkeys(paths) if p.exists() and sha(p.read_bytes()) == expected]
    if not valid:
        raise ValueError("No existing source matching saved Judge hash: " + module)
    valid.sort(key=lambda p: ("PREEXEC" in p.as_posix(), len(p.relative_to(ROOT).parts), len(p.as_posix())))
    return valid[0]


def strip_comments(text):
    # Preserve positions/newlines while removing nested Lean comments and strings.
    output = list(text)
    depth = 0
    quoted = False
    i = 0
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                output[i:i + 2] = "  "
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                output[i:i + 2] = "  "
                i += 2
            else:
                if text[i] != "\n":
                    output[i] = " "
                i += 1
        elif text.startswith("/-", i):
            depth = 1
            output[i:i + 2] = "  "
            i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            end = len(text) if end < 0 else end
            output[i:end] = " " * (end - i)
            i = end
        elif text[i] == '"':
            quoted = not quoted
            output[i] = " "
            i += 1
        elif quoted:
            if text[i] == "\\" and i + 1 < len(text):
                output[i:i + 2] = "  "
                i += 2
            else:
                if text[i] != "\n":
                    output[i] = " "
                i += 1
        else:
            i += 1
    return "".join(output)


def declaration_text(source, name):
    text = source.read_text(encoding="utf-8-sig")
    clean = strip_comments(text)
    generated_ext = name.endswith(".ext")
    local = name.rsplit(".", 2)[-2] if generated_ext else name.rsplit(".", 1)[-1]
    pattern = re.compile(r"(?m)^[ \t]*(?:@\[[^\]]*\][ \t]*)*(?:(?:noncomputable|private|protected|unsafe)\s+)*"
                         r"(theorem|lemma|def|abbrev|structure|class|instance)\s+"
                         + re.escape(local) + r"(?=\s|\{|\(|:|$)")
    found = list(pattern.finditer(clean))
    if not found:
        return "compiler-generated or unnamed declaration", "", ""
    match = found[0]
    end = clean.find(":=", match.end())
    if match.group(1) in ("structure", "class"):
        following = re.search(r"(?m)^[ \t]*(?:(?:noncomputable|private|protected)\s+)*"
                              r"(?:theorem|lemma|def|abbrev|structure|class|instance|end)\b", clean[match.end():])
        if following:
            end = match.end() + following.start()
    if end < 0:
        end = clean.find("\n", match.end())
    header = " ".join(clean[match.start():end].strip().split())
    before = text[:match.start()].rstrip()
    gloss = ""
    if before.endswith("-/"):
        start = before.rfind("/-")
        if start >= 0:
            gloss = " ".join(before[start + 2:-2].lstrip("!").strip().split())
    if not gloss or len(gloss) > 700:
        gloss = ""
    kind = "theorem" if match.group(1) == "lemma" else match.group(1)
    if generated_ext:
        kind = "generated theorem"
        gloss = "Compiler-generated extensionality theorem for the recorded structure " + local + "."
        header = "Generated extensionality theorem for: " + header
    return kind, header, gloss


def write_claims_and_appendix(paper, modules, declarations, inventory):
    by_module = {module["module"]: module for module in modules}
    claims = []
    def add(identifier, statement, status, evidence, **extra):
        claims.append({"id": identifier, "statement": statement, "status": status,
                       "evidence": evidence, **extra})
    for row in declarations:
        module = by_module[row["module"]]
        add("analytic.declaration." + row["module"] + "." + row["declaration"],
            row["informal_statement"] or "Existing recorded declaration " + row["declaration"] + "; no separate informal paraphrase is supplied.", "Compiled Lean", list({x["path"]: x for x in [module["source"], module["judge_receipt"], module["axiom_evidence"]]}.values()),
            declaration=row["declaration"], kind=row["kind"], axioms=row["axioms"],
            lean_statement=row["lean_statement"], partial_batch_credit=row["partial_batch_credit"],
            batch_status=row["batch_status"], informal_statement_status=row["informal_statement_status"],
            statement_scope_note=row["statement_scope_note"])
    def module_evidence(names):
        return list({item["path"]: item for name in names for item in (by_module[name]["source"], by_module[name]["judge_receipt"], by_module[name]["axiom_evidence"])}.values())
    definitions = [
        ("A-CIRCLE", "For every a>0 and natural N, the true von Mangoldt additive coefficient equals the normalized integral of T_a(theta)^2 times exp(-i N theta) on [0,2 pi]; prime powers remain present.", ["ThermalProjectionEnvelope22", "ThermalProjectionIdentity22"]),
        ("A-DISCRETE", "For natural N<=M, positive K and K>max(N,2M-N), the finite K-sample complex projector extracts the coefficient exactly, for every real a.", ["DiscreteThermalProjection22"]),
        ("A-LOG", "The fixed rational 32-term logarithm constructor, nearest-even rounding and clamping give error <=1/S at S=2^58 on 2<=p<=100000000. The true prime-power coefficient envelope is (N+1)(64/S+1/S^2), for N<=100000000.", ["RationalLogQuantization22", "QuantizedLambdaEnvelope22"]),
        ("A-FIELD", "Primitive-root character orthogonality is derived; the five concrete prime fields and roots of order 2^27 instantiate the canonical A32 coefficient projector. This is not native program refinement.", ["FiniteFieldProjection22", "ConcreteNTTRoots22", "ConcreteNTTA32Projection22"]),
        ("A-MELLIN", "For Re(w)>0, P(w)=sum Lambda(n)exp(-nw) equals (1/(2 pi)) integral D(t) Gamma(2+it) w^(-2-it) dt. The genuine series D is continuous and bounded in norm by 6; summability of integrals of norms pays the infinite interchange.", ["ComplexGammaMellinLambda22"]),
        ("A-GAMMA-CHAIN", "The exact inversion chain is GammaPrerequisites22 -> ThermalGammaMellinInverse22 -> ComplexGammaMellinLocal22 -> ComplexGammaMellinHolomorphy22 -> ComplexGammaMellinLambda22. Local22 is a PASS row in FAILED batch26. Local22 also supplies Tail22; Holomorphy22 and Tail22 supply ExpTailBridge22.", ["GammaPrerequisites22", "ThermalGammaMellinInverse22", "ComplexGammaMellinLocal22", "ComplexGammaMellinHolomorphy22", "ComplexGammaMellinLambda22", "ComplexGammaMellinTail22", "ComplexGammaMellinExpTailBridge22"]),
        ("A-IBP", "For a>0, natural N>=1 and complex q, angular integration by parts retains the explicit principal-branch boundary term and q/N recurrence. At q=1 the boundary term is nonzero.", ["AngularMellinBorder22"]),
    ]
    for identifier, statement, names in definitions:
        add(identifier, statement, "Compiled Lean", module_evidence(names),
            module_declaration_counts={name: by_module[name]["axiom_audited_declaration_count"] for name in names})
    next(c for c in claims if c["id"] == "A-FIELD")["concrete_bank"] = [
        {"p": p, "bank_base": g, "root_order": 2**27} for p, g in
        ((2013265921, 31), (2281701377, 3), (3221225473, 5), (3489660929, 3), (3892314113, 3))]
    obstruction_specs = [
        ("A-OBSTRUCTION-PARITY", "Parity detector retains composites", "Three distinct prime factors give oddWeight=1 while their product is composite; the explicit 101*103*107 example also has no prime factor at most 100.", [("ParityWeights", "parity_detector_retains_composite"), ("ParityWeights", "concrete_prime_triprime_same_parity")], "This concerns the defined parity detector, not every sieve or the Goldbach coefficient."),
        ("A-OBSTRUCTION-MULTIFIBRE", "Negative four-site block", "The constructed closed four-site block is negative for every value of its displayed kernel parameter; the literal arithmetic block is negative as well.", [("MultifibreObstruction", "closedFourSiteBlock_neg"), ("MultifibreObstruction", "literalFourSiteBlock_neg")], "It refutes positivity of that block, not all possible kernels or arithmetic correlations."),
        ("A-OBSTRUCTION-AFFINE", "Independent affine forms cannot produce a nonzero constant", "Over the source field, independent affine forms cannot have an identity f*R+g*S=N at every pair of arguments when N is nonzero. The rational and real specializations are recorded.", [("AffineHHObstruction", "independent_cross_forms_cannot_have_constant_nonzero_sum"), ("AffineHHObstruction", "rational_affine_obstruction"), ("AffineHHObstruction", "real_affine_obstruction")], "The result concerns a global identity for the specified two affine forms; it does not forbid identities restricted to an admissible arithmetic set."),
        ("A-OBSTRUCTION-SIGN", "Expanded determinant signs vary", "Two explicit expanded determinant tuples have opposite signs, +1 and -1.", [("DeterminantCoordinates", "concrete_expanded_tuple_sign_change")], "No global sign for all determinant-coordinate tuples follows from the common coordinate construction."),
        ("A-OBSTRUCTION-COMPLETION", "Composite-modulus completion retains a nonunit defect", "The exact finite character completion splits into its unit-frequency term plus nonunitDefect; zero is a nonunit in a nontrivial ZMod ring. Even for functions supported on units, the recorded defect formula is (q-kappa)*the defined arithmetic moment.", [("CompositeCompletion", "nonunit_partition"), ("CompositeCompletion", "zero_frequency_is_nonunit"), ("UnitSupportedCompletion", "unit_supported_nonunitDefect")], "This records the correction term, not a claim that it is nonzero in every specialization."),
        ("A-OBSTRUCTION-TYPEII", "Separated Type-II arithmetic and prime weights have different scope", "Under the complete source guards, the adversarial arithmetic sum equals density times omittedCount. Incorporating ell into the calibrated modulus makes the bilinear term zero; with the stated candidate front the prime-weight bilinear term is also zero. The normalized omitted-ratio lower bound retains all three front/density guards R4a,R4b,R4c.", [("SeparatedTypeII", "adversarial_sum_identity"), ("SeparatedTypeIIPrice", "calibrated_adversarial_zero"), ("SeparatedTypeIIPrice", "prime_weight_bilinear_zero"), ("SeparatedTypeIILower", "omitted_ratio_lower_R5")], "An adversarial bounded arithmetic weight cannot be substituted for the actual prime weight; this does not refute a stronger weighted Type-II estimate."),
        ("A-OBSTRUCTION-COLLISION", "Local collision factors remain in four-form bounds", "The actual four-form and divided-form Euler lower bounds explicitly retain collisionLoss or switchCollisionLoss. Their truncated G bounds additionally retain ordering, coprimality, nonsaturation, logarithmic-cutoff and prime-log-sum hypotheses.", [("FourFormCollisionLoss", "actualEuler_collision_loss"), ("FourFormCollisionLoss", "actualG_collision_loss_half"), ("DividedSelbergBridge", "switchEuler_collision_loss"), ("DividedSelbergBridge", "switchG_collision_loss_half")], "These are bounds with explicit factors and guards, not a proof that all collision losses must be large or prevent a sufficient estimate."),
        ("A-OBSTRUCTION-RANK", "Three-small-prime rank faces exclude the arithmetic mask", "Under the stated distinct-prime, small-square and divisibility assumptions, the three-prime face has beta=0 and is outside the arithmetic mask. With front at least 529 and 1771 dividing the conductor-weighted argument, the canonical profile and both its prime and raw-weight summands are nonpositive. The principal rank-price expression is nonpositive when its mass is nonnegative and t>1.", [("RankCalibrationFace", "three_small_primes_face_beta_zero"), ("RankCalibrationFace", "three_small_primes_face_excludes_physicalMask"), ("RankCalibrationPrice", "canonical_profile_on_rank_face_nonpositive"), ("RankCalibrationPrice", "rank_face_prime_summand_nonpositive"), ("RankCalibrationPrice", "rank_face_raw_summand_nonpositive"), ("RankCalibrationArithmetic", "rank_price_principal_nonpositive")], "The conclusion applies to these specified faces and canonical profiles; it does not prove a sign for the full reference gap."),
        ("A-OBSTRUCTION-LEASTFACTOR", "Nonminimal prime-divisor switch terms are not positive", "For the defined composite least-factor domain and its unit assumptions, switching on a prime divisor other than minFac gives a nonpositive odd-Bonferroni weight and a zero rough indicator.", [("LeastFactorComposite", "nonminimal_prime_oddBonferroni_nonpos"), ("LeastFactorComposite", "nonminimal_prime_roughIndicator_zero")], "The sign is for the displayed switched summands, not a universal estimate for the complete composite correction."),
        ("A-OBSTRUCTION-NONUNIT-SUPPORT", "Nonunit progression and resource support is excluded", "On the specified admissible composite-progression domain, a nonunit modulus cannot satisfy the indicated congruence or divide the switched candidate; the corresponding prime progression sum vanishes. For an admissible ResourceCell, a divisor noncoprime to N cannot divide either resource, and a divisor containing the anchor cannot divide resource0.", [("CompositeAPConductor", "physical_nonunit_AP_impossible"), ("CompositeAPConductor", "physical_nonunit_conductor_zero"), ("SwitchedIncidenceEstimator", "actualPrimeAP_nonunit_zero"), ("FriablePhysicalPrefix", "resource0_N_nonunit_impossible"), ("FriablePhysicalPrefix", "resource0_anchor_nonunit_impossible"), ("FriablePhysicalPrefix", "resource1_N_nonunit_impossible")], "These exact support exclusions do not supply the required aggregate error budget."),
    ]
    catalogue = []
    for identifier, title, statement, selected, limitation in obstruction_specs:
        rows = [next(row for row in declarations if row["module"] == module and row["declaration"].endswith("." + name)) for module, name in selected]
        evidence = module_evidence(list(dict.fromkeys(module for module, name in selected)))
        add(identifier, statement, "Compiled Lean / existing guarded declarations", evidence,
            title=title, declarations=[row["declaration"] for row in rows], what_it_does_not_show=limitation)
        catalogue.append({"claim_id": identifier, "title": title, "statement": statement,
                          "status": "Compiled Lean / existing guarded declarations", "evidence": evidence,
                          "declarations": rows, "what_it_does_not_show": limitation})
    (paper / "analytic_obstruction_catalogue.json").write_text(json.dumps({"schema": "EXISTING_ANALYTIC_OBSTRUCTIONS_V1", "scope": "Grouped existing negative/support/correction declarations; no new obstruction is proved.", "groups": catalogue}, ensure_ascii=False, indent=2) + "\n", encoding="utf-8", newline="\n")
    union = {item["path"]: item for group in catalogue for item in group["evidence"]}
    add("A-ARITHMETIC-OBSTRUCTIONS", "Ten groups of existing guarded declarations record parity retaining composites, a negative four-site block, the affine constant obstruction, determinant sign variation, nonunit completion corrections, separated Type-II weight distinctions, collision factors, rank-face signs, nonminimal-factor signs, and nonunit progression/resource exclusions. They do not establish a universal obstruction to the analytic route.",
        "Compiled Lean / existing guarded declarations", list(union.values()),
        group_claim_ids=[group["claim_id"] for group in catalogue])
    obstruction_tex = [r"\subsection{Existing finite-arithmetic obstruction groups}",
                       r"\label{app:analytic-obstructions}",
                       "The following groups summarize existing negative declarations, support exclusions and retained correction terms. Each has its complete source hypotheses in the pinned Lean file and its recorded Judge credit in the electronic catalogue. The grouping is editorial; it introduces no new mathematical result.\\ev{A-ARITHMETIC-OBSTRUCTIONS}"]
    for start in range(0, len(catalogue), 2):
        obstruction_tex += [r"\begin{center}\small", r"\begin{tabular}{@{}p{0.19\textwidth}p{0.48\textwidth}p{0.25\textwidth}@{}}", r"\toprule Group; status & Guarded statement & What it does not show\\\midrule"]
        for group in catalogue[start:start+2]:
            obstruction_tex.append(tex(group["title"]) + "; Compiled Lean & " + tex(group["statement"]) + r"\ev{" + group["claim_id"] + "} & " + tex(group["what_it_does_not_show"]) + r"\\")
        obstruction_tex += [r"\bottomrule\end{tabular}\end{center}"]
    finite = []
    for number in (14, 15, 16):
        path = ROOT / BASE / ("round" + str(number)) / "judge/judge_receipt.json"
        receipt = load(path)
        for key, value in receipt.get("falsifiers", {}).items():
            # Retain the existing receipt verdict; do not evaluate its bank.
            identifier = "A-FINITE-FALSIFIER-" + str(number) + "-" + key
            add(identifier, "In the saved finite bank, the claim '" + value["claim"] + "' has existing Judge status " + value["status"] + ".",
                "Observed / existing finite Judge verdict", [binding(path)],
                receipt_status=value["status"], falsified_claim=value["claim"],
                what_it_does_not_show="The finite bank is not the source-onset regime and does not prove a universal obstruction or a Goldbach conclusion.")
            finite.append({"claim_id": identifier, "round": number, "saved_key": key,
                           "falsified_claim": value["claim"], "receipt_status": value["status"],
                           "evidence": binding(path)})
    path7 = ROOT / BASE / "round7/judge_receipt.json"
    item7 = load(path7)["native_connection_counterexample"]
    add("A-FINITE-NATIVE-CONNECTION", "The existing round7 receipt records: " + item7 + ".",
        "Observed / existing finite Judge verdict", [binding(path7)],
        what_it_does_not_show="Only the proposed native connection at the recorded tuple is refuted; this is not a universal obstruction to character constructions.")
    add("A-FINITE-FALSIFIERS", "The existing Judge receipts record four finite falsifiers each in rounds14,15,16 and the round7 native-connection counterexample. No-counterexample-in-window promotions are excluded; no finite result is promoted to a source-onset theorem.",
        "Observed / existing finite Judge verdicts", list({x["evidence"]["path"]: x["evidence"] for x in finite}.values()) + [binding(path7)],
        finite_falsifiers=finite, native_connection_record=item7)
    obstruction_tex += [r"\subsection{Saved finite falsifiers in the historical analytic corpus}",
                        "The following are existing finite Judge verdicts, not freshly evaluated banks or unconditional source-onset theorems. The stated claim is the one refuted within its saved bank. Entries reporting only no counterexample in a window are excluded.\\ev{A-FINITE-FALSIFIERS}",
                        r"\noindent Round 7 additionally records the original tuple $k=7$: the proposed two-axis twists vanish while the native centered row is $5/6$. This refutes that proposed connection at the recorded tuple only.\ev{A-FINITE-NATIVE-CONNECTION}"]
    for start in range(0, len(finite), 4):
        obstruction_tex += [r"\begin{center}\small", r"\begin{tabular}{@{}p{0.09\textwidth}p{0.59\textwidth}p{0.23\textwidth}@{}}", r"\toprule Round & Claim refuted in its saved finite bank & Existing Judge status\\\midrule"]
        for item in finite[start:start+4]:
            claim = item["falsified_claim"].replace("physical", "arithmetic")
            obstruction_tex.append(str(item["round"]) + " & " + tex(claim) + r"\ev{" + item["claim_id"] + "} & " + r"\nolinkurl{" + item["receipt_status"] + r"}\\")
        obstruction_tex += [r"\bottomrule\end{tabular}\end{center}"]
    (paper / "analytic_obstructions.tex").write_text("\n".join(obstruction_tex) + "\n", encoding="utf-8", newline="\n")
    checkpoint = ROOT / BASE / ".arbor/sessions/parity/.coordinator/checkpoint.json"
    receipt20 = ROOT / BASE / "round20/judge/final_receipt.json"
    add("A-INVENTORY-COUNTS", "The recorded official counter is 88 modules and 1488 mixed entries: 942 historical theorem-counter entries plus 546 round22 declarations. The extracted table contains 1768 existing axiom-audit rows: 1222 historical plus 546 round22; it is not a count of theorems.",
        "Derived table from existing artifacts", [binding(checkpoint), binding(receipt20)],
        generator_path="paper/generate_analytic_inventory.py", inventory_path="paper/analytic_inventory.json")
    partials = [module for module in modules if module["partial_batch_credit"]]
    add("A-PARTIAL-BATCHES", "Batches 6,7,8,9,11,26 have global FAILED statuses but retain the whole-module PASS rows explicitly listed in the inventory; failed or uninvoked rows receive no credit.",
        "Existing Judge row credit", [module["judge_receipt"] for module in partials],
        pass_modules=[module["module"] for module in partials])
    source_specs = [
        ("weighted_lambda_tail", "round22/role4/complex_gamma_mellin_lambda_tail_source02/ComplexGammaMellinLambdaTail22.lean", "SOURCE: repaired, not compiled"),
        ("uniform_circle_geometry", "round22/role4/complex_gamma_circle_geometry_source01/ComplexGammaCircleGeometry22.lean", "SOURCE: not invoked in failed batch36"),
        ("coefficient_truncation_envelope", "round22/role4/lambda_circle_truncation_source01/LambdaCircleTruncationEnvelope22.lean", "SOURCE: not compiled"),
        ("scalar_connectors", "round22/role4/scalar_radius_real_connectors_source01/ScalarRadiusRealConnectors22.lean", "SOURCE: not compiled"),
        ("coefficient_scalar_bridge", "round22/role3/lambda_circle_scalar_bridge_source01/LambdaCircleScalarRadiusBridge22.lean", "SOURCE: not compiled"),
    ]
    boundary_bindings = []
    for name, path, status in source_specs:
        item = binding(ROOT / BASE / path)
        boundary_bindings.append(item)
        add("A-SOURCE-" + name, "The " + name.replace("_", " ") + " is retained as uncompiled source and is excluded from the compiled inventory.", status, [item])
    failed36 = ROOT / BASE / "round22/judge5/batch36/batch36_attempt01/receipt.json"
    add("A-TRUNCATION-BOUNDARY", "Failed batch36 adds no credit: the weighted Lambda tail failed and the geometry module was not invoked. The complete Mellin-to-coefficient truncation chain remains uncompiled, although unweighted Gamma tails and inversion are compiled.",
        "Failed/SOURCE boundary", [binding(failed36)] + boundary_bindings)
    paper_items = [
        ("A-OBSTRUCTION-SIGNED-GAP", "An enclosure for C_N does not supply the signed bound for R_ref-C_N or the retained prime-power/front/excess corrections in the fixed ledger. The identity D_N=R_ref-C_N+Q_N+2max(e,0)-epsilon_tr retains its inherited bridge conditions.", "round22/role4/continuous_dn_gap_paper01/dn_gap_audit22.md", "PAPER / conditional inherited ledger", "No Goldbach implication or signed target bound is proved by the projection identity."),
        ("A-OBSTRUCTION-BOUNDARY", "Periodicity of the complete arithmetic trace does not make individual truncated principal-branch Mellin kernels periodic; the explicit boundary term must be retained.", "round22/role4/continuous_dn_gap_paper01/dn_gap_audit22.md", "PAPER; boundary recurrence compiled separately", "Does not exclude better analytic cancellation arguments."),
        ("A-OBSTRUCTION-COST", "The proposed sufficient weighted-tail envelope and literal evaluation guards have very large costs at a=1/N. Their insufficiency at smaller cutoffs is an insufficiency of that envelope, not a lower bound on true error or on all algorithms.", "round22/role4/mellin_lambda_feasibility_paper01/feasibility22.md", "PAPER / SOURCE-dependent envelope", "Does not prove whole-route impossibility or a universal computational lower bound."),
        ("A-OBSTRUCTION-LOCAL-KERNEL", "The recorded two-dimensional restriction of the canonical off-diagonal kernel is [[0,1],[1,0]], with a negative direction. Pointwise nonnegativity is insufficient for positive semidefiniteness.", "round22/role4/zero_orbit_source_review01/review22.md", "PAPER", "Does not establish a sign for the full coefficient or exclude all operator methods."),
        ("A-OBSTRUCTION-POSITIVE-RECONSTRUCTION", "The powers-of-two sector has positive spectral reconstruction yet zero additive coefficient at N=14. Positive-definite data and positive moments alone do not force common reflected support.", "round22/role1/spectral_next_paper01/spectral_next22.md", "PAPER", "Does not substitute this sector for the true zeta data or refute extra properties of those data."),
    ]
    for identifier, statement, path, status, limitation in paper_items:
        add(identifier, statement, status, [binding(ROOT / BASE / path)], what_it_does_not_show=limitation)
    verdict_path = ROOT / PUBLICATION / "numerical_verdict.json"
    numerical = load(verdict_path)
    add("A-NUMERICAL", "The existing finite computation at N=100000000, K=134217728 and S=288230376151711744 records five-modulus CRT, direct canonical A32 and auxiliary B40 equality. It does not establish native Lean refinement, B40 real-log refinement, the Mellin truncation chain, D_N or Goldbach.",
        numerical["status"], [binding(verdict_path), binding(ROOT / PUBLICATION / "evidence_v3_1.json")],
        values={key: numerical[key] for key in ("N", "K", "S", "prime_moduli", "modular_residues", "CRT_product",
                 "independent_CRT_integer", "direct_A32_integer", "C_B40_integer", "coefficient_denominator",
                 "actual_difference_numerator", "primary_E_log_numerator", "primary_E_log_decimal",
                 "joint_2E_log_numerator", "joint_2E_log_decimal", "prime_record_count", "native_Lean_refinement",
                 "B40_real_log_refinement_Lean", "Mellin_coefficient_truncation_chain_compiled", "D_N", "WIN")})
    (paper / "analytic_claims.json").write_text(json.dumps({"schema": "ANALYTIC_PUBLICATION_CLAIMS_V1", "claims": claims}, ensure_ascii=False, indent=2) + "\n", encoding="utf-8", newline="\n")
    appendix = [r"\subsection{Analytic inventory from existing Judge artifacts}", r"\label{app:analytic-inventory}",
                "The electronic files \\texttt{analytic\\_inventory.json} and \\texttt{analytic\\_lean\\_inventory.csv} list every extracted axiom-audit row, its declaration kind, recorded axioms, textual declaration header, source and receipt paths, full hashes and existing repository commit. The header is extracted Lean text, not an elaborated type; surrounding section variables and hypotheses remain in the pinned source. A missing separate paraphrase is explicitly labelled. These tables are generated by \\texttt{generate\\_analytic\\_inventory.py} from existing artifacts only.",
                "The recorded official counter is 88 modules and 1,488 mixed historical entries. The exhaustive axiom-row extraction gives 1,768 rows: 1,222 historical and 546 from round 22. The historical counter counts 942 theorems, while later axiom rows also contain definitions and structures. Consequently neither 1,488 nor 1,768 is presented as a theorem count. Definitions without an individual axiom row are not assigned an invented empty axiom list.",
                "The tables below select one recorded theorem per module and give a human paraphrase of its scope. They do not replace the original hypotheses in the pinned source. The electronic inventory retains all 1,768 rows. Commit \\texttt{f7e1fda19a97} contains the existing public artifacts; source and receipt hashes identify their exact bytes. The axiom abbreviations are P=\\texttt{propext}, C=\\texttt{Classical.choice}, Q=\\texttt{Quot.sound}. A partial label means module-row PASS in a globally FAILED batch. Batches 6, 7, 8, 9, 11 and 26 have such retained rows; failed or uninvoked rows are excluded.\\ev{A-INVENTORY-COUNTS}\\ev{A-PARTIAL-BATCHES}"]
    for start in range(0, len(modules), 4):
        appendix += [r"\begin{center}\scriptsize", r"\begin{tabular}{@{}p{0.20\textwidth}p{0.52\textwidth}p{0.19\textwidth}@{}}", r"\toprule Module & Selected theorem and informal statement & Axioms; credit; commit; source SHA\\\midrule"]
        for module in modules[start:start + 4]:
            wanted, gloss = REPRESENTATIVES[module["module"]]
            row = next(row for row in declarations if row["module"] == module["module"] and row["declaration"].endswith("." + wanted))
            local = row["declaration"].rsplit(".", 1)[-1]
            abbreviations = ",".join({"propext": "P", "Classical.choice": "C", "Quot.sound": "Q"}[axiom] for axiom in row["axioms"]) or "none"
            status = "partial row PASS" if module["partial_batch_credit"] else "Compiled Lean"
            name = re.sub(r"(?<=[a-z])(?=[A-Z])", r"\\allowbreak{}", tex(module["module"]))
            appendix.append(name + " & " + r"\nolinkurl{" + local + "}. " + tex(gloss) + " & " + abbreviations + "; " + status + r"; \texttt{f7e1fda}; \texttt{" + module["source"]["sha256"][:12] + r"}\\")
        appendix += [r"\bottomrule\end{tabular}\end{center}"]
    (paper / "analytic_appendix.tex").write_text("\n".join(appendix) + "\n", encoding="utf-8", newline="\n")


def tex(value):
    chars = {"\\": r"\textbackslash{}", "_": r"\_", "&": r"\&", "%": r"\%",
             "#": r"\#", "$": r"\$", "{": r"\{", "}": r"\}", "~": r"\textasciitilde{}",
             "^": r"\textasciicircum{}"}
    return "".join(chars.get(c, c) for c in value)


def main():
    base = ROOT / BASE
    checkpoint_path = base / ".arbor/sessions/parity/.coordinator/checkpoint.json"
    checkpoint = load(checkpoint_path)
    historical = {name.split("/")[-1]: [] for name in checkpoint["retained_verified_modules"]}
    candidates = [base / "judge_receipt.json"]
    for number in (3, 4, 5, 10, 11, 13, 16, 17, 18, 19, 20):
        for path in (base / ("round" + str(number))).rglob("*.json"):
            rel = path.relative_to(base).as_posix()
            if ("judge" not in rel.lower() or "PREEXEC" in rel or path.stat().st_size > 300000
                    or not any(key in path.name.lower() for key in
                               ("receipt", "axiom", "compilations", "fresh_independent"))):
                continue
            candidates.append(path)
    for path in candidates:
        records(load(path), path, historical)
    receipt16 = base / "round16/judge/judge_receipt.json"
    for row in load(receipt16)["independent_new_compiles"]:
        log = base / "round16/judge" / (row["module"] + "_fresh.log")
        if sha(log.read_bytes()) != row["log_sha256"]:
            raise ValueError("Existing round16 axiom log does not match its saved receipt")
        pairs = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", log.read_text(encoding="utf-8-sig"))
        row["axioms"] = {name: [x.strip() for x in axioms.split(",") if x.strip()] for name, axioms in pairs}
        row["source"] = str(base / "round16/judge/build" / (row["module"] + ".lean"))
        row["table_axiom_log"] = log
        historical[row["module"]].append((receipt16, row))
    selected = []
    for name, rows in historical.items():
        if not rows:
            raise ValueError("Missing historical Judge row: " + name)
        rows.sort(key=lambda pair: (len(pair[0].relative_to(base).parts), len(pair[0].as_posix())))
        origin, row = rows[0]
        selected.append((origin, row, "HISTORICAL_INDEPENDENT_COMPILE_STANDARD_AXIOMS", None))
    for path in sorted((base / "round22/judge5").rglob("receipt.json")):
        if "PREEXEC" in path.as_posix():
            continue
        data = load(path)
        for row in data.get("rows", []):
            if row.get("status") == "INDEPENDENT_LEAN_AUX_PASS":
                selected.append((path, row, row["status"], data["status"]))
    modules = []
    declarations = []
    for origin, row, credit, batch_status in selected:
        source = source_for(row, origin)
        axioms = axiom_map(row)
        if any(not set(values).issubset(STANDARD) for values in axioms.values()):
            raise ValueError("Nonstandard axiom in purported credited row")
        module = {"module": row["module"], "source": binding(source), "judge_receipt": binding(origin),
                  "axiom_evidence": binding(row.get("table_axiom_log", origin)),
                  "credit_level": "Compiled Lean", "module_credit_status": credit,
                  "batch_status": batch_status, "partial_batch_credit": bool(batch_status and "FAILED" in batch_status),
                  "axiom_audited_declaration_count": len(axioms), "imports": re.findall(
                      r"(?m)^import\s+([^\n]+)", strip_comments(source.read_text(encoding="utf-8-sig")))}
        modules.append(module)
        for name, used in axioms.items():
            kind, statement, informal = declaration_text(source, name)
            selected_name, selected_gloss = REPRESENTATIVES[row["module"]]
            informal_status = "source comment" if informal else "no separate informal paraphrase; textual header and pinned source available"
            if name.endswith("." + selected_name):
                informal = selected_gloss
                informal_status = "human paraphrase of selected existing declaration"
            scope_note = "Textual declaration header, not an elaborated type; contextual variables and hypotheses are in the pinned source. A first internal := may terminate extraction in a let-based statement."
            declarations.append({"module": row["module"], "declaration": name, "kind": kind,
                                 "informal_statement": informal, "lean_statement": statement,
                                 "informal_statement_status": informal_status, "statement_scope_note": scope_note,
                                 "axioms": used, "credit_level": "Compiled Lean",
                                 "module_credit_status": credit, "batch_status": batch_status,
                                 "partial_batch_credit": module["partial_batch_credit"],
                                 "source_path": module["source"]["path"], "source_sha256": module["source"]["sha256"],
                                 "judge_receipt_path": module["judge_receipt"]["path"],
                                 "judge_receipt_sha256": module["judge_receipt"]["sha256"],
                                 "axiom_evidence_path": module["axiom_evidence"]["path"],
                                 "axiom_evidence_sha256": module["axiom_evidence"]["sha256"], "existing_commit": COMMIT})
    assert len(modules) == 88 and sum(x["axiom_audited_declaration_count"] for x in modules[:57]) == 1222
    assert sum(x["axiom_audited_declaration_count"] for x in modules[57:]) == 546 and len(declarations) == 1768
    inventory = {"schema": "EXISTING_ANALYTIC_JUDGE_ARTIFACT_INVENTORY_V1", "existing_repository_commit": COMMIT,
                 "scope": "Extraction only; no new compilation, arithmetic, certificate replay or mathematical credit.",
                 "recorded_official_counter": {"modules": 88, "entries": 1488, "historical_theorem_counter": 942,
                                               "round22_declarations_including_definitions": 546,
                                               "evidence": binding(checkpoint_path)},
                 "extracted_axiom_audit_rows": {"historical": 1222, "round22": 546, "total": 1768,
                                               "count_is_not_a_theorem_count": True},
                 "count_qualification": "The published 1488 is the retained mixed historical counter, not an exhaustive declaration count. Historical receipts count 942 theorems but audit additional definitions and structures. The table has 1768 recorded axiom rows; unaudited definitions are not silently assigned empty axioms.",
                 "allowed_standard_axioms": sorted(STANDARD), "modules": modules, "declarations": declarations,
                 "older_horizon_scope": "Excluded: no independent Judge credit is inferred from README or dirty-snapshot axiom status."}
    paper = ROOT / "paper"
    paper.mkdir(exist_ok=True)
    (paper / "analytic_inventory.json").write_text(json.dumps(inventory, ensure_ascii=False, indent=2) + "\n", encoding="utf-8", newline="\n")
    columns = ["module", "declaration", "kind", "informal_statement", "informal_statement_status", "lean_statement", "statement_scope_note", "axioms", "credit_level",
               "module_credit_status", "batch_status", "partial_batch_credit", "source_path", "source_sha256",
               "judge_receipt_path", "judge_receipt_sha256", "axiom_evidence_path", "axiom_evidence_sha256", "existing_commit"]
    with (paper / "analytic_lean_inventory.csv").open("w", encoding="utf-8", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=columns, lineterminator="\n")
        writer.writeheader()
        for row in declarations:
            writer.writerow({**row, "axioms": "; ".join(row["axioms"])})
    write_claims_and_appendix(paper, modules, declarations, inventory)
    print("EXISTING_ARTIFACT_TABLES", len(modules), len(declarations))


if __name__ == "__main__":
    main()
