import SignedHyperbolicCRT

/-! The finite support is the physical S minus SS support before theta/raw
selection. All weights below are the imported source D/W functions. -/
namespace GoldbachRound19.NonSS

open Finset GoldbachRound19.Switch GoldbachRound19.SignedCRT
open GoldbachRound10.ShortDivisorComplement
noncomputable section
attribute [local instance] Classical.propDecidable

def smallSemiprime (Z n : ℕ) : Prop := n.minFac ≤ Z ∧ (n / n.minFac).Prime
def nonSSSelector (N Z q : ℕ) : Prop :=
  ((resource1 N q).minFac ≤ Z ∨ (resource0 N q).minFac ≤ Z) ∧
    ¬ (smallSemiprime Z (resource1 N q) ∧ smallSemiprime Z (resource0 N q))

def StructuralSupport (alpha N Z M e q : ℕ) : Prop :=
  ResourceCell N q ∧ q.Prime ∧ M ≤ q ∧ anchor N < e ∧ Squarefree e ∧
    e.Coprime N ∧ e * q + (N - 1) / alpha + 1 ≤ N ∧ nonSSSelector N Z q

def physicalDomain (alpha N Z M : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 1 N).product (Icc 1 N)).filter
    (fun v => StructuralSupport alpha N Z M v.1 v.2)

def encodeLabel (N : ℕ) (v : ℕ × ℕ) : ℕ × FactorTuple := (v.1, encode N v.2)
def decodeLabel (N : ℕ) (v : ℕ × FactorTuple) : ℕ × ℕ := (v.1, decode N v.2)
def factorDomain (alpha N Z M : ℕ) : Finset (ℕ × FactorTuple) :=
  (physicalDomain alpha N Z M).image (encodeLabel N)

theorem physicalDomain_support {alpha N Z M : ℕ} {v : ℕ × ℕ}
    (hv : v ∈ physicalDomain alpha N Z M) : StructuralSupport alpha N Z M v.1 v.2 :=
  (Finset.mem_filter.mp hv).2

theorem decode_encode_label {alpha N Z M : ℕ} {v : ℕ × ℕ}
    (hv : v ∈ physicalDomain alpha N Z M) : decodeLabel N (encodeLabel N v) = v := by
  have hc := (physicalDomain_support hv).1
  exact Prod.ext rfl (decode_encode hc)

theorem encodeLabel_injective (alpha N Z M : ℕ) :
    Set.InjOn (encodeLabel N) (physicalDomain alpha N Z M) := by
  intro v hv w hw he
  have hd := congrArg (decodeLabel N) he
  rwa [decode_encode_label hv, decode_encode_label hw] at hd

/-- An independent full tuple selector characterizes the coordinate image. -/
theorem mem_factorDomain_iff {alpha N Z M : ℕ} {v : ℕ × FactorTuple} :
    v ∈ factorDomain alpha N Z M ↔
      decodeLabel N v ∈ physicalDomain alpha N Z M ∧ ValidTuple N v.2 := by
  constructor
  · intro hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact ⟨by rwa [decode_encode_label hw], encode_valid (physicalDomain_support hw).1⟩
  · rintro ⟨hv, hc⟩
    apply Finset.mem_image.mpr
    refine ⟨decodeLabel N v, hv, ?_⟩
    have hh := encode_decode hc (physicalDomain_support hv).1
    exact Prod.ext rfl hh

def balancedResourceEquiv (alpha N Z M : ℕ) :
    {v // v ∈ physicalDomain alpha N Z M} ≃ {c // c ∈ factorDomain alpha N Z M} where
  toFun v := ⟨encodeLabel N v.val, Finset.mem_image.mpr ⟨v.val, v.property, rfl⟩⟩
  invFun c := ⟨decodeLabel N c.val, (mem_factorDomain_iff.mp c.property).1⟩
  left_inv v := by apply Subtype.ext; exact decode_encode_label v.property
  right_inv c := by
    apply Subtype.ext
    have hc := mem_factorDomain_iff.mp c.property
    exact Prod.ext rfl (encode_decode hc.2 (physicalDomain_support hc.1).1)

def physicalCoefficient (alpha a N e q : ℕ) : ℝ :=
  -mu (e * q) *
    (physicalDivisorKernel ((N - 1) / alpha) a (e * q) (N - e * q) N -
      GoldbachRound11.harmonicKernel ((N - 1) / alpha) a N (N - e * q) (e * q))

def thetaBracket (alpha a N e q : ℕ) : ℝ :=
  GoldbachRound11.primeIncidence N q *
    GoldbachRound11.sourceBracket alpha a N (N - e * q) (e * q)

def rawLambda (N n : ℕ) : ℝ :=
  if n.Coprime N then ArithmeticFunction.vonMangoldt n else 0

def rawBracket (alpha a N e q : ℕ) : ℝ :=
  GoldbachRound11.primeIncidence N q * rawLambda N (N - e * q) *
    physicalCoefficient alpha a N e q

theorem thetaBracket_actual (alpha a N e q : ℕ) : thetaBracket alpha a N e q =
    GoldbachRound11.primeIncidence N q * GoldbachRound11.theta N (N - e * q) *
      physicalCoefficient alpha a N e q := by
  simp only [thetaBracket, GoldbachRound11.sourceBracket, physicalCoefficient, mul_assoc]

theorem raw_prime_equals_theta {N n : ℕ} (hn : n.Prime) :
    rawLambda N n = GoldbachRound11.theta N n := by
  by_cases hu : n.Coprime N
  · simp [rawLambda, GoldbachRound11.theta, GoldbachRound11.primeIncidence,
      hn, hu, ArithmeticFunction.vonMangoldt_apply_prime hn]
  · simp [rawLambda, GoldbachRound11.theta, GoldbachRound11.primeIncidence, hu]

theorem literal_selected_properpower_price (alpha a N e q : ℕ) :
    rawBracket alpha a N e q - thetaBracket alpha a N e q =
      GoldbachRound11.primeIncidence N q *
        (rawLambda N (N - e * q) - GoldbachRound11.theta N (N - e * q)) *
        physicalCoefficient alpha a N e q := by
  rw [thetaBracket_actual]
  unfold rawBracket
  ring

def thetaCoordinateWeight (alpha a N : ℕ) (v : ℕ × FactorTuple) : ℝ :=
  thetaBracket alpha a N v.1 (decode N v.2)
def rawCoordinateWeight (alpha a N : ℕ) (v : ℕ × FactorTuple) : ℝ :=
  rawBracket alpha a N v.1 (decode N v.2)

theorem theta_coordinate_reindex (alpha a N Z M : ℕ) :
    (∑ v ∈ physicalDomain alpha N Z M, thetaBracket alpha a N v.1 v.2) =
      ∑ c ∈ factorDomain alpha N Z M, thetaCoordinateWeight alpha a N c := by
  unfold factorDomain
  rw [Finset.sum_image (encodeLabel_injective alpha N Z M)]
  apply Finset.sum_congr rfl
  intro v hv
  unfold thetaCoordinateWeight encodeLabel
  rw [decode_encode (physicalDomain_support hv).1]

theorem raw_coordinate_reindex (alpha a N Z M : ℕ) :
    (∑ v ∈ physicalDomain alpha N Z M, rawBracket alpha a N v.1 v.2) =
      ∑ c ∈ factorDomain alpha N Z M, rawCoordinateWeight alpha a N c := by
  unfold factorDomain
  rw [Finset.sum_image (encodeLabel_injective alpha N Z M)]
  apply Finset.sum_congr rfl
  intro v hv
  unfold rawCoordinateWeight encodeLabel
  rw [decode_encode (physicalDomain_support hv).1]

theorem nonSS_actual_bracket_switch (alpha a N Z M : ℕ) :
    (∑ v ∈ physicalDomain alpha N Z M, thetaBracket alpha a N v.1 v.2) =
      (∑ c ∈ (factorDomain alpha N Z M).filter (fun c => c.2.direct = true),
        thetaCoordinateWeight alpha a N c) +
      ∑ c ∈ (factorDomain alpha N Z M).filter (fun c => c.2.direct = false),
        thetaCoordinateWeight alpha a N c := by
  rw [theta_coordinate_reindex]
  have hs := Finset.sum_filter_add_sum_filter_not (factorDomain alpha N Z M)
    (fun c => c.2.direct = true) (thetaCoordinateWeight alpha a N)
  simpa using hs.symm

theorem nonSS_actual_raw_switch (alpha a N Z M : ℕ) :
    (∑ v ∈ physicalDomain alpha N Z M, rawBracket alpha a N v.1 v.2) =
      (∑ c ∈ (factorDomain alpha N Z M).filter (fun c => c.2.direct = true),
        rawCoordinateWeight alpha a N c) +
      ∑ c ∈ (factorDomain alpha N Z M).filter (fun c => c.2.direct = false),
        rawCoordinateWeight alpha a N c := by
  rw [raw_coordinate_reindex]
  have hs := Finset.sum_filter_add_sum_filter_not (factorDomain alpha N Z M)
    (fun c => c.2.direct = true) (rawCoordinateWeight alpha a N)
  simpa using hs.symm

theorem actual_conductor_bound {alpha N Z M : ℕ} {c : ℕ × FactorTuple}
    (hc : c ∈ factorDomain alpha N Z M) : GoldbachRound19.Switch.conductor c.2 < N := by
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hc
  exact conductor_lt_N (physicalDomain_support hv).1

/-- This is a partition of signed weights, not a positivity estimate. The
long and medium terms remain literal sums. -/
theorem actual_three_stratum_sum (alpha a N Z M B : ℕ) :
    (∑ c ∈ factorDomain alpha N Z M, thetaCoordinateWeight alpha a N c) =
      (∑ c ∈ (factorDomain alpha N Z M).filter (fun c => GoldbachRound19.Switch.conductor c.2 ≤ B),
        thetaCoordinateWeight alpha a N c) +
      (∑ c ∈ (factorDomain alpha N Z M).filter
        (fun c => B < GoldbachRound19.Switch.conductor c.2 ∧ GoldbachRound19.Switch.conductor c.2 ^ 2 ≤ N),
        thetaCoordinateWeight alpha a N c) +
      ∑ c ∈ (factorDomain alpha N Z M).filter
        (fun c => B < GoldbachRound19.Switch.conductor c.2 ∧ N < GoldbachRound19.Switch.conductor c.2 ^ 2),
        thetaCoordinateWeight alpha a N c := by
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : GoldbachRound19.Switch.conductor c.2 ≤ B
  · simp [hc, not_lt_of_ge hc]
  · have hBc : B < GoldbachRound19.Switch.conductor c.2 := by omega
    by_cases hN : GoldbachRound19.Switch.conductor c.2 ^ 2 ≤ N
    · simp [hc, hBc, hN, not_lt_of_ge hN]
    · have hNl : N < GoldbachRound19.Switch.conductor c.2 ^ 2 := by omega
      simp [hc, hBc, hN, hNl]

def encodeSignedLabel (N : ℕ) (v : ℕ × ℕ) : ℕ × SignedCoordinates :=
  (v.1, encodeSigned N v.2)
def signedDomain (alpha N Z M : ℕ) : Finset (ℕ × SignedCoordinates) :=
  (physicalDomain alpha N Z M).image (encodeSignedLabel N)
def decodeSignedLabel (N : ℕ) (v : ℕ × SignedCoordinates) : ℕ × ℕ :=
  (v.1, (reconstructQ N v.2).toNat)

theorem decode_encode_signed_label {alpha N Z M : ℕ} {v : ℕ × ℕ}
    (hv : v ∈ physicalDomain alpha N Z M) :
    decodeSignedLabel N (encodeSignedLabel N v) = v := by
  unfold decodeSignedLabel encodeSignedLabel
  apply Prod.ext
  · rfl
  · rw [signed_reconstruction (physicalDomain_support hv).1]
    simp

theorem signedLabel_injective (alpha N Z M : ℕ) :
    Set.InjOn (encodeSignedLabel N) (physicalDomain alpha N Z M) := by
  intro v hv w hw he
  have hh := congrArg (decodeSignedLabel N) he
  rwa [decode_encode_signed_label hv, decode_encode_signed_label hw] at hh

theorem mem_signedDomain_iff {alpha N Z M : ℕ} {s : ℕ × SignedCoordinates} :
    s ∈ signedDomain alpha N Z M ↔
      decodeSignedLabel N s ∈ physicalDomain alpha N Z M ∧ SignedGuard N s.2 := by
  constructor
  · intro hs
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hs
    exact ⟨by rwa [decode_encode_signed_label hv],
      signedGuard_encode (physicalDomain_support hv).1⟩
  · rintro ⟨hv, hg⟩
    have hq : (reconstructQ N s.2).toNat = decode N (unpack N s.2) := by
      rw [signed_q_equals_decoded hg]
      simp
    have hcell : ResourceCell N (decode N (unpack N s.2)) := by
      simpa only [decodeSignedLabel, hq] using (physicalDomain_support hv).1
    apply Finset.mem_image.mpr
    refine ⟨decodeSignedLabel N s, hv, ?_⟩
    unfold encodeSignedLabel decodeSignedLabel
    apply Prod.ext
    · rfl
    · simp only [hq]
      exact encodeSigned_unpack hg hcell

def balancedSignedResourceEquiv (alpha N Z M : ℕ) :
    {v // v ∈ physicalDomain alpha N Z M} ≃ {s // s ∈ signedDomain alpha N Z M} where
  toFun v := ⟨encodeSignedLabel N v.val,
    Finset.mem_image.mpr ⟨v.val, v.property, rfl⟩⟩
  invFun s := ⟨decodeSignedLabel N s.val, (mem_signedDomain_iff.mp s.property).1⟩
  left_inv v := by apply Subtype.ext; exact decode_encode_signed_label v.property
  right_inv s := by
    apply Subtype.ext
    change encodeSignedLabel N (decodeSignedLabel N s.val) = s.val
    obtain ⟨v, hv, he⟩ := Finset.mem_image.mp s.property
    rw [← he, decode_encode_signed_label hv]

theorem physical_product_injective (alpha N Z M : ℕ) (hM : N < M ^ 2) :
    Set.InjOn (fun v : ℕ × ℕ => v.1 * v.2) (physicalDomain alpha N Z M) := by
  intro v hv w hw he
  change v.1 * v.2 = w.1 * w.2 at he
  have hs := physicalDomain_support hv
  have ht := physicalDomain_support hw
  have hepos : 0 < v.1 := by
    have hI := (Finset.mem_filter.mp hv).1
    exact (Finset.mem_Icc.mp (Finset.mem_product.mp hI).1).1
  have hmpos : 0 < v.1 * v.2 := Nat.mul_pos hepos hs.1.q_pos
  have hmN : v.1 * v.2 < N := by
    have hbase : v.1 * v.2 ≤ v.1 * v.2 + (N - 1) / alpha := Nat.le_add_right _ _
    have hstep := Nat.add_le_add_right hbase 1
    exact Nat.lt_of_succ_le (hstep.trans hs.2.2.2.2.2.2.1)
  have hqeq : v.2 = w.2 := by
    by_contra hneq
    have hc : v.2.Coprime w.2 := (Nat.coprime_primes hs.2.1 ht.2.1).mpr hneq
    have hqv : v.2 ∣ v.1 * v.2 := dvd_mul_left _ _
    have hqw : w.2 ∣ v.1 * v.2 := by rw [he]; exact dvd_mul_left _ _
    have hprod := hc.mul_dvd_of_dvd_of_dvd hqv hqw
    have hle := Nat.le_of_dvd hmpos hprod
    have hMq := hs.2.2.1
    have hMr := ht.2.2.1
    have hMM := Nat.mul_le_mul hMq hMr
    rw [pow_two] at hM
    omega
  have heeq : v.1 = w.1 := by
    rw [← hqeq] at he
    exact Nat.eq_of_mul_eq_mul_right hs.1.q_pos he
  exact Prod.ext heeq hqeq

theorem nonSquarefree_reciprocal_bracket_zero {alpha a N q : ℕ}
    (hns : ¬ Squarefree (resource1 N q)) :
    GoldbachRound11.sourceBracket alpha a N q (resource1 N q) = 0 := by
  simp [GoldbachRound11.sourceBracket, mu_zero_of_not_squarefree hns]

theorem reciprocal0_raw_zero {N q : ℕ} (h : ResourceCell N q)
    (hq : q.Prime) (hpq : anchor N < q) :
    rawLambda N (N - resource0 N q) = 0 := by
  have hnot := GoldbachRound18.DoubleExtraction.distinct_prime_product_not_primePow
    (anchor_spec h).1 hq (ne_of_lt hpq)
  have hz : ArithmeticFunction.vonMangoldt (anchor N * q) = 0 :=
    ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hnot
  simp [resource0, Nat.sub_sub_self h.anchor_mul_q_lt.le, rawLambda, hz]

theorem reciprocal0_theta_zero {N q : ℕ} (h : ResourceCell N q)
    (hq : q.Prime) (hpq : anchor N < q) :
    GoldbachRound11.theta N (N - resource0 N q) = 0 := by
  have hnot := GoldbachRound18.DoubleExtraction.distinct_prime_product_not_primePow
    (anchor_spec h).1 hq (ne_of_lt hpq)
  have hnp : ¬ (anchor N * q).Prime := fun hp => hnot hp.isPrimePow
  simp [resource0, Nat.sub_sub_self h.anchor_mul_q_lt.le,
    GoldbachRound11.theta, GoldbachRound11.primeIncidence, hnp]

theorem nonSS_actual_signed_CRT_switch (alpha a N Z M : ℕ) :
    (∑ v ∈ physicalDomain alpha N Z M, thetaBracket alpha a N v.1 v.2) =
      ∑ s ∈ signedDomain alpha N Z M,
        thetaBracket alpha a N s.1 ((reconstructQ N s.2).toNat) := by
  unfold signedDomain
  rw [Finset.sum_image (signedLabel_injective alpha N Z M)]
  apply Finset.sum_congr rfl
  intro v hv
  simp only [encodeSignedLabel]
  rw [signed_reconstruction (physicalDomain_support hv).1]
  simp

#print axioms smallSemiprime
#print axioms nonSSSelector
#print axioms StructuralSupport
#print axioms physicalDomain
#print axioms encodeLabel
#print axioms decodeLabel
#print axioms factorDomain
#print axioms physicalDomain_support
#print axioms decode_encode_label
#print axioms encodeLabel_injective
#print axioms mem_factorDomain_iff
#print axioms balancedResourceEquiv
#print axioms physicalCoefficient
#print axioms thetaBracket
#print axioms rawLambda
#print axioms rawBracket
#print axioms thetaBracket_actual
#print axioms raw_prime_equals_theta
#print axioms literal_selected_properpower_price
#print axioms thetaCoordinateWeight
#print axioms rawCoordinateWeight
#print axioms theta_coordinate_reindex
#print axioms raw_coordinate_reindex
#print axioms nonSS_actual_bracket_switch
#print axioms nonSS_actual_raw_switch
#print axioms actual_conductor_bound
#print axioms actual_three_stratum_sum
#print axioms encodeSignedLabel
#print axioms signedDomain
#print axioms decodeSignedLabel
#print axioms decode_encode_signed_label
#print axioms signedLabel_injective
#print axioms mem_signedDomain_iff
#print axioms balancedSignedResourceEquiv
#print axioms physical_product_injective
#print axioms nonSquarefree_reciprocal_bracket_zero
#print axioms reciprocal0_raw_zero
#print axioms reciprocal0_theta_zero
#print axioms nonSS_actual_signed_CRT_switch

end
end GoldbachRound19.NonSS
