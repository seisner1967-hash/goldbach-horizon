/-
  Goldbach/IntervalArith.lean
  Certified interval arithmetic over ℚ with ℝ-correctness proofs.

  Foundation for replacing trusted Python axioms by pure Lean proofs.
  All operations are computable (no `noncomputable`).

  §1: Interval structure
  §2: Membership (ℝ semantics)
  §3: Certified operations (add, sub, neg, mul, div, sq)
  §4: Correctness theorems
  §5: Square root enclosure (via Newton iteration)
  §6: Log enclosure connector
  §7: Tests

  0 sorry, 0 axiom.
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

set_option maxHeartbeats 400000

namespace Goldbach

/-! ## §1 Interval structure -/

/-- A closed rational interval [lo, hi] with proof of validity. -/
structure Interval where
  lo : ℚ
  hi : ℚ
  valid : lo ≤ hi
  deriving Repr

instance : ToString Interval where
  toString I := s!"[{I.lo}, {I.hi}]"

/-! ## §2 Membership -/

/-- A real number x belongs to interval I iff lo ≤ x ≤ hi. -/
def Interval.mem (I : Interval) (x : ℝ) : Prop :=
  (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)

/-- Construct a point interval [q, q]. -/
def Interval.point (q : ℚ) : Interval where
  lo := q
  hi := q
  valid := le_refl q

theorem Interval.point_mem (q : ℚ) : (Interval.point q).mem (q : ℝ) :=
  ⟨le_refl _, le_refl _⟩

/-! ## §3 Certified operations -/

/-- Negation: -[a,b] = [-b, -a]. -/
def Interval.neg (I : Interval) : Interval where
  lo := -I.hi
  hi := -I.lo
  valid := neg_le_neg I.valid

/-- Addition: [a,b] + [c,d] = [a+c, b+d]. -/
def Interval.add (I J : Interval) : Interval where
  lo := I.lo + J.lo
  hi := I.hi + J.hi
  valid := add_le_add I.valid J.valid

/-- Subtraction: [a,b] - [c,d] = [a-d, b-c]. -/
def Interval.sub (I J : Interval) : Interval where
  lo := I.lo - J.hi
  hi := I.hi - J.lo
  valid := sub_le_sub I.valid J.valid

/-- Multiplication: [a,b] × [c,d] via four endpoint products min/max. -/
def Interval.mul (I J : Interval) : Interval where
  lo := min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi))
  hi := max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi))
  valid := le_trans (min_le_left _ _ |>.trans (min_le_left _ _))
                    (le_max_left _ _ |>.trans (le_max_left _ _))

/-- Division: [a,b] / [c,d] when 0 < c (positive denominator). -/
def Interval.div (I : Interval) (J : Interval) (_hlo : 0 < J.lo) : Interval where
  lo := min (min (I.lo / J.lo) (I.lo / J.hi)) (min (I.hi / J.lo) (I.hi / J.hi))
  hi := max (max (I.lo / J.lo) (I.lo / J.hi)) (max (I.hi / J.lo) (I.hi / J.hi))
  valid := le_trans (min_le_left _ _ |>.trans (min_le_left _ _))
                    (le_max_left _ _ |>.trans (le_max_left _ _))

/-- Square: [a,b]² with correct handling of signs. -/
def Interval.sq (I : Interval) : Interval where
  lo := if 0 ≤ I.lo then I.lo * I.lo
        else if I.hi ≤ 0 then I.hi * I.hi
        else 0
  hi := max (I.lo * I.lo) (I.hi * I.hi)
  valid := by
    split
    · exact le_max_left _ _
    · split
      · exact le_max_right _ _
      · exact le_max_of_le_left (mul_self_nonneg I.lo)

/-- Width of an interval. -/
def Interval.width (I : Interval) : ℚ := I.hi - I.lo

/-! ## §4 Correctness theorems -/

section Correctness

variable {I J : Interval} {x y : ℝ}

theorem Interval.neg_correct (hx : I.mem x) :
    I.neg.mem (-x) := by
  constructor <;> simp only [Interval.neg, Rat.cast_neg] <;> linarith [hx.1, hx.2]

theorem Interval.add_correct (hx : I.mem x) (hy : J.mem y) :
    (I.add J).mem (x + y) := by
  constructor <;> simp only [Interval.add, Rat.cast_add] <;> linarith [hx.1, hx.2, hy.1, hy.2]

theorem Interval.sub_correct (hx : I.mem x) (hy : J.mem y) :
    (I.sub J).mem (x - y) := by
  constructor <;> simp only [Interval.sub, Rat.cast_sub] <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-! ### Multiplication correctness

Key insight: x*y is bilinear on [a,b]×[c,d], so its extrema
are at corners. The proof uses sign case-splits to select the
binding corner, with two nonneg products establishing the bound. -/

/-- The minimum of four corner products bounds x*y from below. -/
private theorem min_corners_le_mul {a b c d : ℝ}
    (ha : a ≤ x) (hb : x ≤ b) (hc : c ≤ y) (hd : y ≤ d) :
    min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ x * y := by
  -- Strategy: case split on sign of y and relevant endpoint to find corner ≤ xy
  rcases le_or_lt 0 y with hy | hy
  · rcases le_or_lt 0 a with ha0 | ha0
    · -- y ≥ 0, a ≥ 0: a*c ≤ x*y  [xy - ac = (x-a)*y + a*(y-c) ≥ 0]
      exact le_trans (min_le_left _ _ |>.trans (min_le_left _ _))
        (by nlinarith [mul_nonneg (show (0:ℝ) ≤ x - a by linarith) hy,
                        mul_nonneg ha0 (show (0:ℝ) ≤ y - c by linarith)])
    · -- y ≥ 0, a < 0: a*d ≤ x*y  [xy - ad = (x-a)*y + (-a)*(d-y) ≥ 0]
      exact le_trans (min_le_left _ _ |>.trans (min_le_right _ _))
        (by nlinarith [mul_nonneg (show (0:ℝ) ≤ x - a by linarith) hy,
                        mul_nonneg (show (0:ℝ) ≤ -a by linarith)
                                   (show (0:ℝ) ≤ d - y by linarith)])
  · rcases le_or_lt b 0 with hb0 | hb0
    · -- y < 0, b ≤ 0: b*d ≤ x*y  [xy - bd = (b-x)*(-y) + (-b)*(d-y) ≥ 0]
      exact le_trans (min_le_right _ _ |>.trans (min_le_right _ _))
        (by nlinarith [mul_nonneg (show (0:ℝ) ≤ b - x by linarith)
                                   (show (0:ℝ) ≤ -y by linarith),
                        mul_nonneg (show (0:ℝ) ≤ -b by linarith)
                                   (show (0:ℝ) ≤ d - y by linarith)])
    · -- y < 0, b > 0: b*c ≤ x*y  [xy - bc = (b-x)*(-y) + b*(y-c) ≥ 0]
      exact le_trans (min_le_right _ _ |>.trans (min_le_left _ _))
        (by nlinarith [mul_nonneg (show (0:ℝ) ≤ b - x by linarith)
                                   (show (0:ℝ) ≤ -y by linarith),
                        mul_nonneg (le_of_lt hb0)
                                   (show (0:ℝ) ≤ y - c by linarith)])

/-- x*y is bounded above by the max of four corner products. -/
private theorem mul_le_max_corners {a b c d : ℝ}
    (ha : a ≤ x) (hb : x ≤ b) (hc : c ≤ y) (hd : y ≤ d) :
    x * y ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) := by
  rcases le_or_lt 0 y with hy | hy
  · rcases le_or_lt 0 b with hb0 | hb0
    · -- y ≥ 0, b ≥ 0: x*y ≤ b*d  [bd - xy = (b-x)*y + b*(d-y) ≥ 0]
      exact le_trans
        (by nlinarith [mul_nonneg (show (0:ℝ) ≤ b - x by linarith) hy,
                        mul_nonneg hb0 (show (0:ℝ) ≤ d - y by linarith)])
        (le_max_right _ _ |>.trans (le_max_right _ _))
    · -- y ≥ 0, b < 0: x*y ≤ a*c  [ac - xy = (x-a)*(-y) + (-a)*(y-c)]
      -- But (-y) ≤ 0! Need different approach.
      -- b < 0 ⟹ x ≤ b < 0, a ≤ x < 0.
      -- xy ≤ by [from (b-x)*y ≥ 0] and by ≤ bc [from (-b)*(y-c) ≥ 0]
      -- So xy ≤ bc.
      exact le_trans
        (by nlinarith [mul_nonneg (show (0:ℝ) ≤ b - x by linarith) hy,
                        mul_nonneg (show (0:ℝ) ≤ -b by linarith)
                                   (show (0:ℝ) ≤ y - c by linarith)])
        (le_max_left _ _ |>.trans (le_max_right _ _))
  · rcases le_or_lt 0 a with ha0 | ha0
    · -- y < 0, a ≥ 0: x*y ≤ a*d  [ad - xy = (x-a)*(-y) + a*(d-y) ≥ 0]
      exact le_trans
        (by nlinarith [mul_nonneg (show (0:ℝ) ≤ x - a by linarith)
                                   (show (0:ℝ) ≤ -y by linarith),
                        mul_nonneg ha0 (show (0:ℝ) ≤ d - y by linarith)])
        (le_max_right _ _ |>.trans (le_max_left _ _))
    · -- y < 0, a < 0: x*y ≤ a*c  [ac - xy = (x-a)*(-y) + (-a)*(y-c)]
      -- (x-a)*(-y): x ≥ a so x-a ≥ 0, -y > 0. Gives -xy + ay ≥ 0 ⟹ xy ≤ ay.
      -- (-a)*(y-c): -a > 0, y-c ≥ 0. Gives -ay + ac ≥ 0 ⟹ ay ≤ ac.
      -- Together: xy ≤ ay ≤ ac.
      exact le_trans
        (by nlinarith [mul_nonneg (show (0:ℝ) ≤ x - a by linarith)
                                   (show (0:ℝ) ≤ -y by linarith),
                        mul_nonneg (show (0:ℝ) ≤ -a by linarith)
                                   (show (0:ℝ) ≤ y - c by linarith)])
        (le_max_left _ _ |>.trans (le_max_left _ _))

theorem Interval.mul_correct (hx : I.mem x) (hy : J.mem y) :
    (I.mul J).mem (x * y) := by
  obtain ⟨hxlo, hxhi⟩ := hx
  obtain ⟨hylo, hyhi⟩ := hy
  simp only [Interval.mem, Interval.mul]
  refine ⟨?_, ?_⟩
  · -- Lower bound: ↑(min4 corners) ≤ x * y
    -- Strategy: select the binding corner via exact_mod_cast, then push_cast + nlinarith
    rcases le_or_lt 0 y with hy0 | hy0
    · rcases le_or_lt 0 (I.lo : ℝ) with ha0 | ha0
      · -- y ≥ 0, a ≥ 0: ac ≤ xy
        have h1 : (↑(min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi))) : ℝ) ≤ ↑(I.lo * J.lo) := by
          exact_mod_cast min_le_left _ _ |>.trans (min_le_left _ _)
        have h2 : (↑(I.lo * J.lo) : ℝ) ≤ x * y := by
          push_cast
          nlinarith [mul_nonneg (show (0:ℝ) ≤ x - ↑I.lo by linarith) hy0,
                     mul_nonneg (show (0:ℝ) ≤ ↑I.lo by linarith) (show (0:ℝ) ≤ y - ↑J.lo by linarith)]
        linarith
      · -- y ≥ 0, a < 0: ad ≤ xy
        have h1 : (↑(min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi))) : ℝ) ≤ ↑(I.lo * J.hi) := by
          exact_mod_cast min_le_left _ _ |>.trans (min_le_right _ _)
        have h2 : (↑(I.lo * J.hi) : ℝ) ≤ x * y := by
          push_cast
          nlinarith [mul_nonneg (show (0:ℝ) ≤ x - ↑I.lo by linarith) hy0,
                     mul_nonneg (show (0:ℝ) ≤ -↑I.lo by linarith) (show (0:ℝ) ≤ ↑J.hi - y by linarith)]
        linarith
    · rcases le_or_lt (I.hi : ℝ) 0 with hb0 | hb0
      · -- y < 0, b ≤ 0: bd ≤ xy
        have h1 : (↑(min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi))) : ℝ) ≤ ↑(I.hi * J.hi) := by
          exact_mod_cast min_le_right _ _ |>.trans (min_le_right _ _)
        have h2 : (↑(I.hi * J.hi) : ℝ) ≤ x * y := by
          push_cast
          nlinarith [mul_nonneg (show (0:ℝ) ≤ ↑I.hi - x by linarith) (show (0:ℝ) ≤ -y by linarith),
                     mul_nonneg (show (0:ℝ) ≤ -↑I.hi by linarith) (show (0:ℝ) ≤ ↑J.hi - y by linarith)]
        linarith
      · -- y < 0, b > 0: bc ≤ xy
        have h1 : (↑(min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi))) : ℝ) ≤ ↑(I.hi * J.lo) := by
          exact_mod_cast min_le_right _ _ |>.trans (min_le_left _ _)
        have h2 : (↑(I.hi * J.lo) : ℝ) ≤ x * y := by
          push_cast
          nlinarith [mul_nonneg (show (0:ℝ) ≤ ↑I.hi - x by linarith) (show (0:ℝ) ≤ -y by linarith),
                     mul_nonneg (show (0:ℝ) ≤ ↑I.hi by linarith) (show (0:ℝ) ≤ y - ↑J.lo by linarith)]
        linarith
  · -- Upper bound: x * y ≤ ↑(max4 corners)
    rcases le_or_lt 0 y with hy0 | hy0
    · rcases le_or_lt 0 (I.hi : ℝ) with hb0 | hb0
      · -- y ≥ 0, b ≥ 0: xy ≤ bd
        have h1 : x * y ≤ (↑(I.hi * J.hi) : ℝ) := by
          push_cast
          nlinarith [mul_nonneg (show (0:ℝ) ≤ ↑I.hi - x by linarith) hy0,
                     mul_nonneg hb0 (show (0:ℝ) ≤ ↑J.hi - y by linarith)]
        have h2 : (↑(I.hi * J.hi) : ℝ) ≤ ↑(max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi))) := by
          exact_mod_cast le_max_right _ _ |>.trans (le_max_right _ _)
        linarith
      · -- y ≥ 0, b < 0: xy ≤ bc (since x ≤ b < 0, c ≤ y)
        have h1 : x * y ≤ (↑(I.hi * J.lo) : ℝ) := by
          push_cast
          nlinarith [mul_nonneg (show (0:ℝ) ≤ ↑I.hi - x by linarith) hy0,
                     mul_nonneg (show (0:ℝ) ≤ -↑I.hi by linarith) (show (0:ℝ) ≤ y - ↑J.lo by linarith)]
        have h2 : (↑(I.hi * J.lo) : ℝ) ≤ ↑(max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi))) := by
          exact_mod_cast le_max_left _ _ |>.trans (le_max_right _ _)
        linarith
    · rcases le_or_lt 0 (I.lo : ℝ) with ha0 | ha0
      · -- y < 0, a ≥ 0: xy ≤ ad
        have h1 : x * y ≤ (↑(I.lo * J.hi) : ℝ) := by
          push_cast
          nlinarith [mul_nonneg (show (0:ℝ) ≤ x - ↑I.lo by linarith) (show (0:ℝ) ≤ -y by linarith),
                     mul_nonneg ha0 (show (0:ℝ) ≤ ↑J.hi - y by linarith)]
        have h2 : (↑(I.lo * J.hi) : ℝ) ≤ ↑(max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi))) := by
          exact_mod_cast le_max_right _ _ |>.trans (le_max_left _ _)
        linarith
      · -- y < 0, a < 0: xy ≤ ac
        have h1 : x * y ≤ (↑(I.lo * J.lo) : ℝ) := by
          push_cast
          nlinarith [mul_nonneg (show (0:ℝ) ≤ x - ↑I.lo by linarith) (show (0:ℝ) ≤ -y by linarith),
                     mul_nonneg (show (0:ℝ) ≤ -↑I.lo by linarith) (show (0:ℝ) ≤ y - ↑J.lo by linarith)]
        have h2 : (↑(I.lo * J.lo) : ℝ) ≤ ↑(max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi))) := by
          exact_mod_cast le_max_left _ _ |>.trans (le_max_left _ _)
        linarith

/-- Division correctness when the denominator interval is strictly positive. -/
theorem Interval.div_correct (hx : I.mem x) (hy : J.mem y)
    (hJlo : 0 < J.lo) :
    (I.div J hJlo).mem (x / y) := by
  obtain ⟨hxlo, hxhi⟩ := hx
  obtain ⟨hylo, hyhi⟩ := hy
  have hJlo_r : (0 : ℝ) < (J.lo : ℝ) := by exact_mod_cast hJlo
  have hy_pos : (0 : ℝ) < y := lt_of_lt_of_le hJlo_r hylo
  have hJhi_r : (0 : ℝ) < (J.hi : ℝ) := lt_of_lt_of_le hJlo_r (by exact_mod_cast J.valid)
  -- Since y > 0, x/y is monotone in x and antitone in y.
  -- So min/max of 4 quotients covers all cases.
  -- Reduce to mul_correct by x/y = x * (1/y) on [1/J.hi, 1/J.lo]
  constructor
  · show (↑(Interval.div I J hJlo).lo : ℝ) ≤ x / y
    simp only [Interval.div]
    -- x/y ≥ min of 4 quotients
    rcases le_or_lt 0 x with hx_nn | hx_neg
    · -- x ≥ 0: x/y ≥ I.lo/J.hi
      have h : (↑I.lo : ℝ) / ↑J.hi ≤ x / y := by
        rw [div_le_div_iff₀ hJhi_r hy_pos]
        nlinarith [mul_nonneg hx_nn (show (0:ℝ) ≤ ↑J.hi - y by linarith),
                   mul_nonneg (show (0:ℝ) ≤ x - ↑I.lo by linarith) (le_of_lt hy_pos)]
      have cast_h : (↑(I.lo / J.hi) : ℝ) = ↑I.lo / ↑J.hi := by push_cast; ring
      calc (↑(min (min (I.lo / J.lo) (I.lo / J.hi))
                  (min (I.hi / J.lo) (I.hi / J.hi))) : ℝ)
          ≤ ↑(I.lo / J.hi) := by exact_mod_cast min_le_left _ _ |>.trans (min_le_right _ _)
        _ = ↑I.lo / ↑J.hi := cast_h
        _ ≤ x / y := h
    · -- x < 0: x/y ≥ I.lo/J.lo
      have h : (↑I.lo : ℝ) / ↑J.lo ≤ x / y := by
        rw [div_le_div_iff₀ hJlo_r hy_pos]
        nlinarith [mul_nonneg (show (0:ℝ) ≤ -x by linarith)
                              (show (0:ℝ) ≤ y - ↑J.lo by linarith),
                   mul_nonneg (show (0:ℝ) ≤ x - ↑I.lo by linarith)
                              (le_of_lt hy_pos)]
      have cast_h : (↑(I.lo / J.lo) : ℝ) = ↑I.lo / ↑J.lo := by push_cast; ring
      calc (↑(min (min (I.lo / J.lo) (I.lo / J.hi))
                  (min (I.hi / J.lo) (I.hi / J.hi))) : ℝ)
          ≤ ↑(I.lo / J.lo) := by exact_mod_cast min_le_left _ _ |>.trans (min_le_left _ _)
        _ = ↑I.lo / ↑J.lo := cast_h
        _ ≤ x / y := h
  · show x / y ≤ (↑(Interval.div I J hJlo).hi : ℝ)
    simp only [Interval.div]
    rcases le_or_lt 0 x with hx_nn | hx_neg
    · -- x ≥ 0: x/y ≤ I.hi/J.lo
      have h : x / y ≤ (↑I.hi : ℝ) / ↑J.lo := by
        rw [div_le_div_iff₀ hy_pos hJlo_r]
        nlinarith [mul_nonneg (show (0:ℝ) ≤ ↑I.hi - x by linarith) (le_of_lt hy_pos),
                   mul_nonneg hx_nn (show (0:ℝ) ≤ y - ↑J.lo by linarith)]
      have cast_h : (↑(I.hi / J.lo) : ℝ) = ↑I.hi / ↑J.lo := by push_cast; ring
      calc x / y ≤ ↑I.hi / ↑J.lo := h
        _ = ↑(I.hi / J.lo) := cast_h.symm
        _ ≤ (↑(max (max (I.lo / J.lo) (I.lo / J.hi))
                    (max (I.hi / J.lo) (I.hi / J.hi))) : ℝ) := by
            exact_mod_cast le_max_left _ _ |>.trans (le_max_right _ _)
    · -- x < 0: x/y ≤ I.hi/J.hi
      have h : x / y ≤ (↑I.hi : ℝ) / ↑J.hi := by
        rw [div_le_div_iff₀ hy_pos hJhi_r]
        nlinarith [mul_nonneg (show (0:ℝ) ≤ ↑I.hi - x by linarith) (le_of_lt hy_pos),
                   mul_nonneg (show (0:ℝ) ≤ -x by linarith)
                              (show (0:ℝ) ≤ ↑J.hi - y by linarith)]
      have cast_h : (↑(I.hi / J.hi) : ℝ) = ↑I.hi / ↑J.hi := by push_cast; ring
      calc x / y ≤ ↑I.hi / ↑J.hi := h
        _ = ↑(I.hi / J.hi) := cast_h.symm
        _ ≤ (↑(max (max (I.lo / J.lo) (I.lo / J.hi))
                    (max (I.hi / J.lo) (I.hi / J.hi))) : ℝ) := by
            exact_mod_cast le_max_right _ _ |>.trans (le_max_right _ _)

theorem Interval.sq_correct (hx : I.mem x) :
    I.sq.mem (x ^ 2) := by
  rw [show x ^ 2 = x * x from by ring]
  obtain ⟨hxlo, hxhi⟩ := hx
  simp only [Interval.sq, Interval.mem]
  constructor
  · -- lower bound
    split_ifs with h1 h2
    · -- 0 ≤ I.lo
      show (↑(I.lo * I.lo) : ℝ) ≤ x * x
      push_cast
      exact mul_self_le_mul_self (by exact_mod_cast h1 : (0:ℝ) ≤ ↑I.lo) hxlo
    · -- I.hi ≤ 0
      show (↑(I.hi * I.hi) : ℝ) ≤ x * x
      push_cast
      have hhi_r : (↑I.hi : ℝ) ≤ 0 := by exact_mod_cast h2
      nlinarith [mul_self_le_mul_self (show (0:ℝ) ≤ -(↑I.hi : ℝ) by linarith)
                                       (show -(↑I.hi : ℝ) ≤ -x by linarith)]
    · -- straddles zero
      show (↑(0 : ℚ) : ℝ) ≤ x * x
      simp; exact mul_self_nonneg x
  · -- upper bound: x*x ≤ max(lo*lo, hi*hi)
    show x * x ≤ (↑(max (I.lo * I.lo) (I.hi * I.hi)) : ℝ)
    by_cases hx0 : 0 ≤ x
    · -- x ≥ 0 ⟹ x*x ≤ hi*hi
      have : x * x ≤ (↑(I.hi * I.hi) : ℝ) := by
        push_cast; nlinarith [mul_self_nonneg (↑I.hi - x)]
      calc x * x ≤ ↑(I.hi * I.hi) := this
        _ ≤ ↑(max (I.lo * I.lo) (I.hi * I.hi)) := by exact_mod_cast le_max_right _ _
    · -- x < 0 ⟹ x*x ≤ lo*lo
      push_neg at hx0
      have : x * x ≤ (↑(I.lo * I.lo) : ℝ) := by
        push_cast; nlinarith [mul_self_nonneg (x - ↑I.lo)]
      calc x * x ≤ ↑(I.lo * I.lo) := this
        _ ≤ ↑(max (I.lo * I.lo) (I.hi * I.hi)) := by exact_mod_cast le_max_left _ _

end Correctness

/-! ## §5 Square root enclosure -/

/-- Newton step for approximating √c: x ↦ (x + c/x)/2. Requires x ≠ 0. -/
def sqrtNewtonStep (c x : ℚ) : ℚ := (x + c / x) / 2

/-- k iterations of Newton's method for √c, starting from x₀. -/
def sqrtNewtonIter : ℚ → ℚ → ℕ → ℚ
  | _, x, 0 => x
  | c, x, n + 1 => sqrtNewtonStep c (sqrtNewtonIter c x n)

/-- Compute a rational upper bound for √c using Newton iteration. -/
def sqrtUpperBound (c : ℚ) (iters : ℕ := 10) : ℚ :=
  if c ≤ 0 then 0 else sqrtNewtonIter c (max 1 c) iters

/-- Compute a rational lower bound for √c using Newton iteration.
    Uses the identity: if h ≥ √c then c/h ≤ √c. -/
def sqrtLowerBound (c : ℚ) (iters : ℕ := 10) : ℚ :=
  if c ≤ 0 then 0
  else
    let h := sqrtNewtonIter c (max 1 c) iters
    c / h

/-- Certified square root enclosure.
    Given rational `lo`, `hi` with `lo² ≤ I.lo` and `I.hi ≤ hi²`
    (and `0 ≤ lo ≤ hi`), produce an interval [lo, hi] enclosing
    √x for any x ∈ I. The bounds can be obtained via `sqrtLowerBound`
    and `sqrtUpperBound`, then verified by `native_decide` or `norm_num`. -/
def Interval.sqrtEnclosure (lo hi : ℚ) (hle : lo ≤ hi) : Interval where
  lo := lo
  hi := hi
  valid := hle

/-- Correctness: if lo² ≤ a and b ≤ hi² (with lo, hi ≥ 0),
    then for any x ∈ [a,b] with x ≥ 0, we have √x ∈ [lo, hi]. -/
theorem Interval.sqrtEnclosure_correct
    {I : Interval} (lo hi : ℚ)
    (hlo_nn : 0 ≤ lo) (hhi_nn : 0 ≤ hi)
    (hlo_sq : lo * lo ≤ I.lo) (hhi_sq : I.hi ≤ hi * hi)
    (hle : lo ≤ hi)
    {x : ℝ} (hx : I.mem x) (_hx_nn : 0 ≤ x) :
    (Interval.sqrtEnclosure lo hi hle).mem (Real.sqrt x) := by
  obtain ⟨hxlo, hxhi⟩ := hx
  simp only [Interval.sqrtEnclosure, Interval.mem]
  constructor
  · -- lo ≤ √x: since lo² ≤ a ≤ x, √(lo²) ≤ √x, and √(lo²) = lo
    have hlo_r : (0 : ℝ) ≤ (lo : ℝ) := by exact_mod_cast hlo_nn
    have h_sq : (↑lo : ℝ) ^ 2 ≤ x := by
      have : (↑(lo * lo) : ℝ) ≤ ↑I.lo := by exact_mod_cast hlo_sq
      calc (↑lo : ℝ) ^ 2 = (↑lo : ℝ) * ↑lo := by ring
        _ = ↑(lo * lo) := by push_cast; ring
        _ ≤ ↑I.lo := this
        _ ≤ x := hxlo
    calc (↑lo : ℝ) = Real.sqrt ((↑lo : ℝ) ^ 2) := (Real.sqrt_sq hlo_r).symm
      _ ≤ Real.sqrt x := Real.sqrt_le_sqrt h_sq
  · -- √x ≤ hi: since x ≤ b ≤ hi², √x ≤ √(hi²) = hi
    have hhi_r : (0 : ℝ) ≤ (hi : ℝ) := by exact_mod_cast hhi_nn
    have h_sq : x ≤ (↑hi : ℝ) ^ 2 := by
      have : (↑I.hi : ℝ) ≤ ↑(hi * hi) := by exact_mod_cast hhi_sq
      calc x ≤ ↑I.hi := hxhi
        _ ≤ ↑(hi * hi) := this
        _ = (↑hi : ℝ) * ↑hi := by push_cast; ring
        _ = (↑hi : ℝ) ^ 2 := by ring
    calc Real.sqrt x ≤ Real.sqrt ((↑hi : ℝ) ^ 2) := Real.sqrt_le_sqrt h_sq
      _ = (↑hi : ℝ) := Real.sqrt_sq hhi_r

/-! ## §6 Log enclosure connector -/

/-- Build an Interval from a verified log enclosure.
    Given lo < log(p) < hi (proved in PrimeLogEnclosures),
    produce the interval [lo, hi] containing log(p). -/
def logEnclosure (_p : ℕ) (lo hi : ℚ) (hle : lo ≤ hi) : Interval where
  lo := lo
  hi := hi
  valid := hle

/-- The log enclosure actually contains log(p). -/
theorem logEnclosure_mem (p : ℕ) (lo hi : ℚ) (hle : lo ≤ hi)
    (h : (lo : ℝ) < Real.log p ∧ Real.log p < (hi : ℝ)) :
    (logEnclosure p lo hi hle).mem (Real.log p) :=
  ⟨le_of_lt h.1, le_of_lt h.2⟩

/-- Build an Interval from A2CertificateData's breakpoint enclosures.
    Encodes lo_num/10^9 ≤ log(p) ≤ hi_num/10^9. -/
def intervalFromEnclosure (lo_num hi_num : ℕ) (h : lo_num ≤ hi_num) : Interval where
  lo := (lo_num : ℚ) / 10^9
  hi := (hi_num : ℚ) / 10^9
  valid := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast h

/-! ## §7 Tests -/

-- Test 1: [1/3, 1/2] + [1/4, 1/3] = [7/12, 5/6]
#eval
  let I : Interval := ⟨1/3, 1/2, by norm_num⟩
  let J : Interval := ⟨1/4, 1/3, by norm_num⟩
  let R := I.add J
  (R.lo, R.hi)  -- expect (7/12, 5/6)

-- Test 2: [2, 3] * [4, 5] = [8, 15]
#eval
  let I : Interval := ⟨2, 3, by norm_num⟩
  let J : Interval := ⟨4, 5, by norm_num⟩
  let R := I.mul J
  (R.lo, R.hi)  -- expect (8, 15)

-- Test 3: [-1, 2]² = [0, 4]
#eval
  let I : Interval := ⟨-1, 2, by norm_num⟩
  let R := I.sq
  (R.lo, R.hi)  -- expect (0, 4)

-- Test 4: [2, 3] / [4, 5] = [2/5, 3/4]
#eval
  let I : Interval := ⟨2, 3, by norm_num⟩
  let J : Interval := ⟨4, 5, by norm_num⟩
  let R := I.div J (by norm_num)
  (R.lo, R.hi)  -- expect (2/5, 3/4)

-- Test 5: [1, 3] - [2, 4] = [-3, 1]
#eval
  let I : Interval := ⟨1, 3, by norm_num⟩
  let J : Interval := ⟨2, 4, by norm_num⟩
  let R := I.sub J
  (R.lo, R.hi)  -- expect (-3, 1)

-- Test 6: -[-3, 2] = [-2, 3]
#eval
  let I : Interval := ⟨-3, 2, by norm_num⟩
  let R := I.neg
  (R.lo, R.hi)  -- expect (-2, 3)

-- Test 7: Breakpoint enclosure for prime 2 (lo=693147180, hi=693147181)
#eval
  let I := intervalFromEnclosure 693147180 693147181 (by norm_num)
  (I.lo, I.hi)  -- expect (693147180/10^9, 693147181/10^9)

-- Test 8: √[4, 9] via Newton: sqrtLowerBound 4 ≈ 2, sqrtUpperBound 9 ≈ 3
#eval
  let lo := sqrtLowerBound 4
  let hi := sqrtUpperBound 9
  (lo, hi)  -- expect (2, 3) exactly (Newton converges for perfect squares)

-- Test 9: √[2, 3] via Newton — verify postconditions lo² ≤ 2 and 3 ≤ hi²
#eval
  let lo := sqrtLowerBound 2
  let hi := sqrtUpperBound 3
  (decide (lo * lo ≤ 2), decide (3 ≤ hi * hi))  -- expect (true, true)

end Goldbach
