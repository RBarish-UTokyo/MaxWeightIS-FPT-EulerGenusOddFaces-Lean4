module

public import MWIS.AlgorithmRounding
public import Mathlib.Data.Nat.Sqrt

/-!
# Rational square-root intervals on a dyadic grid

Prepared 2026-10-23.

Integer square root and flooring produce two explicit rational endpoints.
Their squares enclose any nonnegative rational input, their distance is one
grid unit, and their numerator lengths have a linear bound. In particular,
these operations do not use an exact real square-root primitive.
-/

@[expose] public section

namespace MWIS.AlgorithmSqrt

/-- Integer numerator of a dyadic lower approximation to a rational square root. -/
def numerator (k : ℕ) (q : ℚ) : ℕ := Nat.sqrt ⌊q * (2 ^ k) ^ 2⌋₊

/-- Lower dyadic endpoint. -/
def lower (k : ℕ) (q : ℚ) : ℚ := (numerator k q : ℚ) / 2 ^ k

/-- Upper dyadic endpoint; it is strictly positive even at input zero. -/
def upper (k : ℕ) (q : ℚ) : ℚ := (numerator k q + 1 : ℕ) / 2 ^ k

theorem lower_nonnegative (k : ℕ) (q : ℚ) : 0 ≤ lower k q := by
  unfold lower
  positivity

theorem upper_positive (k : ℕ) (q : ℚ) : 0 < upper k q := by
  unfold upper
  positivity

/-- The two rational endpoints are exactly one grid unit apart. -/
theorem endpoint_width (k : ℕ) (q : ℚ) : upper k q - lower k q = 1 / 2 ^ k := by
  simp only [upper, lower, Nat.cast_add, Nat.cast_one]
  ring

/-- Squaring the lower endpoint gives a lower bound on the input. -/
theorem lower_sq_le (k : ℕ) (q : ℚ) (hq : 0 ≤ q) : (lower k q) ^ 2 ≤ q := by
  have hpos : (0 : ℚ) < (2 ^ k) ^ 2 := by positivity
  have hf := Nat.floor_le (mul_nonneg hq (sq_nonneg ((2 : ℚ) ^ k)))
  have hs : (numerator k q : ℚ) ^ 2 ≤ (⌊q * (2 ^ k) ^ 2⌋₊ : ℚ) := by
    let t : ℕ := ⌊q * ((2 : ℚ) ^ k) ^ 2⌋₊
    have hs : (t.sqrt : ℚ) ^ 2 ≤ t := by exact_mod_cast Nat.sqrt_le' t
    exact hs
  unfold lower
  rw [div_pow]
  exact (div_le_iff₀ hpos).mpr (hs.trans hf)

/-- Squaring the upper endpoint gives a strict upper bound on the input. -/
theorem lt_upper_sq (k : ℕ) (q : ℚ) : q < (upper k q) ^ 2 := by
  have hpos : (0 : ℚ) < (2 ^ k) ^ 2 := by positivity
  have hf := Nat.lt_floor_add_one (q * ((2 : ℚ) ^ k) ^ 2)
  have hs : (⌊q * (2 ^ k) ^ 2⌋₊ : ℚ) + 1 ≤ (numerator k q + 1 : ℕ) ^ 2 := by
    let t : ℕ := ⌊q * ((2 : ℚ) ^ k) ^ 2⌋₊
    have hs : (t : ℚ) + 1 ≤ ((t.sqrt + 1 : ℕ) : ℚ) ^ 2 := by
      exact_mod_cast Nat.succ_le_succ_sqrt' t
    exact hs
  unfold upper
  rw [div_pow]
  exact (lt_div_iff₀ hpos).mpr (hf.trans_le hs)

/-- A fully rational specification of the square-root interval computation. -/
theorem interval_spec (k : ℕ) (q : ℚ) (hq : 0 ≤ q) :
    0 ≤ lower k q ∧ (lower k q) ^ 2 ≤ q ∧ q < (upper k q) ^ 2 ∧
      upper k q - lower k q = 1 / 2 ^ k :=
  ⟨lower_nonnegative k q, lower_sq_le k q hq, lt_upper_sq k q, endpoint_width k q⟩

/-- The lower numerator is bounded by the magnitude scale times the grid scale. -/
theorem numerator_le (k B : ℕ) (q : ℚ) (hq : q ≤ (2 ^ B) ^ 2) :
    numerator k q ≤ 2 ^ (k + B) := by
  have hbound : q * ((2 : ℚ) ^ k) ^ 2 ≤ (2 ^ (k + B) : ℕ) ^ 2 := by
    calc
      q * ((2 : ℚ) ^ k) ^ 2 ≤ ((2 : ℚ) ^ B) ^ 2 * ((2 : ℚ) ^ k) ^ 2 :=
        mul_le_mul_of_nonneg_right hq (sq_nonneg _)
      _ = _ := by push_cast; rw [pow_add]; ring
  have hf : ⌊q * ((2 : ℚ) ^ k) ^ 2⌋₊ ≤ (2 ^ (k + B)) ^ 2 := by
    by_cases hq0 : 0 ≤ q
    · have hcast := (Nat.floor_le (mul_nonneg hq0 (sq_nonneg ((2 : ℚ) ^ k)))).trans hbound
      exact_mod_cast hcast
    · have hn : q * ((2 : ℚ) ^ k) ^ 2 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (le_of_lt (lt_of_not_ge hq0)) (sq_nonneg _)
      rw [Nat.floor_of_nonpos hn]
      omega
  calc
    numerator k q ≤ Nat.sqrt ((2 ^ (k + B)) ^ 2) := Nat.sqrt_le_sqrt hf
    _ = _ := Nat.sqrt_eq' _

/-- The lower endpoint's stored numerator has linear binary length. -/
theorem numerator_size (k B : ℕ) (q : ℚ) (hq : q ≤ (2 ^ B) ^ 2) :
    (numerator k q).size ≤ k + B + 1 := by
  simpa only [Nat.size_pow] using Nat.size_le_size (numerator_le k B q hq)

/-- The upper endpoint's stored numerator needs at most one additional bit. -/
theorem upper_numerator_size (k B : ℕ) (q : ℚ) (hq : q ≤ (2 ^ B) ^ 2) :
    (numerator k q + 1).size ≤ k + B + 2 := by
  have hn := numerator_le k B q hq
  apply Nat.size_le.mpr
  have hp : 1 ≤ (2 : ℕ) ^ (k + B) := Nat.one_le_pow _ _ (by omega)
  rw [show k + B + 2 = (k + B) + 2 from rfl, Nat.pow_add 2 (k + B) 2]
  norm_num
  omega

/-- Inverting the positive upper endpoint gives a safe rational inverse-square-root
approximation: multiplying its square by a nonnegative input stays below one. -/
theorem inverse_upper_safe (k : ℕ) (q : ℚ) (hq : 0 ≤ q) :
    0 ≤ q * (upper k q)⁻¹ ^ 2 ∧ q * (upper k q)⁻¹ ^ 2 < 1 := by
  have hp := upper_positive k q
  refine ⟨mul_nonneg hq (sq_nonneg _), ?_⟩
  have h := mul_lt_mul_of_pos_right (lt_upper_sq k q) (sq_pos_of_pos (inv_pos.mpr hp))
  have he : (upper k q) ^ 2 * (upper k q)⁻¹ ^ 2 = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ (ne_of_gt hp), one_pow]
  exact h.trans_eq he

end MWIS.AlgorithmSqrt
