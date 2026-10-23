module

public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Nat.Size
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

/-!
# Finite dyadic rounding for rational computations

Prepared 2026-10-23.

The stored numerator is obtained by integer flooring. The lemmas bound the
rounding error, the stored numerator length, and the error of a finite linear
functional. These are finite rational statements; no real-arithmetic step is
assigned a bit cost.
-/

@[expose] public section

namespace MWIS.AlgorithmRounding

open scoped BigOperators

/-- A dyadic value with an explicit integer numerator and common grid precision. -/
def dyadic (k : ℕ) (a : ℤ) : ℚ := (a : ℚ) / 2 ^ k

/-- Downward rounding stores the integer floor after scaling to the dyadic grid. -/
def roundNumerator (k : ℕ) (q : ℚ) : ℤ := ⌊q * 2 ^ k⌋

/-- The rational value represented by the rounded numerator. -/
def roundDown (k : ℕ) (q : ℚ) : ℚ := dyadic k (roundNumerator k q)

/-- Rounding is implemented by division of integer numerator data. -/
theorem roundNumerator_eq_div (k : ℕ) (q : ℚ) :
    roundNumerator k q = (q * 2 ^ k).num / (q * 2 ^ k).den := by
  exact Rat.floor_def _

/-- Downward rounding never increases the value. -/
theorem roundDown_le (k : ℕ) (q : ℚ) : roundDown k q ≤ q := by
  have hpos : (0 : ℚ) < 2 ^ k := pow_pos (by norm_num) _
  exact (div_le_iff₀ hpos).mpr (Int.floor_le (q * 2 ^ k))

/-- The error is strictly less than one unit of the dyadic grid. -/
theorem roundDown_error (k : ℕ) (q : ℚ) :
    0 ≤ q - roundDown k q ∧ q - roundDown k q < 1 / 2 ^ k := by
  have hpos : (0 : ℚ) < 2 ^ k := pow_pos (by norm_num) _
  refine ⟨sub_nonneg.mpr (roundDown_le k q), ?_⟩
  have hf := Int.lt_floor_add_one (q * 2 ^ k)
  change q - ((⌊q * 2 ^ k⌋ : ℤ) : ℚ) / 2 ^ k < 1 / 2 ^ k
  apply (lt_div_iff₀ hpos).mpr
  rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt hpos)]
  linarith

/-- Absolute error form, useful for matrices and arbitrary signed coefficients. -/
theorem abs_roundDown_error (k : ℕ) (q : ℚ) :
    |roundDown k q - q| < 1 / 2 ^ k := by
  rw [abs_sub_comm, abs_of_nonneg (roundDown_error k q).1]
  exact (roundDown_error k q).2

/-- A magnitude bound controls the finite numerator stored on the grid. -/
theorem roundNumerator_abs_le (k : ℕ) (q R : ℚ) (hq : |q| ≤ R) :
    |(roundNumerator k q : ℚ)| ≤ R * 2 ^ k + 1 := by
  have hpos : (0 : ℚ) < 2 ^ k := pow_pos (by norm_num) _
  have hq' := abs_le.mp hq
  have hlo := mul_le_mul_of_nonneg_right hq'.1 hpos.le
  have hhi := mul_le_mul_of_nonneg_right hq'.2 hpos.le
  have hflo := Int.lt_floor_add_one (q * 2 ^ k)
  have hfhi := Int.floor_le (q * 2 ^ k)
  unfold roundNumerator
  apply abs_le.mpr
  constructor <;> linarith

/-- Bounded magnitudes have a linear-size stored dyadic numerator. -/
theorem roundNumerator_size (k B : ℕ) (q : ℚ) (hq : |q| ≤ 2 ^ B) :
    (roundNumerator k q).natAbs.size ≤ k + B + 2 := by
  have habs := roundNumerator_abs_le k q (2 ^ B) hq
  have hnat : (roundNumerator k q).natAbs ≤ 2 ^ B * 2 ^ k + 1 := by
    have he : ((roundNumerator k q).natAbs : ℚ) = |(roundNumerator k q : ℚ)| := by
      rw [← Int.cast_abs]
      exact congrArg (fun z : ℤ => (z : ℚ)) (Int.natCast_natAbs (roundNumerator k q))
    rw [← he] at habs
    exact_mod_cast habs
  apply Nat.size_le.mpr
  calc
    (roundNumerator k q).natAbs ≤ 2 ^ B * 2 ^ k + 1 := hnat
    _ < 2 ^ (k + B + 2) := by
      have hp : 1 ≤ (2 : ℕ) ^ (k + B) := Nat.one_le_pow _ _ (by omega)
      rw [← pow_add, Nat.add_comm B k, show k + B + 2 = (k + B) + 2 from rfl,
        Nat.pow_add 2 (k + B) 2]
      norm_num
      omega

/-- Rounding a vector changes any bounded-coefficient linear functional by a
controlled amount; signs of coefficients and coordinates are unrestricted. -/
theorem linear_error {V : Type*} [Fintype V]
    (k : ℕ) (a x : V → ℚ) (R : ℚ) (ha : ∀ v, |a v| ≤ R) :
    |(∑ v, a v * roundDown k (x v)) - ∑ v, a v * x v| ≤
      (Fintype.card V : ℚ) * R / 2 ^ k := by
  have hpos : (0 : ℚ) < 2 ^ k := pow_pos (by norm_num) _
  calc
    |(∑ v, a v * roundDown k (x v)) - ∑ v, a v * x v| =
        |∑ v, a v * (roundDown k (x v) - x v)| := by
      rw [← Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro v _
      ring
    _ ≤ ∑ v, |a v * (roundDown k (x v) - x v)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _v : V, R * (1 / 2 ^ k) := by
      apply Finset.sum_le_sum
      intro v _
      rw [abs_mul]
      exact mul_le_mul (ha v) (abs_roundDown_error k (x v)).le (abs_nonneg _) 
        ((abs_nonneg _).trans (ha v))
    _ = (Fintype.card V : ℚ) * R / 2 ^ k := by simp; ring

/-- A row with sufficient slack stays feasible after every coordinate is rounded. -/
theorem linear_feasible_after_rounding {V : Type*} [Fintype V]
    (k : ℕ) (a x : V → ℚ) (R b : ℚ) (ha : ∀ v, |a v| ≤ R)
    (hslack : (∑ v, a v * x v) + (Fintype.card V : ℚ) * R / 2 ^ k ≤ b) :
    (∑ v, a v * roundDown k (x v)) ≤ b := by
  have herr := (abs_le.mp (linear_error k a x R ha)).2
  linarith

end MWIS.AlgorithmRounding
