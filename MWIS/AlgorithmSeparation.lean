module

public import MWIS.AlgorithmRational
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.List.Find

/-!
# Executable exact separation at rational points

Prepared 2026-10-23.

For an integer inequality system, a rational point is scaled by its positive
common denominator. The finite search tests only integer inequalities. It
returns no row exactly at feasible points; any returned row supplies a valid
separating halfspace. This module proves the oracle's mathematical behavior,
without assuming an optimizer or claiming a machine runtime theorem.
-/

@[expose] public section

namespace MWIS.AlgorithmSeparation

open scoped BigOperators

/-- The integer dot product used in the denominator-cleared row test. -/
def integerDot {n : ℕ} (a z : Fin n → ℤ) : ℤ := ∑ j, a j * z j

/-- The rational dot product of an integer row and a rational point. -/
def rationalDot {n : ℕ} (a : Fin n → ℤ) (x : Fin n → ℚ) : ℚ :=
  ∑ j, (a j : ℚ) * x j

/-- Feasibility for a finite family of integer upper-bound inequalities. -/
def Feasible {m n : ℕ} (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ)
    (x : Fin n → ℚ) : Prop := ∀ i, rationalDot (A i) x ≤ b i

/-- The first violated row, found using integer arithmetic after denominator clearing. -/
def separate {m n : ℕ} (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ)
    (x : Fin n → ℚ) : Option (Fin m) :=
  (List.finRange m).find? fun i => decide
    (b i * (AlgorithmRational.denominatorProduct x : ℤ) <
      integerDot (A i) (AlgorithmRational.integerize x))

/-- Denominator clearing commutes exactly with evaluation of every integer row. -/
theorem scaled_dot {n : ℕ} (a : Fin n → ℤ) (x : Fin n → ℚ) :
    (integerDot a (AlgorithmRational.integerize x) : ℚ) =
      (AlgorithmRational.denominatorProduct x : ℚ) * rationalDot a x := by
  simp only [integerDot, rationalDot, Int.cast_sum, Int.cast_mul,
    AlgorithmRational.integerize_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The integer row comparison is equivalent to the original rational comparison. -/
theorem scaled_row_le_iff {n : ℕ} (a : Fin n → ℤ) (b : ℤ) (x : Fin n → ℚ) :
    integerDot a (AlgorithmRational.integerize x) ≤
      b * (AlgorithmRational.denominatorProduct x : ℤ) ↔ rationalDot a x ≤ b := by
  have hpos : (0 : ℚ) < AlgorithmRational.denominatorProduct x := by
    exact_mod_cast AlgorithmRational.denominatorProduct_pos x
  rw [← Int.cast_le (R := ℚ), scaled_dot, Int.cast_mul, Int.cast_natCast,
    mul_comm (b : ℚ), mul_le_mul_iff_right₀ hpos]

/-- The finite search returns `none` exactly when the point is feasible. -/
theorem separate_none_iff {m n : ℕ} (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ)
    (x : Fin n → ℚ) : separate A b x = none ↔ Feasible A b x := by
  simp only [separate, List.find?_eq_none, List.mem_finRange, decide_eq_true_eq,
    not_lt, forall_const, scaled_row_le_iff, Feasible]

/-- Every reported row is strictly violated by the queried point. -/
theorem separate_some_violated {m n : ℕ} (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ)
    (x : Fin n → ℚ) (i : Fin m) (hi : separate A b x = some i) :
    (b i : ℚ) < rationalDot (A i) x := by
  have htest := List.find?_some hi
  simp only [decide_eq_true_eq] at htest
  by_contra hn
  have hle : rationalDot (A i) x ≤ b i := le_of_not_gt hn
  have hs := (scaled_row_le_iff (A i) (b i) x).mpr hle
  omega

/-- The halfspace through the queried point contains every feasible point on its
strict side, so the reported row is a valid cut for an ellipsoid update. -/
theorem separate_halfspace {m n : ℕ} (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ)
    (x : Fin n → ℚ) (i : Fin m) (hi : separate A b x = some i)
    (y : Fin n → ℚ) (hy : Feasible A b y) :
    rationalDot (A i) y < rationalDot (A i) x :=
  (hy i).trans_lt (separate_some_violated A b x i hi)

/-- A zero reported row certifies infeasibility of the entire system. -/
theorem separate_zero_row_infeasible {m n : ℕ}
    (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) (x : Fin n → ℚ)
    (i : Fin m) (hi : separate A b x = some i) (hz : A i = 0) :
    ¬ ∃ y, Feasible A b y := by
  rintro ⟨y, hy⟩
  have hc := separate_halfspace A b x i hi y hy
  simp [hz, rationalDot] at hc

/-- Whenever the system is nonempty, a returned cut has a nonzero normal. -/
theorem separate_normal_ne_zero {m n : ℕ}
    (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) (x : Fin n → ℚ)
    (i : Fin m) (hi : separate A b x = some i) (hne : ∃ y, Feasible A b y) :
    A i ≠ 0 := fun hz => separate_zero_row_infeasible A b x i hi hz hne

end MWIS.AlgorithmSeparation
