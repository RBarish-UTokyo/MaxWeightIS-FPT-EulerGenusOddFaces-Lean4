module

public import MWIS.AlgorithmRounding
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Rat.Cast.Lemmas
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.FieldSimp

/-!
# Controlled dyadic rounding of rational shape matrices

An entrywise error of at most δ changes a quadratic form by at most
`card(V) * δ * ∑ i, v i ^ 2`. Adding that diagonal padding to an entrywise
rounded rational matrix therefore dominates the original form. The construction
uses exact rational arithmetic and preserves symmetry and strict positivity.

Prepared 2026-10-23.
-/

@[expose] public section

namespace MWIS.AlgorithmMatrixRounding

open scoped BigOperators
open MWIS.AlgorithmRounding

/-- The real quadratic form of a finite real matrix. -/
def quadratic {V : Type*} [Fintype V] (A : Matrix V V ℝ) (v : V → ℝ) : ℝ :=
  ∑ i, ∑ j, v i * A i j * v j

/-- Coordinatewise scalar inclusion of a rational matrix into real matrices. -/
def castMatrix {V : Type*} (A : Matrix V V ℚ) : Matrix V V ℝ :=
  fun i j => (A i j : ℝ)

/-- The entrywise dyadic rounding of a rational matrix. -/
def rounded {V : Type*} (k : ℕ) (A : Matrix V V ℚ) : Matrix V V ℚ :=
  fun i j => roundDown k (A i j)

/-- Rounding with a rational diagonal margin that dominates all accumulated
coordinate errors in the quadratic form. -/
def padded {V : Type*} [Fintype V] [DecidableEq V]
    (k : ℕ) (A : Matrix V V ℚ) : Matrix V V ℚ :=
  fun i j => rounded k A i j + if i = j then (Fintype.card V : ℚ) / 2 ^ k else 0

/-- Entrywise perturbations have an operator-independent quadratic bound. -/
theorem quadratic_error_bound {V : Type*} [Fintype V]
    (A D : Matrix V V ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hD : ∀ i j, |D i j - A i j| ≤ δ) (v : V → ℝ) :
    |quadratic D v - quadratic A v| ≤
      (Fintype.card V : ℝ) * δ * ∑ i, v i ^ 2 := by
  have hcs : (∑ i, |v i|) ^ 2 ≤ (Fintype.card V : ℝ) * ∑ i, v i ^ 2 := by
    simpa only [Finset.card_univ, sq_abs] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => |v i|))
  calc
    |quadratic D v - quadratic A v| = |∑ i, ∑ j, v i * (D i j - A i j) * v j| := by
      unfold quadratic
      rw [← Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ ∑ i, ∑ j, |v i| * |D i j - A i j| * |v j| := by
      calc
        _ ≤ ∑ i, |∑ j, v i * (D i j - A i j) * v j| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro i _
          simpa only [abs_mul] using
            Finset.abs_sum_le_sum_abs (fun j => v i * (D i j - A i j) * v j) Finset.univ
    _ ≤ ∑ i, ∑ j, |v i| * δ * |v j| := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hD i j) (abs_nonneg _)) (abs_nonneg _)
    _ = δ * (∑ i, |v i|) ^ 2 := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul]
      ring
    _ ≤ (Fintype.card V : ℝ) * δ * ∑ i, v i ^ 2 := by
      have h := mul_le_mul_of_nonneg_left hcs hδ
      nlinarith

/-- Dyadic entry rounding has a uniform real quadratic error bound. -/
theorem rounded_quadratic_error {V : Type*} [Fintype V]
    (k : ℕ) (A : Matrix V V ℚ) (v : V → ℝ) :
    |quadratic (castMatrix (rounded k A)) v - quadratic (castMatrix A) v| ≤
      (Fintype.card V : ℝ) / 2 ^ k * ∑ i, v i ^ 2 := by
  have h := quadratic_error_bound (castMatrix A) (castMatrix (rounded k A))
    (1 / 2 ^ k) (by positivity) (fun i j => ?_) v
  · simpa only [mul_one_div] using h
  · change |(roundDown k (A i j) : ℝ) - (A i j : ℝ)| ≤ 1 / 2 ^ k
    have hrat : ((|roundDown k (A i j) - A i j| : ℚ) : ℝ) ≤ ((1 / 2 ^ k : ℚ) : ℝ) :=
      Rat.cast_le.mpr (abs_roundDown_error k (A i j)).le
    simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_one,
      Rat.cast_pow, Rat.cast_ofNat] using hrat

/-- The added diagonal has its exact expected effect on every real direction. -/
theorem padded_quadratic {V : Type*} [Fintype V] [DecidableEq V]
    (k : ℕ) (A : Matrix V V ℚ) (v : V → ℝ) :
    quadratic (castMatrix (padded k A)) v = quadratic (castMatrix (rounded k A)) v +
      (Fintype.card V : ℝ) / 2 ^ k * ∑ i, v i ^ 2 := by
  have heq (i j : V) : castMatrix (padded k A) i j =
      castMatrix (rounded k A) i j +
        (if i = j then (Fintype.card V : ℝ) / 2 ^ k else 0) := by
    by_cases h : i = j <;> simp [castMatrix, padded, h]
  simp only [quadratic]
  simp_rw [heq, mul_add, add_mul, Finset.sum_add_distrib]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [mul_ite, pow_two, mul_comm, mul_left_comm, mul_assoc]

/-- Diagonal padding makes the rounded form dominate the original form. -/
theorem padded_dominates {V : Type*} [Fintype V] [DecidableEq V]
    (k : ℕ) (A : Matrix V V ℚ) (v : V → ℝ) :
    quadratic (castMatrix A) v ≤ quadratic (castMatrix (padded k A)) v := by
  rw [padded_quadratic]
  have h := (abs_le.mp (rounded_quadratic_error k A v)).1
  linarith

/-- The padding introduces at most twice the entrywise error allowance. -/
theorem padded_error_upper {V : Type*} [Fintype V] [DecidableEq V]
    (k : ℕ) (A : Matrix V V ℚ) (v : V → ℝ) :
    quadratic (castMatrix (padded k A)) v ≤ quadratic (castMatrix A) v +
      2 * ((Fintype.card V : ℝ) / 2 ^ k) * ∑ i, v i ^ 2 := by
  rw [padded_quadratic]
  have h := (abs_le.mp (rounded_quadratic_error k A v)).2
  linarith

/-- A lower spectral bound converts the absolute rounding allowance into a
relative bound on every real direction. -/
theorem padded_relative_bound {V : Type*} [Fintype V] [DecidableEq V]
    (k : ℕ) (A : Matrix V V ℚ) (lower ε : ℝ) (hε : 0 ≤ ε)
    (hmargin : (Fintype.card V : ℝ) / 2 ^ k ≤ ε * lower)
    (hlower : ∀ v : V → ℝ, lower * ∑ i, v i ^ 2 ≤ quadratic (castMatrix A) v)
    (v : V → ℝ) :
    quadratic (castMatrix (padded k A)) v ≤
      (1 + 2 * ε) * quadratic (castMatrix A) v := by
  have hnorm : 0 ≤ ∑ i, v i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg (v i))
  have hm := mul_le_mul_of_nonneg_right hmargin hnorm
  have hl := mul_le_mul_of_nonneg_left (hlower v) hε
  have hu := padded_error_upper k A v
  nlinarith

/-- Rounding and padding preserve matrix symmetry exactly. -/
theorem padded_symmetric {V : Type*} [Fintype V] [DecidableEq V]
    (k : ℕ) (A : Matrix V V ℚ) (hA : ∀ i j, A i j = A j i) :
    ∀ i j, padded k A i j = padded k A j i := by
  intro i j
  simp only [padded, rounded, hA i j, eq_comm]

/-- A strictly positive form remains strictly positive after rational rounding
and the proved diagonal correction. -/
theorem padded_positive {V : Type*} [Fintype V] [DecidableEq V]
    (k : ℕ) (A : Matrix V V ℚ)
    (hA : ∀ v : V → ℝ, v ≠ 0 → 0 < quadratic (castMatrix A) v) :
    ∀ v : V → ℝ, v ≠ 0 → 0 < quadratic (castMatrix (padded k A)) v := by
  intro v hv
  exact (hA v hv).trans_le (padded_dominates k A v)

/-- The corrected matrix can be stored with the same common dyadic denominator. -/
def paddedNumerator {V : Type*} [Fintype V] [DecidableEq V]
    (k : ℕ) (A : Matrix V V ℚ) (i j : V) : ℤ :=
  roundNumerator k (A i j) + if i = j then (Fintype.card V : ℤ) else 0

/-- The explicit integer numerator evaluates to the corrected rational entry. -/
theorem padded_eq_dyadic {V : Type*} [Fintype V] [DecidableEq V]
    (k : ℕ) (A : Matrix V V ℚ) (i j : V) :
    padded k A i j = dyadic k (paddedNumerator k A i j) := by
  unfold padded rounded roundDown dyadic paddedNumerator
  split_ifs <;> push_cast <;> ring

/-- Padding adds only the dimension's bit length to the stored numerator bound. -/
theorem paddedNumerator_size {V : Type*} [Fintype V] [DecidableEq V]
    (k B : ℕ) (A : Matrix V V ℚ) (hA : ∀ i j, |A i j| ≤ 2 ^ B) (i j : V) :
    (paddedNumerator k A i j).natAbs.size ≤ k + B + (Fintype.card V).size + 3 := by
  have ha := Nat.size_le.mp (roundNumerator_size k B (A i j) (hA i j))
  have hn := Nat.lt_size_self (Fintype.card V)
  let S := k + B + 2 + (Fintype.card V).size
  have ha' : (roundNumerator k (A i j)).natAbs < 2 ^ S :=
    ha.trans_le (Nat.pow_le_pow_right (by norm_num) (by dsimp [S]; omega))
  have hn' : Fintype.card V < 2 ^ S :=
    hn.trans_le (Nat.pow_le_pow_right (by norm_num) (by dsimp [S]; omega))
  have hp : (paddedNumerator k A i j).natAbs ≤
      (roundNumerator k (A i j)).natAbs + Fintype.card V := by
    by_cases hij : i = j
    · simpa [paddedNumerator, hij] using
        Int.natAbs_add_le (roundNumerator k (A i j)) (Fintype.card V)
    · simp [paddedNumerator, hij]
  apply Nat.size_le.mpr
  calc
    (paddedNumerator k A i j).natAbs ≤
        (roundNumerator k (A i j)).natAbs + Fintype.card V := hp
    _ < 2 ^ S + 2 ^ S := Nat.add_lt_add ha' hn'
    _ = 2 ^ (k + B + (Fintype.card V).size + 3) := by
      rw [show k + B + (Fintype.card V).size + 3 = S + 1 by dsimp [S]; omega,
        pow_succ]
      omega

/-- The complete matrix numerator payload has a polynomial bit bound. -/
theorem paddedNumerator_total_size {V : Type*} [Fintype V] [DecidableEq V]
    (k B : ℕ) (A : Matrix V V ℚ) (hA : ∀ i j, |A i j| ≤ 2 ^ B) :
    (∑ i, ∑ j, (paddedNumerator k A i j).natAbs.size) ≤
      (Fintype.card V) ^ 2 * (k + B + (Fintype.card V).size + 3) := by
  calc
    _ ≤ ∑ _i : V, ∑ _j : V, (k + B + (Fintype.card V).size + 3) := by
      exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ =>
        paddedNumerator_size k B A hA i j))
    _ = _ := by simp [pow_two, mul_assoc]

end MWIS.AlgorithmMatrixRounding

end
