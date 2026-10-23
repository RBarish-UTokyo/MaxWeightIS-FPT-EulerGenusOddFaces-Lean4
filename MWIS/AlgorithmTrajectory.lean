module

public import MWIS.AlgorithmEllipsoidGeometry

/-!
# Spectral lower bounds along the finite rational computation

Prepared 2026-10-23.

A deterministic continuation leaves terminal states fixed. Before termination
it is exactly the update used by the executable loop. Every continued shape
is positive definite and loses at most a factor four in any direction per
iteration, so one grid precision can be chosen for the whole finite run.
-/

@[expose] public section
namespace MWIS.AlgorithmTrajectory

open Matrix
open scoped BigOperators
open AlgorithmEllipsoid AlgorithmMatrixRounding AlgorithmEllipsoidGeometry

/-- A single continuation step, with terminal states fixed. -/
def advance {m n : ℕ} (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ)
    (k : ℕ) (ε : ℚ) (s : State n) : State n :=
  match AlgorithmSeparation.separate A b (center k s) with
  | none => s
  | some i => if A i = 0 then s else update k ε s (fun j => -A i j)

/-- The complete continued trajectory, indexed by the number of updates. -/
def trajectory {m n : ℕ} (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ)
    (k : ℕ) (ε : ℚ) (s : State n) : ℕ → State n
  | 0 => s
  | t + 1 => advance A b k ε (trajectory A b k ε s t)

/-- Negating an integer cutting row preserves its nonzero status. -/
theorem neg_normal_ne_zero {n : ℕ} (a : Fin n → ℤ) (ha : a ≠ 0) :
    (fun j => -a j) ≠ 0 := by
  intro h
  apply ha
  ext j
  have hj : -a j = 0 := congrFun h j
  exact neg_eq_zero.mp hj

/-- A continuation step preserves positive definiteness, including terminal states. -/
theorem advance_positive {m n : ℕ} (hn : 2 ≤ n)
    (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) (k : ℕ) (ε : ℚ) (hε : 0 ≤ ε)
    (s : State n) (hs : (castMatrix (shape k s)).PosDef) :
    (castMatrix (shape k (advance A b k ε s))).PosDef := by
  unfold advance
  split
  · exact hs
  · rename_i i hi
    split
    · exact hs
    · rename_i ha
      exact update_positive hn k ε hε s hs _ (neg_normal_ne_zero (A i) ha)

/-- Every continuation step retains at least one quarter of every input quadratic form. -/
theorem advance_lower {m n : ℕ} (hn : 2 ≤ n)
    (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) (k : ℕ) (ε : ℚ) (hε : 0 ≤ ε)
    (s : State n) (hs : (castMatrix (shape k s)).PosDef) (x : Fin n → ℝ) :
    (1 / 4 : ℝ) * quadratic (castMatrix (shape k s)) x ≤
      quadratic (castMatrix (shape k (advance A b k ε s))) x := by
  have hq : 0 ≤ quadratic (castMatrix (shape k s)) x := by
    rw [quadratic_eq_dotProduct]
    exact hs.posSemidef.dotProduct_mulVec_nonneg x
  unfold advance
  split
  · linarith
  · rename_i i hi
    split
    · linarith
    · rename_i ha
      exact update_lower hn k ε hε s hs _ (neg_normal_ne_zero (A i) ha) x

/-- Every shape on the continued trajectory is positive definite. -/
theorem trajectory_positive {m n : ℕ} (hn : 2 ≤ n)
    (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) (k : ℕ) (ε : ℚ) (hε : 0 ≤ ε)
    (s : State n) (hs : (castMatrix (shape k s)).PosDef) (t : ℕ) :
    (castMatrix (shape k (trajectory A b k ε s t))).PosDef := by
  induction t with
  | zero => exact hs
  | succ t ih => exact advance_positive hn A b k ε hε _ ih

/-- A uniform explicit lower spectral envelope for every continued state. -/
theorem trajectory_lower {m n : ℕ} (hn : 2 ≤ n)
    (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) (k : ℕ) (ε : ℚ) (hε : 0 ≤ ε)
    (s : State n) (hs : (castMatrix (shape k s)).PosDef) (t : ℕ) (x : Fin n → ℝ) :
    (1 / 4 : ℝ) ^ t * quadratic (castMatrix (shape k s)) x ≤
      quadratic (castMatrix (shape k (trajectory A b k ε s t))) x := by
  induction t with
  | zero => simp [trajectory]
  | succ t ih =>
      have hnext := advance_lower hn A b k ε hε _
        (trajectory_positive hn A b k ε hε s hs t) x
      have h := mul_le_mul_of_nonneg_left ih (by norm_num : (0 : ℝ) ≤ 1 / 4)
      change _ ≤ quadratic (castMatrix (shape k (advance A b k ε (trajectory A b k ε s t)))) x
      rw [pow_succ]
      nlinarith

/-- The initial dyadic shape decodes to a scalar diagonal matrix. -/
theorem initial_shape_diagonal (n k B : ℕ) :
    castMatrix (shape k (initial n k B)) =
      Matrix.diagonal (fun _ : Fin n => (2 : ℝ) ^ (2 * B)) := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [castMatrix, initial_shape, Matrix.diagonal_apply]
  · simp [castMatrix, initial_shape, Matrix.diagonal_apply, h]

/-- The initial exact Euclidean ball is positive definite in every dimension. -/
theorem initial_positive (n k B : ℕ) : (castMatrix (shape k (initial n k B))).PosDef := by
  rw [initial_shape_diagonal]
  exact Matrix.PosDef.diagonal (fun _ => by positivity)

/-- The exact quadratic form of the initial Euclidean ball. -/
theorem initial_quadratic (n k B : ℕ) (x : Fin n → ℝ) :
    quadratic (castMatrix (shape k (initial n k B))) x =
      (2 : ℝ) ^ (2 * B) * ∑ i, x i ^ 2 := by
  rw [initial_shape_diagonal, quadratic_eq_dotProduct]
  simp only [Matrix.mulVec_diagonal, dotProduct, pow_two, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The stored shape at time `t` dominates the sphere with squared radius `4^-t`.
The initial radius `2^B` is at least one. -/
theorem initial_trajectory_lower {m n : ℕ} (hn : 2 ≤ n)
    (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) (k B : ℕ) (ε : ℚ) (hε : 0 ≤ ε)
    (t : ℕ) (x : Fin n → ℝ) :
    (1 / 4 : ℝ) ^ t * (∑ i, x i ^ 2) ≤
      quadratic (castMatrix (shape k (trajectory A b k ε (initial n k B) t))) x := by
  have h := trajectory_lower hn A b k ε hε (initial n k B) (initial_positive n k B) t x
  rw [initial_quadratic] at h
  have hp : (1 : ℝ) ≤ 2 ^ (2 * B) := one_le_pow₀ (by norm_num)
  have hs : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hl : (∑ i, x i ^ 2) ≤ (2 : ℝ) ^ (2 * B) * ∑ i, x i ^ 2 := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hp hs
  exact (mul_le_mul_of_nonneg_left hl (by positivity)).trans h

/-- A nonzero integer vector has squared Euclidean length at least one. -/
theorem integer_norm_lower {n : ℕ} (a : Fin n → ℤ) (ha : a ≠ 0) :
    (1 : ℝ) ≤ ∑ i, (a i : ℝ) ^ 2 := by
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra h
    apply ha
    ext i
    simpa using not_exists.mp h i
  have hi' : 1 ≤ (a i) ^ 2 := by
    have hcases : a i ≤ -1 ∨ 1 ≤ a i := by omega
    rcases hcases with h | h <;> nlinarith
  have hiR : (1 : ℝ) ≤ (a i : ℝ) ^ 2 := by exact_mod_cast hi'
  exact hiR.trans (Finset.single_le_sum (fun j _ => sq_nonneg (a j : ℝ)) (Finset.mem_univ i))

/-- The exact rational normal square at a trajectory state has the uniform
positive lower bound required by square-root rounding. -/
theorem trajectory_normalSquare_lower {m n : ℕ} (hn : 2 ≤ n)
    (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) (k B : ℕ) (ε : ℚ) (hε : 0 ≤ ε)
    (t : ℕ) (a : Fin n → ℤ) (ha : a ≠ 0) :
    (1 / 4 : ℝ) ^ t ≤ (normalSquare (shape k (trajectory A b k ε (initial n k B) t)) a : ℝ) := by
  rw [normalSquare_cast, ← quadratic_eq_dotProduct]
  have h := initial_trajectory_lower hn A b k B ε hε t (fun i => (a i : ℝ))
  have hm := mul_le_mul_of_nonneg_left (integer_norm_lower a ha)
    (show (0 : ℝ) ≤ (1 / 4) ^ t by positivity)
  simp only [mul_one] at hm
  exact hm.trans h

/-- Exhaustion can occur only when the current separator returns a nonzero row. -/
theorem exhausted_has_cut {m n : ℕ} (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ)
    (k : ℕ) (ε : ℚ) (fuel : ℕ) (s : State n)
    (h : run A b k ε fuel s = .exhausted) :
    ∃ i, AlgorithmSeparation.separate A b (center k s) = some i ∧ A i ≠ 0 := by
  unfold run at h
  split at h
  · contradiction
  · rename_i i hi
    split at h
    · contradiction
    · rename_i ha
      exact ⟨i, hi, ha⟩

/-- Removing one unsuccessful iteration agrees with the continued-state step. -/
theorem exhausted_succ {m n : ℕ} (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ)
    (k : ℕ) (ε : ℚ) (fuel : ℕ) (s : State n)
    (h : run A b k ε (fuel + 1) s = .exhausted) :
    run A b k ε fuel (advance A b k ε s) = .exhausted := by
  obtain ⟨i, hi, ha⟩ := exhausted_has_cut A b k ε (fuel + 1) s h
  rw [run, hi] at h
  simp only [ha, ite_false] at h
  simpa only [advance, hi, ha, ite_false] using h

end MWIS.AlgorithmTrajectory
