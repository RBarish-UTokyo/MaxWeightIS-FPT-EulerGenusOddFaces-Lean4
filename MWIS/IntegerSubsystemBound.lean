module

public import Mathlib
public import MWIS.IntegerSquareSubsystem
public import MWIS.IntegerCramerBound

/-!
# Integer linear feasibility bounds

Adapted from the Apache-2.0 Formalpedia development, commit
07bfe4bbb3858db507bb6ac0d725951c228119fc.
Prepared 2026-10-23.
-/

@[expose] public section

namespace MWIS.IntegerFeasibility

open Matrix LinearOptimization

namespace SubAux

lemma submatrix_map {m n r : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (row : Fin r → Fin m) (col : Fin r → Fin n) :
    (A.map (Int.cast : ℤ → ℝ)).submatrix row col
      = (A.submatrix row col).map (Int.cast : ℤ → ℝ) := by
  ext k j
  simp [Matrix.submatrix_apply, Matrix.map_apply]

end SubAux

open SubAux

theorem SmaleNinth.integer_subsystem_solution_bound {m n : ℕ} (U : ℕ) (hU : 1 ≤ U)
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (I : Finset (Fin m))
    (hA : ∀ i j, |A i j| ≤ (U : ℤ)) (hb : ∀ i, |b i| ≤ (U : ℤ))
    (x : Fin n → ℝ)
    (hx : ∀ i ∈ I, (A.map (Int.cast : ℤ → ℝ)).mulVec x i = (b i : ℝ)) :
    ∃ y : Fin n → ℝ,
      (∀ i ∈ I, (A.map (Int.cast : ℤ → ℝ)).mulVec y i = (b i : ℝ)) ∧
      (∀ j, |y j| ≤ (n.factorial : ℝ) * (U : ℝ) ^ n) := by
  classical
  obtain ⟨r, y, row, col, hsol, hrn, hdet, hmul, hzero⟩ :=
    SmaleNinth.exists_square_subsystem (A.map (Int.cast : ℤ → ℝ))
      (fun i => (b i : ℝ)) I x hx
  refine ⟨y, hsol, ?_⟩
  -- the integer square subsystem
  set M : Matrix (Fin r) (Fin r) ℤ := A.submatrix row col with hM
  set v : Fin r → ℤ := fun k => b (row k) with hv
  have hmapsub : (A.map (Int.cast : ℤ → ℝ)).submatrix row col
      = M.map (Int.cast : ℤ → ℝ) := submatrix_map A row col
  have hdetM : M.det ≠ 0 := by
    intro hc
    rw [hmapsub] at hdet
    exact hdet (by rw [← Int.cast_det, hc]; norm_num)
  have hMbd : ∀ i j, |M i j| ≤ (U : ℤ) := fun i j => hA _ _
  have hvbd : ∀ i, |v i| ≤ (U : ℤ) := fun i => hb _
  have hmul' : (M.map (Int.cast : ℤ → ℝ)).mulVec (fun k => y (col k))
      = fun k => ((v k : ℤ) : ℝ) := by rw [← hmapsub]; exact hmul
  have hcr := SmaleNinth.cramer_solution_bound U M v hMbd hvbd hdetM _ hmul'
  -- the small bound implies the big one
  have hmono : (r.factorial : ℝ) * (U : ℝ) ^ r ≤ (n.factorial : ℝ) * (U : ℝ) ^ n := by
    have h1 : (r.factorial : ℝ) ≤ (n.factorial : ℝ) := by
      exact_mod_cast Nat.factorial_le hrn
    have h2 : (U : ℝ) ^ r ≤ (U : ℝ) ^ n := by
      refine pow_le_pow_right₀ ?_ hrn
      exact_mod_cast hU
    have hpos : (0:ℝ) ≤ (U : ℝ) ^ r := by positivity
    exact mul_le_mul h1 h2 hpos (by positivity)
  intro j
  by_cases hj : j ∈ Set.range col
  · obtain ⟨k, rfl⟩ := hj
    exact le_trans (hcr k) hmono
  · rw [hzero j hj, abs_zero]
    positivity

end MWIS.IntegerFeasibility

end
