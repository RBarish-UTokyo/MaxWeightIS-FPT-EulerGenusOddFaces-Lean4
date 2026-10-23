module

public import MWIS.IntegerFeasibilitySolver

/-!
# Integer linear feasibility in every finite dimension

Two unused coordinates put every input in the dimension range of the
rounded ellipsoid theorem. Padding preserves feasibility and coefficient
bounds, so the executable wrapper has no dimension restriction.

Prepared 2026-10-23.
-/

@[expose] public section
namespace MWIS.IntegerFeasibilityGeneral

open Matrix
open scoped BigOperators
open IntegerFeasibility.LinearOptimization

/-- Append two zero columns to an integer inequality matrix. -/
def paddedMatrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    Matrix (Fin m) (Fin (n + 2)) ℤ := fun i => Fin.addCases (A i) (fun _ => 0)

/-- Append two zero coordinates to a real solution. -/
def paddedVector {n : ℕ} (x : Fin n → ℝ) : Fin (n + 2) → ℝ :=
  Fin.addCases x (fun _ => 0)

/-- The padded system evaluates precisely on the original coordinates. -/
theorem padded_mulVec {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (y : Fin (n + 2) → ℝ) (i : Fin m) :
    ((paddedMatrix A).map (Int.cast : ℤ → ℝ)).mulVec y i =
      (A.map (Int.cast : ℤ → ℝ)).mulVec (fun j => y (Fin.castAdd 2 j)) i := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_add, paddedMatrix]

/-- Adding unused coordinates preserves real feasibility in both directions. -/
theorem padded_feasibility_iff {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) :
    (polyhedron ((paddedMatrix A).map (Int.cast : ℤ → ℝ)) (fun i => (b i : ℝ))).Nonempty ↔
      (polyhedron (A.map (Int.cast : ℤ → ℝ)) (fun i => (b i : ℝ))).Nonempty := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨fun j => y (Fin.castAdd 2 j), fun i => ?_⟩
    rw [← padded_mulVec A y i]
    exact hy i
  · rintro ⟨x, hx⟩
    refine ⟨paddedVector x, fun i => ?_⟩
    rw [padded_mulVec]
    simpa [paddedVector] using hx i

/-- Padding introduces only zero coefficients. -/
theorem padded_abs_le {m n : ℕ} (U : ℕ) (A : Matrix (Fin m) (Fin n) ℤ)
    (hA : ∀ i j, |A i j| ≤ (U : ℤ)) (i : Fin m) (j : Fin (n + 2)) :
    |paddedMatrix A i j| ≤ (U : ℤ) := by
  refine Fin.addCases (fun r => ?_) (fun r => ?_) j
  · simpa [paddedMatrix] using hA i r
  · simp [paddedMatrix]

/-- A Boolean linear-feasibility program defined for every finite dimension. -/
def feasible {m n : ℕ} (U B : ℕ) (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) : Bool :=
  IntegerFeasibilitySolver.feasible U B (paddedMatrix A) b

/-- Unconditional dimension-independent correctness of the executable solver,
under only the stated input coefficient bounds. -/
theorem feasible_iff {m n : ℕ} (U B : ℕ) (hU : 1 ≤ U)
    (hUB : (U : ℝ) ≤ 2 ^ B) (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (hA : ∀ i j, |A i j| ≤ (U : ℤ)) (hb : ∀ i, |b i| ≤ (U : ℤ)) :
    feasible U B A b = true ↔
      (polyhedron (A.map (Int.cast : ℤ → ℝ)) (fun i => (b i : ℝ))).Nonempty := by
  exact (IntegerFeasibilitySolver.feasible_iff (by omega : 2 ≤ n + 2)
    U B hU hUB (paddedMatrix A) b (padded_abs_le U A hA) hb).trans
      (padded_feasibility_iff A b)

end MWIS.IntegerFeasibilityGeneral
end
