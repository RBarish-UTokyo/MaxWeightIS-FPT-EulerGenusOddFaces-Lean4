module

public import Mathlib
public import MWIS.IntegerMinimalFace
public import MWIS.IntegerSubsystemBound

/-!
# Integer linear feasibility bounds

Adapted from the Apache-2.0 Formalpedia development, commit
07bfe4bbb3858db507bb6ac0d725951c228119fc.
Prepared 2026-10-23.
-/

@[expose] public section

namespace MWIS.IntegerFeasibility

open Matrix LinearOptimization

theorem SmaleNinth.integer_polyhedron_solution_bound {m n : ℕ} (U : ℕ) (hU : 1 ≤ U)
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (hA : ∀ i j, |A i j| ≤ (U : ℤ)) (hb : ∀ i, |b i| ≤ (U : ℤ))
    (hne : (polyhedron (A.map (Int.cast : ℤ → ℝ))
      (fun i => (b i : ℝ))).Nonempty) :
    ∃ x ∈ polyhedron (A.map (Int.cast : ℤ → ℝ)) (fun i => (b i : ℝ)),
      ∀ j, |x j| ≤ (n.factorial : ℝ) * (U : ℝ) ^ n := by
  -- a point of a minimal face, together with the constraints tight on that face
  obtain ⟨x, I, hxP, hxTight, hIsub⟩ :=
    SmaleNinth.exists_minimal_face_point (A.map (Int.cast : ℤ → ℝ))
      (fun i => (b i : ℝ)) hne
  -- the tight subsystem is a consistent integer system, so it has a small solution
  obtain ⟨y, hySolves, hySmall⟩ :=
    SmaleNinth.integer_subsystem_solution_bound U hU A b I hA hb x hxTight
  -- every solution of the tight subsystem lies in the polyhedron
  exact ⟨y, hIsub y hySolves, hySmall⟩

end MWIS.IntegerFeasibility

end
