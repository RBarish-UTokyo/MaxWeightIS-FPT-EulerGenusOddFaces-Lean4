module

public import Mathlib

/-!
# Integer linear feasibility bounds

Adapted from the Apache-2.0 Formalpedia development, commit
07bfe4bbb3858db507bb6ac0d725951c228119fc.
Prepared 2026-10-23.
-/

@[expose] public section

namespace MWIS.IntegerFeasibility

namespace LinearOptimization

def polyhedron {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    Set (Fin n → ℝ) := {x | b ≤ A.mulVec x}

end LinearOptimization

open Matrix LinearOptimization

namespace SmaleNinth

/-- The Khachiyan perturbation `ε = 1 / (2 (n+1) (n+1)! U^(n+1))` for a
system in `n` variables with integer entries bounded by `U`. -/
noncomputable def khachiyanEps (n U : ℕ) : ℝ :=
  1 / (2 * ((n : ℝ) + 1) * ((n + 1).factorial : ℝ) * (U : ℝ) ^ (n + 1))

/-- The Khachiyan box radius `M = n!·U^n + 1`: a nonempty system with data
bounded by `U` has a solution of sup-norm at most `M − 1`. -/
noncomputable def khachiyanBox (n U : ℕ) : ℝ :=
  (n.factorial : ℝ) * (U : ℝ) ^ n + 1

/-- The constraint matrix of the perturbed-and-boxed system: the rows of
`A` (cast to `ℝ`), then `I` (the constraints `x_j ≥ −M`), then `−I` (the
constraints `−x_j ≥ −M`). -/
noncomputable def khachiyanSystemA {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    Matrix (Fin (m + n + n)) (Fin n) ℝ :=
  fun i j =>
    if h : (i : ℕ) < m then (A ⟨(i : ℕ), h⟩ j : ℝ)
    else if (i : ℕ) < m + n then (if (j : ℕ) = (i : ℕ) - m then 1 else 0)
    else (if (j : ℕ) = (i : ℕ) - m - n then -1 else 0)

/-- The right-hand side of the perturbed-and-boxed system: `b_i − ε` on the
original rows, `−M` on all `2n` box rows. -/
noncomputable def khachiyanSystemb {m : ℕ} (n U : ℕ) (b : Fin m → ℤ) :
    Fin (m + n + n) → ℝ :=
  fun i =>
    if h : (i : ℕ) < m then (b ⟨(i : ℕ), h⟩ : ℝ) - khachiyanEps n U
    else -(khachiyanBox n U)

/-- The volume lower bound `v = (ε/(nU))^n` for the nonempty case. -/
noncomputable def khachiyanVolLB (n U : ℕ) : ℝ :=
  (khachiyanEps n U / ((n : ℝ) * (U : ℝ))) ^ n

/-- The enclosing-ball radius `r = (n+1)·M` for the perturbed-and-boxed
system. -/
noncomputable def khachiyanRadius (n U : ℕ) : ℝ :=
  ((n : ℝ) + 1) * khachiyanBox n U


end SmaleNinth

end MWIS.IntegerFeasibility

end
