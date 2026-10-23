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

open Matrix Finset

theorem SmaleNinth.abs_det_le_factorial_mul_pow {r : ℕ} (U : ℕ)
    (M : Matrix (Fin r) (Fin r) ℤ) (hM : ∀ i j, |M i j| ≤ (U : ℤ)) :
    |M.det| ≤ (r.factorial : ℤ) * (U : ℤ) ^ r := by
  classical
  rw [Matrix.det_apply]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ σ : Equiv.Perm (Fin r),
      |(Equiv.Perm.sign σ : ℤ) • ∏ i, M (σ i) i| ≤ (U : ℤ) ^ r := by
    intro σ
    have h1 : |(Equiv.Perm.sign σ : ℤ) • ∏ i, M (σ i) i| = |∏ i, M (σ i) i| := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
        simp [h, abs_neg]
    rw [h1, Finset.abs_prod]
    calc ∏ i, |M (σ i) i| ≤ ∏ _i : Fin r, (U : ℤ) :=
          Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) (fun i _ => hM _ _)
      _ = (U : ℤ) ^ r := by simp
  refine le_trans (Finset.sum_le_sum (fun σ _ => hterm σ)) ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

end MWIS.IntegerFeasibility

end
