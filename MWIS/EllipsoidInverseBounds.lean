module

public import MWIS.EllipsoidPerturbation

/-!
# Entry bounds for inverse ellipsoid shapes

A positive lower bound on a real symmetric quadratic form bounds every
entry of its inverse. The estimate provides a concrete precision budget
for rounding the stored centre.

Prepared 2026-10-23.
-/

@[expose] public section
namespace MWIS.EllipsoidInverseBounds

open Matrix
open scoped BigOperators

/-- A lower spectral bound becomes the reciprocal upper bound for the inverse form. -/
theorem inverse_quadratic_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (lower : ℝ) (hlower : 0 < lower)
    (hbound : ∀ v : Fin n → ℝ, lower * ∑ i, v i ^ 2 ≤ v ⬝ᵥ A.mulVec v)
    (v : Fin n → ℝ) :
    v ⬝ᵥ A⁻¹.mulVec v ≤ lower⁻¹ * ∑ i, v i ^ 2 := by
  have hI : (1 : Matrix (Fin n) (Fin n) ℝ).PosDef := Matrix.PosDef.one
  have h := EllipsoidPerturbation.inverse_form_antitone
    (lower • (1 : Matrix (Fin n) (Fin n) ℝ)) A (hI.smul hlower) hA
    (fun w => by
      rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
      simpa only [dotProduct, pow_two] using hbound w) v
  rw [EllipsoidPerturbation.inverse_smul _ hI lower hlower.ne', inv_one,
    Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul] at h
  simpa only [dotProduct, pow_two] using h

/-- Bounding all diagonal entries of a positive-semidefinite real matrix also
bounds every entry in absolute value. -/
theorem abs_entry_le_of_diagonal_le {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P.PosSemidef) (R : ℝ) (hdiag : ∀ i, P i i ≤ R) (i j : Fin n) :
    |P i j| ≤ R := by
  have hsym : P j i = P i j := by
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hP.isHermitian.eq
    simpa only [Matrix.conjTranspose_apply, star_trivial] using h
  have hp := hP.dotProduct_mulVec_nonneg (Pi.single i 1 + Pi.single j 1)
  have hm := hP.dotProduct_mulVec_nonneg (Pi.single i 1 - Pi.single j 1)
  simp only [star_trivial, Matrix.mulVec_add, Matrix.mulVec_sub,
    add_dotProduct, dotProduct_add, sub_dotProduct, dotProduct_sub,
    Matrix.mulVec_single_one, single_dotProduct, one_mul, Matrix.col_apply] at hp hm
  rw [hsym] at hp hm
  rw [abs_le]
  constructor <;> linarith [hdiag i, hdiag j]

/-- Every inverse entry is bounded by the reciprocal of a positive lower
spectral bound, with no diagonalization or eigenvector choices required. -/
theorem abs_inverse_entry_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (lower : ℝ) (hlower : 0 < lower)
    (hbound : ∀ v : Fin n → ℝ, lower * ∑ i, v i ^ 2 ≤ v ⬝ᵥ A.mulVec v)
    (i j : Fin n) : |A⁻¹ i j| ≤ lower⁻¹ := by
  apply abs_entry_le_of_diagonal_le A⁻¹ hA.inv.posSemidef lower⁻¹
  intro r
  have h := inverse_quadratic_le A hA lower hlower hbound (Pi.single r 1)
  simpa [Matrix.mulVec_single_one, single_dotProduct, Matrix.col_apply,
    Pi.single_apply] using h

end MWIS.EllipsoidInverseBounds
end
