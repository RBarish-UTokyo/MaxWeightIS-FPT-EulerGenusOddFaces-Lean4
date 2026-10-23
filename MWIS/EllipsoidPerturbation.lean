module

public import MWIS.EllipsoidGeometry

/-!
# Ellipsoid containment under controlled perturbations

Quadratic-form domination gives containment of shape-matrix ellipsoids.
A centre displacement bounded in the inverse-shape metric is absorbed by
an explicit scalar inflation. These results connect rational rounding to
exact central-cut geometry.
Prepared 2026-10-23.
-/

@[expose] public section

namespace MWIS.EllipsoidPerturbation

open Matrix MeasureTheory
open MWIS.EllipsoidGeometry

/-- Symmetry of the real bilinear form associated with a positive-definite matrix. -/
theorem symmetric_form {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ) (hD : D.PosDef)
    (x y : Fin n → ℝ) : x ⬝ᵥ D.mulVec y = y ⬝ᵥ D.mulVec x := by
  have hDt : Dᵀ = D := by
    simpa [Matrix.IsHermitian, Matrix.conjTranspose_apply] using hD.isHermitian.eq
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hDt, dotProduct_comm]

/-- Inverse quadratic forms reverse the order of positive-definite forms. -/
theorem inverse_form_antitone {n : ℕ} (A D : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (hD : D.PosDef)
    (hAD : ∀ v, v ⬝ᵥ A.mulVec v ≤ v ⬝ᵥ D.mulVec v)
    (x : Fin n → ℝ) : x ⬝ᵥ D⁻¹.mulVec x ≤ x ⬝ᵥ A⁻¹.mulVec x := by
  let u := D⁻¹.mulVec x
  let w := A⁻¹.mulVec x
  have hu : D.mulVec u = x := by
    dsimp [u]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).mp hD.isUnit), Matrix.one_mulVec]
  have hw : A.mulVec w = x := by
    dsimp [w]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit), Matrix.one_mulVec]
  have hp := hA.posSemidef.dotProduct_mulVec_nonneg (w - u)
  simp only [star_trivial, Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub] at hp
  rw [symmetric_form A hA w u, hw] at hp
  have hle := hAD u
  rw [hu] at hle
  change x ⬝ᵥ u ≤ x ⬝ᵥ w
  rw [dotProduct_comm x u, dotProduct_comm x w]
  linarith

/-- Increasing the positive-definite shape contains the original ellipsoid. -/
theorem ellipsoid_monotone {n : ℕ} (z : Fin n → ℝ)
    (A D : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (hD : D.PosDef)
    (hAD : ∀ v, v ⬝ᵥ A.mulVec v ≤ v ⬝ᵥ D.mulVec v) :
    ellipsoid z A ⊆ ellipsoid z D := by
  intro x hx
  exact (inverse_form_antitone A D hA hD hAD (x - z)).trans hx

/-- Scalar inflation has the expected inverse matrix. -/
theorem inverse_smul {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ) (hD : D.PosDef)
    (s : ℝ) (hs : s ≠ 0) : (s • D)⁻¹ = s⁻¹ • D⁻¹ := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.nonsing_inv_mul _
    ((Matrix.isUnit_iff_isUnit_det _).mp hD.isUnit), smul_smul,
    inv_mul_cancel₀ hs, one_smul]

/-- A controlled centre displacement is absorbed by a squared scalar inflation. -/
theorem center_perturbation {n : ℕ} (z δ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin n) ℝ) (hD : D.PosDef)
    (ε : ℝ) (hε : 0 < ε)
    (hδ : δ ⬝ᵥ D⁻¹.mulVec δ ≤ ε ^ 2) :
    ellipsoid z D ⊆ ellipsoid (z + δ) ((1 + ε) ^ 2 • D) := by
  intro x hx
  let u := x - z
  have hu : u ⬝ᵥ D⁻¹.mulVec u ≤ 1 := hx
  have hp := hD.inv.posSemidef.dotProduct_mulVec_nonneg (ε • u + δ)
  simp only [star_trivial, Matrix.mulVec_add, Matrix.mulVec_smul,
    add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
    smul_eq_mul] at hp
  rw [symmetric_form D⁻¹ hD.inv δ u] at hp
  have hcross : -ε ≤ u ⬝ᵥ D⁻¹.mulVec δ := by
    have hsmall := mul_le_mul_of_nonneg_left hu (sq_nonneg ε)
    nlinarith
  have hq : (u - δ) ⬝ᵥ D⁻¹.mulVec (u - δ) ≤ (1 + ε) ^ 2 := by
    simp only [Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub]
    rw [symmetric_form D⁻¹ hD.inv δ u]
    nlinarith
  have hs : 0 < (1 + ε) ^ 2 := sq_pos_of_pos (by linarith)
  change (x - (z + δ)) ⬝ᵥ ((1 + ε) ^ 2 • D)⁻¹.mulVec (x - (z + δ)) ≤ 1
  have hv : x - (z + δ) = u - δ := by dsimp [u]; abel
  rw [hv, inverse_smul D hD _ hs.ne', Matrix.smul_mulVec, dotProduct_smul,
    smul_eq_mul, inv_mul_eq_div]
  exact (div_le_one hs).mpr hq

/-- Combining centre correction and form domination yields containment in a
rounded positive-definite shape. -/
theorem center_and_shape_perturbation {n : ℕ} (z δ : Fin n → ℝ)
    (A D : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (hD : D.PosDef)
    (ε : ℝ) (hε : 0 < ε)
    (hδ : δ ⬝ᵥ A⁻¹.mulVec δ ≤ ε ^ 2)
    (hAD : ∀ v, (1 + ε) ^ 2 * (v ⬝ᵥ A.mulVec v) ≤ v ⬝ᵥ D.mulVec v) :
    ellipsoid z A ⊆ ellipsoid (z + δ) D := by
  apply (center_perturbation z δ A hA ε hε hδ).trans
  apply ellipsoid_monotone _ _ D (hA.smul (sq_pos_of_pos (by linarith))) hD
  intro v
  simpa only [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] using hAD v

/-- Inflating every semiaxis by a positive scalar multiplies volume by its
`n`th power. Centres do not affect the volume. -/
theorem volume_smul_square {n : ℕ} (z z' : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin n) ℝ) (hD : D.PosDef)
    (s : ℝ) (hs : 0 < s) :
    volume (ellipsoid z' (s ^ 2 • D)) =
      ENNReal.ofReal (s ^ n) * volume (ellipsoid z D) := by
  rw [ellipsoid_volume_formula _ _ (hD.smul (sq_pos_of_pos hs)),
    ellipsoid_volume_formula z D hD, Matrix.det_smul, Fintype.card_fin]
  rw [show (s ^ 2) ^ n = (s ^ n) ^ 2 by rw [← pow_mul, ← pow_mul, Nat.mul_comm],
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (pow_nonneg hs.le _),
    ENNReal.ofReal_mul (pow_nonneg hs.le _), mul_assoc]

/-- A relative quadratic upper bound controls the volume of a perturbed shape. -/
theorem volume_le_of_form_le {n : ℕ} (z z' : Fin n → ℝ)
    (A D : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (hD : D.PosDef)
    (s : ℝ) (hs : 0 < s)
    (hDA : ∀ v, v ⬝ᵥ D.mulVec v ≤ s ^ 2 * (v ⬝ᵥ A.mulVec v)) :
    volume (ellipsoid z' D) ≤ ENNReal.ofReal (s ^ n) * volume (ellipsoid z A) := by
  rw [← volume_smul_square z z' A hA s hs]
  apply measure_mono
  apply ellipsoid_monotone z' D _ hD (hA.smul (sq_pos_of_pos hs))
  intro v
  simpa only [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] using hDA v

/-- A small relative enlargement still leaves a uniform central-cut volume
contraction. The two squared factors allow one inflation for centre error and
one for matrix rounding. -/
theorem rounded_update_volume_le {n : ℕ} (hn : 2 ≤ n)
    (z z' : Fin n → ℝ) (A D : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (hD : D.PosDef) (a : Fin n → ℝ) (ha : a ≠ 0)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hbudget : 2 * (n : ℝ) * ε ≤ 1 / (4 * ((n : ℝ) + 1)))
    (hDA : ∀ v, v ⬝ᵥ D.mulVec v ≤
      (1 + ε) ^ 4 * (v ⬝ᵥ (ellipsoidUpdateMatrix A a).mulVec v)) :
    volume (ellipsoid z' D) ≤
      ENNReal.ofReal (Real.exp (-(1 : ℝ) / (4 * ((n : ℝ) + 1)))) *
        volume (ellipsoid z A) := by
  have hε1 : 0 < 1 + ε := by linarith
  let s : ℝ := (1 + ε) ^ 2
  have hs : 0 < s := sq_pos_of_pos hε1
  have hshape : volume (ellipsoid z' D) ≤
      ENNReal.ofReal (s ^ n) *
        volume (ellipsoid (ellipsoidUpdateCenter z A a) (ellipsoidUpdateMatrix A a)) := by
    apply volume_le_of_form_le _ z' _ D (update_positive hn A hA a ha) hD s hs
    intro v
    simpa only [s, ← pow_mul] using hDA v
  have hpow : s ^ n ≤ Real.exp (2 * (n : ℝ) * ε) := by
    have he : 1 + ε ≤ Real.exp ε := by simpa [add_comm] using Real.add_one_le_exp ε
    have hp := pow_le_pow_left₀ hε1.le he (2 * n)
    rw [← Real.exp_nat_mul] at hp
    simpa only [s, ← pow_mul, Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using hp
  have hfactor : s ^ n * Real.exp (-(1 : ℝ) / (2 * ((n : ℝ) + 1))) ≤
      Real.exp (-(1 : ℝ) / (4 * ((n : ℝ) + 1))) := by
    calc
      _ ≤ Real.exp (2 * (n : ℝ) * ε) *
          Real.exp (-(1 : ℝ) / (2 * ((n : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
      _ = Real.exp (2 * (n : ℝ) * ε + -(1 : ℝ) / (2 * ((n : ℝ) + 1))) :=
        (Real.exp_add _ _).symm
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
        have hnp : 0 < (n : ℝ) + 1 := by linarith
        have heq : (1 : ℝ) / (4 * ((n : ℝ) + 1)) +
            -(1 : ℝ) / (2 * ((n : ℝ) + 1)) =
            -(1 : ℝ) / (4 * ((n : ℝ) + 1)) := by
          field_simp
          ring
        linarith
  calc
    _ ≤ ENNReal.ofReal (s ^ n) *
        volume (ellipsoid (ellipsoidUpdateCenter z A a) (ellipsoidUpdateMatrix A a)) := hshape
    _ ≤ ENNReal.ofReal (s ^ n) *
        (ENNReal.ofReal (Real.exp (-(1 : ℝ) / (2 * ((n : ℝ) + 1)))) *
          volume (ellipsoid z A)) :=
      mul_le_mul_right (update_volume_lt hn z A hA a ha).le _
    _ = ENNReal.ofReal
        (s ^ n * Real.exp (-(1 : ℝ) / (2 * ((n : ℝ) + 1)))) *
          volume (ellipsoid z A) := by
      rw [ENNReal.ofReal_mul (pow_nonneg hs.le _), mul_assoc]
    _ ≤ _ := mul_le_mul_left (ENNReal.ofReal_le_ofReal hfactor) _

/-- The fixed rational inflation used by the finite algorithm satisfies the
contraction budget. -/
theorem inflation_budget {n : ℕ} (hn : 2 ≤ n) (ε : ℝ)
    (hε : ε ≤ 1 / (32 * ((n : ℝ) + 1) ^ 2)) :
    2 * (n : ℝ) * ε ≤ 1 / (4 * ((n : ℝ) + 1)) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnp : 0 < (n : ℝ) + 1 := by linarith
  calc
    _ ≤ 2 * (n : ℝ) * (1 / (32 * ((n : ℝ) + 1) ^ 2)) :=
      mul_le_mul_of_nonneg_left hε (by positivity)
    _ ≤ _ := by
      field_simp
      nlinarith

end MWIS.EllipsoidPerturbation

end
