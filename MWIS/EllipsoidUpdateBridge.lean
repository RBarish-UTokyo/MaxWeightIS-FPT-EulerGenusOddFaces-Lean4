module

public import MWIS.EllipsoidCenterRounding
public import MWIS.EllipsoidPerturbation
public import MWIS.AlgorithmEllipsoidGeometry

/-!
# Geometry of the stored rational ellipsoid update

The executable rational shape agrees with the exact real update before
inflation and rounding. Diagonal padding supplies the required lower form
bound, while the precision margin bounds the upper form distortion.

Prepared 2026-10-23.
-/

@[expose] public section
namespace MWIS.EllipsoidUpdateBridge

open Matrix
open scoped BigOperators
open AlgorithmMatrixRounding EllipsoidCenterRounding

/-- Explicit arithmetic precision conditions for a concrete stored update. -/
structure StepPrecision {n : ℕ} (k : ℕ) (ε : ℚ)
    (state : AlgorithmEllipsoid.State n) (a : Fin n → ℤ) where
  normalLower : ℝ
  inverseBound : ℝ
  shapeLower : ℝ
  normalLower_pos : 0 < normalLower
  inverseBound_nonneg : 0 ≤ inverseBound
  normalSquare_lower : normalLower ^ 2 ≤
    (AlgorithmEllipsoid.normalSquare (AlgorithmEllipsoid.shape k state) a : ℝ)
  sqrt_margin : 1 / (2 : ℝ) ^ k ≤ (n : ℝ) * ((ε : ℝ) / 2) * normalLower
  inverse_entries : ∀ i j, |(EllipsoidGeometry.ellipsoidUpdateMatrix
    (castMatrix (AlgorithmEllipsoid.shape k state)) (castNormal a))⁻¹ i j| ≤ inverseBound
  center_margin : (n : ℝ) ^ 2 * inverseBound / ((2 : ℝ) ^ k) ^ 2 ≤ ((ε : ℝ) / 2) ^ 2
  shape_margin : (n : ℝ) / 2 ^ k ≤ (ε : ℝ) * shapeLower
  enlarged_lower : ∀ v : Fin n → ℝ, shapeLower * ∑ i, v i ^ 2 ≤
    quadratic (castMatrix (AlgorithmEllipsoid.enlargedShape ε
      (AlgorithmEllipsoid.shape k state) a)) v

/-- The rational enlargement is the actual scalar enlargement of the exact shape. -/
theorem enlargedShape_cast {n : ℕ} (ε : ℚ) (D : Matrix (Fin n) (Fin n) ℚ)
    (hD : (castMatrix D).PosDef) (a : Fin n → ℤ) :
    castMatrix (AlgorithmEllipsoid.enlargedShape ε D a) =
      (1 + (ε : ℝ)) ^ 2 • EllipsoidGeometry.ellipsoidUpdateMatrix (castMatrix D) (castNormal a) := by
  unfold castNormal
  rw [← AlgorithmEllipsoidGeometry.rawShape_cast D
    (AlgorithmEllipsoidGeometry.rational_symmetric D hD) a]
  ext i j
  simp [castMatrix, AlgorithmEllipsoid.enlargedShape]

/-- The shape actually stored after updating dominates the required enlargement. -/
theorem stored_shape_dominates {n : ℕ} (k : ℕ) (ε : ℚ)
    (state : AlgorithmEllipsoid.State n) (a : Fin n → ℤ)
    (hD : (castMatrix (AlgorithmEllipsoid.shape k state)).PosDef) (v : Fin n → ℝ) :
    (1 + (ε : ℝ)) ^ 2 * (v ⬝ᵥ (EllipsoidGeometry.ellipsoidUpdateMatrix
      (castMatrix (AlgorithmEllipsoid.shape k state)) (castNormal a)).mulVec v) ≤
      v ⬝ᵥ (castMatrix (AlgorithmEllipsoid.shape k (AlgorithmEllipsoid.update k ε state a))).mulVec v := by
  rw [AlgorithmEllipsoid.update_shape]
  have h := padded_dominates k
    (AlgorithmEllipsoid.enlargedShape ε (AlgorithmEllipsoid.shape k state) a) v
  rw [quadratic_eq_dot, quadratic_eq_dot, enlargedShape_cast ε _ hD a,
    Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at h
  exact h

/-- The stored shape has a controlled multiplicative upper form bound whenever
the dyadic grid is fine enough for a lower spectral bound of the enlarged shape. -/
theorem stored_shape_upper {n : ℕ} (hn : 2 ≤ n) (k : ℕ) (ε : ℚ)
    (hε : 0 ≤ ε) (state : AlgorithmEllipsoid.State n) (a : Fin n → ℤ)
    (hD : (castMatrix (AlgorithmEllipsoid.shape k state)).PosDef) (ha : a ≠ 0)
    (lower : ℝ) (hmargin : (n : ℝ) / 2 ^ k ≤ (ε : ℝ) * lower)
    (hlower : ∀ v : Fin n → ℝ, lower * ∑ i, v i ^ 2 ≤
      quadratic (castMatrix (AlgorithmEllipsoid.enlargedShape ε
        (AlgorithmEllipsoid.shape k state) a)) v)
    (v : Fin n → ℝ) :
    v ⬝ᵥ (castMatrix (AlgorithmEllipsoid.shape k (AlgorithmEllipsoid.update k ε state a))).mulVec v ≤
      (1 + (ε : ℝ)) ^ 4 * (v ⬝ᵥ (EllipsoidGeometry.ellipsoidUpdateMatrix
        (castMatrix (AlgorithmEllipsoid.shape k state)) (castNormal a)).mulVec v) := by
  have hεR : (0 : ℝ) ≤ ε := Rat.cast_nonneg.mpr hε
  have hp : 0 ≤ v ⬝ᵥ (EllipsoidGeometry.ellipsoidUpdateMatrix
      (castMatrix (AlgorithmEllipsoid.shape k state)) (castNormal a)).mulVec v :=
    (EllipsoidGeometry.update_positive hn _ hD (castNormal a)
      (AlgorithmEllipsoidGeometry.normal_cast_ne_zero a ha)).posSemidef.dotProduct_mulVec_nonneg v
  have h := padded_relative_bound k
    (AlgorithmEllipsoid.enlargedShape ε (AlgorithmEllipsoid.shape k state) a)
    lower (ε : ℝ) hεR (by simpa using hmargin) hlower v
  rw [quadratic_eq_dot, quadratic_eq_dot, enlargedShape_cast ε _ hD a,
    Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at h
  rw [AlgorithmEllipsoid.update_shape]
  refine h.trans ?_
  have he : (1 + 2 * (ε : ℝ)) * (1 + (ε : ℝ)) ^ 2 ≤ (1 + (ε : ℝ)) ^ 4 := by
    nlinarith [sq_nonneg (ε : ℝ), sq_nonneg ((ε : ℝ) + 1)]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right he hp

/-- The executable update contains the retained half of the preceding ellipsoid.
Both centre approximation errors are discharged by explicit grid bounds. -/
theorem update_halfspace_subset {n : ℕ} (hn : 2 ≤ n) (k : ℕ) (ε : ℚ)
    (hε : 0 < ε) (state : AlgorithmEllipsoid.State n) (a : Fin n → ℤ)
    (hD : (castMatrix (AlgorithmEllipsoid.shape k state)).PosDef) (ha : a ≠ 0)
    (lower R : ℝ) (hlower : 0 < lower) (hR : 0 ≤ R)
    (hbound : lower ^ 2 ≤ (AlgorithmEllipsoid.normalSquare (AlgorithmEllipsoid.shape k state) a : ℝ))
    (hprecision : 1 / (2 : ℝ) ^ k ≤ (n : ℝ) * ((ε : ℝ) / 2) * lower)
    (hentries : ∀ i j, |(EllipsoidGeometry.ellipsoidUpdateMatrix
      (castMatrix (AlgorithmEllipsoid.shape k state)) (castNormal a))⁻¹ i j| ≤ R)
    (hround : (n : ℝ) ^ 2 * R / ((2 : ℝ) ^ k) ^ 2 ≤ ((ε : ℝ) / 2) ^ 2) :
    let z := castVector (AlgorithmEllipsoid.center k state)
    let D := castMatrix (AlgorithmEllipsoid.shape k state)
    EllipsoidGeometry.ellipsoid z D ∩ {x | castNormal a ⬝ᵥ z ≤ castNormal a ⬝ᵥ x} ⊆
      EllipsoidGeometry.ellipsoid
        (castVector (AlgorithmEllipsoid.center k (AlgorithmEllipsoid.update k ε state a)))
        (castMatrix (AlgorithmEllipsoid.shape k (AlgorithmEllipsoid.update k ε state a))) := by
  let z := castVector (AlgorithmEllipsoid.center k state)
  let D := castMatrix (AlgorithmEllipsoid.shape k state)
  let z' := castVector (AlgorithmEllipsoid.center k (AlgorithmEllipsoid.update k ε state a))
  let D' := castMatrix (AlgorithmEllipsoid.shape k (AlgorithmEllipsoid.update k ε state a))
  let exactCenter := EllipsoidGeometry.ellipsoidUpdateCenter z D (castNormal a)
  let exactShape := EllipsoidGeometry.ellipsoidUpdateMatrix D (castNormal a)
  have haR := AlgorithmEllipsoidGeometry.normal_cast_ne_zero a ha
  have hεR : (0 : ℝ) < ε := Rat.cast_pos.mpr hε
  have hp := EllipsoidGeometry.update_positive hn D hD (castNormal a) haR
  have hp' := AlgorithmEllipsoidGeometry.update_positive hn k ε hε.le state hD a ha
  have hc := stored_center_error hn k ε state a hD haR lower (ε : ℝ) R
    hlower hεR.le hR hbound hprecision hentries hround
  have hs := EllipsoidPerturbation.center_and_shape_perturbation
    exactCenter (z' - exactCenter) exactShape D' hp hp' (ε : ℝ) hεR hc
    (stored_shape_dominates k ε state a hD)
  have heq : exactCenter + (z' - exactCenter) = z' := by abel
  rw [heq] at hs
  exact (EllipsoidGeometry.update_halfspace_subset hn z D hD (castNormal a) haR).trans hs

/-- A sufficiently fine stored update contracts actual ellipsoid volume by the
uniform factor used in the finite iteration count. -/
theorem update_volume_le {n : ℕ} (hn : 2 ≤ n) (k : ℕ) (ε : ℚ)
    (hε : 0 ≤ ε) (hεmax : (ε : ℝ) ≤ 1 / (32 * ((n : ℝ) + 1) ^ 2))
    (state : AlgorithmEllipsoid.State n) (a : Fin n → ℤ)
    (hD : (castMatrix (AlgorithmEllipsoid.shape k state)).PosDef) (ha : a ≠ 0)
    (lower : ℝ) (hmargin : (n : ℝ) / 2 ^ k ≤ (ε : ℝ) * lower)
    (hlower : ∀ v : Fin n → ℝ, lower * ∑ i, v i ^ 2 ≤
      quadratic (castMatrix (AlgorithmEllipsoid.enlargedShape ε
        (AlgorithmEllipsoid.shape k state) a)) v) :
    MeasureTheory.volume (EllipsoidGeometry.ellipsoid
      (castVector (AlgorithmEllipsoid.center k (AlgorithmEllipsoid.update k ε state a)))
      (castMatrix (AlgorithmEllipsoid.shape k (AlgorithmEllipsoid.update k ε state a)))) ≤
      ENNReal.ofReal (Real.exp (-(1 : ℝ) / (4 * ((n : ℝ) + 1)))) *
        MeasureTheory.volume (EllipsoidGeometry.ellipsoid
          (castVector (AlgorithmEllipsoid.center k state))
          (castMatrix (AlgorithmEllipsoid.shape k state))) := by
  apply EllipsoidPerturbation.rounded_update_volume_le hn _ _ _ _ hD
    (AlgorithmEllipsoidGeometry.update_positive hn k ε hε state hD a ha)
    (castNormal a) (AlgorithmEllipsoidGeometry.normal_cast_ne_zero a ha)
    (ε : ℝ) (Rat.cast_nonneg.mpr hε)
    (EllipsoidPerturbation.inflation_budget hn (ε : ℝ) hεmax)
  exact stored_shape_upper hn k ε hε state a hD ha lower hmargin hlower

end MWIS.EllipsoidUpdateBridge
end
