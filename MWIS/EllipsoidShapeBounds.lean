module

public import MWIS.AlgorithmEllipsoidGeometry

/-!
# Uniform upper bounds for the stored ellipsoid shapes

The relative rounding allowance and a small fixed inflation keep the shape
below four times the previous shape in every direction. Together with the
quarter lower bound, this gives simple powers-of-four spectral invariants.
Prepared 2026-10-23.
-/

@[expose] public section

namespace MWIS.EllipsoidShapeBounds

open Matrix
open scoped BigOperators
open AlgorithmMatrixRounding AlgorithmEllipsoidGeometry

/-- The exact shape update is at most twice the preceding shape in every
direction in dimensions at least two. -/
theorem rawShape_upper {n : ℕ} (hn : 2 ≤ n)
    (D : Matrix (Fin n) (Fin n) ℚ) (hD : (castMatrix D).PosDef)
    (a : Fin n → ℤ) (ha : a ≠ 0) (x : Fin n → ℝ) :
    quadratic (castMatrix (AlgorithmEllipsoid.rawShape D a)) x ≤
      2 * quadratic (castMatrix D) x := by
  have hb := (EllipsoidGeometry.update_quadratic_bounds hn (castMatrix D) hD
    (fun i => (a i : ℝ)) (normal_cast_ne_zero a ha) x).2
  rw [← rawShape_cast D (rational_symmetric D hD) a,
    ← quadratic_eq_dotProduct, ← quadratic_eq_dotProduct] at hb
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hden : 0 < (n : ℝ) ^ 2 - 1 := by nlinarith
  have hcoef : (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1) ≤ 2 := by
    rw [div_le_iff₀ hden]
    nlinarith
  have hq : 0 ≤ quadratic (castMatrix D) x := by
    rw [quadratic_eq_dotProduct]
    exact hD.posSemidef.dotProduct_mulVec_nonneg x
  exact hb.trans (mul_le_mul_of_nonneg_right hcoef hq)

/-- The executable stored update has a uniform factor-four upper bound whenever
the dyadic grid meets the relative matrix-rounding allowance. -/
theorem update_upper {n : ℕ} (hn : 2 ≤ n) (k : ℕ) (ε : ℚ)
    (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 32)
    (s : AlgorithmEllipsoid.State n)
    (hD : (castMatrix (AlgorithmEllipsoid.shape k s)).PosDef)
    (a : Fin n → ℤ) (ha : a ≠ 0) (lower : ℝ)
    (hmargin : (n : ℝ) / 2 ^ k ≤ (ε : ℝ) * lower)
    (hlower : ∀ x : Fin n → ℝ, lower * ∑ i, x i ^ 2 ≤
      quadratic (castMatrix (AlgorithmEllipsoid.enlargedShape ε
        (AlgorithmEllipsoid.shape k s) a)) x)
    (x : Fin n → ℝ) :
    quadratic (castMatrix (AlgorithmEllipsoid.shape k
        (AlgorithmEllipsoid.update k ε s a))) x ≤
      4 * quadratic (castMatrix (AlgorithmEllipsoid.shape k s)) x := by
  let D := AlgorithmEllipsoid.shape k s
  have hεR : (0 : ℝ) ≤ ε := Rat.cast_nonneg.mpr hε
  have hεRsmall : (ε : ℝ) ≤ 1 / 32 := by
    have hh : (ε : ℝ) ≤ ((1 / 32 : ℚ) : ℝ) := Rat.cast_le.mpr hεsmall
    norm_num at hh
    exact hh
  have hraw : (castMatrix (AlgorithmEllipsoid.rawShape D a)).PosDef := by
    rw [rawShape_cast D (rational_symmetric D hD) a]
    exact EllipsoidGeometry.update_positive hn _ hD _ (normal_cast_ne_zero a ha)
  have hraw0 : 0 ≤ quadratic (castMatrix (AlgorithmEllipsoid.rawShape D a)) x := by
    rw [quadratic_eq_dotProduct]
    exact hraw.posSemidef.dotProduct_mulVec_nonneg x
  have hfactor : (1 + 2 * (ε : ℝ)) * (1 + (ε : ℝ)) ^ 2 ≤ 2 := by
    calc
      _ ≤ (17 / 16 : ℝ) * (33 / 32 : ℝ) ^ 2 := by
        apply mul_le_mul
        · linarith
        · apply pow_le_pow_left₀ (by linarith)
          linarith
        · positivity
        · norm_num
      _ ≤ 2 := by norm_num
  rw [AlgorithmEllipsoid.update_shape]
  have hm : (Fintype.card (Fin n) : ℝ) / 2 ^ k ≤ (ε : ℝ) * lower := by
    simpa using hmargin
  calc
    _ ≤ (1 + 2 * (ε : ℝ)) * quadratic
        (castMatrix (AlgorithmEllipsoid.enlargedShape ε D a)) x :=
      padded_relative_bound k _ lower ε hεR hm hlower x
    _ = ((1 + 2 * (ε : ℝ)) * (1 + (ε : ℝ)) ^ 2) *
        quadratic (castMatrix (AlgorithmEllipsoid.rawShape D a)) x := by
      rw [enlargedShape_quadratic, mul_assoc]
    _ ≤ 2 * quadratic (castMatrix (AlgorithmEllipsoid.rawShape D a)) x :=
      mul_le_mul_of_nonneg_right hfactor hraw0
    _ ≤ 2 * (2 * quadratic (castMatrix D) x) :=
      mul_le_mul_of_nonneg_left (rawShape_upper hn D hD a ha x) (by norm_num)
    _ = _ := by ring

end MWIS.EllipsoidShapeBounds

end
