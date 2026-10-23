module

public import MWIS.AlgorithmEllipsoid
public import MWIS.EllipsoidGeometry
public import MWIS.EllipsoidPerturbation
public import Mathlib.Data.Rat.BigOperators

/-!
# Geometry of the executable rational shape update

Prepared 2026-10-23.

The explicitly evaluated rational update agrees with the real central-cut
formula. Diagonal padding therefore preserves strict positivity and gives a
controlled enlargement in every direction.
-/

@[expose] public section

namespace MWIS.AlgorithmEllipsoidGeometry

open Matrix
open scoped BigOperators
open AlgorithmMatrixRounding

/-- Coordinatewise inclusion of rational vectors into real vectors. -/
def castVector {n : ℕ} (x : Fin n → ℚ) : Fin n → ℝ := fun i => (x i : ℝ)

/-- Matrix multiplication commutes with the exact rational-to-real inclusion. -/
theorem direction_cast {n : ℕ} (D : Matrix (Fin n) (Fin n) ℚ)
    (a : Fin n → ℤ) :
    castVector (AlgorithmEllipsoid.direction D a) =
      (castMatrix D).mulVec (fun i => (a i : ℝ)) := by
  ext i
  simp [castVector, AlgorithmEllipsoid.direction, castMatrix, Matrix.mulVec, dotProduct]

/-- The computed cut norm is exactly its real quadratic-form value. -/
theorem normalSquare_cast {n : ℕ} (D : Matrix (Fin n) (Fin n) ℚ)
    (a : Fin n → ℤ) :
    (AlgorithmEllipsoid.normalSquare D a : ℝ) =
      (fun i => (a i : ℝ)) ⬝ᵥ (castMatrix D).mulVec (fun i => (a i : ℝ)) := by
  simp only [AlgorithmEllipsoid.normalSquare, Rat.cast_sum, Rat.cast_mul,
    Rat.cast_intCast]
  change (fun i => (a i : ℝ)) ⬝ᵥ castVector (AlgorithmEllipsoid.direction D a) = _
  rw [direction_cast]

/-- The concrete rational rank-one update is the exact shape-matrix update. -/
theorem rawShape_cast {n : ℕ} (D : Matrix (Fin n) (Fin n) ℚ)
    (hD : ∀ i j, D i j = D j i) (a : Fin n → ℤ) :
    castMatrix (AlgorithmEllipsoid.rawShape D a) =
      EllipsoidGeometry.ellipsoidUpdateMatrix (castMatrix D) (fun i => (a i : ℝ)) := by
  have hsymm : (castMatrix D)ᵀ = castMatrix D := by
    ext i j
    simp [castMatrix, Matrix.transpose_apply, hD i j]
  have houter : castMatrix D * vecMulVec (fun i => (a i : ℝ)) (fun i => (a i : ℝ)) *
      castMatrix D = vecMulVec (castVector (AlgorithmEllipsoid.direction D a))
        (castVector (AlgorithmEllipsoid.direction D a)) := by
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.mulVec_transpose,
      hsymm, direction_cast]
  ext i j
  simp only [AlgorithmEllipsoid.rawShape, castMatrix, Rat.cast_mul, Rat.cast_div,
    Rat.cast_sub, Rat.cast_pow, Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_one,
    Rat.cast_inv, Rat.cast_add, EllipsoidGeometry.ellipsoidUpdateMatrix,
    Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  have hq := normalSquare_cast D a
  rw [← hq, houter]
  simp only [vecMulVec, Matrix.of_apply, castVector]
  ring

/-- The scalar-enlarged rational matrix has the exact scaled real quadratic form. -/
theorem enlargedShape_quadratic {n : ℕ} (ε : ℚ)
    (D : Matrix (Fin n) (Fin n) ℚ) (a : Fin n → ℤ) (x : Fin n → ℝ) :
    quadratic (castMatrix (AlgorithmEllipsoid.enlargedShape ε D a)) x =
      (1 + (ε : ℝ)) ^ 2 * quadratic (castMatrix (AlgorithmEllipsoid.rawShape D a)) x := by
  change (∑ i, ∑ j, x i * (((1 + ε) ^ 2 * AlgorithmEllipsoid.rawShape D a i j : ℚ) : ℝ) * x j) = _
  push_cast
  change (∑ i, ∑ j, x i * ((1 + (ε : ℝ)) ^ 2 * (AlgorithmEllipsoid.rawShape D a i j : ℝ)) * x j) =
    (1 + (ε : ℝ)) ^ 2 * ∑ i, ∑ j, x i * (AlgorithmEllipsoid.rawShape D a i j : ℝ) * x j
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The local quadratic-form convention agrees with matrix-vector notation. -/
theorem quadratic_eq_dotProduct {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) : quadratic D x = x ⬝ᵥ D.mulVec x := by
  simp only [quadratic, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

/-- Positive definiteness of the included rational matrix gives its exact rational symmetry. -/
theorem rational_symmetric {n : ℕ} (D : Matrix (Fin n) (Fin n) ℚ)
    (hD : (castMatrix D).PosDef) : ∀ i j, D i j = D j i := by
  intro i j
  have h := congrFun (congrFun hD.isHermitian.eq j) i
  have hc : (D i j : ℝ) = (D j i : ℝ) := by
    simpa [Matrix.conjTranspose_apply, castMatrix] using h
  exact Rat.cast_injective hc

/-- An integer normal stays nonzero after inclusion into the reals. -/
theorem normal_cast_ne_zero {n : ℕ} (a : Fin n → ℤ) (ha : a ≠ 0) :
    (fun i => (a i : ℝ)) ≠ 0 := by
  intro hz
  apply ha
  ext i
  have h : (a i : ℝ) = 0 := congrFun hz i
  change a i = 0
  exact_mod_cast h

/-- The stored shape update is positive definite whenever its input is and the
cut is nonzero; rounding does not require a separate positivity assumption. -/
theorem update_positive {n : ℕ} (hn : 2 ≤ n) (k : ℕ) (ε : ℚ) (hε : 0 ≤ ε)
    (s : AlgorithmEllipsoid.State n)
    (hD : (castMatrix (AlgorithmEllipsoid.shape k s)).PosDef)
    (a : Fin n → ℤ) (ha : a ≠ 0) :
    (castMatrix (AlgorithmEllipsoid.shape k (AlgorithmEllipsoid.update k ε s a))).PosDef := by
  let D := AlgorithmEllipsoid.shape k s
  have hsym := rational_symmetric D hD
  have hraw : (castMatrix (AlgorithmEllipsoid.rawShape D a)).PosDef := by
    rw [rawShape_cast D hsym a]
    exact EllipsoidGeometry.update_positive hn _ hD _ (normal_cast_ne_zero a ha)
  have hεR : (0 : ℝ) ≤ ε := Rat.cast_nonneg.mpr hε
  have hpos : 0 < (1 + (ε : ℝ)) ^ 2 := sq_pos_of_pos (by linarith)
  have hnew := AlgorithmEllipsoid.update_symmetric k ε s hsym a
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · change (castMatrix (AlgorithmEllipsoid.shape k (AlgorithmEllipsoid.update k ε s a)))ᴴ = _
    ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial, castMatrix]
    exact congrArg (fun r : ℚ => (r : ℝ)) (hnew j i)
  · intro x hx
    simp only [star_trivial]
    rw [← quadratic_eq_dotProduct, AlgorithmEllipsoid.update_shape]
    have hp : 0 < quadratic (castMatrix (AlgorithmEllipsoid.enlargedShape ε D a)) x := by
      rw [enlargedShape_quadratic, quadratic_eq_dotProduct]
      exact mul_pos hpos (hraw.dotProduct_mulVec_pos hx)
    exact hp.trans_le (padded_dominates k (AlgorithmEllipsoid.enlargedShape ε D a) x)

/-- Every nonzero cut keeps at least one quarter of the preceding shape in
all directions, including the actual finite-precision storage step. -/
theorem update_lower {n : ℕ} (hn : 2 ≤ n) (k : ℕ) (ε : ℚ) (hε : 0 ≤ ε)
    (s : AlgorithmEllipsoid.State n)
    (hD : (castMatrix (AlgorithmEllipsoid.shape k s)).PosDef)
    (a : Fin n → ℤ) (ha : a ≠ 0) (x : Fin n → ℝ) :
    (1 / 4 : ℝ) * quadratic (castMatrix (AlgorithmEllipsoid.shape k s)) x ≤
      quadratic (castMatrix (AlgorithmEllipsoid.shape k (AlgorithmEllipsoid.update k ε s a))) x := by
  let D := AlgorithmEllipsoid.shape k s
  have hsym := rational_symmetric D hD
  have hbound := (EllipsoidGeometry.update_quadratic_bounds hn (castMatrix D) hD
    (fun i => (a i : ℝ)) (normal_cast_ne_zero a ha) x).1
  rw [← rawShape_cast D hsym a, ← quadratic_eq_dotProduct,
    ← quadratic_eq_dotProduct] at hbound
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hcoef : (1 / 4 : ℝ) ≤ (n : ℝ) ^ 2 / ((n : ℝ) + 1) ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos (by linarith))).mpr
    nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have hq : 0 ≤ quadratic (castMatrix D) x := by
    rw [quadratic_eq_dotProduct]
    exact hD.posSemidef.dotProduct_mulVec_nonneg x
  have hraw0 : 0 ≤ quadratic (castMatrix (AlgorithmEllipsoid.rawShape D a)) x :=
    (mul_nonneg (by positivity) hq).trans hbound
  have hεR : (0 : ℝ) ≤ ε := Rat.cast_nonneg.mpr hε
  have hscale : 1 ≤ (1 + (ε : ℝ)) ^ 2 := by nlinarith
  rw [AlgorithmEllipsoid.update_shape]
  calc
    (1 / 4 : ℝ) * quadratic (castMatrix D) x ≤
        (n : ℝ) ^ 2 / ((n : ℝ) + 1) ^ 2 * quadratic (castMatrix D) x :=
      mul_le_mul_of_nonneg_right hcoef hq
    _ ≤ quadratic (castMatrix (AlgorithmEllipsoid.rawShape D a)) x := hbound
    _ ≤ (1 + (ε : ℝ)) ^ 2 * quadratic (castMatrix (AlgorithmEllipsoid.rawShape D a)) x := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hscale hraw0
    _ = quadratic (castMatrix (AlgorithmEllipsoid.enlargedShape ε D a)) x :=
      (enlargedShape_quadratic ε D a x).symm
    _ ≤ _ := padded_dominates k _ x

end MWIS.AlgorithmEllipsoidGeometry
