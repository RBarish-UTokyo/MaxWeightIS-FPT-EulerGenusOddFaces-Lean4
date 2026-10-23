module

public import MWIS.AlgorithmEllipsoid
public import Mathlib.Data.Rat.BigOperators
public import MWIS.EllipsoidGeometry
public import MWIS.AlgorithmMatrixRounding

/-!
# Rational approximation of the central-cut centre

A dyadic square-root upper endpoint supplies an explicit rational scaling of
the update direction. The induced error is bounded in the inverse metric of
the exact updated shape, using a lower bound on the cut's quadratic value and
the chosen grid precision.

Prepared 2026-10-23.
-/

@[expose] public section

namespace MWIS.EllipsoidCenterRounding

open Matrix
open scoped BigOperators

/-- A centre update with a supplied inverse-square-root scaling. -/
noncomputable def centerWithScale {n : ℕ} (z : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) (s : ℝ) : Fin n → ℝ :=
  z + ((1 : ℝ) / (n + 1)) • s • D.mulVec a

/-- The rational upper endpoint encloses the actual real square root. -/
theorem sqrt_enclosure (k : ℕ) (q : ℚ) (hq : 0 ≤ q) :
    (AlgorithmSqrt.lower k q : ℝ) ≤ Real.sqrt (q : ℝ) ∧
      Real.sqrt (q : ℝ) < (AlgorithmSqrt.upper k q : ℝ) := by
  have hl := AlgorithmSqrt.lower_sq_le k q hq
  have hu := AlgorithmSqrt.lt_upper_sq k q
  have hlo : (0 : ℝ) ≤ (AlgorithmSqrt.lower k q : ℝ) :=
    Rat.cast_nonneg.mpr (AlgorithmSqrt.lower_nonnegative k q)
  have hup : (0 : ℝ) < (AlgorithmSqrt.upper k q : ℝ) :=
    Rat.cast_pos.mpr (AlgorithmSqrt.upper_positive k q)
  have hqR : (0 : ℝ) ≤ q := Rat.cast_nonneg.mpr hq
  have hlR : (AlgorithmSqrt.lower k q : ℝ) ^ 2 ≤ (q : ℝ) := by exact_mod_cast hl
  have huR : (q : ℝ) < (AlgorithmSqrt.upper k q : ℝ) ^ 2 := by exact_mod_cast hu
  have hs := Real.sq_sqrt hqR
  have hsn := Real.sqrt_nonneg (q : ℝ)
  constructor <;> nlinarith

/-- A positive lower bound on the square root controls the relative error of
the explicit rational inverse-square-root approximation. -/
theorem inverse_sqrt_relative_error (k : ℕ) (q : ℚ) (hq : 0 ≤ q)
    (lower : ℝ) (hlower : 0 < lower) (hbound : lower ^ 2 ≤ (q : ℝ)) :
    |(AlgorithmSqrt.upper k q : ℝ)⁻¹ * Real.sqrt (q : ℝ) - 1| ≤
      (1 / 2 ^ k) / lower := by
  obtain ⟨hlo, hhi⟩ := sqrt_enclosure k q hq
  have hu : (0 : ℝ) < (AlgorithmSqrt.upper k q : ℝ) :=
    Rat.cast_pos.mpr (AlgorithmSqrt.upper_positive k q)
  have hr : lower ≤ Real.sqrt (q : ℝ) := by
    have hsq := Real.sq_sqrt (Rat.cast_nonneg.mpr hq : (0 : ℝ) ≤ q)
    have hn := Real.sqrt_nonneg (q : ℝ)
    nlinarith
  have hwidth : (AlgorithmSqrt.upper k q : ℝ) - (AlgorithmSqrt.lower k q : ℝ) =
      1 / 2 ^ k := by
    have h := congrArg (fun r : ℚ => (r : ℝ)) (AlgorithmSqrt.endpoint_width k q)
    simpa only [Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat] using h
  have herror : (AlgorithmSqrt.upper k q : ℝ) - Real.sqrt (q : ℝ) ≤ 1 / 2 ^ k := by
    linarith
  have habs : |(AlgorithmSqrt.upper k q : ℝ)⁻¹ * Real.sqrt (q : ℝ) - 1| =
      ((AlgorithmSqrt.upper k q : ℝ) - Real.sqrt (q : ℝ)) /
        (AlgorithmSqrt.upper k q : ℝ) := by
    rw [abs_of_nonpos]
    · field_simp
      ring
    · have hdiv : Real.sqrt (q : ℝ) / (AlgorithmSqrt.upper k q : ℝ) ≤ 1 :=
        (div_le_one hu).mpr hhi.le
      simpa [div_eq_mul_inv, mul_comm] using sub_nonpos.mpr hdiv
  rw [habs]
  exact (div_le_div_of_nonneg_right herror hu.le).trans
    (div_le_div_of_nonneg_left (by positivity) hlower (hr.trans hhi.le))

/-- The update-direction metric has a closed exact expression. -/
theorem update_direction_metric {n : ℕ} (hn : 2 ≤ n)
    (D : Matrix (Fin n) (Fin n) ℝ) (hD : D.PosDef)
    (a : Fin n → ℝ) (ha : a ≠ 0) :
    D.mulVec a ⬝ᵥ (EllipsoidGeometry.ellipsoidUpdateMatrix D a)⁻¹.mulVec (D.mulVec a) =
      (((n : ℝ) + 1) ^ 2 / (n : ℝ) ^ 2) * (a ⬝ᵥ D.mulVec a) := by
  let q := a ⬝ᵥ D.mulVec a
  have hq : 0 < q := hD.dotProduct_mulVec_pos ha
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have huinv : D⁻¹.mulVec (D.mulVec a) = a := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul D
      ((Matrix.isUnit_iff_isUnit_det D).mp hD.isUnit)]
    simp
  have hrank : (vecMulVec a a).mulVec (D.mulVec a) = q • a := by
    ext i
    simp only [mulVec, vecMulVec, Matrix.of_apply, dotProduct, Pi.smul_apply, smul_eq_mul, q]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hdot : D.mulVec a ⬝ᵥ a = q := dotProduct_comm _ _
  rw [EllipsoidGeometry.update_inverse hn D hD a ha]
  simp only [Matrix.smul_mulVec, Matrix.add_mulVec, huinv, hrank,
    dotProduct_smul, dotProduct_add, smul_eq_mul, hdot]
  change ((n : ℝ) ^ 2 - 1) / (n : ℝ) ^ 2 *
      (q + 2 / ((n : ℝ) - 1) * (q⁻¹ * (q * q))) = _
  dsimp only [q] at hq ⊢
  field_simp [hn0, hn1, ne_of_gt hq]
  ring

/-- The centre scaling error has an exact squared inverse-metric norm. -/
theorem center_error_metric {n : ℕ} (hn : 2 ≤ n)
    (z : Fin n → ℝ) (D : Matrix (Fin n) (Fin n) ℝ) (hD : D.PosDef)
    (a : Fin n → ℝ) (ha : a ≠ 0) (s : ℝ) :
    let δ := centerWithScale z D a s - EllipsoidGeometry.ellipsoidUpdateCenter z D a
    δ ⬝ᵥ (EllipsoidGeometry.ellipsoidUpdateMatrix D a)⁻¹.mulVec δ =
      (s * Real.sqrt (a ⬝ᵥ D.mulVec a) - 1) ^ 2 / (n : ℝ) ^ 2 := by
  let q := a ⬝ᵥ D.mulVec a
  have hq : 0 < q := hD.dotProduct_mulVec_pos ha
  have hr : Real.sqrt q ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hq)
  have hr2 := Real.sq_sqrt hq.le
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hn1 : (n : ℝ) + 1 ≠ 0 := by linarith
  have hδ : centerWithScale z D a s - EllipsoidGeometry.ellipsoidUpdateCenter z D a =
      (1 / ((n : ℝ) + 1) * (s - (Real.sqrt q)⁻¹)) • D.mulVec a := by
    ext i
    simp [centerWithScale, EllipsoidGeometry.ellipsoidUpdateCenter, q,
      Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
    ring
  dsimp only
  rw [hδ, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, update_direction_metric hn D hD a ha]
  simp only [smul_eq_mul]
  change _ = (s * Real.sqrt q - 1) ^ 2 / (n : ℝ) ^ 2
  have hid : (s - (Real.sqrt q)⁻¹) ^ 2 * q = (s * Real.sqrt q - 1) ^ 2 := by
    calc
      _ = (s - (Real.sqrt q)⁻¹) ^ 2 * (Real.sqrt q) ^ 2 := by rw [hr2]
      _ = _ := by field_simp [hr]
  calc
    _ = ((s - (Real.sqrt q)⁻¹) ^ 2 * q) / (n : ℝ) ^ 2 := by
      dsimp only [q]
      field_simp [hn0, hn1]
    _ = _ := by rw [hid]

/-- Real scalar inclusion of a finite rational vector. -/
def castVector {n : ℕ} (z : Fin n → ℚ) : Fin n → ℝ := fun i => z i

/-- Real scalar inclusion of the integer normal vector. -/
def castNormal {n : ℕ} (a : Fin n → ℤ) : Fin n → ℝ := fun i => a i

/-- The executable rational direction agrees with ordinary real matrix multiplication. -/
theorem direction_cast {n : ℕ} (D : Matrix (Fin n) (Fin n) ℚ) (a : Fin n → ℤ) :
    castVector (AlgorithmEllipsoid.direction D a) =
      (AlgorithmMatrixRounding.castMatrix D).mulVec (castNormal a) := by
  ext i
  simp [castVector, castNormal, AlgorithmEllipsoid.direction,
    AlgorithmMatrixRounding.castMatrix, mulVec, dotProduct]

/-- The executable rational cut square agrees with its real quadratic value. -/
theorem normalSquare_cast {n : ℕ} (D : Matrix (Fin n) (Fin n) ℚ) (a : Fin n → ℤ) :
    (AlgorithmEllipsoid.normalSquare D a : ℝ) =
      castNormal a ⬝ᵥ (AlgorithmMatrixRounding.castMatrix D).mulVec (castNormal a) := by
  simp only [AlgorithmEllipsoid.normalSquare, Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast,
    dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  rw [← direction_cast]
  rfl

/-- The executable rational centre is exactly the specified approximate scaling
of the real update direction. -/
theorem approximateCenter_cast {n : ℕ} (k : ℕ) (z : Fin n → ℚ)
    (D : Matrix (Fin n) (Fin n) ℚ) (a : Fin n → ℤ) :
    castVector (AlgorithmEllipsoid.approximateCenter k z D a) =
      centerWithScale (castVector z) (AlgorithmMatrixRounding.castMatrix D) (castNormal a)
        (AlgorithmSqrt.upper k (AlgorithmEllipsoid.normalSquare D a) : ℝ)⁻¹ := by
  ext i
  simp only [castVector, AlgorithmEllipsoid.approximateCenter, centerWithScale,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, Rat.cast_add, Rat.cast_div, Rat.cast_mul,
    Rat.cast_natCast, Rat.cast_one]
  rw [← direction_cast]
  simp only [castVector, div_eq_mul_inv, _root_.mul_inv_rev]
  ring

/-- The actual rational approximation meets a prescribed inverse-metric centre
error whenever its grid is fine enough for the supplied positive lower bound. -/
theorem approximateCenter_error {n : ℕ} (hn : 2 ≤ n)
    (k : ℕ) (z : Fin n → ℚ) (D : Matrix (Fin n) (Fin n) ℚ) (a : Fin n → ℤ)
    (hD : (AlgorithmMatrixRounding.castMatrix D).PosDef) (ha : castNormal a ≠ 0)
    (lower ε : ℝ) (hlower : 0 < lower) (hε : 0 ≤ ε)
    (hbound : lower ^ 2 ≤ (AlgorithmEllipsoid.normalSquare D a : ℝ))
    (hprecision : 1 / (2 : ℝ) ^ k ≤ (n : ℝ) * ε * lower) :
    let δ := castVector (AlgorithmEllipsoid.approximateCenter k z D a) -
      EllipsoidGeometry.ellipsoidUpdateCenter (castVector z)
        (AlgorithmMatrixRounding.castMatrix D) (castNormal a)
    δ ⬝ᵥ (EllipsoidGeometry.ellipsoidUpdateMatrix
      (AlgorithmMatrixRounding.castMatrix D) (castNormal a))⁻¹.mulVec δ ≤ ε ^ 2 := by
  have hqR : (0 : ℝ) < (AlgorithmEllipsoid.normalSquare D a : ℝ) := by
    rw [normalSquare_cast]
    exact hD.dotProduct_mulVec_pos ha
  have hq : 0 ≤ AlgorithmEllipsoid.normalSquare D a := Rat.cast_nonneg.mp hqR.le
  have he := inverse_sqrt_relative_error k (AlgorithmEllipsoid.normalSquare D a)
    hq lower hlower hbound
  have hp : (1 / (2 : ℝ) ^ k) / lower ≤ (n : ℝ) * ε :=
    (div_le_iff₀ hlower).mpr hprecision
  have he' := he.trans hp
  have hsq := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg n) hε)).mpr he'
  rw [sq_abs] at hsq
  dsimp only
  rw [approximateCenter_cast, center_error_metric hn _ _ hD _ ha]
  rw [← normalSquare_cast]
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  apply (div_le_iff₀ (sq_pos_of_pos hnR)).mpr
  nlinarith

/-- Quadratic-form notation agrees with the shape-matrix metric convention. -/
theorem quadratic_eq_dot {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    AlgorithmMatrixRounding.quadratic P v = v ⬝ᵥ P.mulVec v := by
  simp [AlgorithmMatrixRounding.quadratic, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

/-- Coordinate rounding changes the centre by a controlled amount in any
inverse metric with a known entry bound. -/
theorem rounded_vector_error {n : ℕ} (k : ℕ) (x : Fin n → ℚ)
    (P : Matrix (Fin n) (Fin n) ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hP : ∀ i j, |P i j| ≤ R) :
    let δ := castVector (fun i => AlgorithmRounding.roundDown k (x i)) - castVector x
    δ ⬝ᵥ P.mulVec δ ≤ (n : ℝ) ^ 2 * R / ((2 : ℝ) ^ k) ^ 2 := by
  let δ := castVector (fun i => AlgorithmRounding.roundDown k (x i)) - castVector x
  have he (i : Fin n) : |δ i| ≤ 1 / (2 : ℝ) ^ k := by
    have hrat : ((|AlgorithmRounding.roundDown k (x i) - x i| : ℚ) : ℝ) ≤
        ((1 / (2 : ℚ) ^ k : ℚ) : ℝ) :=
      Rat.cast_le.mpr (AlgorithmRounding.abs_roundDown_error k (x i)).le
    simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_pow,
      Rat.cast_ofNat, δ, castVector, Pi.sub_apply] using hrat
  have hnorm : (∑ i, δ i ^ 2) ≤ (n : ℝ) * (1 / (2 : ℝ) ^ k) ^ 2 := by
    calc
      _ ≤ ∑ _i : Fin n, (1 / (2 : ℝ) ^ k) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have h := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr (he i)
        simpa only [sq_abs] using h
      _ = _ := by simp
  have hb := AlgorithmMatrixRounding.quadratic_error_bound (0 : Matrix (Fin n) (Fin n) ℝ)
    P R hR (by simpa using hP) δ
  have hz : AlgorithmMatrixRounding.quadratic (0 : Matrix (Fin n) (Fin n) ℝ) δ = 0 := by
    simp [AlgorithmMatrixRounding.quadratic]
  rw [hz, sub_zero, quadratic_eq_dot] at hb
  simp only [Fintype.card_fin] at hb
  dsimp only
  change δ ⬝ᵥ P.mulVec δ ≤ _
  calc
    _ ≤ |δ ⬝ᵥ P.mulVec δ| := le_abs_self _
    _ ≤ (n : ℝ) * R * ∑ i, δ i ^ 2 := hb
    _ ≤ (n : ℝ) * R * ((n : ℝ) * (1 / (2 : ℝ) ^ k) ^ 2) :=
      mul_le_mul_of_nonneg_left hnorm (mul_nonneg (Nat.cast_nonneg n) hR)
    _ = _ := by ring

/-- Positive semidefinite metrics satisfy the two-vector squared-norm bound. -/
theorem metric_add_le_twice {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P.PosSemidef) (u v : Fin n → ℝ) :
    (u + v) ⬝ᵥ P.mulVec (u + v) ≤
      2 * (u ⬝ᵥ P.mulVec u) + 2 * (v ⬝ᵥ P.mulVec v) := by
  have h := hP.dotProduct_mulVec_nonneg (u - v)
  simp only [star_trivial, Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub] at h
  simp only [Matrix.mulVec_add, add_dotProduct, dotProduct_add]
  linarith

/-- Both numerical centre approximations in the actual stored update meet one
combined inverse-metric tolerance. The assumptions quantify the two required
grid-precision margins explicitly. -/
theorem stored_center_error {n : ℕ} (hn : 2 ≤ n) (k : ℕ) (εq : ℚ)
    (state : AlgorithmEllipsoid.State n) (a : Fin n → ℤ)
    (hD : (AlgorithmMatrixRounding.castMatrix (AlgorithmEllipsoid.shape k state)).PosDef)
    (ha : castNormal a ≠ 0) (lower ε R : ℝ) (hlower : 0 < lower) (hε : 0 ≤ ε) (hR : 0 ≤ R)
    (hbound : lower ^ 2 ≤ (AlgorithmEllipsoid.normalSquare (AlgorithmEllipsoid.shape k state) a : ℝ))
    (hprecision : 1 / (2 : ℝ) ^ k ≤ (n : ℝ) * (ε / 2) * lower)
    (hentries : ∀ i j, |(EllipsoidGeometry.ellipsoidUpdateMatrix
      (AlgorithmMatrixRounding.castMatrix (AlgorithmEllipsoid.shape k state)) (castNormal a))⁻¹ i j| ≤ R)
    (hround : (n : ℝ) ^ 2 * R / ((2 : ℝ) ^ k) ^ 2 ≤ (ε / 2) ^ 2) :
    let z := castVector (AlgorithmEllipsoid.center k state)
    let D := AlgorithmMatrixRounding.castMatrix (AlgorithmEllipsoid.shape k state)
    let δ := castVector (AlgorithmEllipsoid.center k (AlgorithmEllipsoid.update k εq state a)) -
      EllipsoidGeometry.ellipsoidUpdateCenter z D (castNormal a)
    δ ⬝ᵥ (EllipsoidGeometry.ellipsoidUpdateMatrix D (castNormal a))⁻¹.mulVec δ ≤ ε ^ 2 := by
  let D := AlgorithmMatrixRounding.castMatrix (AlgorithmEllipsoid.shape k state)
  let z := castVector (AlgorithmEllipsoid.center k state)
  let x := AlgorithmEllipsoid.approximateCenter k
    (AlgorithmEllipsoid.center k state) (AlgorithmEllipsoid.shape k state) a
  let u := castVector x - EllipsoidGeometry.ellipsoidUpdateCenter z D (castNormal a)
  let v := castVector (AlgorithmEllipsoid.center k (AlgorithmEllipsoid.update k εq state a)) - castVector x
  let P := (EllipsoidGeometry.ellipsoidUpdateMatrix D (castNormal a))⁻¹
  have hu : u ⬝ᵥ P.mulVec u ≤ (ε / 2) ^ 2 :=
    approximateCenter_error hn k _ _ a hD ha lower (ε / 2) hlower (by positivity) hbound hprecision
  have hv : v ⬝ᵥ P.mulVec v ≤ (ε / 2) ^ 2 := by
    have h := rounded_vector_error k x P R hR hentries
    have hcenter : AlgorithmEllipsoid.center k (AlgorithmEllipsoid.update k εq state a) =
        fun i => AlgorithmRounding.roundDown k (x i) := by
      funext i
      exact AlgorithmEllipsoid.update_center k εq state a i
    dsimp only at h
    dsimp only [v]
    rw [hcenter]
    exact h.trans hround
  have hP : P.PosSemidef := (EllipsoidGeometry.update_positive hn D hD (castNormal a) ha).inv.posSemidef
  have heq : castVector (AlgorithmEllipsoid.center k (AlgorithmEllipsoid.update k εq state a)) -
      EllipsoidGeometry.ellipsoidUpdateCenter z D (castNormal a) = u + v := by
    dsimp only [u, v]
    abel
  dsimp only
  change _ ⬝ᵥ P.mulVec _ ≤ _
  rw [heq]
  have h := metric_add_le_twice P hP u v
  nlinarith

end MWIS.EllipsoidCenterRounding

end
