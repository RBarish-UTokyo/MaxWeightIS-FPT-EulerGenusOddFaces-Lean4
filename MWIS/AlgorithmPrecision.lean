module

public import MWIS.AlgorithmTrajectory
public import MWIS.EllipsoidUpdateBridge
public import MWIS.EllipsoidInverseBounds

/-!
# A fixed polynomial dyadic precision

Prepared 2026-10-23.

A single precision, linear in the dimension and iteration budget, is sufficient
for the rounding margins of every step. The values used below are explicit
rational expressions and integer powers.
-/

@[expose] public section
set_option maxHeartbeats 400000

namespace MWIS.AlgorithmPrecision

open Matrix
open scoped BigOperators
open AlgorithmEllipsoid AlgorithmMatrixRounding AlgorithmEllipsoidGeometry AlgorithmTrajectory

/-- The scalar inflation used throughout one finite run. -/
def inflation (n : ℕ) : ℚ := 1 / (32 * (n + 1 : ℚ) ^ 2)

/-- Fixed dyadic denominator exponent for a run of at most `T` updates. -/
def precision (n T : ℕ) : ℕ := 2 * T + 4 * n + 32

theorem inflation_pos (n : ℕ) : 0 < inflation n := by unfold inflation; positivity

theorem inflation_le (n : ℕ) : inflation n ≤ 1 / 32 := by
  unfold inflation
  apply one_div_le_one_div_of_le (by norm_num)
  have hn : (1 : ℚ) ≤ n + 1 := by have h := Nat.cast_nonneg (α := ℚ) n; linarith
  nlinarith

/-- An elementary exponential dominates the required cubic dimension factor. -/
theorem dimension_power (n : ℕ) : 128 * n * (n + 1) ^ 2 ≤ 2 ^ (4 * n + 32) := by
  have hn : n ≤ 2 ^ n := Nat.le_of_lt n.lt_two_pow_self
  have hn1 : n + 1 ≤ 2 ^ (n + 1) := Nat.le_of_lt (n + 1).lt_two_pow_self
  calc
    128 * n * (n + 1) ^ 2 ≤ 2 ^ 7 * 2 ^ n * (2 ^ (n + 1)) ^ 2 := by gcongr; norm_num
    _ = 2 ^ (3 * n + 9) := by rw [← pow_add, ← pow_mul, ← pow_add]; congr 1 <;> omega
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- The strongest required grid margin holds with the explicit precision. -/
theorem uniform_grid (n T : ℕ) :
    (n : ℝ) / 2 ^ (precision n T) ≤
      (inflation n : ℝ) * (1 / 4 ^ (T + 1)) := by
  have hp : (4 : ℕ) ^ T = 2 ^ (2 * T) := by
    rw [pow_mul]
    norm_num
  have hi : n * (32 * (n + 1) ^ 2 * 4 ^ (T + 1)) ≤ 2 ^ (precision n T) := by
    calc
      n * (32 * (n + 1) ^ 2 * 4 ^ (T + 1)) =
          (128 * n * (n + 1) ^ 2) * 4 ^ T := by rw [pow_succ]; ring
      _ ≤ 2 ^ (4 * n + 32) * 4 ^ T := Nat.mul_le_mul_right _ (dimension_power n)
      _ = _ := by rw [hp, ← pow_add]; congr 1; unfold precision; omega
  have hiR : (n : ℝ) * (32 * ((n : ℝ) + 1) ^ 2 * 4 ^ (T + 1)) ≤ 2 ^ (precision n T) := by
    exact_mod_cast hi
  have he : (inflation n : ℝ) * (1 / 4 ^ (T + 1)) =
      1 / (32 * ((n : ℝ) + 1) ^ 2 * 4 ^ (T + 1)) := by
    simp only [inflation, Rat.cast_div, Rat.cast_one, Rat.cast_mul, Rat.cast_ofNat,
      Rat.cast_pow, Rat.cast_add, Rat.cast_natCast]
    exact one_div_mul_one_div _ _
  rw [he]
  have hp1 : (0 : ℝ) < 2 ^ precision n T := by positivity
  have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by have h := Nat.cast_nonneg (α := ℝ) n; linarith
  have hp2 : (0 : ℝ) < 32 * ((n : ℝ) + 1) ^ 2 * 4 ^ (T + 1) :=
    mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hnpos)) (pow_pos (by norm_num) _)
  exact (div_le_div_iff₀ hp1 hp2).mpr (by simpa using hiR)

/-- A stronger matrix-grid margin implies the square-root and stored-centre
margins with the same fixed precision. -/
theorem center_margins {n : ℕ} (hn : 2 ≤ n) (T : ℕ) :
    1 / (2 : ℝ) ^ precision n T ≤
        (n : ℝ) * ((inflation n : ℝ) / 2) * (1 / 2 ^ T) ∧
      (n : ℝ) ^ 2 * 4 ^ (T + 1) / ((2 : ℝ) ^ precision n T) ^ 2 ≤
        ((inflation n : ℝ) / 2) ^ 2 := by
  let a : ℝ := 2 ^ T
  let d : ℝ := 1 / 2 ^ precision n T
  let e : ℝ := inflation n
  have ha : 1 ≤ a := one_le_pow₀ (by norm_num)
  have ha0 : 0 < a := by positivity
  have hd : 0 ≤ d := by positivity
  have he : 0 ≤ e := Rat.cast_nonneg.mpr (inflation_pos n).le
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by linarith
  have hpow : (4 : ℝ) ^ (T + 1) = 4 * a ^ 2 := by
    dsimp [a]
    have hh : ((2 : ℝ) ^ T) ^ 2 = 4 ^ T := by
      rw [← pow_mul, Nat.mul_comm T 2, pow_mul]
      norm_num
    rw [pow_succ, hh]
    ring
  have hg := uniform_grid n T
  rw [hpow] at hg
  rw [div_eq_mul_one_div] at hg
  change (n : ℝ) * d ≤ e * (1 / (4 * a ^ 2)) at hg
  rw [← div_eq_mul_one_div e (4 * a ^ 2)] at hg
  have hg' : 4 * (n : ℝ) * a ^ 2 * d ≤ e := by
    have h := (le_div_iff₀ (show (0 : ℝ) < 4 * a ^ 2 by positivity)).mp hg
    nlinarith
  have had : 0 ≤ a * d := mul_nonneg ha0.le hd
  have hna : 0 ≤ (n : ℝ) * a * d := by positivity
  have hsmall : 2 * (n : ℝ) * a * d ≤ e / 2 := by
    have h := mul_le_mul_of_nonneg_right ha (show 0 ≤ 4 * (n : ℝ) * a * d by positivity)
    nlinarith
  constructor
  · change d ≤ (n : ℝ) * (e / 2) * (1 / a)
    rw [← div_eq_mul_one_div, le_div_iff₀ ha0]
    have hnn : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    have h := mul_le_mul_of_nonneg_left hsmall hn0.le
    have hmon := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 2 * (n : ℝ) ^ 2 by nlinarith) had
    nlinarith
  · rw [hpow]
    change (n : ℝ) ^ 2 * (4 * a ^ 2) / ((2 : ℝ) ^ precision n T) ^ 2 ≤ (e / 2) ^ 2
    have hsq : (2 * (n : ℝ) * a * d) ^ 2 ≤ (e / 2) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hsmall 2
    dsimp [d] at hsq
    convert hsq using 1 <;> ring

/-- A coarse lower bound on the exact shape before rounding. -/
theorem raw_lower {n : ℕ} (hn : 2 ≤ n) (D : Matrix (Fin n) (Fin n) ℚ)
    (hD : (castMatrix D).PosDef) (a : Fin n → ℤ) (ha : a ≠ 0) (x : Fin n → ℝ) :
    (1 / 4 : ℝ) * quadratic (castMatrix D) x ≤
      quadratic (castMatrix (rawShape D a)) x := by
  have h := (EllipsoidGeometry.update_quadratic_bounds hn (castMatrix D) hD
    (fun i => (a i : ℝ)) (normal_cast_ne_zero a ha) x).1
  rw [← rawShape_cast D (rational_symmetric D hD) a,
    ← quadratic_eq_dotProduct, ← quadratic_eq_dotProduct] at h
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hcoef : (1 / 4 : ℝ) ≤ (n : ℝ) ^ 2 / ((n : ℝ) + 1) ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos (by linarith))).mpr
    nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have hq : 0 ≤ quadratic (castMatrix D) x := by
    rw [quadratic_eq_dotProduct]
    exact hD.posSemidef.dotProduct_mulVec_nonneg x
  exact (mul_le_mul_of_nonneg_right hcoef hq).trans h

/-- One fixed dyadic precision discharges every numerical hypothesis for every
nonzero integer cut in the entire finite trajectory. -/
noncomputable def trajectory_stepPrecision {m n : ℕ} (hn : 2 ≤ n)
    (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) (B T t : ℕ) (ht : t ≤ T)
    (a : Fin n → ℤ) (ha : a ≠ 0) :
    EllipsoidUpdateBridge.StepPrecision (precision n T) (inflation n)
      (trajectory A b (precision n T) (inflation n) (initial n (precision n T) B) t) a := by
  let k := precision n T
  let e := inflation n
  let s := trajectory A b k e (initial n k B) t
  let D := shape k s
  have he : 0 ≤ e := (inflation_pos n).le
  have hD : (castMatrix D).PosDef :=
    trajectory_positive hn A b k e he _ (initial_positive n k B) t
  have hpow : (1 / 4 : ℝ) ^ T ≤ (1 / 4 : ℝ) ^ t :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) ht
  have hlow (x : Fin n → ℝ) :
      (1 / 4 : ℝ) ^ T * ∑ i, x i ^ 2 ≤ quadratic (castMatrix D) x := by
    exact (mul_le_mul_of_nonneg_right hpow
      (Finset.sum_nonneg (fun i _ => sq_nonneg (x i)))).trans
        (initial_trajectory_lower hn A b k B e he t x)
  have hraw (x : Fin n → ℝ) :
      (1 / 4 ^ (T + 1) : ℝ) * ∑ i, x i ^ 2 ≤ quadratic (castMatrix (rawShape D a)) x := by
    have h := mul_le_mul_of_nonneg_left (hlow x) (show (0 : ℝ) ≤ 1 / 4 by norm_num)
    have hp : (1 / 4 ^ (T + 1) : ℝ) = (1 / 4) * (1 / 4) ^ T := by
      rw [← _root_.one_div_pow, pow_succ]
      ring
    rw [hp, mul_assoc]
    exact h.trans (raw_lower hn D hD a ha x)
  have hnorm : (1 / (2 : ℝ) ^ T) ^ 2 ≤ (normalSquare D a : ℝ) := by
    have hq := trajectory_normalSquare_lower hn A b k B e he t a ha
    have hp : (1 / (2 : ℝ) ^ T) ^ 2 = (1 / 4 : ℝ) ^ T := by
      rw [← _root_.one_div_pow, ← pow_mul, Nat.mul_comm T 2, pow_mul]
      norm_num
    rw [hp]
    exact hpow.trans hq
  refine {
    normalLower := 1 / 2 ^ T
    inverseBound := 4 ^ (T + 1)
    shapeLower := 1 / 4 ^ (T + 1)
    normalLower_pos := by positivity
    inverseBound_nonneg := by positivity
    normalSquare_lower := hnorm
    sqrt_margin := (center_margins hn T).1
    inverse_entries := ?_
    center_margin := (center_margins hn T).2
    shape_margin := uniform_grid n T
    enlarged_lower := ?_
  }
  · intro i j
    have hp := EllipsoidGeometry.update_positive hn (castMatrix D) hD
      (fun i => (a i : ℝ)) (normal_cast_ne_zero a ha)
    have hh := EllipsoidInverseBounds.abs_inverse_entry_le _ hp
      (1 / 4 ^ (T + 1)) (by positivity) (fun x => ?_) i j
    · change |(EllipsoidGeometry.ellipsoidUpdateMatrix (castMatrix D)
        (fun i => (a i : ℝ)))⁻¹ i j| ≤ 4 ^ (T + 1)
      simpa only [one_div, inv_inv] using hh
    · rw [← rawShape_cast D (rational_symmetric D hD) a, ← quadratic_eq_dotProduct]
      exact hraw x
  · intro x
    rw [enlargedShape_quadratic]
    have hnonneg : 0 ≤ quadratic (castMatrix (rawShape D a)) x :=
      (show (0 : ℝ) ≤ (1 / 4 ^ (T + 1)) * ∑ i, x i ^ 2 by positivity).trans (hraw x)
    have heR : (0 : ℝ) ≤ e := Rat.cast_nonneg.mpr he
    have hf : 1 ≤ (1 + (e : ℝ)) ^ 2 := by nlinarith
    exact (hraw x).trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hf hnonneg)

end MWIS.AlgorithmPrecision
