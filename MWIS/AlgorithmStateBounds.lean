module

public import MWIS.AlgorithmPrecision
public import MWIS.EllipsoidShapeBounds

/-!
# Polynomial integer payload bounds along the rational solver

Prepared 2026-10-23.

The fixed precision controls each shape by a power of four. Positive-definite
Cauchy--Schwarz bounds each centre displacement independently of the size of
the separating normal, and rounding adds at most one grid unit.
-/

@[expose] public section
namespace MWIS.AlgorithmStateBounds

open Matrix
open scoped BigOperators
open AlgorithmEllipsoid AlgorithmMatrixRounding AlgorithmEllipsoidGeometry
open AlgorithmTrajectory AlgorithmPrecision

/-- The fixed-precision trajectory has a uniform power-of-four upper envelope. -/
theorem trajectory_upper {m n : ℕ} (hn : 2 ≤ n)
    (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) (B T t : ℕ) (ht : t ≤ T)
    (x : Fin n → ℝ) :
    quadratic (castMatrix (shape (precision n T)
      (trajectory A b (precision n T) (inflation n) (initial n (precision n T) B) t))) x ≤
      (4 : ℝ) ^ t * (2 : ℝ) ^ (2 * B) * ∑ i, x i ^ 2 := by
  let k := precision n T
  let e := inflation n
  induction t with
  | zero => simp [trajectory, initial_quadratic]
  | succ t ih =>
      have ht' : t ≤ T := by omega
      have ih := ih ht'
      let s := trajectory A b k e (initial n k B) t
      have hD := trajectory_positive hn A b k e (inflation_pos n).le
        _ (initial_positive n k B) t
      have hq : 0 ≤ quadratic (castMatrix (shape k s)) x := by
        rw [quadratic_eq_dotProduct]
        exact hD.posSemidef.dotProduct_mulVec_nonneg x
      have hstep : quadratic (castMatrix (shape k (advance A b k e s))) x ≤
          4 * quadratic (castMatrix (shape k s)) x := by
        unfold advance
        split
        · linarith
        · rename_i i hi
          split
          · linarith
          · rename_i ha
            let p := trajectory_stepPrecision hn A b B T t ht' (fun j => -A i j)
              (neg_normal_ne_zero (A i) ha)
            exact EllipsoidShapeBounds.update_upper hn k e (inflation_pos n).le (inflation_le n)
              s hD _ (neg_normal_ne_zero (A i) ha) p.shapeLower p.shape_margin p.enlarged_lower x
      change quadratic (castMatrix (shape k (advance A b k e s))) x ≤ _
      have h := mul_le_mul_of_nonneg_left ih (show (0 : ℝ) ≤ 4 by norm_num)
      rw [pow_succ]
      nlinarith

/-- Every diagonal entry of a continued shape satisfies the same upper envelope. -/
theorem trajectory_diagonal {m n : ℕ} (hn : 2 ≤ n)
    (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) (B T t : ℕ) (ht : t ≤ T)
    (i : Fin n) :
    (shape (precision n T)
      (trajectory A b (precision n T) (inflation n) (initial n (precision n T) B) t) i i : ℝ) ≤
      (4 : ℝ) ^ t * (2 : ℝ) ^ (2 * B) := by
  have h := trajectory_upper hn A b B T t ht (Pi.single i 1)
  rw [quadratic_eq_dotProduct] at h
  simpa [Matrix.mulVec_single_one, single_dotProduct, Matrix.col_apply,
    Pi.single_apply, castMatrix] using h

/-- Positive-definite Cauchy--Schwarz bounds each computed centre displacement
by a diagonal-radius bound, independently of the magnitude of the integer cut. -/
theorem approximate_displacement {n : ℕ} (k : ℕ) (z : Fin n → ℚ)
    (D : Matrix (Fin n) (Fin n) ℚ) (hD : (castMatrix D).PosDef)
    (a : Fin n → ℤ) (ha : a ≠ 0) (R : ℝ) (hR : 0 ≤ R)
    (hdiag : ∀ i, (D i i : ℝ) ≤ R ^ 2) (i : Fin n) :
    |(approximateCenter k z D a i : ℝ) - (z i : ℝ)| ≤ R := by
  let v : Fin n → ℝ := fun i => a i
  let q : ℝ := normalSquare D a
  let u : ℝ := AlgorithmSqrt.upper k (normalSquare D a)
  let d : ℝ := direction D a i
  have hq : 0 < q := by
    rw [show q = v ⬝ᵥ (castMatrix D).mulVec v from normalSquare_cast D a]
    exact hD.dotProduct_mulVec_pos (normal_cast_ne_zero a ha)
  have hu : 0 < u := Rat.cast_pos.mpr (AlgorithmSqrt.upper_positive k _)
  have hqu : q < u ^ 2 := by
    have h : (normalSquare D a : ℝ) < (AlgorithmSqrt.upper k (normalSquare D a) : ℝ) ^ 2 := by
      exact_mod_cast AlgorithmSqrt.lt_upper_sq k (normalSquare D a)
    exact h
  have hcs : d ^ 2 ≤ (D i i : ℝ) * q := by
    have h := hD.star_dotProduct_mulVec_mul_le (Pi.single i 1) v
    have hd : d = (castMatrix D).mulVec v i := congrFun (direction_cast D a) i
    have hqeq : q = v ⬝ᵥ (castMatrix D).mulVec v := normalSquare_cast D a
    simpa [pow_two, hd, hqeq, castMatrix] using h
  have hd : |d| ≤ R * u := by
    apply abs_le_of_sq_le_sq _ (mul_nonneg hR hu.le)
    have h := mul_le_mul_of_nonneg_right (hdiag i) hq.le
    have hu' := mul_le_mul_of_nonneg_left hqu.le (sq_nonneg R)
    nlinarith
  have hn : (1 : ℝ) ≤ n + 1 := by have h := Nat.cast_nonneg (α := ℝ) n; linarith
  have hden : 0 < ((n : ℝ) + 1) * u := mul_pos (by linarith) hu
  have hdisp : (approximateCenter k z D a i : ℝ) - (z i : ℝ) = d / (((n : ℝ) + 1) * u) := by
    simp [approximateCenter, d, u]
  rw [hdisp, abs_div, abs_of_pos hden]
  apply (div_le_iff₀ hden).mpr
  have h := mul_le_mul_of_nonneg_left hn (mul_nonneg hR hu.le)
  nlinarith

/-- Powers of four give the corresponding squared dyadic radius. -/
theorem shape_radius_identity (T B : ℕ) :
    (4 : ℝ) ^ T * (2 : ℝ) ^ (2 * B) = (2 ^ (T + B) : ℝ) ^ 2 := by
  have ht : ((2 : ℝ) ^ T) ^ 2 = 4 ^ T := by
    rw [← pow_mul, Nat.mul_comm T 2, pow_mul]
    norm_num
  rw [pow_add, mul_pow, ht, ← pow_mul, Nat.mul_comm B 2]

/-- One dyadic radius bound controls every diagonal throughout the finite run. -/
theorem uniform_diagonal {m n : ℕ} (hn : 2 ≤ n)
    (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) (B T t : ℕ) (ht : t ≤ T)
    (i : Fin n) :
    (shape (precision n T)
      (trajectory A b (precision n T) (inflation n) (initial n (precision n T) B) t) i i : ℝ) ≤
      (2 ^ (T + B) : ℝ) ^ 2 := by
  apply (trajectory_diagonal hn A b B T t ht i).trans
  rw [← shape_radius_identity]
  gcongr <;> norm_num

/-- The actual stored centre step moves each coordinate by at most the radius
bound plus one; the last unit accounts for dyadic coordinate rounding. -/
theorem stored_displacement {n : ℕ} (k : ℕ) (ε : ℚ) (s : State n)
    (hD : (castMatrix (shape k s)).PosDef) (a : Fin n → ℤ) (ha : a ≠ 0)
    (R : ℝ) (hR : 0 ≤ R) (hdiag : ∀ i, (shape k s i i : ℝ) ≤ R ^ 2)
    (i : Fin n) :
    |(center k (update k ε s a) i : ℝ) - (center k s i : ℝ)| ≤ R + 1 := by
  have hd := approximate_displacement k (center k s) (shape k s) hD a ha R hR hdiag i
  have hr : |(center k (update k ε s a) i : ℝ) -
      (approximateCenter k (center k s) (shape k s) a i : ℝ)| < 1 / (2 : ℝ) ^ k := by
    have h : ((|center k (update k ε s a) i -
        approximateCenter k (center k s) (shape k s) a i| : ℚ) : ℝ) < ((1 / 2 ^ k : ℚ) : ℝ) :=
      Rat.cast_lt.mpr (update_center_error k ε s a i)
    simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_one,
      Rat.cast_pow, Rat.cast_ofNat] using h
  have hg : 1 / (2 : ℝ) ^ k ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    exact one_le_pow₀ (by norm_num)
  have ht := abs_sub_le (center k (update k ε s a) i : ℝ)
    (approximateCenter k (center k s) (shape k s) a i : ℝ) (center k s i : ℝ)
  linarith

/-- Every stored centre coordinate grows at most linearly in the step count
and the uniform radius bound. -/
theorem trajectory_center {m n : ℕ} (hn : 2 ≤ n)
    (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) (B T t : ℕ) (ht : t ≤ T)
    (i : Fin n) :
    |(center (precision n T)
      (trajectory A b (precision n T) (inflation n) (initial n (precision n T) B) t) i : ℝ)| ≤
      (t : ℝ) * (2 ^ (T + B) + 1) := by
  let k := precision n T
  let e := inflation n
  let R : ℝ := 2 ^ (T + B)
  have hR : 0 ≤ R := by positivity
  induction t with
  | zero => simp [trajectory, initial_center]
  | succ t ih =>
      have ht' : t ≤ T := by omega
      have ih := ih ht'
      let s := trajectory A b k e (initial n k B) t
      have hD := trajectory_positive hn A b k e (inflation_pos n).le _ (initial_positive n k B) t
      change |(center k (advance A b k e s) i : ℝ)| ≤ _
      unfold advance
      split
      · simp only [Nat.cast_add, Nat.cast_one]
        change |(center k s i : ℝ)| ≤ ((t : ℝ) + 1) * (R + 1)
        change |(center k s i : ℝ)| ≤ (t : ℝ) * (R + 1) at ih
        nlinarith
      · rename_i j hj
        split
        · simp only [Nat.cast_add, Nat.cast_one]
          change |(center k s i : ℝ)| ≤ ((t : ℝ) + 1) * (R + 1)
          change |(center k s i : ℝ)| ≤ (t : ℝ) * (R + 1) at ih
          nlinarith
        · rename_i ha
          have hd := stored_displacement k e s hD (fun l => -A j l)
            (neg_normal_ne_zero (A j) ha) R hR (uniform_diagonal hn A b B T t ht') i
          have ht := abs_sub_le (center k (update k e s (fun l => -A j l)) i : ℝ)
            (center k s i : ℝ) 0
          simp only [sub_zero, Nat.cast_add, Nat.cast_one] at *
          change |(center k s i : ℝ)| ≤ (t : ℝ) * (R + 1) at ih
          nlinarith

/-- A binary exponent polynomial in the run budget bounds every centre magnitude. -/
theorem trajectory_center_power {m n : ℕ} (hn : 2 ≤ n)
    (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) (B T t : ℕ) (ht : t ≤ T)
    (i : Fin n) :
    |(center (precision n T)
      (trajectory A b (precision n T) (inflation n) (initial n (precision n T) B) t) i : ℝ)| ≤
      (2 : ℝ) ^ (2 * T + B + 1) := by
  have h := trajectory_center hn A b B T t ht i
  have htR : (t : ℝ) ≤ T := by exact_mod_cast ht
  have hT : (T : ℝ) ≤ (2 : ℝ) ^ T := by exact_mod_cast Nat.le_of_lt T.lt_two_pow_self
  have hp : (1 : ℝ) ≤ 2 ^ (T + B) := one_le_pow₀ (by norm_num)
  calc
    _ ≤ (t : ℝ) * (2 ^ (T + B) + 1) := h
    _ ≤ (2 : ℝ) ^ T * (2 * 2 ^ (T + B)) :=
      mul_le_mul (htR.trans hT) (by linarith) (by positivity) (by positivity)
    _ = _ := by rw [show 2 * T + B + 1 = T + (T + B) + 1 by omega, pow_add, pow_add]; ring

/-- Every stored shape entry has the uniform exponential magnitude envelope. -/
theorem trajectory_shape_power {m n : ℕ} (hn : 2 ≤ n)
    (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) (B T t : ℕ) (ht : t ≤ T)
    (i j : Fin n) :
    |(shape (precision n T)
      (trajectory A b (precision n T) (inflation n) (initial n (precision n T) B) t) i j : ℝ)| ≤
      (2 : ℝ) ^ (2 * T + 2 * B) := by
  have hD := trajectory_positive hn A b (precision n T) (inflation n) (inflation_pos n).le
    _ (initial_positive n (precision n T) B) t
  have h := EllipsoidInverseBounds.abs_entry_le_of_diagonal_le _ hD.posSemidef
    (((2 : ℝ) ^ (T + B)) ^ 2) (uniform_diagonal hn A b B T t ht) i j
  change |(_ : ℝ)| ≤ _ at h
  convert h using 1
  · rfl
  · rw [← pow_mul]
    congr 1
    omega

/-- A dyadic value of bounded magnitude has a linearly bounded stored numerator. -/
theorem dyadic_numerator_size (k B : ℕ) (a : ℤ)
    (ha : |((AlgorithmRounding.dyadic k a : ℚ) : ℝ)| ≤ 2 ^ B) :
    a.natAbs.size ≤ k + B + 1 := by
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  have habs : |(a : ℝ)| ≤ (2 : ℝ) ^ B * 2 ^ k := by
    simp only [AlgorithmRounding.dyadic, Rat.cast_div, Rat.cast_intCast,
      Rat.cast_pow, Rat.cast_ofNat, abs_div, abs_of_pos hp] at ha
    exact (div_le_iff₀ hp).mp ha
  have he : (a.natAbs : ℝ) = |(a : ℝ)| := by
    rw [← Int.cast_abs]
    exact congrArg (fun z : ℤ => (z : ℝ)) (Int.natCast_natAbs a)
  rw [← he, ← pow_add, Nat.add_comm B k] at habs
  have hn : a.natAbs ≤ (2 : ℕ) ^ (k + B) := by exact_mod_cast habs
  simpa only [Nat.size_pow] using Nat.size_le_size hn

/-- All integer payloads actually stored during the finite run have one explicit
polynomial binary-length bound. This includes every centre and shape entry. -/
theorem trajectory_payloadBits {m n : ℕ} (hn : 2 ≤ n)
    (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) (B T t : ℕ) (ht : t ≤ T) :
    payloadBits
      (trajectory A b (precision n T) (inflation n) (initial n (precision n T) B) t) ≤
      n * (precision n T + 2 * T + B + 3) +
        n ^ 2 * (precision n T + 2 * T + 2 * B + 2) := by
  let k := precision n T
  let s := trajectory A b k (inflation n) (initial n k B) t
  have hc (i : Fin n) : (s.centerNumerator i).natAbs.size ≤ k + 2 * T + B + 2 := by
    have h := dyadic_numerator_size k (2 * T + B + 1) (s.centerNumerator i)
      (trajectory_center_power hn A b B T t ht i)
    omega
  have hs (i j : Fin n) : (s.shapeNumerator i j).natAbs.size ≤ k + 2 * T + 2 * B + 1 := by
    have h := dyadic_numerator_size k (2 * T + 2 * B) (s.shapeNumerator i j)
      (trajectory_shape_power hn A b B T t ht i j)
    omega
  change payloadBits s ≤ _
  unfold payloadBits
  apply add_le_add
  · calc
      _ ≤ ∑ _i : Fin n, (k + 2 * T + B + 3) :=
        Finset.sum_le_sum (fun i _ => by have h := hc i; omega)
      _ = _ := by simp [k]
  · calc
      _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, (k + 2 * T + 2 * B + 2) :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => by have h := hs i j; omega))
      _ = _ := by simp [k, pow_two, mul_assoc]

end MWIS.AlgorithmStateBounds
