module

public import MWIS.IntegerFeasibilityEquiv
public import MWIS.IntegerFeasibilityInterior
public import MWIS.EllipsoidIteration

/-!
# Explicit inner and outer radii for integer linear feasibility

The perturbed system has a polynomial logarithmic radius ratio.
Prepared 2026-10-23.
-/

@[expose] public section

namespace MWIS.IntegerFeasibility

open Matrix LinearOptimization

namespace KhachAux

variable {m n : ℕ} {U : ℕ} {A : Matrix (Fin m) (Fin n) ℤ} {b : Fin m → ℤ}

lemma box_pos (n U : ℕ) : 0 < SmaleNinth.khachiyanBox n U := by
  unfold SmaleNinth.khachiyanBox
  positivity

/-- Every point of the perturbed-and-boxed polyhedron has sup-norm at most the box radius. -/
lemma abs_le_box {x : Fin n → ℝ}
    (hx : x ∈ polyhedron (SmaleNinth.khachiyanSystemA A) (SmaleNinth.khachiyanSystemb n U b))
    (j : Fin n) : |x j| ≤ SmaleNinth.khachiyanBox n U := by
  have hmem : ∀ i, SmaleNinth.khachiyanSystemb n U b i ≤
      (SmaleNinth.khachiyanSystemA A).mulVec x i := hx
  -- the row `m + j` says `x j ≥ -M`
  have hlow : -(SmaleNinth.khachiyanBox n U) ≤ x j := by
    have hij : (m + (j : ℕ)) < m + n + n := by omega
    have h := hmem ⟨m + (j : ℕ), hij⟩
    have hb : SmaleNinth.khachiyanSystemb n U b ⟨m + (j : ℕ), hij⟩
        = -(SmaleNinth.khachiyanBox n U) := by
      have hnlt : ¬ ((m + (j : ℕ)) < m) := by omega
      simp [SmaleNinth.khachiyanSystemb, dif_neg hnlt]
    have hA : (SmaleNinth.khachiyanSystemA A).mulVec x ⟨m + (j : ℕ), hij⟩ = x j := by
      have harith : (m + (j : ℕ)) - m = (j : ℕ) := by omega
      have hnlt1 : ¬ ((m + (j : ℕ)) < m) := by omega
      have hlt2 : (m + (j : ℕ)) < m + n := by omega
      simp only [Matrix.mulVec, dotProduct, SmaleNinth.khachiyanSystemA,
        dif_neg hnlt1, if_pos hlt2, harith]
      rw [Finset.sum_eq_single j]
      · simp
      · intro k _ hk
        have hkj : (k : ℕ) ≠ (j : ℕ) := fun hc => hk (Fin.ext hc)
        simp [hkj]
      · simp
    rw [hb, hA] at h
    exact h
  -- the row `m + n + j` says `-x j ≥ -M`
  have hhigh : x j ≤ SmaleNinth.khachiyanBox n U := by
    have hij : (m + n + (j : ℕ)) < m + n + n := by omega
    have h := hmem ⟨m + n + (j : ℕ), hij⟩
    have hb : SmaleNinth.khachiyanSystemb n U b ⟨m + n + (j : ℕ), hij⟩
        = -(SmaleNinth.khachiyanBox n U) := by
      have hnlt : ¬ ((m + n + (j : ℕ)) < m) := by omega
      simp [SmaleNinth.khachiyanSystemb, dif_neg hnlt]
    have hA : (SmaleNinth.khachiyanSystemA A).mulVec x ⟨m + n + (j : ℕ), hij⟩ = -x j := by
      have harith : (m + n + (j : ℕ)) - m - n = (j : ℕ) := by omega
      have hnlt1 : ¬ ((m + n + (j : ℕ)) < m) := by omega
      have hnlt2 : ¬ ((m + n + (j : ℕ)) < m + n) := by omega
      simp only [Matrix.mulVec, dotProduct, SmaleNinth.khachiyanSystemA,
        dif_neg hnlt1, if_neg hnlt2, harith]
      rw [Finset.sum_eq_single j]
      · simp
      · intro k _ hk
        have hkj : (k : ℕ) ≠ (j : ℕ) := fun hc => hk (Fin.ext hc)
        simp [hkj]
      · simp
    rw [hb, hA] at h
    linarith
  rw [abs_le]
  exact ⟨hlow, hhigh⟩


end KhachAux

open Matrix LinearOptimization SmaleNinth
open MWIS.EllipsoidGeometry MWIS.EllipsoidIteration

/-- A rational enclosing radius for the boxed system. -/
noncomputable def outerRadius (n U : ℕ) : ℝ := (n : ℝ) * khachiyanBox n U

/-- The perturbed system is enclosed in an explicitly specified sphere. -/
theorem boxed_subset_sphere {m n U : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) :
    polyhedron (khachiyanSystemA A) (khachiyanSystemb n U b) ⊆
      ellipsoid 0 (outerRadius n U ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
  intro x hx
  apply coordinate_box_subset_spherical_ellipsoid (by omega) 0 x _ (KhachAux.box_pos n U)
  intro i
  simpa using KhachAux.abs_le_box hx i

/-- Every feasible integer system gives an inner sphere in its perturbed system. -/
theorem exists_inner_sphere {m n U : ℕ} (hn : 1 ≤ n) (hU : 1 ≤ U)
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (hA : ∀ i j, |A i j| ≤ (U : ℤ)) (hb : ∀ i, |b i| ≤ (U : ℤ))
    (hne : (polyhedron (A.map (Int.cast : ℤ → ℝ)) (fun i => (b i : ℝ))).Nonempty) :
    ∃ x, ellipsoid x (VolAux.halfSide n U ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)) ⊆
      polyhedron (khachiyanSystemA A) (khachiyanSystemb n U b) := by
  obtain ⟨x, hx, hbd⟩ := integer_polyhedron_solution_bound U hU A b hA hb hne
  refine ⟨x, fun y hy => VolAux.cube_subset hn hU hA x hx hbd ?_⟩
  intro i _
  have hi := spherical_ellipsoid_coordinate_bound x y _ (VolAux.halfSide_pos hn hU) hy i
  rw [abs_le] at hi
  exact ⟨by linarith [hi.1], by linarith [hi.2]⟩

lemma nat_le_two_pow (n : ℕ) : (n : ℝ) ≤ 2 ^ n := by
  exact_mod_cast (Nat.lt_two_pow_self (n := n)).le

lemma factorial_le_dyadic (n : ℕ) : (n.factorial : ℝ) ≤ 2 ^ (n * n) := by
  have h : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
  calc
    (n.factorial : ℝ) ≤ (n : ℝ) ^ n := h
    _ ≤ (2 ^ n : ℝ) ^ n := pow_le_pow_left₀ (by positivity) (nat_le_two_pow n) n
    _ = 2 ^ (n * n) := (pow_mul _ _ _).symm

lemma box_le_dyadic (n U B : ℕ) (hU : (U : ℝ) ≤ 2 ^ B) :
    khachiyanBox n U ≤ 2 ^ (n * n + B * n + 1) := by
  have hu : (U : ℝ) ^ n ≤ 2 ^ (B * n) := by
    simpa only [pow_mul] using pow_le_pow_left₀ (by positivity) hU n
  have hp : (n.factorial : ℝ) * (U : ℝ) ^ n ≤ 2 ^ (n * n + B * n) := by
    rw [pow_add]
    exact mul_le_mul (factorial_le_dyadic n) hu (by positivity) (by positivity)
  have h1 : (1 : ℝ) ≤ 2 ^ (n * n + B * n) := one_le_pow₀ (by norm_num)
  unfold khachiyanBox
  rw [pow_succ]
  linarith

/-- A natural denominator of the inner radius. -/
def innerDenominator (n U : ℕ) : ℕ :=
  4 * n * U * (n + 1) * (n + 1).factorial * U ^ (n + 1)

theorem halfSide_eq_one_div (n U : ℕ) :
    VolAux.halfSide n U = 1 / (innerDenominator n U : ℝ) := by
  unfold VolAux.halfSide khachiyanEps innerDenominator
  push_cast
  simp only [div_div]
  congr 1
  ring

/-- Explicit logarithmic bounds for the inner denominator and outer radius. -/
def innerExponent (n B : ℕ) : ℕ :=
  2 + n + B + (n + 1) + (n + 1) * (n + 1) + B * (n + 1)

def outerExponent (n B : ℕ) : ℕ := n + (n * n + B * n + 1)

theorem innerDenominator_le_dyadic (n U B : ℕ) (hU : (U : ℝ) ≤ 2 ^ B) :
    (innerDenominator n U : ℝ) ≤ 2 ^ innerExponent n B := by
  have hn := nat_le_two_pow n
  have hn1 := nat_le_two_pow (n + 1)
  have hf := factorial_le_dyadic (n + 1)
  have hu : (U : ℝ) ^ (n + 1) ≤ 2 ^ (B * (n + 1)) := by
    simpa only [pow_mul] using pow_le_pow_left₀ (by positivity) hU (n + 1)
  unfold innerDenominator
  push_cast
  calc
    4 * (n : ℝ) * U * (n + 1) * (n + 1).factorial * U ^ (n + 1) ≤
        4 * 2 ^ n * 2 ^ B * 2 ^ (n + 1) * 2 ^ ((n + 1) * (n + 1)) *
          2 ^ (B * (n + 1)) := by
      gcongr
      simpa using hn1
    _ = 2 ^ innerExponent n B := by
      unfold innerExponent
      simp only [pow_add]
      norm_num

theorem outerRadius_le_dyadic (n U B : ℕ) (hU : (U : ℝ) ≤ 2 ^ B) :
    outerRadius n U ≤ 2 ^ outerExponent n B := by
  unfold outerRadius outerExponent
  rw [pow_add]
  exact mul_le_mul (nat_le_two_pow n) (box_le_dyadic n U B hU)
    (KhachAux.box_pos n U).le (by positivity)

/-- Polynomial exponent bounding the ratio needed in the volume argument. -/
def radiusExponent (n B : ℕ) : ℕ := 8 * (n + 2) ^ 2 * (B + 1)

theorem radius_ratio_le_dyadic (n U B : ℕ) (hU : (U : ℝ) ≤ 2 ^ B) :
    outerRadius n U / VolAux.halfSide n U ≤ 2 ^ radiusExponent n B := by
  rw [halfSide_eq_one_div, div_div_eq_mul_div, div_one]
  calc
    outerRadius n U * (innerDenominator n U : ℝ) ≤
        2 ^ (outerExponent n B + innerExponent n B) := by
      rw [pow_add]
      exact mul_le_mul (outerRadius_le_dyadic n U B hU)
        (innerDenominator_le_dyadic n U B hU) (by positivity) (by positivity)
    _ ≤ 2 ^ radiusExponent n B := by
      apply pow_le_pow_right₀ (by norm_num)
      unfold outerExponent innerExponent radiusExponent
      nlinarith

/-- The solver starts with a dyadic radius; its ratio has the same bound. -/
theorem dyadic_radius_ratio_le (n U B : ℕ) (hU : (U : ℝ) ≤ 2 ^ B) :
    (2 : ℝ) ^ outerExponent n B / VolAux.halfSide n U ≤ 2 ^ radiusExponent n B := by
  rw [halfSide_eq_one_div, div_div_eq_mul_div, div_one]
  calc
    (2 : ℝ) ^ outerExponent n B * (innerDenominator n U : ℝ) ≤
        2 ^ (outerExponent n B + innerExponent n B) := by
      rw [pow_add]
      exact mul_le_mul_of_nonneg_left (innerDenominator_le_dyadic n U B hU) (by positivity)
    _ ≤ 2 ^ radiusExponent n B := by
      apply pow_le_pow_right₀ (by norm_num)
      unfold outerExponent innerExponent radiusExponent
      nlinarith

/-- A concrete polynomial iteration budget for the rounded solver. -/
def feasibilityIterations (n B : ℕ) : ℕ :=
  4 * (n + 1) * n * radiusExponent n B + 1

theorem feasibilityIterations_polynomial (n B : ℕ) :
    feasibilityIterations n B ≤ 33 * (n + 2) ^ 4 * (B + 1) := by
  have h : (n + 1) * n ≤ (n + 2) ^ 2 := by nlinarith
  have hh := Nat.mul_le_mul_right (32 * (n + 2) ^ 2 * (B + 1)) h
  have h1 : 1 ≤ (n + 2) ^ 4 * (B + 1) := Nat.succ_le_of_lt (by positivity)
  unfold feasibilityIterations radiusExponent
  nlinarith [hh]

end MWIS.IntegerFeasibility

end
