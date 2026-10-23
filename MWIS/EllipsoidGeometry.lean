module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

/-!
# Exact central-cut ellipsoid geometry

The shape-matrix ellipsoid update preserves positive definiteness, contains
its retained half, and decreases volume by an explicit exponential factor.
Adapted from the accepted Formalpedia solutions for
`LinearOptimization.ellipsoid_update_halfspace_subset`,
`LinearOptimization.ellipsoid_update_matrix_posDef`, and
`LinearOptimization.ellipsoid_update_volume_lt` at source commit
`07bfe4bbb3858db507bb6ac0d725951c228119fc` (Apache-2.0).
The statements and proofs have been namespaced and the imports restricted.
Prepared 2026-10-23.
-/

@[expose] public section

namespace MWIS.EllipsoidGeometry

open Matrix MeasureTheory
open scoped MatrixOrder

/-- An ellipsoid with centre `z` and positive-definite shape matrix `D`.
Results below explicitly require positive definiteness. -/
def ellipsoid {n : ℕ} (z : Fin n → ℝ) (D : Matrix (Fin n) (Fin n) ℝ) :
    Set (Fin n → ℝ) :=
  {x | (x - z) ⬝ᵥ D⁻¹.mulVec (x - z) ≤ 1}

/-- Exact centre after retaining the halfspace whose inward normal is `a`. -/
noncomputable def ellipsoidUpdateCenter {n : ℕ} (z : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) : Fin n → ℝ :=
  z + ((1 : ℝ) / (n + 1)) • (Real.sqrt (a ⬝ᵥ D.mulVec a))⁻¹ • D.mulVec a

/-- Exact shape after a central cut in dimension at least two. -/
noncomputable def ellipsoidUpdateMatrix {n : ℕ}
    (D : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) •
    (D - ((2 : ℝ) / (n + 1)) • (a ⬝ᵥ D.mulVec a)⁻¹ •
      (D * vecMulVec a a * D))

theorem update_positive {n : ℕ} (hn : 2 ≤ n)
    (D : Matrix (Fin n) (Fin n) ℝ) (hD : D.PosDef)
    (a : Fin n → ℝ) (ha : a ≠ 0) :
    (ellipsoidUpdateMatrix D a).PosDef := by
  classical
  have hq : 0 < a ⬝ᵥ D.mulVec a := hD.dotProduct_mulVec_pos ha
  have hDt : Dᵀ = D := by
    simpa [Matrix.IsHermitian, Matrix.conjTranspose_apply] using hD.isHermitian.eq
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · unfold ellipsoidUpdateMatrix
    apply Matrix.IsHermitian.smul
    · apply Matrix.IsHermitian.sub hD.isHermitian
      apply Matrix.IsHermitian.smul
      apply Matrix.IsHermitian.smul
      have haHerm : (vecMulVec a a : Matrix (Fin n) (Fin n) ℝ).IsHermitian := by
        ext i j
        simp [vecMulVec, mul_comm]
      simpa [hDt] using Matrix.isHermitian_mul_mul_conjTranspose D haHerm
      exact isSelfAdjoint_iff.mpr (by simp)
      exact isSelfAdjoint_iff.mpr (by simp)
    · exact isSelfAdjoint_iff.mpr (by simp)
  · intro x hx
    have hs : 0 < x ⬝ᵥ D.mulVec x := hD.dotProduct_mulVec_pos hx
    let q : ℝ := a ⬝ᵥ D.mulVec a
    let p : ℝ := a ⬝ᵥ D.mulVec x
    let s : ℝ := x ⬝ᵥ D.mulVec x
    have hq' : 0 < q := by simpa [q] using hq
    have hs' : 0 < s := by simpa [s] using hs
    have hnonneg := hD.posSemidef.dotProduct_mulVec_nonneg
      (x - (p / q) • a)
    have hsymm : x ⬝ᵥ D.mulVec a = p := by
      dsimp [p]
      have hv : x ᵥ* D = Dᵀ.mulVec x := by
        simpa using Matrix.vecMul_transpose Dᵀ x
      calc
        x ⬝ᵥ D.mulVec a = x ᵥ* D ⬝ᵥ a := Matrix.dotProduct_mulVec _ _ _
        _ = Dᵀ.mulVec x ⬝ᵥ a := by rw [hv]
        _ = D.mulVec x ⬝ᵥ a := by rw [hDt]
        _ = a ⬝ᵥ D.mulVec x := dotProduct_comm _ _
    have hcs : p ^ 2 ≤ q * s := by
      simp only [star_trivial, Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct,
        smul_dotProduct, dotProduct_sub, dotProduct_smul, smul_eq_mul] at hnonneg
      rw [hsymm] at hnonneg
      change 0 ≤ s - (p / q) * p - (p / q) * (p - (p / q) * q) at hnonneg
      have hmul := mul_nonneg hq'.le hnonneg
      field_simp [ne_of_gt hq'] at hmul
      nlinarith
    have hquad :
        x ⬝ᵥ (D * vecMulVec a a * D).mulVec x = p ^ 2 := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        Matrix.vecMulVec_mulVec]
      simp [Matrix.mulVec_smul, dotProduct_smul, hsymm, p, pow_two]
    unfold ellipsoidUpdateMatrix
    simp only [star_trivial, Matrix.smul_mulVec, Matrix.sub_mulVec,
      dotProduct_smul, dotProduct_sub, smul_eq_mul]
    rw [hquad]
    change 0 < ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) *
      (s - (2 / ((n : ℝ) + 1)) * (q⁻¹ * p ^ 2))
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le (by norm_num) hnR
    have hden : 0 < (n : ℝ) ^ 2 - 1 := by
      nlinarith [sq_nonneg ((n : ℝ) - 2)]
    have hα : 0 < (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1) :=
      div_pos (sq_pos_of_pos hnpos) hden
    have hγ0 : 0 ≤ (2 : ℝ) / ((n : ℝ) + 1) := by positivity
    have hγ1 : (2 : ℝ) / ((n : ℝ) + 1) < 1 := by
      rw [div_lt_one (by positivity)]
      linarith
    have hpq : q⁻¹ * p ^ 2 ≤ s := by
      rw [inv_mul_eq_div, div_le_iff₀ hq']
      simpa [mul_comm] using hcs
    have hpq0 : 0 ≤ q⁻¹ * p ^ 2 := by positivity
    apply mul_pos hα
    nlinarith [mul_le_mul_of_nonneg_left hpq hγ0]

theorem update_inverse {n : ℕ} (hn : 2 ≤ n)
    (D : Matrix (Fin n) (Fin n) ℝ) (hD : D.PosDef)
    (a : Fin n → ℝ) (ha : a ≠ 0) :
    (ellipsoidUpdateMatrix D a)⁻¹ =
      ((((n : ℝ) ^ 2 - 1) / (n : ℝ) ^ 2) •
        (D⁻¹ + ((2 : ℝ) / ((n : ℝ) - 1)) •
          (a ⬝ᵥ D.mulVec a)⁻¹ • vecMulVec a a)) := by
  classical
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hn1 : (n : ℝ) - 1 ≠ 0 := by nlinarith
  have hden : (n : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith [sq_nonneg ((n : ℝ) - 2)]
  have hq : 0 < a ⬝ᵥ D.mulVec a := hD.dotProduct_mulVec_pos ha
  have hq0 : a ⬝ᵥ D.mulVec a ≠ 0 := ne_of_gt hq
  have hDunit : IsUnit D.det := (Matrix.isUnit_iff_isUnit_det D).mp hD.isUnit
  have hrank :
      vecMulVec a a * D * vecMulVec a a =
        (a ⬝ᵥ D.mulVec a) • vecMulVec a a := by
    ext i j
    simp only [Matrix.mul_apply, vecMulVec, Matrix.of_apply, dotProduct, mulVec,
      Matrix.smul_apply, smul_eq_mul]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y hy
    ring
  apply Matrix.inv_eq_left_inv
  unfold ellipsoidUpdateMatrix
  simp only [Matrix.smul_mul, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_sub]
  simp_rw [← Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul D hDunit]
  simp only [Matrix.one_mul]
  rw [hrank]
  simp only [Matrix.smul_mul]
  ext i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply, smul_eq_mul]
  field_simp [hn0, hn1, hden, hq0]
  ring_nf

theorem update_halfspace_subset {n : ℕ} (hn : 2 ≤ n)
    (z : Fin n → ℝ) (D : Matrix (Fin n) (Fin n) ℝ) (hD : D.PosDef)
    (a : Fin n → ℝ) (ha : a ≠ 0) :
    ellipsoid z D ∩ {x | a ⬝ᵥ z ≤ a ⬝ᵥ x} ⊆
      ellipsoid (ellipsoidUpdateCenter z D a) (ellipsoidUpdateMatrix D a) := by
  classical
  rintro x ⟨hxE, hxH⟩
  unfold ellipsoid at hxE ⊢
  let y : Fin n → ℝ := x - z
  let u : Fin n → ℝ := D.mulVec a
  let q : ℝ := a ⬝ᵥ D.mulVec a
  let p : ℝ := a ⬝ᵥ y
  let s : ℝ := y ⬝ᵥ D⁻¹.mulVec y
  let c : ℝ := 1 / ((n : ℝ) + 1)
  let δ : ℝ := 2 / ((n : ℝ) - 1)
  let β : ℝ := ((n : ℝ) ^ 2 - 1) / (n : ℝ) ^ 2
  let r : ℝ := Real.sqrt q
  change s ≤ 1 at hxE
  change a ⬝ᵥ z ≤ a ⬝ᵥ x at hxH
  have hp : 0 ≤ p := by
    dsimp [p, y]
    rw [dotProduct_sub]
    linarith
  have hq : 0 < q := by
    dsimp [q]
    exact hD.dotProduct_mulVec_pos ha
  have hr0 : 0 ≤ r := by simp [r]
  have hr : 0 < r := Real.sqrt_pos.2 hq
  have hr2 : r ^ 2 = q := by simp [r, Real.sq_sqrt hq.le]
  have hDunit : IsUnit D.det := (Matrix.isUnit_iff_isUnit_det D).mp hD.isUnit
  have hu : u ≠ 0 := by
    intro hu0
    have h := congrArg (D⁻¹.mulVec) hu0
    dsimp [u] at h
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul D hDunit] at h
    have : a = 0 := by simpa using h
    exact ha this
  have hDinvT : D⁻¹ᵀ = D⁻¹ := by
    simpa [Matrix.IsHermitian, Matrix.conjTranspose_apply] using hD.inv.isHermitian.eq
  have hsymmInv (v w : Fin n → ℝ) :
      v ⬝ᵥ D⁻¹.mulVec w = w ⬝ᵥ D⁻¹.mulVec v := by
    have hv : v ᵥ* D⁻¹ = D⁻¹ᵀ.mulVec v := by
      simpa using Matrix.vecMul_transpose D⁻¹ᵀ v
    calc
      v ⬝ᵥ D⁻¹.mulVec w = v ᵥ* D⁻¹ ⬝ᵥ w := Matrix.dotProduct_mulVec _ _ _
      _ = D⁻¹ᵀ.mulVec v ⬝ᵥ w := by rw [hv]
      _ = D⁻¹.mulVec v ⬝ᵥ w := by rw [hDinvT]
      _ = w ⬝ᵥ D⁻¹.mulVec v := dotProduct_comm _ _
  have hinvDmul (v : Fin n → ℝ) : D⁻¹.mulVec (D.mulVec v) = v := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul D hDunit]
    simp
  have hqu : u ⬝ᵥ D⁻¹.mulVec u = q := by
    rw [hsymmInv]
    simp [u, q, hinvDmul, dotProduct_comm]
  have hpu : u ⬝ᵥ D⁻¹.mulVec y = p := by
    rw [hsymmInv]
    simp [u, p, hinvDmul, dotProduct_comm]
  have hcs : p ^ 2 ≤ q * s := by
    have hnonneg := hD.inv.posSemidef.dotProduct_mulVec_nonneg
      (y - (p / q) • u)
    simp only [star_trivial, Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct,
      smul_dotProduct, dotProduct_sub, dotProduct_smul, smul_eq_mul] at hnonneg
    rw [hpu, hsymmInv y u, hpu, hqu] at hnonneg
    change 0 ≤ s - (p / q) * p - (p / q) * (p - (p / q) * q) at hnonneg
    have hmul := mul_nonneg hq.le hnonneg
    field_simp [ne_of_gt hq] at hmul
    nlinarith
  let t : ℝ := p / r
  have ht0 : 0 ≤ t := div_nonneg hp hr0
  have ht1 : t ≤ 1 := by
    have hp2q : p ^ 2 ≤ q := by nlinarith [mul_le_mul_of_nonneg_left hxE hq.le]
    dsimp [t]
    rw [div_le_one hr]
    nlinarith
  have hyb :
      x - ellipsoidUpdateCenter z D a = y - (c / r) • u := by
    ext i
    simp only [ellipsoidUpdateCenter, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    dsimp [y, u, c, r, q]
    field_simp [ne_of_gt hr]
    ring
  change (x - ellipsoidUpdateCenter z D a) ⬝ᵥ
      (ellipsoidUpdateMatrix D a)⁻¹.mulVec
        (x - ellipsoidUpdateCenter z D a) ≤ 1
  rw [update_inverse hn D hD a ha, hyb]
  change (y - (c / r) • u) ⬝ᵥ
      (β • (D⁻¹ + δ • q⁻¹ • vecMulVec a a)).mulVec
        (y - (c / r) • u) ≤ 1
  have hay : a ⬝ᵥ y = p := rfl
  have hau : a ⬝ᵥ u = q := rfl
  have hya : y ⬝ᵥ a = p := (dotProduct_comm y a).trans hay
  have hua : u ⬝ᵥ a = q := (dotProduct_comm u a).trans hau
  have hcalc :
      (y - (c / r) • u) ⬝ᵥ
          (β • (D⁻¹ + δ • q⁻¹ • vecMulVec a a)).mulVec
            (y - (c / r) • u) =
        β * (s + δ * t ^ 2 - (2 / ((n : ℝ) - 1)) * t +
          1 / ((n : ℝ) ^ 2 - 1)) := by
    simp only [Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.mulVec_sub,
      Matrix.mulVec_smul, Matrix.vecMulVec_mulVec, sub_dotProduct,
      smul_dotProduct, dotProduct_sub, dotProduct_smul,
      dotProduct_add, op_smul_eq_smul, smul_eq_mul]
    rw [hpu, hsymmInv y u, hpu, hqu]
    simp only [hay, hau, hya, hua]
    have hnR' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hnm1 : (n : ℝ) - 1 ≠ 0 := by nlinarith
    have hnp1 : (n : ℝ) + 1 ≠ 0 := by nlinarith
    have hnsq1 : (n : ℝ) ^ 2 - 1 ≠ 0 := by
      nlinarith [sq_nonneg ((n : ℝ) - 2)]
    dsimp [β, δ, c, t, s]
    rw [← hr2]
    field_simp [ne_of_gt hq, ne_of_gt hr, hnm1, hnp1, hnsq1]
    ring_nf
  rw [hcalc]
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by linarith
  have hn1 : 0 < (n : ℝ) - 1 := by linarith
  have hdenpos : 0 < (n : ℝ) ^ 2 - 1 := by
    nlinarith [sq_nonneg ((n : ℝ) - 2)]
  have hβ : 0 < β := by
    dsimp [β]
    positivity
  have htquad : t ^ 2 - t ≤ 0 := by nlinarith [mul_nonneg ht0 (sub_nonneg.mpr ht1)]
  dsimp [δ]
  have hinside :
      s + (2 / ((n : ℝ) - 1)) * t ^ 2 -
          (2 / ((n : ℝ) - 1)) * t + 1 / ((n : ℝ) ^ 2 - 1) ≤
        1 + 1 / ((n : ℝ) ^ 2 - 1) := by
    have hcoef : 0 ≤ (2 : ℝ) / ((n : ℝ) - 1) := by positivity
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hcoef htquad]
  have hβid : β * (1 + 1 / ((n : ℝ) ^ 2 - 1)) = 1 := by
    dsimp [β]
    field_simp [ne_of_gt hn0, ne_of_gt hdenpos]
    ring_nf
  calc
    β * (s + 2 / (↑n - 1) * t ^ 2 - 2 / (↑n - 1) * t +
      1 / (↑n ^ 2 - 1))
        ≤ β * (1 + 1 / (↑n ^ 2 - 1)) :=
          mul_le_mul_of_nonneg_left hinside hβ.le
    _ = 1 := hβid

/-- Euclidean unit ball in coordinate form. -/
def quadBall (n : ℕ) : Set (Fin n → ℝ) :=
  {x | x ⬝ᵥ x ≤ 1}

private theorem measurable_quadBall (n : ℕ) : MeasurableSet (quadBall n) := by
  apply IsClosed.measurableSet
  change IsClosed ((fun x : Fin n → ℝ => x ⬝ᵥ x) ⁻¹' Set.Iic 1)
  exact isClosed_Iic.preimage (by fun_prop)

theorem volume_quadBall_pos {n : ℕ} [Nonempty (Fin n)] :
    0 < volume (quadBall n) := by
  let U : Set (Fin n → ℝ) := {x | x ⬝ᵥ x < 1}
  have hUopen : IsOpen U := by
    change IsOpen ((fun x : Fin n → ℝ => x ⬝ᵥ x) ⁻¹' Set.Iio 1)
    exact isOpen_Iio.preimage (by fun_prop)
  have hUne : U.Nonempty := by
    refine ⟨0, ?_⟩
    simp [U, dotProduct]
  exact (hUopen.measure_pos volume hUne).trans_le <|
    measure_mono fun x hx => by
      change x ⬝ᵥ x < 1 at hx
      exact le_of_lt hx

theorem volume_quadBall_lt_top {n : ℕ} :
    volume (quadBall n) < ⊤ := by
  apply IsCompact.measure_lt_top
  rw [Metric.isCompact_iff_isClosed_bounded]
  constructor
  · change IsClosed ((fun x : Fin n → ℝ => x ⬝ᵥ x) ⁻¹' Set.Iic 1)
    exact isClosed_Iic.preimage (by fun_prop)
  · apply Metric.isBounded_closedBall.subset
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg zero_le_one).2
    intro i
    rw [Real.norm_eq_abs, abs_le]
    change x ⬝ᵥ x ≤ 1 at hx
    have hterm : x i ^ 2 ≤ x ⬝ᵥ x := by
      change x i ^ 2 ≤ ∑ j, x j * x j
      rw [sq]
      exact Finset.single_le_sum (fun j _ => mul_self_nonneg (x j)) (Finset.mem_univ i)
    constructor <;> nlinarith

private theorem ellipsoid_eq_preimage_invS {n : ℕ} (z : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin n) ℝ) (hD : D.PosDef) :
    ellipsoid z D =
      (fun x => (CFC.sqrt D)⁻¹.mulVec (x - z)) ⁻¹' quadBall n := by
  classical
  let S : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt D
  have hSsymm : S⁻¹ᵀ = S⁻¹ := by
    simpa [S, Matrix.IsHermitian, Matrix.conjTranspose_apply] using
      ((CFC.sqrt_nonneg D).posSemidef.isHermitian.inv.eq)
  have hDinvsq : D⁻¹ = S⁻¹ * S⁻¹ := by
    rw [← CFC.sq_sqrt D hD.posSemidef.nonneg]
    change (S ^ 2)⁻¹ = S⁻¹ * S⁻¹
    rw [← Matrix.inv_pow']
    simp [pow_two]
  ext x
  change ((x - z) ⬝ᵥ D⁻¹.mulVec (x - z) ≤ 1) ↔
    (S⁻¹.mulVec (x - z) ⬝ᵥ S⁻¹.mulVec (x - z) ≤ 1)
  rw [hDinvsq, ← Matrix.mulVec_mulVec]
  have hv : (x - z) ᵥ* S⁻¹ = S⁻¹ᵀ.mulVec (x - z) := by
    simpa using Matrix.vecMul_transpose S⁻¹ᵀ (x - z)
  rw [Matrix.dotProduct_mulVec, hv, hSsymm]

theorem ellipsoid_volume_formula {n : ℕ} (z : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin n) ℝ) (hD : D.PosDef) :
    volume (ellipsoid z D) =
      ENNReal.ofReal (Real.sqrt D.det) * volume (quadBall n) := by
  classical
  let S : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt D
  have hSdet : S.det = Real.sqrt D.det := by
    simpa [S] using hD.posSemidef.det_sqrt
  have hdetpos : 0 < D.det := hD.det_pos
  have hSdetpos : 0 < S.det := by rw [hSdet]; positivity
  have hSinvdet : S⁻¹.det ≠ 0 := by
    have hsqrt0 : Real.sqrt D.det ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hdetpos)
    simp [Matrix.det_nonsing_inv, hSdet, hsqrt0]
  rw [ellipsoid_eq_preimage_invS z D hD]
  -- Translation by `z` does not change volume.
  have htranslate :
      volume ((fun x => S⁻¹.mulVec (x - z)) ⁻¹' quadBall n) =
        volume ((fun x => S⁻¹.mulVec x) ⁻¹' quadBall n) := by
    let A : Set (Fin n → ℝ) := (fun x => S⁻¹.mulVec x) ⁻¹' quadBall n
    have hset :
        (fun x => S⁻¹.mulVec (x - z)) ⁻¹' quadBall n =
          (fun x => x + (-z)) ⁻¹' A := by
      ext x
      simp only [Set.mem_preimage, A]
      simp [sub_eq_add_neg]
    rw [hset, measure_preimage_add_right]
  rw [htranslate]
  have hmap := Real.map_matrix_volume_pi_eq_smul_volume_pi hSinvdet
  have happly := congrArg (fun μ : Measure (Fin n → ℝ) => μ (quadBall n)) hmap
  change (Measure.map (Matrix.toLin' S⁻¹) volume) (quadBall n) =
    (ENNReal.ofReal |S⁻¹.det⁻¹| • volume) (quadBall n) at happly
  rw [Measure.map_apply (by fun_prop) (measurable_quadBall n), Measure.smul_apply] at happly
  simp only [smul_eq_mul] at happly
  change volume ((fun x => S⁻¹.mulVec x) ⁻¹' quadBall n) =
    ENNReal.ofReal |S⁻¹.det⁻¹| * volume (quadBall n) at happly
  rw [happly]
  congr 1
  rw [Matrix.det_nonsing_inv, hSdet]
  simp [Ring.inverse_eq_inv, abs_of_pos (Real.sqrt_pos.2 hdetpos)]

theorem det_one_sub_vecMulVec {n : ℕ} (u v : Fin n → ℝ) (c : ℝ) :
    det (1 - c • vecMulVec u v) = 1 - c * (v ⬝ᵥ u) := by
  classical
  have hmat :
      -(c • vecMulVec u v) =
        Matrix.replicateCol Unit (-(c • u)) * Matrix.replicateRow Unit v := by
    ext i j
    simp [Matrix.mul_apply, Matrix.replicateCol, Matrix.replicateRow, vecMulVec]
    ring
  rw [sub_eq_add_neg, hmat, Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp only [dotProduct, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  have hsum : (∑ x, v x * -(c * u x)) = -c * (∑ x, v x * u x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  rw [hsum]
  ring

theorem ellipsoid_update_det {n : ℕ} (hn : 2 ≤ n)
    (D : Matrix (Fin n) (Fin n) ℝ) (hD : D.PosDef)
    (a : Fin n → ℝ) (ha : a ≠ 0) :
    (ellipsoidUpdateMatrix D a).det =
      (((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) ^ n) *
        (((n : ℝ) - 1) / ((n : ℝ) + 1)) * D.det := by
  classical
  let q : ℝ := a ⬝ᵥ D.mulVec a
  let c : ℝ := 2 / ((n : ℝ) + 1)
  have hq : 0 < q := by
    dsimp [q]
    exact hD.dotProduct_mulVec_pos ha
  have hsymm : Dᵀ = D := by
    simpa [Matrix.IsHermitian, Matrix.conjTranspose_apply] using hD.isHermitian.eq
  have hrank : vecMulVec a a * D = vecMulVec a (D.mulVec a) := by
    ext i j
    simp only [Matrix.mul_apply, vecMulVec, Matrix.of_apply, mulVec, dotProduct]
    have hentry (x : Fin n) : D x j = D j x := by
      have := congrFun (congrFun hsymm j) x
      simpa using this
    simp_rw [hentry]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  have hfactor :
      D - c • q⁻¹ • (D * vecMulVec a a * D) =
        D * (1 - (c * q⁻¹) • vecMulVec a (D.mulVec a)) := by
    rw [smul_smul]
    rw [Matrix.mul_assoc, hrank]
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul]
  unfold ellipsoidUpdateMatrix
  change det (((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) •
      (D - c • q⁻¹ • (D * vecMulVec a a * D))) = _
  rw [hfactor, Matrix.det_smul, Matrix.det_mul,
    det_one_sub_vecMulVec]
  simp only [Fintype.card_fin]
  have hdot : D.mulVec a ⬝ᵥ a = q := by
    dsimp [q]
    rw [dotProduct_comm]
  rw [hdot]
  have hq0 : q ≠ 0 := ne_of_gt hq
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  dsimp [c]
  field_simp [hq0]
  ring

theorem ellipsoid_ratio_lt_exp {n : ℕ} (hn : 2 ≤ n) :
    Real.sqrt
        ((((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) ^ n) *
          (((n : ℝ) - 1) / ((n : ℝ) + 1))) <
      Real.exp (-(1 : ℝ) / (2 * ((n : ℝ) + 1))) := by
  let N : ℝ := n
  let α : ℝ := N ^ 2 / (N ^ 2 - 1)
  let r : ℝ := (N - 1) / (N + 1)
  let A : ℝ := α ^ n * r
  have hN : (2 : ℝ) ≤ N := by
    dsimp [N]
    exact_mod_cast hn
  have hN0 : 0 < N := by linarith
  have hNm1 : 0 < N - 1 := by linarith
  have hNp1 : 0 < N + 1 := by linarith
  have hNsq : 0 < N ^ 2 - 1 := by nlinarith [sq_nonneg (N - 2)]
  have hα : 0 < α := by dsimp [α]; positivity
  have hr : 0 < r := by dsimp [r]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hαne : α ≠ 1 := by
    dsimp [α]
    intro h
    field_simp at h
    nlinarith
  have hαsub : α - 1 = 1 / (N ^ 2 - 1) := by
    dsimp [α]
    field_simp
    ring
  have hlogα : Real.log α < 1 / (N ^ 2 - 1) := by
    rw [← hαsub]
    exact Real.log_lt_sub_one_of_pos hα hαne
  let x : ℝ := 1 / N
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx1 : x < 1 := by dsimp [x]; rw [div_lt_one hN0]; linarith
  have hseries := Real.sum_range_le_log_div hx0 hx1 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.reduceMul, pow_one] at hseries
  have hlogbig : 2 * x ≤ Real.log ((1 + x) / (1 - x)) := by
    nlinarith
  have hratio_inv : r = ((1 + x) / (1 - x))⁻¹ := by
    dsimp [r, x]
    field_simp
  have hlogr : Real.log r ≤ -2 / N := by
    rw [hratio_inv, Real.log_inv]
    dsimp [x] at hlogbig ⊢
    have htwodiv : 2 * (1 / N) = 2 / N := by ring
    rw [htwodiv] at hlogbig
    calc
      -Real.log ((1 + 1 / N) / (1 - 1 / N)) ≤ -(2 / N) := neg_le_neg hlogbig
      _ = -2 / N := by ring
  have hlogAeq : Real.log A = N * Real.log α + Real.log r := by
    dsimp [A]
    rw [Real.log_mul (pow_ne_zero _ hα.ne') hr.ne', Real.log_pow]
  have hfirst : N * Real.log α < N / (N ^ 2 - 1) := by
    have := mul_lt_mul_of_pos_left hlogα hN0
    rwa [mul_one_div] at this
  have hrough : Real.log A < N / (N ^ 2 - 1) - 2 / N := by
    rw [hlogAeq]
    calc
      N * Real.log α + Real.log r < N / (N ^ 2 - 1) + Real.log r :=
        add_lt_add_of_lt_of_le hfirst (le_refl _)
      _ ≤ N / (N ^ 2 - 1) + (-2 / N) := add_le_add (le_refl _) hlogr
      _ = N / (N ^ 2 - 1) - 2 / N := by ring
  have hratbound : N / (N ^ 2 - 1) - 2 / N ≤ -1 / (N + 1) := by
    field_simp [ne_of_gt hN0, ne_of_gt hNsq, ne_of_gt hNp1]
    nlinarith [mul_nonneg (sub_nonneg.mpr hN) (by linarith : 0 ≤ N + 1)]
  have hlogA : Real.log A < -1 / (N + 1) := hrough.trans_le hratbound
  have hAexp : A < Real.exp (-1 / (N + 1)) :=
    (Real.log_lt_iff_lt_exp hA).mp hlogA
  change Real.sqrt A < Real.exp (-(1 : ℝ) / (2 * (N + 1)))
  rw [Real.sqrt_lt' (Real.exp_pos _)]
  rw [pow_two, ← Real.exp_add]
  have heq :
      -(1 : ℝ) / (2 * (N + 1)) + -(1 : ℝ) / (2 * (N + 1)) =
        -1 / (N + 1) := by
    field_simp [ne_of_gt hNp1]
    ring
  rw [heq]
  exact hAexp

theorem update_volume_lt {n : ℕ} (hn : 2 ≤ n)
    (z : Fin n → ℝ) (D : Matrix (Fin n) (Fin n) ℝ) (hD : D.PosDef)
    (a : Fin n → ℝ) (ha : a ≠ 0) :
    volume (ellipsoid (ellipsoidUpdateCenter z D a)
        (ellipsoidUpdateMatrix D a)) <
      ENNReal.ofReal (Real.exp (-(1 : ℝ) / (2 * ((n : ℝ) + 1)))) *
        volume (ellipsoid z D) := by
  classical
  let R : ℝ :=
    (((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) ^ n) *
      (((n : ℝ) - 1) / ((n : ℝ) + 1))
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hRpos : 0 < R := by
    have hn0R : 0 < (n : ℝ) := by linarith
    have hden : 0 < (n : ℝ) ^ 2 - 1 := by
      nlinarith [sq_nonneg ((n : ℝ) - 2)]
    dsimp [R]
    exact mul_pos (pow_pos (div_pos (sq_pos_of_pos hn0R) hden) _)
      (div_pos (by linarith) (by linarith))
  have hDbar : (ellipsoidUpdateMatrix D a).PosDef :=
    update_positive hn D hD a ha
  rw [ellipsoid_volume_formula _ _ hDbar,
    ellipsoid_volume_formula z D hD]
  rw [ellipsoid_update_det hn D hD a ha]
  change ENNReal.ofReal (Real.sqrt (R * D.det)) * volume (quadBall n) <
    ENNReal.ofReal (Real.exp (-(1 : ℝ) / (2 * ((n : ℝ) + 1)))) *
      (ENNReal.ofReal (Real.sqrt D.det) * volume (quadBall n))
  rw [Real.sqrt_mul hRpos.le]
  rw [ENNReal.ofReal_mul (Real.sqrt_nonneg R)]
  have hcoef :
      ENNReal.ofReal (Real.sqrt R) <
        ENNReal.ofReal (Real.exp (-(1 : ℝ) / (2 * ((n : ℝ) + 1)))) :=
    (ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos _)).2
      (by simpa [R] using ellipsoid_ratio_lt_exp hn)
  have hn0 : 0 < n := lt_of_lt_of_le (by omega : 0 < 2) hn
  let i0 : Fin n := ⟨0, hn0⟩
  let : Nonempty (Fin n) := ⟨i0⟩
  let K := ENNReal.ofReal (Real.sqrt D.det) * volume (quadBall n)
  have hKpos : 0 < K := by
    dsimp [K]
    exact ENNReal.mul_pos_iff.2
      ⟨ENNReal.ofReal_pos.2 (Real.sqrt_pos.2 hD.det_pos), volume_quadBall_pos⟩
  have hKtop : K ≠ ⊤ := by
    dsimp [K]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_of_lt volume_quadBall_lt_top)
  calc
    ENNReal.ofReal (Real.sqrt R) * ENNReal.ofReal (Real.sqrt D.det) *
          volume (quadBall n) = K * ENNReal.ofReal (Real.sqrt R) := by
            dsimp [K]; ac_rfl
    _ < K * ENNReal.ofReal (Real.exp (-(1 : ℝ) / (2 * ((n : ℝ) + 1)))) :=
      ENNReal.mul_lt_mul_right hKpos.ne' hKtop hcoef
    _ = ENNReal.ofReal (Real.exp (-(1 : ℝ) / (2 * ((n : ℝ) + 1)))) *
          (ENNReal.ofReal (Real.sqrt D.det) * volume (quadBall n)) := by
            dsimp [K]; ac_rfl

/-- The exact shape update has explicit lower and upper quadratic bounds. -/
theorem update_quadratic_bounds {n : ℕ} (hn : 2 ≤ n)
    (D : Matrix (Fin n) (Fin n) ℝ) (hD : D.PosDef)
    (a : Fin n → ℝ) (ha : a ≠ 0) (x : Fin n → ℝ) :
    ((n : ℝ) ^ 2 / ((n : ℝ) + 1) ^ 2) * (x ⬝ᵥ D.mulVec x) ≤
        x ⬝ᵥ (ellipsoidUpdateMatrix D a).mulVec x ∧
      x ⬝ᵥ (ellipsoidUpdateMatrix D a).mulVec x ≤
        ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) * (x ⬝ᵥ D.mulVec x) := by
  have hq : 0 < a ⬝ᵥ D.mulVec a := hD.dotProduct_mulVec_pos ha
  have hDt : Dᵀ = D := by
    simpa [Matrix.IsHermitian, Matrix.conjTranspose_apply] using hD.isHermitian.eq
  let q : ℝ := a ⬝ᵥ D.mulVec a
  let p : ℝ := a ⬝ᵥ D.mulVec x
  let s : ℝ := x ⬝ᵥ D.mulVec x
  have hq' : 0 < q := hq
  have hsymm : x ⬝ᵥ D.mulVec a = p := by
    dsimp [p]
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hDt, dotProduct_comm]
  have hnonneg := hD.posSemidef.dotProduct_mulVec_nonneg (x - (p / q) • a)
  simp only [star_trivial, Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct,
    smul_dotProduct, dotProduct_sub, dotProduct_smul, smul_eq_mul] at hnonneg
  rw [hsymm] at hnonneg
  change 0 ≤ s - (p / q) * p - (p / q) * (p - (p / q) * q) at hnonneg
  have hcs : p ^ 2 ≤ q * s := by
    have hmul := mul_nonneg hq'.le hnonneg
    field_simp [ne_of_gt hq'] at hmul
    nlinarith
  have hquad : x ⬝ᵥ (D * vecMulVec a a * D).mulVec x = p ^ 2 := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.vecMulVec_mulVec]
    simp [Matrix.mulVec_smul, dotProduct_smul, hsymm, p, pow_two]
  have heq : x ⬝ᵥ (ellipsoidUpdateMatrix D a).mulVec x =
      ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) *
        (s - (2 / ((n : ℝ) + 1)) * (q⁻¹ * p ^ 2)) := by
    unfold ellipsoidUpdateMatrix
    simp only [Matrix.smul_mulVec, Matrix.sub_mulVec, dotProduct_smul,
      dotProduct_sub, smul_eq_mul, hquad]
    rfl
  rw [heq]
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by linarith
  have hden : 0 < (n : ℝ) ^ 2 - 1 := by nlinarith
  have hnp : 0 < (n : ℝ) + 1 := by linarith
  have hα : 0 < (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1) :=
    div_pos (sq_pos_of_pos hnpos) hden
  have hγ : 0 ≤ (2 : ℝ) / ((n : ℝ) + 1) := by positivity
  have hpq : q⁻¹ * p ^ 2 ≤ s := by
    rw [inv_mul_eq_div, div_le_iff₀ hq']
    simpa [mul_comm] using hcs
  have hpq0 : 0 ≤ q⁻¹ * p ^ 2 := by positivity
  have hlow : ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) *
      (1 - 2 / ((n : ℝ) + 1)) = (n : ℝ) ^ 2 / ((n : ℝ) + 1) ^ 2 := by
    field_simp [hden.ne', hnp.ne']
    ring
  constructor
  · change ((n : ℝ) ^ 2 / ((n : ℝ) + 1) ^ 2) * s ≤ _
    rw [← hlow]
    have h := mul_le_mul_of_nonneg_left hpq hγ
    have hh := mul_le_mul_of_nonneg_left (show s - (2 / ((n : ℝ) + 1)) * s ≤
      s - (2 / ((n : ℝ) + 1)) * (q⁻¹ * p ^ 2) by linarith) hα.le
    nlinarith
  · change _ ≤ ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) * s
    apply mul_le_mul_of_nonneg_left _ hα.le
    exact sub_le_self _ (mul_nonneg hγ hpq0)

end MWIS.EllipsoidGeometry

end
