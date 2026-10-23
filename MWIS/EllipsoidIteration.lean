module

public import MWIS.EllipsoidPerturbation

/-!
# Finite iteration bounds from rounded ellipsoid volume contraction

A sequence retaining a fixed feasible region cannot keep contracting after its
volume becomes smaller than a ball inside that region.
Prepared 2026-10-23.
-/

@[expose] public section

namespace MWIS.EllipsoidIteration

open Matrix MeasureTheory
open MWIS.EllipsoidGeometry MWIS.EllipsoidPerturbation

/-- Iterating a uniform exponential volume contraction gives an explicit
bound at every finite iteration count. -/
theorem volume_decay {n : ℕ} (E : ℕ → Set (Fin n → ℝ)) (γ : ℝ) (N : ℕ)
    (hstep : ∀ t < N,
      volume (E (t + 1)) ≤ ENNReal.ofReal (Real.exp (-γ)) * volume (E t)) :
    volume (E N) ≤ ENNReal.ofReal (Real.exp (-(N : ℝ) * γ)) * volume (E 0) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hprev := ih (fun t ht => hstep t (Nat.lt_trans ht (Nat.lt_succ_self N)))
    calc
      _ ≤ ENNReal.ofReal (Real.exp (-γ)) * volume (E N) :=
        hstep N (Nat.lt_succ_self N)
      _ ≤ ENNReal.ofReal (Real.exp (-γ)) *
          (ENNReal.ofReal (Real.exp (-(N : ℝ) * γ)) * volume (E 0)) :=
        mul_le_mul_right hprev _
      _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        congr 3
        push_cast
        ring

/-- The initial and inner balls may have different centres. A volume threshold
alone rules out continued containment after enough contractions. -/
theorem excludes_inner_ball {n : ℕ} (hn : 0 < n)
    (E : ℕ → Set (Fin n → ℝ)) (γ : ℝ) (N : ℕ)
    (z z' : Fin n → ℝ) (R r : ℝ) (hR : 0 < R) (hr : 0 < r)
    (hinit : E 0 = ellipsoid z (R ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)))
    (hstep : ∀ t < N,
      volume (E (t + 1)) ≤ ENNReal.ofReal (Real.exp (-γ)) * volume (E t))
    (hthreshold : Real.exp (-(N : ℝ) * γ) * R ^ n < r ^ n) :
    ¬ ellipsoid z' (r ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)) ⊆ E N := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  intro hcontain
  have hbound := (measure_mono hcontain).trans (volume_decay E γ N hstep)
  rw [hinit,
    volume_smul_square (0 : Fin n → ℝ) z _ Matrix.PosDef.one R hR,
    volume_smul_square (0 : Fin n → ℝ) z' _ Matrix.PosDef.one r hr] at hbound
  have hbase : ellipsoid (0 : Fin n → ℝ) (1 : Matrix (Fin n) (Fin n) ℝ) = quadBall n := by
    ext x
    simp only [ellipsoid, quadBall, inv_one, sub_zero, Matrix.one_mulVec,
      Set.mem_ofPred_eq]
  rw [hbase] at hbound
  have hcoef : ENNReal.ofReal (Real.exp (-(N : ℝ) * γ) * R ^ n) <
      ENNReal.ofReal (r ^ n) :=
    (ENNReal.ofReal_lt_ofReal_iff (pow_pos hr _)).mpr hthreshold
  have hstrict := ENNReal.mul_lt_mul_right
    (ne_of_gt (volume_quadBall_pos (n := n)))
    (ne_of_lt (volume_quadBall_lt_top (n := n))) hcoef
  have hstrict' : ENNReal.ofReal (Real.exp (-(N : ℝ) * γ)) *
      (ENNReal.ofReal (R ^ n) * volume (quadBall n)) <
      ENNReal.ofReal (r ^ n) * volume (quadBall n) := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    simpa only [mul_comm (volume (quadBall n))] using hstrict
  exact (not_lt_of_ge hbound) hstrict'

/-- The usual logarithmic iteration count implies the volume threshold. -/
theorem exponential_threshold (n N : ℕ) (γ R r : ℝ)
    (hR : 0 < R) (hr : 0 < r)
    (hcount : (n : ℝ) * Real.log (R / r) < (N : ℝ) * γ) :
    Real.exp (-(N : ℝ) * γ) * R ^ n < r ^ n := by
  have hlog : Real.log (R / r) = Real.log R - Real.log r :=
    Real.log_div hR.ne' hr.ne'
  have heqR : R ^ n = Real.exp ((n : ℝ) * Real.log R) := by
    rw [Real.exp_nat_mul, Real.exp_log hR]
  have heqr : r ^ n = Real.exp ((n : ℝ) * Real.log r) := by
    rw [Real.exp_nat_mul, Real.exp_log hr]
  rw [heqR, heqr, ← Real.exp_add]
  apply Real.exp_lt_exp.mpr
  rw [hlog] at hcount
  nlinarith

/-- A concrete rounded ellipsoid sequence cannot continue retaining an inner
ball beyond its logarithmic volume budget. -/
theorem rounded_excludes_inner_ball {n : ℕ} (hn : 2 ≤ n)
    (E : ℕ → Set (Fin n → ℝ)) (N : ℕ)
    (z z' : Fin n → ℝ) (R r : ℝ) (hR : 0 < R) (hr : 0 < r)
    (hinit : E 0 = ellipsoid z (R ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)))
    (hstep : ∀ t < N, volume (E (t + 1)) ≤
      ENNReal.ofReal (Real.exp (-(1 : ℝ) / (4 * ((n : ℝ) + 1)))) * volume (E t))
    (hcount : 4 * ((n : ℝ) + 1) * (n : ℝ) * Real.log (R / r) < N) :
    ¬ ellipsoid z' (r ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)) ⊆ E N := by
  apply excludes_inner_ball (by omega : 0 < n) E (1 / (4 * ((n : ℝ) + 1))) N
    z z' R r hR hr hinit
  · simpa only [neg_div] using hstep
  · apply exponential_threshold n N (1 / (4 * ((n : ℝ) + 1))) R r hR hr
    have hden : 0 < 4 * ((n : ℝ) + 1) := by positivity
    rw [mul_one_div, lt_div_iff₀ hden]
    nlinarith

/-- A dyadic bound on the outer-to-inner radius ratio gives a linear bound on
its logarithm. -/
theorem log_ratio_le_of_dyadic_bound (R r : ℝ) (hR : 0 < R) (hr : 0 < r)
    (L : ℕ) (hratio : R / r ≤ 2 ^ L) : Real.log (R / r) ≤ L := by
  have hlog := Real.log_le_log (div_pos hR hr) hratio
  rw [Real.log_pow] at hlog
  have htwo : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    exact hh
  exact hlog.trans (by simpa using mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg L))

/-- Powers-of-two radius bounds give an explicit polynomial number of rounded
central cuts. -/
theorem rounded_excludes_inner_ball_dyadic {n : ℕ} (hn : 2 ≤ n)
    (E : ℕ → Set (Fin n → ℝ)) (N L : ℕ)
    (z z' : Fin n → ℝ) (R r : ℝ) (hR : 0 < R) (hr : 0 < r)
    (hinit : E 0 = ellipsoid z (R ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)))
    (hstep : ∀ t < N, volume (E (t + 1)) ≤
      ENNReal.ofReal (Real.exp (-(1 : ℝ) / (4 * ((n : ℝ) + 1)))) * volume (E t))
    (hratio : R / r ≤ 2 ^ L) (hcount : 4 * (n + 1) * n * L < N) :
    ¬ ellipsoid z' (r ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)) ⊆ E N := by
  apply rounded_excludes_inner_ball hn E N z z' R r hR hr hinit hstep
  have hlog := log_ratio_le_of_dyadic_bound R r hR hr L hratio
  have hcountR : 4 * ((n : ℝ) + 1) * (n : ℝ) * (L : ℝ) < N := by
    exact_mod_cast hcount
  exact (mul_le_mul_of_nonneg_left hlog (by positivity)).trans_lt hcountR

/-- Membership in a spherical shape-matrix ellipsoid is the usual sum-of-
squares inequality. -/
theorem mem_spherical_ellipsoid_iff {n : ℕ} (z x : Fin n → ℝ)
    (r : ℝ) (hr : 0 < r) :
    x ∈ ellipsoid z (r ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)) ↔
      ∑ i, (x i - z i) ^ 2 ≤ r ^ 2 := by
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  change (x - z) ⬝ᵥ (r ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹.mulVec (x - z) ≤ 1 ↔ _
  rw [inverse_smul 1 Matrix.PosDef.one _ hr2.ne', inv_one, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_smul, smul_eq_mul, inv_mul_eq_div,
    div_le_one hr2]
  simp only [dotProduct, Pi.sub_apply, pow_two]

/-- A spherical ellipsoid of radius `r` lies inside the coordinate box of
radius `r` about the same centre. -/
theorem spherical_ellipsoid_coordinate_bound {n : ℕ} (z x : Fin n → ℝ)
    (r : ℝ) (hr : 0 < r)
    (hx : x ∈ ellipsoid z (r ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ))) (i : Fin n) :
    |x i - z i| ≤ r := by
  have hsum := (mem_spherical_ellipsoid_iff z x r hr).mp hx
  have hi : (x i - z i) ^ 2 ≤ ∑ j, (x j - z j) ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (x j - z j)) (Finset.mem_univ i)
  exact (sq_le_sq₀ (abs_nonneg _) hr.le).mp (by simpa using hi.trans hsum)

/-- A coordinate box of radius `M` lies in the spherical ellipsoid of radius
`n*M`; this avoids introducing a square root into the initial rational state. -/
theorem coordinate_box_subset_spherical_ellipsoid {n : ℕ} (hn : 0 < n)
    (z x : Fin n → ℝ) (M : ℝ) (hM : 0 < M)
    (hx : ∀ i, |x i - z i| ≤ M) :
    x ∈ ellipsoid z (((n : ℝ) * M) ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  apply (mem_spherical_ellipsoid_iff z x _ (mul_pos (by positivity) hM)).mpr
  calc
    ∑ i, (x i - z i) ^ 2 ≤ ∑ _ : Fin n, M ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have hi := (sq_le_sq₀ (abs_nonneg _) hM.le).mpr (hx i)
      simpa using hi
    _ = (n : ℝ) * M ^ 2 := by simp
    _ ≤ ((n : ℝ) * M) ^ 2 := by
      have hnn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hnn (sq_nonneg M)]

end MWIS.EllipsoidIteration

end
