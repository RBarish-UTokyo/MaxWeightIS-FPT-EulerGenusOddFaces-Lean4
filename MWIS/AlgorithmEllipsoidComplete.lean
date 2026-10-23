module

public import MWIS.AlgorithmTrajectory
public import MWIS.EllipsoidUpdateBridge
public import MWIS.EllipsoidIteration

/-!
# Completeness of finite rounded ellipsoid runs

An exhausted execution supplies every actual separating cut along its
continued trajectory. The verified numerical margins imply retention of
all feasible points and uniform volume contraction. Consequently, a
feasible inner ball rules out exhaustion after the explicit volume budget.

Prepared 2026-10-23.
-/

@[expose] public section
namespace MWIS.AlgorithmEllipsoidComplete

open Matrix MeasureTheory
open scoped BigOperators
open AlgorithmEllipsoid AlgorithmMatrixRounding AlgorithmTrajectory
open EllipsoidCenterRounding EllipsoidUpdateBridge

/-- The real solution set tested by the executable integer-row separator. -/
def realFeasible {m n : ℕ} (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) :
    Set (Fin n → ℝ) := {x | ∀ i, (∑ j, (A i j : ℝ) * x j) ≤ (b i : ℝ)}

/-- The real ellipsoid represented by one finite integer payload. -/
def stateEllipsoid {n : ℕ} (k : ℕ) (state : State n) : Set (Fin n → ℝ) :=
  EllipsoidGeometry.ellipsoid (castVector (center k state)) (castMatrix (shape k state))

/-- The executable initial payload represents exactly its claimed dyadic ball. -/
theorem initial_ellipsoid (n k B : ℕ) :
    stateEllipsoid k (initial n k B) = EllipsoidGeometry.ellipsoid 0
      (((2 : ℝ) ^ B) ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
  have hc : castVector (center k (initial n k B)) = 0 := by
    rw [initial_center]
    ext i
    simp [castVector]
  have hD : castMatrix (shape k (initial n k B)) =
      ((2 : ℝ) ^ B) ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    simp only [castMatrix, initial_shape, Matrix.smul_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst j
      simp [pow_mul, Nat.mul_comm]
    · simp [hij]
  rw [stateEllipsoid, hc, hD]

/-- Casting a rational feasible point gives exactly real feasibility. -/
theorem feasible_cast_iff {m n : ℕ} (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ)
    (x : Fin n → ℚ) : castVector x ∈ realFeasible A b ↔ AlgorithmSeparation.Feasible A b x := by
  unfold realFeasible AlgorithmSeparation.Feasible
  simp only [Set.mem_ofPred_eq]
  apply forall_congr'
  intro i
  have he : (∑ j, (A i j : ℝ) * castVector x j) =
      (AlgorithmSeparation.rationalDot (A i) x : ℝ) := by
    simp [AlgorithmSeparation.rationalDot, castVector]
  rw [he]
  exact Rat.cast_le

/-- The sign-reversed reported row defines a central cut retaining every real
feasible point, including irrational points. -/
theorem separate_real_halfspace {m n : ℕ} (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ)
    (x : Fin n → ℚ) (i : Fin m) (hi : AlgorithmSeparation.separate A b x = some i)
    (y : Fin n → ℝ) (hy : y ∈ realFeasible A b) :
    castNormal (fun j => -A i j) ⬝ᵥ castVector x ≤
      castNormal (fun j => -A i j) ⬝ᵥ y := by
  have hv := AlgorithmSeparation.separate_some_violated A b x i hi
  have hvR : (b i : ℝ) < (AlgorithmSeparation.rationalDot (A i) x : ℝ) :=
    Rat.cast_lt.mpr hv
  have hxcast : (AlgorithmSeparation.rationalDot (A i) x : ℝ) =
      ∑ j, (A i j : ℝ) * castVector x j := by
    simp [AlgorithmSeparation.rationalDot, castVector]
  rw [hxcast] at hvR
  have hyi := hy i
  simp only [castNormal, Int.cast_neg, dotProduct, neg_mul, Finset.sum_neg_distrib]
  linarith

/-- A zero reported row also rules out real feasible points. -/
theorem separate_zeroRow_real {m n : ℕ} (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ)
    (x : Fin n → ℚ) (i : Fin m) (hi : AlgorithmSeparation.separate A b x = some i)
    (hz : A i = 0) : ¬ (realFeasible A b).Nonempty := by
  rintro ⟨y, hy⟩
  have hv := AlgorithmSeparation.separate_some_violated A b x i hi
  have hvR : (b i : ℝ) < (AlgorithmSeparation.rationalDot (A i) x : ℝ) :=
    Rat.cast_lt.mpr hv
  have hyi := hy i
  simp [hz, AlgorithmSeparation.rationalDot] at hvR hyi
  linarith

/-- A reported zero-row result certifies real infeasibility. -/
theorem run_zeroRow_real {m n : ℕ} (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ)
    (k : ℕ) (ε : ℚ) (fuel : ℕ) (s : State n)
    (h : run A b k ε fuel s = .zeroRow) : ¬ (realFeasible A b).Nonempty := by
  induction fuel generalizing s with
  | zero =>
      unfold run at h
      split at h
      · contradiction
      · rename_i i hi
        split at h
        · rename_i hz
          exact separate_zeroRow_real A b _ i hi hz
        · contradiction
  | succ fuel ih =>
      unfold run at h
      split at h
      · contradiction
      · rename_i i hi
        split at h
        · rename_i hz
          exact separate_zeroRow_real A b _ i hi hz
        · exact ih _ h

/-- An exhausted execution remains exhausted after removing any initial number
of its performed updates. -/
theorem exhausted_at {m n : ℕ} (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ)
    (k : ℕ) (ε : ℚ) (T : ℕ) (s : State n)
    (h : run A b k ε T s = .exhausted) (t : ℕ) (ht : t ≤ T) :
    run A b k ε (T - t) (trajectory A b k ε s t) = .exhausted := by
  have hc : ∀ t, t ≤ T → run A b k ε (T - t) (trajectory A b k ε s t) = .exhausted := by
    intro t
    induction t with
    | zero => intro _; simpa [trajectory] using h
    | succ t ih =>
        intro ht
        have hh := ih (by omega)
        have he : T - t = (T - (t + 1)) + 1 := by omega
        rw [he] at hh
        exact exhausted_succ A b k ε (T - (t + 1)) _ hh
  exact hc t ht

/-- Every state up to the exhausted budget has an actual nonzero separating row. -/
theorem exhausted_cut_at {m n : ℕ} (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ)
    (k : ℕ) (ε : ℚ) (T : ℕ) (s : State n)
    (h : run A b k ε T s = .exhausted) (t : ℕ) (ht : t ≤ T) :
    ∃ i, AlgorithmSeparation.separate A b (center k (trajectory A b k ε s t)) = some i ∧ A i ≠ 0 :=
  exhausted_has_cut A b k ε (T - t) _ (exhausted_at A b k ε T s h t ht)

/-- A feasible region contained initially remains inside every ellipsoid of an
exhausted computation, under the explicit per-update arithmetic margins. -/
theorem exhausted_retains {m n : ℕ} (hn : 2 ≤ n)
    (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) (k : ℕ) (ε : ℚ) (hε : 0 < ε)
    (T : ℕ) (s : State n) (hs : (castMatrix (shape k s)).PosDef)
    (h : run A b k ε T s = .exhausted)
    (hprecision : ∀ t < T, ∀ i,
      AlgorithmSeparation.separate A b (center k (trajectory A b k ε s t)) = some i →
      A i ≠ 0 → Nonempty (StepPrecision k ε (trajectory A b k ε s t) (fun j => -A i j)))
    (region : Set (Fin n → ℝ)) (hfeas : region ⊆ realFeasible A b)
    (hinit : region ⊆ stateEllipsoid k s) (t : ℕ) (ht : t ≤ T) :
    region ⊆ stateEllipsoid k (trajectory A b k ε s t) := by
  have hc : ∀ t, t ≤ T → region ⊆ stateEllipsoid k (trajectory A b k ε s t) := by
    intro t
    induction t with
    | zero => intro _; exact hinit
    | succ t ih =>
        intro ht
        obtain ⟨i, hi, ha⟩ := exhausted_cut_at A b k ε T s h t (by omega)
        obtain ⟨p⟩ := hprecision t (by omega) i hi ha
        have hp := trajectory_positive hn A b k ε hε.le s hs t
        have hcut := update_halfspace_subset hn k ε hε _ (fun j => -A i j) hp
          (neg_normal_ne_zero (A i) ha) p.normalLower p.inverseBound
          p.normalLower_pos p.inverseBound_nonneg p.normalSquare_lower
          p.sqrt_margin p.inverse_entries p.center_margin
        have hadv : trajectory A b k ε s (t + 1) =
            update k ε (trajectory A b k ε s t) (fun j => -A i j) := by
          simp only [trajectory, advance, hi, ite_eq_right (by exact ha)]
        rw [hadv]
        intro y hy
        apply hcut
        exact ⟨ih (by omega) hy, separate_real_halfspace A b _ i hi y (hfeas hy)⟩
  exact hc t ht

/-- Every update of an exhausted computation has the proved uniform volume
contraction; the conclusion is about the actual integer payload trajectory. -/
theorem exhausted_volume_step {m n : ℕ} (hn : 2 ≤ n)
    (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) (k : ℕ) (ε : ℚ) (hε : 0 < ε)
    (hεmax : (ε : ℝ) ≤ 1 / (32 * ((n : ℝ) + 1) ^ 2))
    (T : ℕ) (s : State n) (hs : (castMatrix (shape k s)).PosDef)
    (h : run A b k ε T s = .exhausted)
    (hprecision : ∀ t < T, ∀ i,
      AlgorithmSeparation.separate A b (center k (trajectory A b k ε s t)) = some i →
      A i ≠ 0 → Nonempty (StepPrecision k ε (trajectory A b k ε s t) (fun j => -A i j)))
    (t : ℕ) (ht : t < T) :
    volume (stateEllipsoid k (trajectory A b k ε s (t + 1))) ≤
      ENNReal.ofReal (Real.exp (-(1 : ℝ) / (4 * ((n : ℝ) + 1)))) *
        volume (stateEllipsoid k (trajectory A b k ε s t)) := by
  obtain ⟨i, hi, ha⟩ := exhausted_cut_at A b k ε T s h t ht.le
  obtain ⟨p⟩ := hprecision t ht i hi ha
  have hp := trajectory_positive hn A b k ε hε.le s hs t
  have hadv : trajectory A b k ε s (t + 1) =
      update k ε (trajectory A b k ε s t) (fun j => -A i j) := by
    simp only [trajectory, advance, hi, ite_eq_right (by exact ha)]
  rw [hadv]
  exact update_volume_le hn k ε hε.le hεmax _ _ hp
    (neg_normal_ne_zero (A i) ha) p.shapeLower p.shape_margin p.enlarged_lower

/-- A feasible inner ball excludes budget exhaustion after the explicit
polynomial number of volume-reducing updates. -/
theorem not_exhausted_of_inner_ball {m n : ℕ} (hn : 2 ≤ n)
    (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) (k : ℕ) (ε : ℚ) (hε : 0 < ε)
    (hεmax : (ε : ℝ) ≤ 1 / (32 * ((n : ℝ) + 1) ^ 2))
    (T L : ℕ) (s : State n) (hs : (castMatrix (shape k s)).PosDef)
    (hprecision : ∀ t < T, ∀ i,
      AlgorithmSeparation.separate A b (center k (trajectory A b k ε s t)) = some i →
      A i ≠ 0 → Nonempty (StepPrecision k ε (trajectory A b k ε s t) (fun j => -A i j)))
    (z : Fin n → ℝ) (R r : ℝ) (hR : 0 < R) (hr : 0 < r)
    (hinit : stateEllipsoid k s = EllipsoidGeometry.ellipsoid 0
      (R ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)))
    (hball : EllipsoidGeometry.ellipsoid z (r ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)) ⊆
      realFeasible A b)
    (hboxed : realFeasible A b ⊆ stateEllipsoid k s)
    (hratio : R / r ≤ 2 ^ L) (hcount : 4 * (n + 1) * n * L < T) :
    run A b k ε T s ≠ .exhausted := by
  intro h
  have hretain := exhausted_retains hn A b k ε hε T s hs h hprecision
    _ hball (hball.trans hboxed) T le_rfl
  have hvol := exhausted_volume_step hn A b k ε hε hεmax T s hs h hprecision
  exact EllipsoidIteration.rounded_excludes_inner_ball_dyadic hn
    (fun t => stateEllipsoid k (trajectory A b k ε s t)) T L 0 z R r hR hr
    hinit hvol hratio hcount hretain

/-- With an inner ball and the explicit precision and iteration budgets, the
actual finite program returns a feasible rational centre. -/
theorem run_feasible_of_inner_ball {m n : ℕ} (hn : 2 ≤ n)
    (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) (k : ℕ) (ε : ℚ) (hε : 0 < ε)
    (hεmax : (ε : ℝ) ≤ 1 / (32 * ((n : ℝ) + 1) ^ 2))
    (T L : ℕ) (s : State n) (hs : (castMatrix (shape k s)).PosDef)
    (hprecision : ∀ t < T, ∀ i,
      AlgorithmSeparation.separate A b (center k (trajectory A b k ε s t)) = some i →
      A i ≠ 0 → Nonempty (StepPrecision k ε (trajectory A b k ε s t) (fun j => -A i j)))
    (z : Fin n → ℝ) (R r : ℝ) (hR : 0 < R) (hr : 0 < r)
    (hinit : stateEllipsoid k s = EllipsoidGeometry.ellipsoid 0
      (R ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)))
    (hball : EllipsoidGeometry.ellipsoid z (r ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)) ⊆ realFeasible A b)
    (hboxed : realFeasible A b ⊆ stateEllipsoid k s)
    (hratio : R / r ≤ 2 ^ L) (hcount : 4 * (n + 1) * n * L < T) :
    ∃ result, run A b k ε T s = .feasible result ∧
      AlgorithmSeparation.Feasible A b (center k result) := by
  have hex := not_exhausted_of_inner_ball hn A b k ε hε hεmax T L s hs hprecision
    z R r hR hr hinit hball hboxed hratio hcount
  cases hout : run A b k ε T s with
  | feasible result => exact ⟨result, rfl, run_feasible A b k ε T s result hout⟩
  | zeroRow =>
      have hnempty := run_zeroRow_real A b k ε T s hout
      exfalso
      apply hnempty
      refine ⟨z, hball ?_⟩
      simp [EllipsoidGeometry.ellipsoid]
  | exhausted => exact (hex hout).elim

end MWIS.AlgorithmEllipsoidComplete
end
