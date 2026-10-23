module

public import MWIS.GroupNetwork
public import Mathlib.Analysis.Convex.Birkhoff
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Birkhoff decomposition of bounded directed circulations

A nonnegative circulation with coordinates at most one is represented by a
doubly stochastic routing matrix. Its permutation decomposition gives binary
integral circulations and preserves any coordinates fixed to one.

Prepared 2026-10-23.
-/

@[expose] public section

namespace MWIS.NetworkBirkhoff

open scoped BigOperators

variable {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]

/-- Total outgoing mass at a vertex. -/
def throughput (source : E → V) (x : E → ℝ) (v : V) : ℝ :=
  ∑ e, if source e = v then x e else 0

/-- Proportional routing from an arriving arc to a departing arc. -/
noncomputable def route (source target : E → V) (x : E → ℝ) (i j : E) : ℝ :=
  if target i = source j then x i * x j / throughput source x (source j) else 0

omit [DecidableEq E] in
lemma throughput_nonneg (source : E → V) (x : E → ℝ) (hx : ∀ e, 0 ≤ x e)
    (v : V) : 0 ≤ throughput source x v := by
  apply Finset.sum_nonneg
  intro e _
  split_ifs <;> simp_all

omit [DecidableEq E] in
lemma le_throughput_source (source : E → V) (x : E → ℝ) (hx : ∀ e, 0 ≤ x e)
    (i : E) : x i ≤ throughput source x (source i) := by
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun e => if source e = source i then x e else 0)
    (fun e _ => by split_ifs <;> simp_all) (Finset.mem_univ i)
  simpa [throughput] using h

omit [DecidableEq E] in
lemma le_throughput_target (source target : E → V) (x : E → ℝ)
    (hx : ∀ e, 0 ≤ x e) (hbal : ∀ v, MWIS.GroupNetwork.boundary source target x v = 0)
    (i : E) : x i ≤ throughput source x (target i) := by
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun e => if target e = target i then x e else 0)
    (fun e _ => by split_ifs <;> simp_all) (Finset.mem_univ i)
  have hb := hbal (target i)
  simp only [MWIS.GroupNetwork.boundary, sub_eq_zero] at hb
  simpa only [ite_true, ← hb, throughput] using h

omit [DecidableEq E] in
lemma route_nonneg (source target : E → V) (x : E → ℝ)
    (hx : ∀ e, 0 ≤ x e) (i j : E) : 0 ≤ route source target x i j := by
  unfold route
  split_ifs
  · exact div_nonneg (mul_nonneg (hx i) (hx j)) (throughput_nonneg source x hx _)
  · exact le_rfl

omit [DecidableEq E] in
lemma route_row (source target : E → V) (x : E → ℝ)
    (hx : ∀ e, 0 ≤ x e) (hbal : ∀ v, MWIS.GroupNetwork.boundary source target x v = 0)
    (i : E) : (∑ j, route source target x i j) = x i := by
  have heq (j : E) : route source target x i j =
      (x i / throughput source x (target i)) *
        (if source j = target i then x j else 0) := by
    by_cases h : target i = source j
    · simp only [route, ite_eq_left h, ite_eq_left h.symm]
      rw [h]
      ring
    · simp [route, h, Ne.symm h]
  simp_rw [heq]
  rw [← Finset.mul_sum]
  change x i / throughput source x (target i) * throughput source x (target i) = x i
  by_cases hT : throughput source x (target i) = 0
  · have hi := le_throughput_target source target x hx hbal i
    have hi0 : x i = 0 := by linarith [hx i]
    simp [hT, hi0]
  · exact div_mul_cancel₀ _ hT

omit [DecidableEq E] in
lemma route_column (source target : E → V) (x : E → ℝ)
    (hx : ∀ e, 0 ≤ x e) (hbal : ∀ v, MWIS.GroupNetwork.boundary source target x v = 0)
    (j : E) : (∑ i, route source target x i j) = x j := by
  have heq (i : E) : route source target x i j =
      (x j / throughput source x (source j)) *
        (if target i = source j then x i else 0) := by
    by_cases h : target i = source j
    · simp [route, h]
      ring
    · simp [route, h]
  simp_rw [heq]
  rw [← Finset.mul_sum]
  have hb := hbal (source j)
  simp only [MWIS.GroupNetwork.boundary, sub_eq_zero] at hb
  rw [hb]
  change x j / throughput source x (source j) * throughput source x (source j) = x j
  by_cases hT : throughput source x (source j) = 0
  · have hi := le_throughput_source source x hx j
    have hi0 : x j = 0 := by linarith [hx j]
    simp [hT, hi0]
  · exact div_mul_cancel₀ _ hT

/-- Two copies of every arc separate selection from routing, including loops. -/
noncomputable def routingMatrix (source target : E → V) (x : E → ℝ) :
    Matrix (Bool × E) (Bool × E) ℝ
  | (false, i), (false, j) => if i = j then 1 - x i else 0
  | (false, i), (true, j) => if i = j then x i else 0
  | (true, i), (false, j) => route source target x i j
  | (true, i), (true, j) => if i = j then 1 - x i else 0

/-- A bounded circulation gives an actual doubly stochastic matrix. -/
theorem routingMatrix_doublyStochastic (source target : E → V) (x : E → ℝ)
    (hx : ∀ e, 0 ≤ x e) (hx1 : ∀ e, x e ≤ 1)
    (hbal : ∀ v, MWIS.GroupNetwork.boundary source target x v = 0) :
    routingMatrix source target x ∈ doublyStochastic ℝ (Bool × E) := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨b, i⟩ ⟨d, j⟩
    cases b <;> cases d <;> dsimp [routingMatrix]
    · split_ifs <;> linarith [hx1 i]
    · split_ifs <;> simp_all
    · exact route_nonneg source target x hx i j
    · split_ifs <;> linarith [hx1 i]
  · rintro ⟨b, i⟩
    cases b <;> simp [Fintype.sum_prod_type, routingMatrix,
      route_row source target x hx hbal]
  · rintro ⟨b, i⟩
    cases b <;> simp [Fintype.sum_prod_type, routingMatrix,
      route_column source target x hx hbal]

/-- Reading the arc-selection entry of a routing matrix. -/
def selection (M : Matrix (Bool × E) (Bool × E) ℝ) (i : E) : ℝ :=
  M (false, i) (true, i)

/-- The support of a routing matrix forces selection to be a circulation. -/
theorem selection_balanced (source target : E → V) (x : E → ℝ)
    (M : Matrix (Bool × E) (Bool × E) ℝ)
    (hM : M ∈ doublyStochastic ℝ (Bool × E))
    (hs : ∀ i j, routingMatrix source target x i j = 0 → M i j = 0) :
    ∀ v, MWIS.GroupNetwork.boundary source target (selection M) v = 0 := by
  have hff (i j : E) (hij : i ≠ j) : M (false, i) (false, j) = 0 :=
    hs _ _ (by simp [routingMatrix, hij])
  have hft (i j : E) (hij : i ≠ j) : M (false, i) (true, j) = 0 :=
    hs _ _ (by simp [routingMatrix, hij])
  have htt (i j : E) (hij : i ≠ j) : M (true, i) (true, j) = 0 :=
    hs _ _ (by simp [routingMatrix, hij])
  have htf (i j : E) (hij : target i ≠ source j) : M (true, i) (false, j) = 0 :=
    hs _ _ (by simp [routingMatrix, route, hij])
  have sum_ff_row (i : E) : (∑ j, M (false, i) (false, j)) = M (false, i) (false, i) := by
    apply Finset.sum_eq_single i
    · intro j _ hji; exact hff i j hji.symm
    · simp
  have sum_ft_row (i : E) : (∑ j, M (false, i) (true, j)) = selection M i := by
    apply Finset.sum_eq_single i
    · intro j _ hji; exact hft i j hji.symm
    · simp
  have sum_tt_row (i : E) : (∑ j, M (true, i) (true, j)) = M (true, i) (true, i) := by
    apply Finset.sum_eq_single i
    · intro j _ hji; exact htt i j hji.symm
    · simp
  have sum_ff_col (i : E) : (∑ j, M (false, j) (false, i)) = M (false, i) (false, i) := by
    apply Finset.sum_eq_single i
    · intro j _ hji; exact hff j i hji
    · simp
  have sum_ft_col (i : E) : (∑ j, M (false, j) (true, i)) = selection M i := by
    apply Finset.sum_eq_single i
    · intro j _ hji; exact hft j i hji
    · simp
  have sum_tt_col (i : E) : (∑ j, M (true, j) (true, i)) = M (true, i) (true, i) := by
    apply Finset.sum_eq_single i
    · intro j _ hji; exact htt j i hji
    · simp
  have hrow (i : E) : (∑ j, M (true, i) (false, j)) = selection M i := by
    have hr := sum_row_of_mem_doublyStochastic hM (true, i)
    have hc := sum_col_of_mem_doublyStochastic hM (true, i)
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, sum_tt_row,
      sum_ft_col, sum_tt_col] at hr hc
    linarith
  have hcol (i : E) : (∑ j, M (true, j) (false, i)) = selection M i := by
    have hr := sum_row_of_mem_doublyStochastic hM (false, i)
    have hc := sum_col_of_mem_doublyStochastic hM (false, i)
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, sum_ff_row,
      sum_ft_row, sum_ff_col] at hr hc
    linarith
  intro v
  unfold MWIS.GroupNetwork.boundary
  rw [sub_eq_zero]
  calc
    (∑ i, if target i = v then selection M i else 0) =
        ∑ i, ∑ j, if target i = v then M (true, i) (false, j) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : target i = v <;> simp [h, hrow]
    _ = ∑ i, ∑ j, if source j = v then M (true, i) (false, j) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : target i = source j
      · rw [h]
      · simp [htf i j h]
    _ = ∑ j, if source j = v then selection M j else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : source j = v <;> simp [h, hcol]

/-- Unit coordinates remain unit in any doubly stochastic matrix with the same
allowed support. -/
theorem selection_forced_one (source target : E → V) (x : E → ℝ)
    (M : Matrix (Bool × E) (Bool × E) ℝ)
    (hM : M ∈ doublyStochastic ℝ (Bool × E))
    (hs : ∀ i j, routingMatrix source target x i j = 0 → M i j = 0)
    (e : E) (he : x e = 1) : selection M e = 1 := by
  have hrow := sum_row_of_mem_doublyStochastic hM (false, e)
  have hzero (j : Bool × E) (hj : j ≠ (true, e)) : M (false, e) j = 0 := by
    apply hs
    rcases j with ⟨b, j⟩
    cases b
    · simp [routingMatrix, he]
    · have hej : e ≠ j := fun h => hj (by simp [h])
      simp [routingMatrix, hej]
  rw [Finset.sum_eq_single (true, e) (fun j _ hj => hzero j hj) (by simp)] at hrow
  exact hrow

/-- The binary integer circulation selected by a permutation of arc copies. -/
def integerSelection (σ : Equiv.Perm (Bool × E)) (e : E) : ℤ :=
  if σ (false, e) = (true, e) then 1 else 0

omit [Fintype E] in
lemma integerSelection_binary (σ : Equiv.Perm (Bool × E)) (e : E) :
    integerSelection σ e = 0 ∨ integerSelection σ e = 1 := by
  unfold integerSelection
  split_ifs <;> simp

omit [Fintype E] in
lemma integerSelection_cast (σ : Equiv.Perm (Bool × E)) (e : E) :
    (integerSelection σ e : ℝ) = selection (σ.permMatrix ℝ) e := by
  simp [integerSelection, selection, Equiv.toPEquiv_apply, PEquiv.toMatrix_apply]

/-- A positive-weight term of a nonnegative matrix decomposition respects
all zero entries of the decomposed matrix. -/
lemma positive_weight_support {ι N : Type*} [Fintype ι]
    (w : ι → ℝ) (A : ι → Matrix N N ℝ) (M : Matrix N N ℝ)
    (hw : ∀ i, 0 ≤ w i) (hA : ∀ i u v, 0 ≤ A i u v)
    (heq : ∑ i, w i • A i = M)
    (i : ι) (hi : 0 < w i) (u v : N) (hzero : M u v = 0) : A i u v = 0 := by
  classical
  have hsum : (∑ j, w j * A j u v) = 0 := by
    have h := congrArg (fun P : Matrix N N ℝ => P u v) heq
    simpa [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, hzero] using h
  have hle := Finset.single_le_sum (s := Finset.univ) (f := fun j => w j * A j u v)
    (fun j _ => mul_nonneg (hw j) (hA j u v)) (Finset.mem_univ i)
  rw [hsum] at hle
  have hprod : w i * A i u v = 0 := le_antisymm hle (mul_nonneg (hw i) (hA i u v))
  exact (mul_eq_zero.mp hprod).resolve_left (ne_of_gt hi)

/-- Every bounded real circulation is a convex combination of binary integer
circulations; coordinates fixed to one remain one in every constituent. -/
theorem bounded_circulation_mem_convexHull (source target : E → V) (x : E → ℝ)
    (hx : ∀ e, 0 ≤ x e) (hx1 : ∀ e, x e ≤ 1)
    (hbal : ∀ v, MWIS.GroupNetwork.boundary source target x v = 0) :
    x ∈ convexHull ℝ ((fun y : E → ℤ => fun e => (y e : ℝ)) ''
      {y | (∀ e, y e = 0 ∨ y e = 1) ∧
        (∀ v, MWIS.GroupNetwork.boundary source target y v = 0) ∧
        (∀ e, x e = 1 → y e = 1)}) := by
  classical
  obtain ⟨w, hw, hw1, heq⟩ := exists_eq_sum_perm_of_mem_doublyStochastic
    (routingMatrix_doublyStochastic source target x hx hx1 hbal)
  have hsupport (σ : Equiv.Perm (Bool × E)) (hσ : 0 < w σ) :
      ∀ i j, routingMatrix source target x i j = 0 → σ.permMatrix ℝ i j = 0 := by
    intro i j hij
    exact positive_weight_support w (fun τ => τ.permMatrix ℝ)
      (routingMatrix source target x) hw
      (fun τ _ _ => nonneg_of_mem_doublyStochastic (permMatrix_mem_doublyStochastic (σ := τ)))
      heq σ hσ i j hij
  have hgood (σ : Equiv.Perm (Bool × E)) (hσ : 0 < w σ) :
      (∀ e, integerSelection σ e = 0 ∨ integerSelection σ e = 1) ∧
      (∀ v, MWIS.GroupNetwork.boundary source target (integerSelection σ) v = 0) ∧
      (∀ e, x e = 1 → integerSelection σ e = 1) := by
    refine ⟨integerSelection_binary σ, ?_, ?_⟩
    · intro v
      have h := selection_balanced source target x (σ.permMatrix ℝ)
        permMatrix_mem_doublyStochastic (hsupport σ hσ) v
      simp only [MWIS.GroupNetwork.boundary, ← integerSelection_cast] at h ⊢
      exact_mod_cast h
    · intro e he
      have h := selection_forced_one source target x (σ.permMatrix ℝ)
        permMatrix_mem_doublyStochastic (hsupport σ hσ) e he
      rw [← integerSelection_cast] at h
      exact_mod_cast h
  have hex : ∃ σ, 0 < w σ := by
    by_contra! h
    have hz : ∀ σ, w σ = 0 := fun σ => le_antisymm (h σ) (hw σ)
    simp [hz] at hw1
  obtain ⟨σ₀, hσ₀⟩ := hex
  let y (σ : Equiv.Perm (Bool × E)) : E → ℤ :=
    if 0 < w σ then integerSelection σ else integerSelection σ₀
  have hy (σ : Equiv.Perm (Bool × E)) :
      (∀ e, y σ e = 0 ∨ y σ e = 1) ∧
      (∀ v, MWIS.GroupNetwork.boundary source target (y σ) v = 0) ∧
      (∀ e, x e = 1 → y σ e = 1) := by
    dsimp only [y]
    split_ifs with h
    · exact hgood σ h
    · exact hgood σ₀ hσ₀
  apply mem_convexHull_of_exists_fintype w (fun σ e => (y σ e : ℝ)) hw hw1
  · intro σ
    exact ⟨y σ, hy σ, rfl⟩
  · funext e
    have h := congrArg (fun M : Matrix (Bool × E) (Bool × E) ℝ => M (false, e) (true, e)) heq
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, routingMatrix, ite_true] at h
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [← h]
    apply Finset.sum_congr rfl
    intro σ _
    by_cases hσ : 0 < w σ
    · simp [y, hσ, integerSelection_cast, selection]
    · have hw0 : w σ = 0 := le_antisymm (le_of_not_gt hσ) (hw σ)
      simp [hw0]

end MWIS.NetworkBirkhoff

end
