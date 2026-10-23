module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Basic
public import Mathlib.Tactic

/-!
# Unit-triangular integer systems

A pivot is a coordinate together with integer coefficients expressing it in terms of other
coordinates. A pivot list is triangular over a free set `X` when every pivot coordinate is
new and its coefficients involve only free coordinates and later pivots. The solutions of a
triangular system that vanish off `X` and the pivots are then parametrized exactly by their
values on `X`: restriction to `X` is a bijection, and `extend` is its explicit inverse.
-/

@[expose] public section

namespace MWIS.TreeCotree

variable {m : ℕ}

/-- A pivot coordinate and the coefficients of the equation that determines it. -/
abbrev Pivot (m : ℕ) := Fin m × (Fin m → ℤ)

/-- The set of pivot coordinates of a pivot list. -/
def pivots : List (Pivot m) → Finset (Fin m)
  | [] => ∅
  | p :: ps => insert p.1 (pivots ps)

@[simp] theorem pivots_nil : pivots ([] : List (Pivot m)) = ∅ := rfl

@[simp] theorem pivots_cons (p : Pivot m) (ps : List (Pivot m)) :
    pivots (p :: ps) = insert p.1 (pivots ps) := rfl

theorem pivots_append (ps qs : List (Pivot m)) : pivots (ps ++ qs) = pivots ps ∪ pivots qs := by
  induction ps with
  | nil => simp
  | cons p ps ih => simp [ih, Finset.insert_union]

theorem mem_pivots {ps : List (Pivot m)} {p : Pivot m} (hp : p ∈ ps) : p.1 ∈ pivots ps := by
  induction ps with
  | nil => simp at hp
  | cons q ps ih =>
    rcases List.mem_cons.mp hp with rfl | h
    · simp
    · simp [ih h]

/-- Triangularity of a pivot list over the free set `X`. -/
def Triangular (X : Finset (Fin m)) : List (Pivot m) → Prop
  | [] => True
  | p :: ps => p.1 ∉ X ∪ pivots ps ∧ (∀ e, p.2 e ≠ 0 → e ∈ X ∪ pivots ps) ∧ Triangular X ps

/-- All pivot equations hold. -/
def Holds (ps : List (Pivot m)) (u : Fin m → ℤ) : Prop :=
  ∀ p ∈ ps, u p.1 = ∑ e, p.2 e * u e

theorem holds_nil (u : Fin m → ℤ) : Holds [] u := by simp [Holds]

theorem holds_cons {p : Pivot m} {ps : List (Pivot m)} {u : Fin m → ℤ} :
    Holds (p :: ps) u ↔ u p.1 = ∑ e, p.2 e * u e ∧ Holds ps u := by
  simp [Holds]

theorem holds_append {ps qs : List (Pivot m)} {u : Fin m → ℤ} :
    Holds (ps ++ qs) u ↔ Holds ps u ∧ Holds qs u := by
  simp only [Holds, List.mem_append]
  constructor
  · intro h; exact ⟨fun p hp => h p (Or.inl hp), fun p hp => h p (Or.inr hp)⟩
  · rintro ⟨h1, h2⟩ p (hp | hp)
    exacts [h1 p hp, h2 p hp]

theorem holds_sub {ps : List (Pivot m)} {u v : Fin m → ℤ} (hu : Holds ps u) (hv : Holds ps v) :
    Holds ps (u - v) := by
  intro p hp
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, hu p hp, hv p hp]

theorem holds_smul {ps : List (Pivot m)} {u : Fin m → ℤ} (a : ℤ) (hu : Holds ps u) :
    Holds ps (a • u) := by
  intro p hp
  simp only [Pi.smul_apply, smul_eq_mul, hu p hp, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro e _; ring

/-- In a triangular list every equation involves only free coordinates and pivots. -/
theorem triangular_support {X : Finset (Fin m)} {ps : List (Pivot m)} (h : Triangular X ps) :
    ∀ p ∈ ps, ∀ e, p.2 e ≠ 0 → e ∈ X ∪ pivots ps := by
  induction ps with
  | nil => simp
  | cons q ps ih =>
    intro p hp e he
    obtain ⟨_, hq, hrest⟩ := h
    rcases List.mem_cons.mp hp with rfl | hp
    · have := hq e he
      simp only [Finset.mem_union, pivots_cons, Finset.mem_insert] at this ⊢
      tauto
    · have := ih hrest p hp e he
      simp only [Finset.mem_union, pivots_cons, Finset.mem_insert] at this ⊢
      tauto

/-- Pivot coordinates of a triangular list are not free. -/
theorem triangular_disjoint {X : Finset (Fin m)} {ps : List (Pivot m)} (h : Triangular X ps) :
    ∀ e ∈ pivots ps, e ∉ X := by
  induction ps with
  | nil => simp
  | cons q ps ih =>
    intro e he
    obtain ⟨hq, _, hrest⟩ := h
    rcases Finset.mem_insert.mp he with rfl | he
    · intro hx; exact hq (Finset.mem_union_left _ hx)
    · exact ih hrest e he

/-- Appending one pivot at the end. -/
theorem triangular_append_single {X : Finset (Fin m)} {ps : List (Pivot m)} {c : Fin m}
    {g : Fin m → ℤ} (hps : Triangular (insert c X) ps) (hc : c ∉ X)
    (hg : ∀ e, g e ≠ 0 → e ∈ X) : Triangular X (ps ++ [(c, g)]) := by
  induction ps with
  | nil =>
    refine ⟨?_, ?_, trivial⟩
    · simpa using hc
    · intro e he; simpa using hg e he
  | cons p ps ih =>
    obtain ⟨hp, hsupp, hrest⟩ := hps
    refine ⟨?_, ?_, ih hrest⟩
    · change p.1 ∉ X ∪ pivots (ps ++ [(c, g)])
      rw [pivots_append]
      simp only [Finset.mem_union, Finset.mem_insert, pivots_cons, pivots_nil,
        Finset.notMem_empty, or_false] at hp ⊢
      tauto
    · intro e he
      have := hsupp e he
      change e ∈ X ∪ pivots (ps ++ [(c, g)])
      rw [pivots_append]
      simp only [Finset.mem_union, Finset.mem_insert, pivots_cons, pivots_nil,
        Finset.notMem_empty, or_false] at this ⊢
      tauto

/-- Solve the pivot equations from the last pivot to the first. -/
def extend (ps : List (Pivot m)) (z : Fin m → ℤ) : Fin m → ℤ :=
  ps.foldr (fun p u => Function.update u p.1 (∑ e, p.2 e * u e)) z

@[simp] theorem extend_nil (z : Fin m → ℤ) : extend [] z = z := rfl

theorem extend_cons (p : Pivot m) (ps : List (Pivot m)) (z : Fin m → ℤ) :
    extend (p :: ps) z =
      Function.update (extend ps z) p.1 (∑ e, p.2 e * extend ps z e) := rfl

theorem extend_of_not_mem (ps : List (Pivot m)) (z : Fin m → ℤ) {e : Fin m}
    (he : e ∉ pivots ps) : extend ps z e = z e := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rw [extend_cons]
    simp only [pivots_cons, Finset.mem_insert, not_or] at he
    rw [Function.update_of_ne he.1]
    exact ih he.2

/-- Coefficients of a pivot vanish at a coordinate outside free set and later pivots. -/
theorem coeff_zero {g : Fin m → ℤ} {S : Finset (Fin m)}
    (hg : ∀ e, g e ≠ 0 → e ∈ S) {c : Fin m} (hc : c ∉ S) : g c = 0 := by
  by_contra h; exact hc (hg c h)

/-- Updating a coordinate that no equation mentions preserves all equations. -/
theorem holds_update {X : Finset (Fin m)} {ps : List (Pivot m)} (h : Triangular X ps)
    {u : Fin m → ℤ} (hu : Holds ps u) {c : Fin m} (hc : c ∉ X ∪ pivots ps) (v : ℤ) :
    Holds ps (Function.update u c v) := by
  intro p hp
  have hp1 : p.1 ≠ c := by
    intro he; apply hc; rw [← he]; exact Finset.mem_union_right _ (mem_pivots hp)
  rw [Function.update_of_ne hp1, hu p hp]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hec : e = c
  · subst hec
    rw [coeff_zero (triangular_support h p hp) hc]
    simp
  · rw [Function.update_of_ne hec]

/-- The extension satisfies every pivot equation. -/
theorem extend_holds {X : Finset (Fin m)} {ps : List (Pivot m)} (h : Triangular X ps)
    (z : Fin m → ℤ) : Holds ps (extend ps z) := by
  induction ps with
  | nil => exact holds_nil _
  | cons p ps ih =>
    obtain ⟨hp, hsupp, hrest⟩ := h
    rw [holds_cons, extend_cons]
    refine ⟨?_, holds_update hrest (ih hrest) hp _⟩
    rw [Function.update_self]
    apply Finset.sum_congr rfl
    intro e _
    by_cases hec : e = p.1
    · subst hec
      rw [coeff_zero hsupp hp]
      simp
    · rw [Function.update_of_ne hec]

/-- Two solutions that agree off the pivot coordinates agree everywhere. -/
theorem holds_unique {X : Finset (Fin m)} {ps : List (Pivot m)} (h : Triangular X ps)
    {u v : Fin m → ℤ} (hu : Holds ps u) (hv : Holds ps v)
    (hagree : ∀ e ∉ pivots ps, u e = v e) : u = v := by
  induction ps generalizing u v with
  | nil => funext e; exact hagree e (by simp)
  | cons p ps ih =>
    obtain ⟨hp, hsupp, hrest⟩ := h
    rw [holds_cons] at hu hv
    let u' := Function.update u p.1 (v p.1)
    have hu' : Holds ps u' := holds_update hrest hu.2 hp _
    have heq : u' = v := by
      apply ih hrest hu' hv.2
      intro e he
      by_cases hep : e = p.1
      · subst hep; simp [u']
      · simp only [u', Function.update_of_ne hep]
        apply hagree e
        simp [hep, he]
    have hoff : ∀ e, e ≠ p.1 → u e = v e := by
      intro e he
      have := congrFun heq e
      simpa [u', Function.update_of_ne he] using this
    funext e
    by_cases hep : e = p.1
    · subst hep
      rw [hu.1, hv.1]
      apply Finset.sum_congr rfl
      intro d _
      by_cases hd : d = p.1
      · subst hd; rw [coeff_zero hsupp hp]; simp
      · rw [hoff d hd]
    · exact hoff e hep

/-- Keep the coordinates in `X` and set all others to zero. -/
def restrictZero (X : Finset (Fin m)) (z : Fin m → ℤ) : Fin m → ℤ :=
  fun e => if e ∈ X then z e else 0

/-- The extension of free values has those free values, satisfies the equations and
vanishes off the free and pivot coordinates. -/
theorem extend_spec {X : Finset (Fin m)} {ps : List (Pivot m)} (h : Triangular X ps)
    (z : Fin m → ℤ) :
    Holds ps (extend ps (restrictZero X z)) ∧
      (∀ e ∈ X, extend ps (restrictZero X z) e = z e) ∧
      (∀ e ∉ X ∪ pivots ps, extend ps (restrictZero X z) e = 0) := by
  refine ⟨extend_holds h _, ?_, ?_⟩
  · intro e he
    rw [extend_of_not_mem _ _ (fun hp => triangular_disjoint h e hp he)]
    simp [restrictZero, he]
  · intro e he
    simp only [Finset.mem_union, not_or] at he
    rw [extend_of_not_mem _ _ he.2]
    simp [restrictZero, he.1]

/-- Every solution vanishing off the free and pivot coordinates is the extension of its
free values. -/
theorem eq_extend {X : Finset (Fin m)} {ps : List (Pivot m)} (h : Triangular X ps)
    {u : Fin m → ℤ} (hu : Holds ps u) (hzero : ∀ e ∉ X ∪ pivots ps, u e = 0) :
    u = extend ps (restrictZero X u) := by
  obtain ⟨hx, hfree, hz⟩ := extend_spec h u
  apply holds_unique h hu hx
  intro e he
  by_cases heX : e ∈ X
  · rw [hfree e heX]
  · have hn : e ∉ X ∪ pivots ps := by simp [heX, he]
    rw [hzero e hn, hz e hn]

/-- A solution vanishing off the free and pivot coordinates and on all free coordinates
vanishes everywhere. -/
theorem eq_zero_of_free {X : Finset (Fin m)} {ps : List (Pivot m)} (h : Triangular X ps)
    {u : Fin m → ℤ} (hu : Holds ps u) (hzero : ∀ e ∉ X ∪ pivots ps, u e = 0)
    (hfree : ∀ e ∈ X, u e = 0) : u = 0 := by
  have h0 : Holds ps (0 : Fin m → ℤ) := by intro p _; simp
  apply holds_unique h hu h0
  intro e he
  by_cases heX : e ∈ X
  · simpa using hfree e heX
  · simpa using hzero e (by simp [heX, he])

end MWIS.TreeCotree

end
