module

public import MWIS.TreeCotreeTriangular
public import MWIS.Walks

/-!
# Unit-pivot elimination of signed face equations

The integer kernel of a matrix whose columns have absolute entry sum at most two is
computed by elimination with unit pivots only. When no remaining row has a unit entry,
every entry is `0` or `±2`, so a nonzero row is halved and then has a unit entry. Every
step removes one row, the column bound is preserved, and each step replaces the current
equations by an equivalent pivot equation plus the reduced system. After as many steps as
there are rows, the original equations are equivalent to a unit-triangular pivot system.
Signed face columns (`Walks.Column`) satisfy the column bound.
-/

@[expose] public section

namespace MWIS.TreeCotree

variable {f m : ℕ}

/-- The state of the elimination: remaining rows, active columns, the current matrix and
the pivots found so far, in elimination order. -/
structure ElimState (f m : ℕ) where
  rows : Finset (Fin f)
  act : Finset (Fin m)
  M : Fin f → Fin m → ℤ
  piv : List (Pivot m)

namespace ElimState

/-- The value of row `r` on `u`. -/
def rowSum (S : ElimState f m) (r : Fin f) (u : Fin m → ℤ) : ℤ := ∑ e, S.M r e * u e

/-- All remaining equations hold. -/
def Sys (S : ElimState f m) (u : Fin m → ℤ) : Prop := ∀ r ∈ S.rows, S.rowSum r u = 0

/-- The first active unit entry of row `r`. -/
def unitIn (S : ElimState f m) (r : Fin f) : Option (Fin m) :=
  (List.finRange m).find? fun c => decide (c ∈ S.act ∧ (S.M r c = 1 ∨ S.M r c = -1))

/-- The first remaining row with an active unit entry, and that entry. -/
def unitAt (S : ElimState f m) : Option (Fin f × Fin m) :=
  (List.finRange f).findSome? fun r => if r ∈ S.rows then (S.unitIn r).map (r, ·) else none

/-- The first remaining row with a nonzero active entry. -/
def nonzeroRow (S : ElimState f m) : Option (Fin f) :=
  (List.finRange f).find? fun r => decide (r ∈ S.rows ∧ ∃ c ∈ S.act, S.M r c ≠ 0)

/-- Coefficients expressing the pivot coordinate `c` through row `r`. -/
def pivotCoeff (S : ElimState f m) (r : Fin f) (c : Fin m) : Fin m → ℤ :=
  fun e => if e = c then 0 else -(S.M r c * S.M r e)

/-- Eliminate column `c` using the unit entry in row `r`. -/
def pivotAt (S : ElimState f m) (r : Fin f) (c : Fin m) : ElimState f m where
  rows := S.rows.erase r
  act := S.act.erase c
  M := fun r' e => S.M r' e - S.M r' c * S.M r c * S.M r e
  piv := S.piv ++ [(c, S.pivotCoeff r c)]

/-- Halve row `r`. -/
def halve (S : ElimState f m) (r : Fin f) : ElimState f m :=
  { S with M := fun r' e => if r' = r then S.M r e / 2 else S.M r' e }

/-- One elimination step. -/
def step (S : ElimState f m) : ElimState f m :=
  match S.unitAt with
  | some (r, c) => S.pivotAt r c
  | none =>
    match S.nonzeroRow with
    | some r =>
      match (S.halve r).unitIn r with
      | some c => (S.halve r).pivotAt r c
      | none => S.halve r
    | none => S

/-- As many steps as there are possible rows. -/
def run (S : ElimState f m) : ElimState f m := step^[f] S

/-- All remaining rows vanish. -/
def AllZero (S : ElimState f m) : Prop := ∀ r ∈ S.rows, ∀ e, S.M r e = 0

/-- The invariant of the elimination started at `S₀`. -/
structure Inv (S₀ S : ElimState f m) : Prop where
  zero_off : ∀ r ∈ S.rows, ∀ e ∉ S.act, S.M r e = 0
  l1 : ∀ e, ∑ r ∈ S.rows, |S.M r e| ≤ 2
  equiv : ∀ u : Fin m → ℤ, (∀ e ∉ S₀.act, u e = 0) → (S₀.Sys u ↔ Holds S.piv u ∧ S.Sys u)
  tri : Triangular S.act S.piv
  part : ∀ e, e ∈ S₀.act ↔ e ∈ S.act ∪ pivots S.piv

/-! ## Search lemmas -/

theorem unitIn_some {S : ElimState f m} {r : Fin f} {c : Fin m} (h : S.unitIn r = some c) :
    c ∈ S.act ∧ (S.M r c = 1 ∨ S.M r c = -1) := by
  have := List.find?_some h
  simpa using this

theorem unitIn_none {S : ElimState f m} {r : Fin f} (h : S.unitIn r = none) :
    ∀ c ∈ S.act, ¬ (S.M r c = 1 ∨ S.M r c = -1) := by
  intro c hc
  have := List.find?_eq_none.mp h c (List.mem_finRange c)
  simp only [decide_eq_true_eq, not_and] at this
  exact this hc

theorem unitAt_some {S : ElimState f m} {r : Fin f} {c : Fin m}
    (h : S.unitAt = some (r, c)) : r ∈ S.rows ∧ S.unitIn r = some c := by
  obtain ⟨r', _, hr'⟩ := List.exists_of_findSome?_eq_some h
  by_cases hm : r' ∈ S.rows
  · rw [if_pos hm] at hr'
    cases hu : S.unitIn r' with
    | none => rw [hu] at hr'; simp at hr'
    | some c' =>
      rw [hu] at hr'
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hr'
      obtain ⟨rfl, rfl⟩ := hr'
      exact ⟨hm, hu⟩
  · rw [if_neg hm] at hr'; simp at hr'

theorem unitAt_none {S : ElimState f m} (h : S.unitAt = none) :
    ∀ r ∈ S.rows, S.unitIn r = none := by
  intro r hr
  have := List.findSome?_eq_none_iff.mp h r (List.mem_finRange r)
  rw [if_pos hr] at this
  simpa using this

theorem nonzeroRow_some {S : ElimState f m} {r : Fin f} (h : S.nonzeroRow = some r) :
    r ∈ S.rows ∧ ∃ c ∈ S.act, S.M r c ≠ 0 := by
  have := List.find?_some h
  simpa using this

theorem nonzeroRow_none {S : ElimState f m} (h : S.nonzeroRow = none) :
    ∀ r ∈ S.rows, ∀ c ∈ S.act, S.M r c = 0 := by
  intro r hr c hc
  have := List.find?_eq_none.mp h r (List.mem_finRange r)
  simp only [decide_eq_true_eq, not_and, not_exists, not_not] at this
  exact this hr c hc

/-! ## The pivot step -/

theorem unit_sq {s : ℤ} (hs : s = 1 ∨ s = -1) : s * s = 1 := by
  rcases hs with rfl | rfl <;> norm_num

theorem unit_abs {s : ℤ} (hs : s = 1 ∨ s = -1) : |s| = 1 := by
  rcases hs with rfl | rfl <;> norm_num

theorem pivotCoeff_sum (S : ElimState f m) (r : Fin f) (c : Fin m)
    (hs : S.M r c = 1 ∨ S.M r c = -1) (u : Fin m → ℤ) :
    ∑ e, S.pivotCoeff r c e * u e = -(S.M r c * S.rowSum r u) + u c := by
  have hpt : ∀ e, S.pivotCoeff r c e * u e =
      -(S.M r c * (S.M r e * u e)) + (if e = c then S.M r c * S.M r e * u e else 0) := by
    intro e
    unfold pivotCoeff
    split_ifs with he
    · subst he; ring
    · ring
  rw [Finset.sum_congr rfl (fun e _ => hpt e), Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true, rowSum, Finset.mul_sum, Finset.sum_neg_distrib]
  rw [unit_sq hs, one_mul]

theorem pivotAt_rowSum (S : ElimState f m) (r : Fin f) (c : Fin m) (r' : Fin f)
    (u : Fin m → ℤ) :
    (S.pivotAt r c).rowSum r' u = S.rowSum r' u - S.M r' c * S.M r c * S.rowSum r u := by
  simp only [rowSum, pivotAt, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem pivotAt_inv {S₀ S : ElimState f m} (h : Inv S₀ S) {r : Fin f} {c : Fin m}
    (hr : r ∈ S.rows) (hc : c ∈ S.act) (hs : S.M r c = 1 ∨ S.M r c = -1) :
    Inv S₀ (S.pivotAt r c) := by
  have hss := unit_sq hs
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r' hr' e he
    simp only [pivotAt, Finset.mem_erase] at hr' he ⊢
    by_cases hec : e = c
    · subst hec
      calc S.M r' e - S.M r' e * S.M r e * S.M r e
          = S.M r' e * (1 - S.M r e * S.M r e) := by ring
        _ = 0 := by rw [hss]; ring
    · have he' : e ∉ S.act := fun h' => he ⟨hec, h'⟩
      rw [h.zero_off r' hr'.2 e he', h.zero_off r hr e he']
      ring
  · intro e
    simp only [pivotAt]
    have hc1 := h.l1 c
    rw [← Finset.add_sum_erase _ _ hr, unit_abs hs] at hc1
    have he1 := h.l1 e
    rw [← Finset.add_sum_erase _ _ hr] at he1
    have hstep : ∀ r' ∈ S.rows.erase r,
        |S.M r' e - S.M r' c * S.M r c * S.M r e| ≤ |S.M r' e| + |S.M r e| * |S.M r' c| := by
      intro r' _
      calc |S.M r' e - S.M r' c * S.M r c * S.M r e|
          ≤ |S.M r' e| + |S.M r' c * S.M r c * S.M r e| := abs_sub _ _
        _ = |S.M r' e| + |S.M r e| * |S.M r' c| := by
          rw [abs_mul, abs_mul, unit_abs hs]; ring
    calc ∑ r' ∈ S.rows.erase r, |S.M r' e - S.M r' c * S.M r c * S.M r e|
        ≤ ∑ r' ∈ S.rows.erase r, (|S.M r' e| + |S.M r e| * |S.M r' c|) :=
          Finset.sum_le_sum hstep
      _ = ∑ r' ∈ S.rows.erase r, |S.M r' e| + |S.M r e| * ∑ r' ∈ S.rows.erase r, |S.M r' c| := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ ∑ r' ∈ S.rows.erase r, |S.M r' e| + |S.M r e| * 1 := by
          gcongr
          linarith
      _ ≤ 2 := by linarith
  · intro u hu
    rw [h.equiv u hu, show (S.pivotAt r c).piv = S.piv ++ [(c, S.pivotCoeff r c)] from rfl,
      holds_append, holds_cons]
    simp only [holds_nil, and_true]
    have hsum := pivotCoeff_sum S r c hs u
    constructor
    · rintro ⟨hp, hsys⟩
      have hL : S.rowSum r u = 0 := hsys r hr
      refine ⟨⟨hp, ?_⟩, ?_⟩
      · rw [hsum, hL]; ring
      · intro r' hr'
        rw [pivotAt_rowSum, hsys r' (Finset.mem_of_mem_erase hr'), hL]
        ring
    · rintro ⟨⟨hp, hpe⟩, hsys⟩
      have hL : S.rowSum r u = 0 := by
        rw [hsum] at hpe
        have h1 : S.M r c * S.rowSum r u = 0 := by linarith
        rcases hs with hs | hs <;> rw [hs] at h1 <;> linarith
      refine ⟨hp, ?_⟩
      intro r' hr'
      by_cases hrr : r' = r
      · subst hrr; exact hL
      · have := hsys r' (show r' ∈ S.rows.erase r from Finset.mem_erase.mpr ⟨hrr, hr'⟩)
        rw [pivotAt_rowSum, hL] at this
        linarith
  · simp only [pivotAt]
    apply triangular_append_single
    · rw [Finset.insert_erase hc]; exact h.tri
    · simp
    · intro e he
      unfold pivotCoeff at he
      split_ifs at he with hec
      · exact absurd rfl he
      · refine Finset.mem_erase.mpr ⟨hec, ?_⟩
        by_contra hn
        apply he
        rw [h.zero_off r hr e hn]; ring
  · intro e
    rw [h.part e]
    simp only [pivotAt, pivots_append, pivots_cons, pivots_nil, Finset.mem_union,
      Finset.mem_erase, Finset.mem_insert, Finset.notMem_empty, or_false]
    constructor
    · rintro (he | he)
      · by_cases hec : e = c
        · exact Or.inr (Or.inr hec)
        · exact Or.inl ⟨hec, he⟩
      · exact Or.inr (Or.inl he)
    · rintro (⟨_, he⟩ | he | he)
      · exact Or.inl he
      · exact Or.inr he
      · subst he; exact Or.inl hc

/-! ## The halving step -/

theorem halve_inv {S₀ S : ElimState f m} (h : Inv S₀ S) {r : Fin f} (hr : r ∈ S.rows)
    (heven : ∀ e, Even (S.M r e)) : Inv S₀ (S.halve r) := by
  have hhalf : ∀ e, S.M r e = 2 * (S.M r e / 2) := by
    intro e
    obtain ⟨k, hk⟩ := heven e
    rw [hk]; omega
  refine ⟨?_, ?_, ?_, h.tri, h.part⟩
  · intro r' hr' e he
    simp only [halve] at hr' he ⊢
    split_ifs with hrr
    · subst hrr; rw [h.zero_off r' hr' e he]; rfl
    · exact h.zero_off r' hr' e he
  · intro e
    refine le_trans (Finset.sum_le_sum fun r' _ => ?_) (h.l1 e)
    simp only [halve]
    split_ifs with hrr
    · subst hrr
      conv_rhs => rw [hhalf e]
      rw [abs_mul]
      have : (0 : ℤ) ≤ |S.M r' e / 2| := abs_nonneg _
      norm_num
      linarith
    · exact le_rfl
  · intro u hu
    rw [h.equiv u hu]
    apply and_congr Iff.rfl
    simp only [Sys, halve]
    apply forall₂_congr
    intro r' _
    by_cases hrr : r' = r
    · subst hrr
      have hsum : S.rowSum r' u = 2 * (S.halve r').rowSum r' u := by
        simp only [rowSum, halve, if_true, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e _
        nth_rewrite 1 [hhalf e]; ring
      change S.rowSum r' u = 0 ↔ (S.halve r').rowSum r' u = 0
      rw [hsum]; omega
    · change S.rowSum r' u = 0 ↔ (S.halve r).rowSum r' u = 0
      simp only [rowSum, halve, if_neg hrr]

/-! ## Progress -/

theorem entry_abs_le {S₀ S : ElimState f m} (h : Inv S₀ S) {r : Fin f} (hr : r ∈ S.rows)
    (e : Fin m) : |S.M r e| ≤ 2 :=
  le_trans (Finset.single_le_sum (f := fun r' => |S.M r' e|) (fun _ _ => abs_nonneg _) hr)
    (h.l1 e)

theorem step_of_allZero {S : ElimState f m} (h : S.AllZero) : S.step = S := by
  have hu : S.unitAt = none := by
    apply List.findSome?_eq_none_iff.mpr
    intro r _
    split_ifs with hr
    · cases hc : S.unitIn r with
      | none => rfl
      | some c =>
        have := (unitIn_some hc).2
        rw [h r hr c] at this
        norm_num at this
    · rfl
  have hn : S.nonzeroRow = none := by
    apply List.find?_eq_none.mpr
    intro r _
    simp only [decide_eq_true_eq, not_and, not_exists, not_not]
    intro hr c _
    exact h r hr c
  unfold step
  rw [hu, hn]

theorem step_eq_pivot {S : ElimState f m} {r : Fin f} {c : Fin m}
    (hu : S.unitAt = some (r, c)) : S.step = S.pivotAt r c := by
  simp only [step, hu]

theorem step_eq_halve_pivot {S : ElimState f m} {r : Fin f} {c : Fin m}
    (hu : S.unitAt = none) (hn : S.nonzeroRow = some r) (hc : (S.halve r).unitIn r = some c) :
    S.step = (S.halve r).pivotAt r c := by
  simp only [step, hu, hn, hc]

theorem step_eq_self {S : ElimState f m} (hu : S.unitAt = none) (hn : S.nonzeroRow = none) :
    S.step = S := by
  simp only [step, hu, hn]

theorem step_progress {S₀ S : ElimState f m} (h : Inv S₀ S) :
    Inv S₀ S.step ∧ (S.step.rows.card < S.rows.card ∨ S.AllZero) := by
  cases hu : S.unitAt with
  | some p =>
    obtain ⟨r, c⟩ := p
    obtain ⟨hr, hc⟩ := unitAt_some hu
    obtain ⟨hca, hs⟩ := unitIn_some hc
    rw [step_eq_pivot hu]
    refine ⟨pivotAt_inv h hr hca hs, Or.inl ?_⟩
    exact Finset.card_erase_lt_of_mem hr
  | none =>
    have hnu := unitAt_none hu
    cases hn : S.nonzeroRow with
    | none =>
      rw [step_eq_self hu hn]
      refine ⟨h, Or.inr ?_⟩
      intro r hr e
      by_cases he : e ∈ S.act
      · exact nonzeroRow_none hn r hr e he
      · exact h.zero_off r hr e he
    | some r =>
      obtain ⟨hr, c, hc, hne⟩ := nonzeroRow_some hn
      have hnoUnit : ∀ e ∈ S.act, ¬ (S.M r e = 1 ∨ S.M r e = -1) := unitIn_none (hnu r hr)
      have heven : ∀ e, Even (S.M r e) := by
        intro e
        by_cases he : e ∈ S.act
        · have hb := entry_abs_le h hr e
          have hnu' := hnoUnit e he
          rw [abs_le] at hb
          have : S.M r e = -2 ∨ S.M r e = 0 ∨ S.M r e = 2 := by omega
          rcases this with h' | h' | h' <;> rw [h'] <;> decide
        · rw [h.zero_off r hr e he]; decide
      have hh := halve_inv h hr heven
      have hunit : (S.halve r).M r c = 1 ∨ (S.halve r).M r c = -1 := by
        have hb := entry_abs_le h hr c
        have hnu' := hnoUnit c hc
        rw [abs_le] at hb
        have : S.M r c = -2 ∨ S.M r c = 2 := by omega
        simp only [halve, if_true]
        rcases this with h' | h' <;> rw [h'] <;> norm_num
      cases hc' : (S.halve r).unitIn r with
      | none =>
        exact absurd hunit (unitIn_none hc' c hc)
      | some c' =>
        obtain ⟨hca', hs'⟩ := unitIn_some hc'
        rw [step_eq_halve_pivot hu hn hc']
        refine ⟨pivotAt_inv hh hr hca' hs', Or.inl ?_⟩
        exact Finset.card_erase_lt_of_mem hr

theorem iterate_progress {S₀ S : ElimState f m} (h : Inv S₀ S) (k : ℕ) :
    Inv S₀ (step^[k] S) ∧
      ((step^[k] S).rows.card + k ≤ S.rows.card ∨ (step^[k] S).AllZero) := by
  induction k with
  | zero => exact ⟨h, Or.inl (by simp)⟩
  | succ k ih =>
    obtain ⟨hinv, hprog⟩ := ih
    rw [Function.iterate_succ_apply']
    by_cases hz : (step^[k] S).AllZero
    · rw [step_of_allZero hz]; exact ⟨hinv, Or.inr hz⟩
    · obtain ⟨hinv', hp⟩ := step_progress hinv
      refine ⟨hinv', ?_⟩
      rcases hp with hp | hp
      · rcases hprog with hprog | hprog
        · left; omega
        · exact absurd hprog hz
      · exact absurd hp hz

/-- After `f` steps all remaining rows vanish. -/
theorem run_spec {S₀ : ElimState f m} (h : Inv S₀ S₀) :
    Inv S₀ S₀.run ∧ S₀.run.AllZero := by
  obtain ⟨hinv, hprog⟩ := iterate_progress h f
  refine ⟨hinv, ?_⟩
  rcases hprog with hprog | hprog
  · have hc : S₀.rows.card ≤ f := by
      simpa using Finset.card_le_univ S₀.rows
    have h0 : (step^[f] S₀).rows.card = 0 := by omega
    intro r hr
    rw [run, Finset.card_eq_zero.mp h0] at *
    simp at hr
  · exact hprog

/-- The original equations are equivalent to a unit-triangular pivot system over the final
active columns. -/
theorem run_kernel {S₀ : ElimState f m} (h : Inv S₀ S₀) :
    Triangular S₀.run.act S₀.run.piv ∧
      (∀ e, e ∈ S₀.act ↔ e ∈ S₀.run.act ∪ pivots S₀.run.piv) ∧
      ∀ u : Fin m → ℤ, (∀ e ∉ S₀.act, u e = 0) → (S₀.Sys u ↔ Holds S₀.run.piv u) := by
  obtain ⟨hinv, hz⟩ := run_spec h
  refine ⟨hinv.tri, hinv.part, fun u hu => ?_⟩
  rw [hinv.equiv u hu]
  constructor
  · exact fun h' => h'.1
  · intro hp
    refine ⟨hp, fun r hr => ?_⟩
    simp [rowSum, hz r hr]

end ElimState

/-! ## Signed face columns -/

/-- Signed columns have absolute entry sum at most two. -/
theorem column_l1 {f : ℕ} (c : Walks.Column (Fin f)) :
    ∑ r, |Walks.columnVector c r| ≤ 2 := by
  have hpot : ∀ s : Walks.Stub (Fin f), ∑ r, |Walks.potential (some s) r| = 1 := by
    rintro ⟨v, σ⟩
    simp only [Walks.potential]
    rw [Finset.sum_eq_single v]
    · cases σ <;> simp [Walks.signValue]
    · intro b _ hb; simp [hb]
    · simp
  cases c with
  | zero => simp [Walks.columnVector]
  | one s => simp only [Walks.columnVector]; rw [hpot s]; norm_num
  | two s t =>
    simp only [Walks.columnVector]
    calc ∑ r, |Walks.potential (some s) r + Walks.potential (some t) r|
        ≤ ∑ r, (|Walks.potential (some s) r| + |Walks.potential (some t) r|) :=
          Finset.sum_le_sum fun r _ => abs_add_le _ _
      _ = 2 := by rw [Finset.sum_add_distrib, hpot s, hpot t]; norm_num

/-- The elimination started from the columns `C` restricted to the active columns `N`. -/
def columnState (C : Fin m → Walks.Column (Fin f)) (N : Finset (Fin m)) : ElimState f m where
  rows := Finset.univ
  act := N
  M := fun r e => if e ∈ N then Walks.columnVector (C e) r else 0
  piv := []

theorem columnState_inv (C : Fin m → Walks.Column (Fin f)) (N : Finset (Fin m)) :
    ElimState.Inv (columnState C N) (columnState C N) := by
  refine ⟨?_, ?_, ?_, trivial, ?_⟩
  · intro r _ e he
    simp [columnState, if_neg (show e ∉ N from he)]
  · intro e
    simp only [columnState]
    split_ifs with he
    · exact column_l1 (C e)
    · simp
  · intro u _
    exact ⟨fun h => ⟨holds_nil u, h⟩, fun h => h.2⟩
  · intro e
    simp [columnState]

/-- The kernel equations of the columns on `N`, for vectors supported on `N`. -/
theorem columnState_sys (C : Fin m → Walks.Column (Fin f)) (N : Finset (Fin m))
    (u : Fin m → ℤ) (hu : ∀ e ∉ N, u e = 0) :
    (columnState C N).Sys u ↔ ∀ r, ∑ e, Walks.columnVector (C e) r * u e = 0 := by
  simp only [ElimState.Sys, ElimState.rowSum, columnState, Finset.mem_univ, true_implies]
  apply forall_congr'
  intro r
  have : ∀ e, (if e ∈ N then Walks.columnVector (C e) r else 0) * u e =
      Walks.columnVector (C e) r * u e := by
    intro e
    split_ifs with he
    · rfl
    · rw [hu e he]; ring
  simp only [this]

end MWIS.TreeCotree

end
