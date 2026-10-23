module

public import MWIS.FunCoordinatesCostBase

/-!
# Cost of one encoded elimination step

On an encoded state whose lists have length at most `N` and whose matrix entries are at most
`2` in absolute value, one step `elimStepFn` costs at most `K * N ^ 5`.
-/

@[expose] public section

namespace MWIS.FunCoordinates

open MWIS.Fun MWIS.FunLP

variable {N : ℕ}

/-! ## Value bounds -/

theorem getI_abs_le {l : List ℤ} {B : ℤ} (hB : 0 ≤ B) (h : ∀ x ∈ l, |x| ≤ B) (i : ℤ) :
    |getI l 0 i| ≤ B := by
  unfold getI
  split_ifs
  · rw [List.getD_eq_getElem?_getD]
    cases hx : l[i.toNat]? with
    | none => simpa using hB
    | some x => exact h x (List.mem_of_getElem? hx)
  · simpa using hB

theorem getI_list_mem {α : Type*} (l : List (List α)) (i : ℤ) :
    getI l [] i ∈ l ∨ getI l [] i = [] := by
  unfold getI
  split_ifs
  · rw [List.getD_eq_getElem?_getD]
    cases hx : l[i.toNat]? with
    | none => right; rfl
    | some x => left; exact List.mem_of_getElem? hx
  · right; rfl

theorem bits_optInt {o : Option ℕ} (hN : 1 ≤ N) (h : ∀ k, o = some k → k < N) :
    bits (optInt o) ≤ N := by
  cases o with
  | none => simp [optInt]; omega
  | some k =>
    simp only [optInt]
    exact bits_lt_pow (lt_trans (h k rfl) Nat.lt_two_pow_self)

theorem bits_findIdx {α : Type*} (l : List α) (p : α → Bool) (hN : 1 ≤ N) (hl : l.length ≤ N) :
    bits (optInt (l.findIdx? p)) ≤ N := by
  apply bits_optInt hN
  intro k hk
  have := (List.findIdx?_eq_some_iff_getElem.mp hk).1
  omega

theorem bits_index {k : ℕ} (hN : 1 ≤ N) (hk : k < N) : bits (k : ℤ) ≤ N :=
  bits_lt_pow (lt_trans hk Nat.lt_two_pow_self)

theorem bits_le_two {x : ℤ} (hx : |x| ≤ 2) : bits x ≤ 2 := by
  have := bits_mono (x := x) (y := 2) (by simpa using hx)
  simpa using this

theorem bits_le_four {x : ℤ} (hx : |x| ≤ 4) : bits x ≤ 3 := by
  have := bits_mono (x := x) (y := 4) (by simpa using hx)
  simpa using this

theorem bits_le_eight {x : ℤ} (hx : |x| ≤ 8) : bits x ≤ 4 := by
  have := bits_mono (x := x) (y := 8) (by simpa using hx)
  have h8 : bits 8 = 4 := by decide
  omega

/-! ## Searching a row -/

theorem indexedFn_costN (hN : 1 ≤ N) (a : Ty) (l : List a.denote) (hl : l.length ≤ N) :
    (indexedFn a).costAt l ≤ 90 * N ^ 2 := by
  rw [Fn.costAt]
  simp only [indexedFn, Expr.cost, cost_call, Expr.denote, Var.get, Var.index]
  have h := mapIdxFn_costN (pairItem a) () l (K := 2) (d := 1) hN le_rfl hl (fun j hj => by
    rw [Fn.costAt]; simp [pairItem, Expr.cost, Var.index]; omega)
  have h1 := const_le_pow hN 4 2
  simp only [Nat.reduceAdd] at h
  omega

theorem unitPred_costN (hN : 1 ≤ N) (act : List Bool) (cx : ℤ × ℤ) (hl : act.length ≤ N)
    (hc : bits cx.1 ≤ N) (hx : |cx.2| ≤ 2) : unitPred.costAt (act, cx) ≤ 120 * N ^ 2 := by
  rw [Fn.costAt]
  simp only [unitPred, Expr.cost, cost_call, Var.index, CmpOp.charge]
  have h := getBoolFn_costN hN act cx.1 hl hc
  have hb := bits_le_two hx
  have h1 := const_le_pow hN 20 2
  repeat' split
  all_goals (try simp only [Expr.denote, Var.get, bits_one', bits_neg_one'] at *)
  all_goals omega

theorem nonzeroPred_costN (hN : 1 ≤ N) (act : List Bool) (cx : ℤ × ℤ) (hl : act.length ≤ N)
    (hc : bits cx.1 ≤ N) (hx : |cx.2| ≤ 2) : nonzeroPred.costAt (act, cx) ≤ 120 * N ^ 2 := by
  rw [Fn.costAt]
  simp only [nonzeroPred, Expr.cost, cost_call, Var.index, CmpOp.charge]
  have h := getBoolFn_costN hN act cx.1 hl hc
  have hb := bits_le_two hx
  have h1 := const_le_pow hN 20 2
  repeat' split
  all_goals (try simp only [Expr.denote, Var.get, bits_zero'] at *)
  all_goals omega

theorem mem_indexed {α : Type*} {l : List α} {kx : ℤ × α} (h : kx ∈ indexed l) :
    ∃ k, ∃ hk : k < l.length, kx = ((k : ℤ), l[k]) := by
  unfold indexed at h
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp h
  simp only [List.length_mapIdx] at hk
  exact ⟨k, hk, by simp⟩

theorem length_indexed {α : Type*} (l : List α) : (indexed l).length = l.length := by
  simp [indexed]

theorem unitInFn_costN (hN : 1 ≤ N) (act : List Bool) (row : List ℤ) (hl : act.length ≤ N)
    (hr : row.length ≤ N) (hx : ∀ x ∈ row, |x| ≤ 2) :
    unitInFn.costAt (act, row) ≤ 500 * N ^ 3 := by
  rw [Fn.costAt]
  simp only [unitInFn, Expr.cost, cost_call, Expr.denote, Var.get, Var.index, denote_call,
    indexedFn_apply]
  have h1 := indexedFn_costN hN .int row hr
  have h2 := findIdxFn_costN unitPred act (indexed row) (K := 120) (d := 2) hN (by norm_num)
    (by rw [length_indexed]; exact hr) (fun kx hkx => by
      obtain ⟨k, hk, rfl⟩ := mem_indexed hkx
      exact unitPred_costN hN act _ hl (bits_index hN (by omega)) (hx _ (List.getElem_mem hk)))
  have h3 := pow_mono hN (show 2 ≤ 3 by norm_num)
  have h4 := const_le_pow hN 10 3
  simp only [Nat.reduceAdd] at h2
  omega

theorem nonzeroInFn_costN (hN : 1 ≤ N) (act : List Bool) (row : List ℤ) (hl : act.length ≤ N)
    (hr : row.length ≤ N) (hx : ∀ x ∈ row, |x| ≤ 2) :
    nonzeroInFn.costAt (act, row) ≤ 500 * N ^ 3 := by
  rw [Fn.costAt]
  simp only [nonzeroInFn, Expr.cost, cost_call, Expr.denote, Var.get, Var.index, denote_call,
    indexedFn_apply]
  have h1 := indexedFn_costN hN .int row hr
  have h2 := findIdxFn_costN nonzeroPred act (indexed row) (K := 120) (d := 2) hN (by norm_num)
    (by rw [length_indexed]; exact hr) (fun kx hkx => by
      obtain ⟨k, hk, rfl⟩ := mem_indexed hkx
      exact nonzeroPred_costN hN act _ hl (bits_index hN (by omega)) (hx _ (List.getElem_mem hk)))
  have h3 := pow_mono hN (show 2 ≤ 3 by norm_num)
  have h4 := const_le_pow hN 10 3
  simp only [Nat.reduceAdd] at h2
  omega

theorem bits_unitInS (hN : 1 ≤ N) (act : List Bool) (row : List ℤ) (hr : row.length ≤ N) :
    bits (unitInS act row) ≤ N :=
  bits_findIdx _ _ hN (by rw [length_indexed]; exact hr)

theorem bits_nonzeroInS (hN : 1 ≤ N) (act : List Bool) (row : List ℤ) (hr : row.length ≤ N) :
    bits (nonzeroInS act row) ≤ N :=
  bits_findIdx _ _ hN (by rw [length_indexed]; exact hr)

theorem rowUnitPred_costN (hN : 1 ≤ N) (act rows : List Bool) (rrow : ℤ × List ℤ)
    (hl : act.length ≤ N) (hrs : rows.length ≤ N) (hb : bits rrow.1 ≤ N)
    (hr : rrow.2.length ≤ N) (hx : ∀ x ∈ rrow.2, |x| ≤ 2) :
    rowUnitPred.costAt ((act, rows), rrow) ≤ 600 * N ^ 3 := by
  rw [Fn.costAt]
  simp only [rowUnitPred, Expr.cost, cost_call, Var.index, CmpOp.charge]
  have h1 := getBoolFn_costN hN rows rrow.1 hrs hb
  have h2 := unitInFn_costN hN act rrow.2 hl hr hx
  have h3 := bits_unitInS hN act rrow.2 hr
  have h4 := pow_mono hN (show 2 ≤ 3 by norm_num)
  have h5 := pow_mono hN (show 1 ≤ 3 by norm_num)
  have h6 := const_le_pow hN 20 3
  simp only [pow_one] at h5
  repeat' split
  all_goals (try simp only [Expr.denote, Var.get, denote_call, unitInFn_apply, nonzeroInFn_apply,
    bits_zero'] at *)
  all_goals omega

theorem rowNonzeroPred_costN (hN : 1 ≤ N) (act rows : List Bool) (rrow : ℤ × List ℤ)
    (hl : act.length ≤ N) (hrs : rows.length ≤ N) (hb : bits rrow.1 ≤ N)
    (hr : rrow.2.length ≤ N) (hx : ∀ x ∈ rrow.2, |x| ≤ 2) :
    rowNonzeroPred.costAt ((act, rows), rrow) ≤ 600 * N ^ 3 := by
  rw [Fn.costAt]
  simp only [rowNonzeroPred, Expr.cost, cost_call, Var.index, CmpOp.charge]
  have h1 := getBoolFn_costN hN rows rrow.1 hrs hb
  have h2 := nonzeroInFn_costN hN act rrow.2 hl hr hx
  have h3 := bits_nonzeroInS hN act rrow.2 hr
  have h4 := pow_mono hN (show 2 ≤ 3 by norm_num)
  have h5 := pow_mono hN (show 1 ≤ 3 by norm_num)
  have h6 := const_le_pow hN 20 3
  simp only [pow_one] at h5
  repeat' split
  all_goals (try simp only [Expr.denote, Var.get, denote_call, unitInFn_apply, nonzeroInFn_apply,
    bits_zero'] at *)
  all_goals omega

/-! ## Pivots and halving -/

theorem clearFn_costN (hN : 1 ≤ N) (i : ℤ) (l : List Bool) (hi : bits i ≤ N) (hl : l.length ≤ N) :
    clearFn.costAt (i, l) ≤ 130 * N ^ 2 := by
  show (mapIdxFn clearItem).costAt (i, l) ≤ _
  have h := mapIdxFn_costN clearItem i l (K := 20) (d := 1) hN le_rfl hl (fun j hj => by
    rw [Fn.costAt]
    simp only [clearItem, Expr.cost, Var.index, CmpOp.charge]
    have hj' := bits_index hN (show j < N by omega)
    rw [pow_one]
    repeat' split
    all_goals (try simp only [Expr.denote, Var.get] at *)
    all_goals omega)
  simp only [Nat.reduceAdd] at h
  omega

theorem updItem_costN (hN : 1 ≤ N) (rowR : List ℤ) (t : ℤ) (kx : ℤ × ℤ) (hl : rowR.length ≤ N)
    (hR : ∀ y ∈ rowR, |y| ≤ 2) (ht : |t| ≤ 4) (hk : bits kx.1 ≤ N) (hx : |kx.2| ≤ 2) :
    updItem.costAt ((rowR, t), kx) ≤ 110 * N ^ 2 := by
  rw [Fn.costAt]
  simp only [updItem, Expr.cost, cost_call, Var.index, Expr.denote, Var.get, IntOp.charge,
    getIntFn_apply', denote_call, IntOp.eval]
  have h := getIntFn_costN hN rowR kx.1 hl hk
  have hg := getI_abs_le (by norm_num) hR kx.1
  have h1 := bits_le_four ht
  have h2 := bits_le_two hg
  have h3 := bits_le_two hx
  have h4 : bits (t * getI rowR 0 kx.1) ≤ 4 := bits_le_eight (by
    rw [abs_mul]; nlinarith [abs_nonneg t, abs_nonneg (getI rowR 0 kx.1)])
  have h5 : (bits t + 1) * (bits (getI rowR 0 kx.1) + 1) ≤ 12 := by nlinarith
  have h6 := const_le_pow hN 36 2
  omega

theorem updRow_costN (hN : 1 ≤ N) (rowR : List ℤ) (c s : ℤ) (row : List ℤ)
    (hl : rowR.length ≤ N) (hR : ∀ y ∈ rowR, |y| ≤ 2) (hs : |s| ≤ 2) (hc : bits c ≤ N)
    (hr : row.length ≤ N) (hx : ∀ y ∈ row, |y| ≤ 2) :
    updRow.costAt ((rowR, (c, s)), row) ≤ 420 * N ^ 3 := by
  rw [Fn.costAt]
  simp only [updRow, Expr.cost, cost_call, Var.index, Expr.denote, Var.get, IntOp.charge,
    getIntFn_apply', denote_call, IntOp.eval]
  have h := getIntFn_costN hN row c hr hc
  have hg := getI_abs_le (by norm_num) hx c
  have ht : |getI row 0 c * s| ≤ 4 := by
    rw [abs_mul]; nlinarith [abs_nonneg s, abs_nonneg (getI row 0 c)]
  have h1 := bits_le_two hg
  have h2 := bits_le_two hs
  have h3 : (bits (getI row 0 c) + 1) * (bits s + 1) ≤ 9 := by nlinarith
  have h4 := mapIdxFn_costN updItem (rowR, getI row 0 c * s) row (K := 110) (d := 2) hN
    (by norm_num) hr (fun j hj => updItem_costN hN rowR _ _ hl hR ht
      (bits_index hN (by omega)) (hx _ (List.getElem_mem hj)))
  simp only [Nat.reduceAdd] at h4
  have h5 := pow_mono hN (show 2 ≤ 3 by norm_num)
  have h6 := const_le_pow hN 20 3
  omega

/-- An encoded state with lists of length at most `N` and entries at most `2`. -/
def SmallSt (N : ℕ) (st : List Bool × List Bool × List (List ℤ)) : Prop :=
  st.1.length ≤ N ∧ st.2.1.length ≤ N ∧ st.2.2.length ≤ N ∧
    ∀ row ∈ st.2.2, row.length ≤ N ∧ ∀ x ∈ row, |x| ≤ 2

theorem SmallSt.getRow {st : List Bool × List Bool × List (List ℤ)} (h : SmallSt N st) (r : ℤ) :
    (getI st.2.2 [] r).length ≤ N ∧ ∀ x ∈ getI st.2.2 [] r, |x| ≤ 2 := by
  rcases getI_list_mem st.2.2 r with hm | hm
  · exact h.2.2.2 _ hm
  · rw [hm]; simp

theorem pivotFn_costN (hN : 1 ≤ N) (st : List Bool × List Bool × List (List ℤ)) (r c : ℤ)
    (h : SmallSt N st) (hr : bits r ≤ N) (hc : bits c ≤ N) :
    pivotFn.costAt (st, (r, c)) ≤ 1500 * N ^ 4 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [Fn.costAt]
  simp only [pivotFn, Expr.cost, cost_call, Var.index, Expr.denote, Var.get, getListFn_apply',
    getIntFn_apply', denote_call]
  have hR := SmallSt.getRow ⟨h1, h2, h3, h4⟩ r
  have k1 := getListFn_costN hN .int st.2.2 r h3 hr
  have k2 := clearFn_costN hN r st.1 hr h1
  have k3 := clearFn_costN hN c st.2.1 hc h2
  have k4 := getIntFn_costN hN (getI st.2.2 [] r) c hR.1 hc
  have k5 := cmapFn_costN updRow (getI st.2.2 [] r, (c, getI (getI st.2.2 [] r) 0 c)) st.2.2
    (K := 420) (d := 3) hN (by norm_num) h3 (fun row hrow =>
      updRow_costN hN _ _ _ row hR.1 hR.2 (getI_abs_le (by norm_num) hR.2 c) hc (h4 row hrow).1
        (h4 row hrow).2)
  simp only [Nat.reduceAdd] at k5
  have p1 := pow_mono hN (show 2 ≤ 4 by norm_num)
  have p2 := const_le_pow hN 30 4
  omega

theorem halveItem_costN (hN : 1 ≤ N) (r : ℤ) (krow : ℤ × List ℤ) (hr : bits r ≤ N)
    (hk : bits krow.1 ≤ N) (hl : krow.2.length ≤ N) (hx : ∀ x ∈ krow.2, |x| ≤ 2) :
    halveItem.costAt (r, krow) ≤ 120 * N ^ 2 := by
  rw [Fn.costAt]
  simp only [halveItem, Expr.cost, cost_call, Var.index, CmpOp.charge]
  have h := cmapFn_costN (p := .unit) (Expr.arith .div (.snd v0) (.int 2)) () krow.2 (K := 35)
    (d := 1) hN le_rfl hl (fun x hxm => by
      rw [Fn.costAt]
      simp only [Expr.cost, Var.index, Expr.denote, Var.get, IntOp.charge, bits_two']
      have := bits_le_two (hx x hxm)
      have h5 : (bits x + 2 + 1) ^ 2 ≤ 25 := by nlinarith
      have := const_le_pow hN 35 1
      omega)
  simp only [Nat.reduceAdd] at h
  have h1 := const_le_pow hN 10 2
  have h2 := pow_mono hN (show 1 ≤ 2 by norm_num)
  simp only [pow_one] at h2
  repeat' split
  all_goals (try simp only [Expr.denote, Var.get] at *)
  all_goals omega

theorem halveFn_costN (hN : 1 ≤ N) (st : List Bool × List Bool × List (List ℤ)) (r : ℤ)
    (h : SmallSt N st) (hr : bits r ≤ N) : halveFn.costAt (st, r) ≤ 340 * N ^ 3 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [Fn.costAt]
  simp only [halveFn, Expr.cost, cost_call, Var.index, Expr.denote, Var.get]
  have k := mapIdxFn_costN halveItem r st.2.2 (K := 120) (d := 2) hN (by norm_num) h3
    (fun j hj => halveItem_costN hN r _ hr (bits_index hN (by omega))
      (h4 _ (List.getElem_mem hj)).1 (h4 _ (List.getElem_mem hj)).2)
  simp only [Nat.reduceAdd] at k
  have p := const_le_pow hN 20 3
  omega

theorem SmallSt.halve {st : List Bool × List Bool × List (List ℤ)} (h : SmallSt N st) (r : ℤ) :
    SmallSt N (halveS st r) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, by simpa [halveS] using h3, ?_⟩
  intro row hrow
  simp only [halveS, List.mem_mapIdx] at hrow
  obtain ⟨k, hk, rfl⟩ := hrow
  have hm := h4 _ (List.getElem_mem hk)
  split_ifs
  · refine ⟨by simpa using hm.1, ?_⟩
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have := hm.2 y hy
    rw [abs_le] at this ⊢
    constructor <;> omega
  · exact hm

/-! ## One step -/

theorem elimStepFn_costN (hN : 1 ≤ N) (st : List Bool × List Bool × List (List ℤ))
    (h : SmallSt N st) : elimStepFn.costAt st ≤ 6000 * N ^ 4 := by
  have hS := h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hlen : (indexed st.2.2).length ≤ N := by rw [length_indexed]; exact h3
  have k1 := indexedFn_costN hN (.list .int) st.2.2 h3
  have k2 := findIdxFn_costN rowUnitPred (st.2.1, st.1) (indexed st.2.2) (K := 600) (d := 3) hN
    (by norm_num) hlen (fun kx hkx => by
      obtain ⟨k, hk, rfl⟩ := mem_indexed hkx
      exact rowUnitPred_costN hN _ _ _ h2 h1 (bits_index hN (by omega))
        (h4 _ (List.getElem_mem hk)).1 (h4 _ (List.getElem_mem hk)).2)
  have k3 := findIdxFn_costN rowNonzeroPred (st.2.1, st.1) (indexed st.2.2) (K := 600) (d := 3)
    hN (by norm_num) hlen (fun kx hkx => by
      obtain ⟨k, hk, rfl⟩ := mem_indexed hkx
      exact rowNonzeroPred_costN hN _ _ _ h2 h1 (bits_index hN (by omega))
        (h4 _ (List.getElem_mem hk)).1 (h4 _ (List.getElem_mem hk)).2)
  simp only [Nat.reduceAdd] at k2 k3
  have p1 := pow_mono hN (show 2 ≤ 4 by norm_num)
  have p2 := pow_mono hN (show 3 ≤ 4 by norm_num)
  have p3 := pow_mono hN (show 1 ≤ 4 by norm_num)
  have p4 := const_le_pow hN 100 4
  have p5 := pow_mono hN (show 2 ≤ 3 by norm_num)
  have p6 := const_le_pow hN 100 3
  simp only [pow_one] at p3
  rw [Fn.costAt, elimStepFn]
  refine (cost_letE_le _ _ _ (fun r1 : ℤ => bits r1 ≤ N) (A := 1284 * N ^ 4 + 90 * N ^ 2 + 20)
    (B := 4110 * N ^ 4) ?_ ?_ ?_).trans (by omega)
  · simp only [Expr.cost, cost_call, Var.index, Expr.denote, Var.get, denote_call, indexedFn_apply]
    omega
  · simp only [Expr.denote, Var.get, denote_call, findIdxFn_apply', indexedFn_apply]
    exact bits_findIdx _ _ hN hlen
  intro r1 hr1
  refine (cost_ite_le _ _ _ _ (A := N + 5) (B := 4100 * N ^ 4) ?_ ?_ ?_).trans (by omega)
  · exact (cost_ltZero _ _ (a := 2) (by simp [Expr.cost, Var.index]) hr1).trans (by omega)
  · intro _
    refine (cost_letE_le _ _ _ (fun r2 : ℤ => bits r2 ≤ N) (A := 1284 * N ^ 4 + 90 * N ^ 2 + 20)
      (B := 2610 * N ^ 4) ?_ ?_ ?_).trans (by omega)
    · simp only [Expr.cost, cost_call, Var.index, Expr.denote, Var.get, denote_call,
        indexedFn_apply]
      omega
    · simp only [Expr.denote, Var.get, denote_call, findIdxFn_apply', indexedFn_apply]
      exact bits_findIdx _ _ hN hlen
    intro r2 hr2
    refine (cost_ite_le _ _ _ _ (A := N + 5) (B := 2600 * N ^ 4) ?_ ?_ ?_).trans (by omega)
    · exact (cost_ltZero _ _ (a := 2) (by simp [Expr.cost, Var.index]) hr2).trans (by omega)
    · intro _; simp only [Expr.cost, Var.index]; omega
    · intro _
      refine (cost_letE_le _ _ _ (fun H => SmallSt N H) (A := 340 * N ^ 3 + 10)
        (B := 2200 * N ^ 4) ?_ ?_ ?_).trans (by omega)
      · simp only [Expr.cost, cost_call, Var.index, Expr.denote, Var.get]
        have := halveFn_costN hN st r2 hS hr2
        omega
      · simp only [Expr.denote, Var.get, denote_call, halveFn_apply]
        exact hS.halve r2
      intro H hH
      obtain ⟨g1, g2, g3, g4⟩ := hH
      have hR := SmallSt.getRow ⟨g1, g2, g3, g4⟩ r2
      refine (cost_letE_le _ _ _ (fun c : ℤ => bits c ≤ N) (A := 600 * N ^ 3 + 20)
        (B := 1520 * N ^ 4) ?_ ?_ ?_).trans (by omega)
      · simp only [Expr.cost, cost_call, Var.index, Expr.denote, Var.get, denote_call,
          getListFn_apply']
        have := getListFn_costN hN .int H.2.2 r2 g3 hr2
        have := unitInFn_costN hN H.2.1 _ g2 hR.1 hR.2
        omega
      · simp only [Expr.denote, Var.get, denote_call, getListFn_apply', unitInFn_apply]
        exact bits_unitInS hN _ _ hR.1
      intro c hc
      refine (cost_ite_le _ _ _ _ (A := N + 5) (B := 1510 * N ^ 4) ?_ ?_ ?_).trans (by omega)
      · exact (cost_ltZero _ _ (a := 2) (by simp [Expr.cost, Var.index]) hc).trans (by omega)
      · intro _; simp only [Expr.cost, Var.index]; omega
      · intro _
        simp only [Expr.cost, cost_call, Var.index, Expr.denote, Var.get]
        have := pivotFn_costN hN H r2 c ⟨g1, g2, g3, g4⟩ hr2 hc
        omega
  · intro _
    have hR := SmallSt.getRow hS r1
    simp only [Expr.cost, cost_call, Var.index, Expr.denote, Var.get, denote_call,
      getListFn_apply', unitInFn_apply]
    have := getListFn_costN hN .int st.2.2 r1 h3 hr1
    have := unitInFn_costN hN st.2.1 _ h2 hR.1 hR.2
    have := pivotFn_costN hN st r1 _ hS hr1 (bits_unitInS hN st.2.1 _ hR.1)
    omega

end MWIS.FunCoordinates

end
