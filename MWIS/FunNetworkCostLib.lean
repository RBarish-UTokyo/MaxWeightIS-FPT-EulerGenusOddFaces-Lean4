module

public import MWIS.FunNetworkCostCore
public import MWIS.FunNetworkFn

/-!
# Side conditions of the network list utilities

For every closed function of `MWIS.FunNetworkLib` and `MWIS.FunNetworkFn`, the side
condition `OkAt L B` of the syntactic cost bound holds under explicit bounds on
the lengths of the lists and the binary lengths of the integers involved.

Prepared 2026-10-23.
-/

@[expose] public section

namespace MWIS.FunNetwork

open MWIS.Fun MWIS.FunLP

/-! ## Helpers -/

theorem FoldOK.of_forall {α β : Type*} (F : β → α → β) (P : β → α → Prop) (l : List α)
    (b : β) (h : ∀ c y, y ∈ l → P c y) : FoldOK F P b l :=
  FoldOK.of_inv F P (fun _ => True) l b trivial (fun c y hy _ => ⟨h c y hy, trivial⟩)

theorem IterOK.of_forall {β : Type*} (F : β → β) (P : β → Prop) (k : ℕ) (b : β)
    (h : ∀ c, P c) : IterOK F P b k :=
  IterOK.of_inv F P (fun _ _ => True) k b trivial (fun _ c _ _ => ⟨h c, trivial⟩)

theorem bits_le_natAbs (z : ℤ) : bits z ≤ z.natAbs := Nat.size_le.mpr Nat.lt_two_pow_self

theorem bits_le_of_natAbs {z : ℤ} {B : ℕ} (h : z.natAbs ≤ B) : bits z ≤ B :=
  (bits_le_natAbs z).trans h

theorem bits_le_iff {z : ℤ} {k : ℕ} : bits z ≤ k ↔ z.natAbs < 2 ^ k := Nat.size_le

theorem bits_mono {x y : ℤ} (h : x.natAbs ≤ y.natAbs) : bits x ≤ bits y := Nat.size_le_size h

theorem bits_two_pow (i : ℕ) : bits ((2 : ℤ) ^ i) = i + 1 := by
  unfold bits
  rw [Int.natAbs_pow]
  simp [Nat.size_pow]

@[simp] theorem bits_one : bits (1 : ℤ) = 1 := by decide
@[simp] theorem bits_two : bits (2 : ℤ) = 2 := by decide
@[simp] theorem bits_zero : bits (0 : ℤ) = 0 := by decide

/-- A call of `rev` on an inner expression, with the length of the result. -/
theorem ok_rev_call (L B : ℕ) {σ : Ty} {a : Ty} (inner : Expr [σ] (.list a)) (x : σ.denote)
    (h1 : Ok L B inner (x, ())) (h2 : (Fn.apply (call (rev a) inner) x).length ≤ L) :
    OkAt L B (call (rev a) inner) x := by
  simp only [OkAt, ok_call]
  refine ⟨h1, ?_⟩
  have e : Fn.apply (call (rev a) inner) x = (inner.denote (x, ())).reverse := by
    rw [Fn.apply, denote_call, rev_apply]
  rw [e, List.length_reverse] at h2
  simp only [rev, Ok, Expr.denote, Var.get, true_and]
  exact ⟨h2, FoldOK.of_forall _ _ _ _ (fun _ _ _ => trivial)⟩

/-! ## Library functions -/

theorem rev_ok (L B : ℕ) (a : Ty) (l : List a.denote) (h : l.length ≤ L) :
    OkAt L B (rev a) l := by
  simp only [OkAt, rev, Ok, Expr.denote, Var.get, true_and]
  exact ⟨h, FoldOK.of_forall _ _ _ _ (fun _ _ _ => trivial)⟩

theorem mapWith_ok (L B : ℕ) {γ α β : Ty} (f : Fn (.prod γ α) β) (x : γ.denote × List α.denote)
    (hl : x.2.length ≤ L) (hf : ∀ a ∈ x.2, OkAt L B f (x.1, a)) : OkAt L B (mapWith f) x := by
  have happ := mapWith_apply f x
  unfold mapWith at happ ⊢
  apply ok_rev_call
  · simp only [Ok, Expr.denote, Var.get, ok_call, true_and, and_true]
    exact ⟨hl, FoldOK.of_forall _ _ _ _ (fun _ y hy => hf y hy)⟩
  · rw [happ, List.length_map]; exact hl

theorem flatMapWith_ok (L B : ℕ) {γ α β : Ty} (f : Fn (.prod γ α) (.list β))
    (x : γ.denote × List α.denote) (hl : x.2.length ≤ L)
    (hf : ∀ a ∈ x.2, OkAt L B f (x.1, a) ∧ (f.apply (x.1, a)).length ≤ L)
    (hall : (x.2.flatMap (fun a => f.apply (x.1, a))).length ≤ L) :
    OkAt L B (flatMapWith f) x := by
  have happ := flatMapWith_apply f x
  unfold flatMapWith at happ ⊢
  apply ok_rev_call
  · simp only [Ok, Expr.denote, Var.get, ok_call, true_and, and_true, denote_call]
    refine ⟨hl, FoldOK.of_forall _ _ _ _ (fun _ y hy => ⟨(hf y hy).1, (hf y hy).2,
      FoldOK.of_forall _ _ _ _ (fun _ _ _ => trivial)⟩)⟩
  · rw [happ]; exact hall

theorem range_ok (L B : ℕ) (n : ℤ) (hn : n.toNat ≤ L) (hb : bits n ≤ B) (hB : 1 ≤ B) :
    OkAt L B range n := by
  simp only [OkAt, range, Ok, Expr.denote, Var.get, IntOp.eval, true_and, and_true, bits_one]
  refine ⟨hn, hb, IterOK.of_inv _ _ (fun i (s : ℤ × List ℤ) => s.1 = n - i) _ _ (by simp) ?_⟩
  intro i c hi hc
  have hbc : bits c.1 ≤ B := by
    rw [hc]
    refine le_trans (bits_mono ?_) hb
    have : (i : ℤ) < n := by omega
    omega
  refine ⟨by simp only [hbc, hB, and_self], ?_⟩
  simp only [hc]; push_cast; ring

theorem eqList_ok (L B : ℕ) (x : List ℤ × List ℤ) (hl : x.1.length ≤ L)
    (h1 : ∀ z ∈ x.1, bits z ≤ B) (h2 : ∀ z ∈ x.2, bits z ≤ B) : OkAt L B eqList x := by
  simp only [OkAt, eqList, Ok, Expr.denote, Var.get, true_and]
  refine ⟨⟨hl, ?_⟩, ?_⟩
  · refine FoldOK.of_inv _ _ (fun (s : Bool × List ℤ) => ∀ z ∈ s.2, bits z ≤ B) _ _ h2 ?_
    rintro ⟨flag, l⟩ y hy hc
    cases l with
    | nil => simp
    | cons h t =>
      simp only [List.mem_cons, forall_eq_or_imp] at hc
      refine ⟨⟨?_, trivial⟩, ?_⟩
      · cases flag <;> simp [h1 y hy, hc.1]
      · exact hc.2
  · split <;> trivial

theorem consFn_ok (L B : ℕ) (a : Ty) (x : a.denote × List a.denote) : OkAt L B (consFn a) x := by
  simp [OkAt, consFn, Ok]

theorem extendFn_ok (L B : ℕ) (x : List (List ℤ) × ℤ) (hl : x.1.length ≤ L) :
    OkAt L B extendFn x := by
  simp only [OkAt, extendFn, ok_call, Ok, true_and, Expr.denote, Var.get]
  exact mapWith_ok L B _ _ hl (fun a _ => consFn_ok L B _ _)

theorem appendFn_ok (L B : ℕ) (a : Ty) (x : List a.denote × List a.denote) (hl : x.1.length ≤ L) :
    OkAt L B (appendFn a) x := by
  simp only [OkAt, appendFn, ok_call, Ok, true_and, Expr.denote, Var.get, and_true, denote_call,
    rev_apply, List.length_reverse]
  exact ⟨rev_ok L B a _ hl, hl, FoldOK.of_forall _ _ _ _ (fun _ _ _ => trivial)⟩

theorem lengthFn_ok (L B : ℕ) (a : Ty) (l : List a.denote) (hl : l.length ≤ L)
    (hLB : L + 1 ≤ B) : OkAt L B (lengthFn a) l := by
  simp only [OkAt, lengthFn, Ok, Expr.denote, Var.get, IntOp.eval, true_and, bits_one]
  refine ⟨hl, FoldOK.of_prefix _ _ _ _ (fun i hi => ⟨?_, by omega⟩)⟩
  rw [foldl_succ_int]
  apply bits_le_of_natAbs
  simp only [List.length_take, zero_add]
  omega

theorem powFn_ok (L B : ℕ) (n : ℤ) (hn : n.toNat ≤ L) (hb : bits n ≤ B) (hB : n.toNat + 2 ≤ B) :
    OkAt L B powFn n := by
  simp only [OkAt, powFn, Ok, Expr.denote, Var.get, IntOp.eval, true_and, bits_two]
  refine ⟨hn, hb, IterOK.of_inv _ _ (fun i (s : ℤ) => s = 2 ^ i) _ _ (by simp) ?_⟩
  intro i c hi hc
  subst hc
  refine ⟨⟨by omega, by rw [bits_two_pow]; omega⟩, by ring⟩

theorem replFn_ok (L B : ℕ) (n : ℤ) (hn : n.toNat ≤ L) (hb : bits n ≤ B) :
    OkAt L B replFn n := by
  simp only [OkAt, replFn, Ok, Expr.denote, Var.get, true_and]
  exact ⟨hn, hb, IterOK.of_forall _ _ _ _ (fun _ => trivial)⟩

theorem length_indexFrom {α : Type*} (k : ℤ) (l : List α) : (indexFrom k l).length = l.length := by
  induction l generalizing k with
  | nil => rfl
  | cons _ l ih => simp [indexFrom, ih]

theorem length_indexPow {α : Type*} (k p : ℤ) (l : List α) :
    (indexPow k p l).length = l.length := by
  induction l generalizing k p with
  | nil => rfl
  | cons _ l ih => simp [indexPow, ih]

theorem indexFromFn_ok (L B : ℕ) (a : Ty) (l : List a.denote) (hl : l.length ≤ L)
    (hLB : L + 1 ≤ B) : OkAt L B (indexFromFn a) l := by
  have happ := indexFromFn_apply a l
  unfold indexFromFn at happ ⊢
  apply ok_rev_call
  · simp only [Ok, Expr.denote, Var.get, IntOp.eval, true_and, and_true, bits_one]
    refine ⟨hl, FoldOK.of_prefix _ _ _ _ (fun i hi => ⟨?_, by omega⟩)⟩
    rw [indexFrom_foldl]
    apply bits_le_of_natAbs
    simp only [List.length_take, zero_add]
    omega
  · rw [happ, length_indexFrom]; exact hl

theorem indexPowFn_ok (L B : ℕ) (l : List (List ℤ × List ℤ × List ℤ × ℤ)) (hl : l.length ≤ L)
    (hLB : L + 2 ≤ B) : OkAt L B indexPowFn l := by
  have happ := indexPowFn_apply l
  unfold indexPowFn at happ ⊢
  apply ok_rev_call
  · simp only [Ok, Expr.denote, Var.get, IntOp.eval, true_and, and_true, bits_one, bits_two]
    refine ⟨hl, FoldOK.of_prefix _ _ _ _ (fun i hi => ⟨⟨?_, by omega⟩, by omega, ?_⟩)⟩
    · rw [indexPow_foldl]
      apply bits_le_of_natAbs
      simp only [List.length_take, zero_add]
      omega
    · rw [indexPow_foldl]
      simp only [List.length_take, one_mul, bits_two_pow]
      omega
  · rw [happ, length_indexPow]; exact hl

/-! ## Lengths -/

theorem length_flatMap_le {α β : Type*} (l : List α) (g : α → List β) (c : ℕ)
    (h : ∀ a ∈ l, (g a).length ≤ c) : (l.flatMap g).length ≤ l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    have h1 := h a (by simp)
    have h2 := ih (fun b hb => h b (by simp [hb]))
    omega

theorem length_flatMap_const {α β : Type*} (l : List α) (g : α → List β) (c : ℕ)
    (h : ∀ a ∈ l, (g a).length = c) : (l.flatMap g).length = l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul,
      h a (by simp), ih (fun b hb => h b (by simp [hb]))]
    omega

theorem mem_zrange {z n : ℤ} (h : z ∈ zrange n) : 0 ≤ z ∧ z < n := by
  simp only [zrange, List.mem_map, List.mem_range] at h
  obtain ⟨i, hi, rfl⟩ := h
  omega

theorem length_zrange (n : ℤ) : (zrange n).length = n.toNat := by simp [zrange]

theorem length_vecsE (μ : ℤ) : ∀ k, (vecsE μ k).length = μ.toNat ^ k
  | 0 => rfl
  | k + 1 => by
    rw [vecsE, length_flatMap_const _ _ (μ.toNat ^ k) (fun a _ => by
      rw [List.length_map, length_vecsE μ k]), length_zrange, pow_succ, Nat.mul_comm]

theorem mem_vecsE (μ : ℤ) : ∀ (k : ℕ) (v : List ℤ), v ∈ vecsE μ k →
    v.length = k ∧ ∀ z ∈ v, 0 ≤ z ∧ z < μ
  | 0, v, h => by simp [vecsE] at h; subst h; simp
  | k + 1, v, h => by
    simp only [vecsE, List.mem_flatMap, List.mem_map] at h
    obtain ⟨x, hx, w, hw, rfl⟩ := h
    obtain ⟨h1, h2⟩ := mem_vecsE μ k w hw
    refine ⟨by simp [h1], ?_⟩
    intro z hz
    simp only [List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact mem_zrange hx
    · exact h2 z hz

theorem length_groupE (r μ : ℤ) : (groupE r μ).length = 2 * μ.toNat ^ r.toNat := by
  rw [groupE, length_flatMap_const _ _ (μ.toNat ^ r.toNat) (fun a _ => by
    rw [List.length_map, length_vecsE]), length_zrange]
  rfl

theorem mem_groupE (r μ : ℤ) (hμ : 2 ≤ μ) (g : List ℤ) (h : g ∈ groupE r μ) :
    g.length = r.toNat + 1 ∧ ∀ z ∈ g, 0 ≤ z ∧ z < μ := by
  simp only [groupE, List.mem_flatMap, List.mem_map] at h
  obtain ⟨p, hp, w, hw, rfl⟩ := h
  obtain ⟨h1, h2⟩ := mem_vecsE μ r.toNat w hw
  have hp' := mem_zrange hp
  refine ⟨by simp [h1], ?_⟩
  intro z hz
  simp only [List.mem_cons] at hz
  rcases hz with rfl | hz
  · omega
  · exact h2 z hz

theorem length_statesE (f : ℤ) : (statesE f).length = 2 * f.toNat + 1 := by
  rw [statesE, List.length_cons, length_flatMap_const _ _ 2 (fun _ _ => rfl), length_zrange]
  ring

theorem mem_statesE (f : ℤ) (hf : 0 ≤ f) (z : ℤ) (h : z ∈ statesE f) : 0 ≤ z ∧ z ≤ 2 * f := by
  simp only [statesE, List.mem_cons, List.mem_flatMap] at h
  rcases h with rfl | ⟨k, hk, hz⟩
  · omega
  · have := mem_zrange hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    omega

/-! ## States and residues -/

theorem stubPairFn_ok (L B : ℕ) (x : Unit × ℤ) (hk : 2 * x.2.natAbs + 2 ≤ B) :
    OkAt L B stubPairFn x := by
  have h1 : bits x.2 ≤ B := bits_le_of_natAbs (by omega)
  have h2 : bits (2 * x.2) ≤ B := bits_le_of_natAbs (by rw [Int.natAbs_mul]; simp; omega)
  simp only [OkAt, stubPairFn, Ok, Expr.denote, Var.get, IntOp.eval, true_and, and_true,
    bits_one, bits_two, h1, h2]
  omega

theorem stubPairFn_length (x : Unit × ℤ) : (stubPairFn.apply x).length = 2 := rfl

theorem statesFn_ok (L B : ℕ) (f : ℤ) (hL : 2 * f.toNat + 1 ≤ L)
    (hB : 2 * L + 2 ≤ B) (hfB : bits f ≤ B) : OkAt L B statesFn f := by
  simp only [OkAt, statesFn, Ok, ok_call, Expr.denote, Var.get, true_and, denote_call]
  refine ⟨range_ok L B f (by omega) hfB (by omega), ?_⟩
  apply flatMapWith_ok
  · simp only [range_apply, List.length_map, List.length_range]; omega
  · intro a ha
    simp only [range_apply, List.mem_map, List.mem_range] at ha
    obtain ⟨i, hi, rfl⟩ := ha
    refine ⟨stubPairFn_ok L B _ (by simp; omega), by rw [stubPairFn_length]; omega⟩
  · rw [length_flatMap_const _ _ 2 (fun _ _ => rfl)]
    simp only [range_apply, List.length_map, List.length_range]; omega

theorem vecsFn_ok (L B : ℕ) (x : ℤ × ℤ) (hμ : 1 ≤ x.1) (hμL : x.1.toNat ≤ L)
    (hμB : bits x.1 ≤ B) (hk : x.2.toNat ≤ L) (hkB : bits x.2 ≤ B)
    (hpow : x.1.toNat ^ x.2.toNat ≤ L) (hB : 1 ≤ B) : OkAt L B vecsFn x := by
  simp only [OkAt, vecsFn, Ok, ok_call, Expr.denote, Var.get, true_and, denote_call]
  refine ⟨hk, hkB, IterOK.of_inv _ _ (fun i (s : List (List ℤ)) => s = vecsE x.1 i) _ _ rfl ?_⟩
  intro i c hi hc
  subst hc
  have hpi : ∀ j, j ≤ x.2.toNat → x.1.toNat ^ j ≤ L := fun j hj =>
    (Nat.pow_le_pow_right (by omega) hj).trans hpow
  refine ⟨⟨range_ok L B _ hμL hμB hB, ?_⟩, ?_⟩
  · apply flatMapWith_ok
    · simp only [range_apply, List.length_map, List.length_range]; exact hμL
    · intro a _
      refine ⟨extendFn_ok L B _ ?_, ?_⟩
      · rw [length_vecsE]; exact hpi i (by omega)
      · rw [extendFn_apply, List.length_map, length_vecsE]; exact hpi i (by omega)
    · rw [length_flatMap_const _ _ (x.1.toNat ^ i) (fun a _ => by
        rw [extendFn_apply, List.length_map, length_vecsE])]
      simp only [range_apply, List.length_map, List.length_range]
      rw [← pow_succ']
      exact hpi (i + 1) (by omega)
  · simp only [flatMapWith_apply, range_apply, extendFn_apply]
    rfl

theorem groupFn_ok (L B : ℕ) (x : ℤ × ℤ) (hμ : 2 ≤ x.2) (hμL : x.2.toNat ≤ L)
    (hμB : bits x.2 ≤ B) (hk : x.1.toNat ≤ L) (hkB : bits x.1 ≤ B)
    (hpow : 2 * x.2.toNat ^ x.1.toNat ≤ L) (hB : 2 ≤ B) : OkAt L B groupFn x := by
  simp only [OkAt, groupFn, Ok, ok_call, Expr.denote, Var.get, true_and, denote_call]
  have hp1 : x.2.toNat ^ x.1.toNat ≤ L := by omega
  have h2L : 2 ≤ L := by
    have : 1 ≤ x.2.toNat ^ x.1.toNat := Nat.one_le_pow _ _ (by omega)
    omega
  refine ⟨⟨vecsFn_ok L B _ (by simp; omega) hμL hμB hk hkB hp1 (by omega),
    range_ok L B 2 (by simp; omega) (by simp; omega) (by omega)⟩, ?_⟩
  apply flatMapWith_ok
  · simp only [range_apply, List.length_map, List.length_range]; simp; omega
  · intro a _
    simp only [vecsFn_apply]
    refine ⟨extendFn_ok L B _ ?_, ?_⟩
    · rw [length_vecsE]; exact hp1
    · rw [extendFn_apply, List.length_map, length_vecsE]; exact hp1
  · simp only [vecsFn_apply]
    rw [length_flatMap_const _ _ (x.2.toNat ^ x.1.toNat) (fun a _ => by
      rw [extendFn_apply, List.length_map, length_vecsE])]
    simp only [range_apply, List.length_map, List.length_range]
    simpa [Nat.mul_comm] using hpow

theorem zipModFn_ok (L B A : ℕ) (x : ℤ × List ℤ × List ℤ) (hg : ∀ z ∈ x.2.1, z.natAbs ≤ A)
    (hh : ∀ z ∈ x.2.2, z.natAbs ≤ A) (hA : 2 * A ≤ B) (hμ : bits x.1 ≤ B)
    (hl : x.2.1.length ≤ L) : OkAt L B zipModFn x := by
  have happ := zipModFn_apply x
  unfold zipModFn at happ ⊢
  apply ok_rev_call
  · simp only [Ok, Expr.denote, Var.get, IntOp.eval, true_and, and_true]
    refine ⟨hl, FoldOK.of_inv _ _ (fun (s : List ℤ × List ℤ) => ∀ z ∈ s.1, z.natAbs ≤ A) _ _ hh ?_⟩
    rintro ⟨l, a⟩ y hy hc
    cases l with
    | nil => simp [hc]
    | cons h t =>
      simp only [List.mem_cons, forall_eq_or_imp] at hc
      have e1 := hg y hy
      refine ⟨⟨⟨bits_le_of_natAbs (by omega), bits_le_of_natAbs (by omega)⟩,
        bits_le_of_natAbs (by omega), hμ⟩, hc.2⟩
  · rw [happ, List.length_zipWith]; omega

theorem addFn_ok (L B A : ℕ) (x : ℤ × List ℤ × List ℤ) (hg : ∀ z ∈ x.2.1, z.natAbs ≤ A)
    (hh : ∀ z ∈ x.2.2, z.natAbs ≤ A) (hA : 2 * A ≤ B) (hμ : bits x.1 ≤ B) (hB : 2 ≤ B)
    (hl : x.2.1.length ≤ L) : OkAt L B addFn x := by
  rcases x with ⟨μ, g, h⟩
  cases g with
  | nil => simp [OkAt, addFn, Ok, Expr.denote, Var.get]
  | cons a g =>
    cases h with
    | nil => simp [OkAt, addFn, Ok, Expr.denote, Var.get]
    | cons b h =>
      simp only [List.mem_cons, forall_eq_or_imp] at hg hh
      simp only [OkAt, addFn, Ok, ok_call, Expr.denote, Var.get, IntOp.eval, true_and,
        and_true, bits_two]
      refine ⟨⟨⟨bits_le_of_natAbs (by omega), bits_le_of_natAbs (by omega)⟩,
        bits_le_of_natAbs (by omega), hB⟩, ?_⟩
      exact zipModFn_ok L B A _ hg.2 hh.2 hA hμ (by simp at hl ⊢; omega)

/-! ## Arcs -/

theorem oppFn_ok (L B : ℕ) (c : ℤ) (hc : c.natAbs + 1 ≤ B) (hB : 2 ≤ B) : OkAt L B oppFn c := by
  have h1 : bits c ≤ B := bits_le_of_natAbs (by omega)
  have h2 : bits (c % 2) ≤ B := bits_le_of_natAbs (by
    rcases Int.emod_two_eq_zero_or_one c with h | h <;> rw [h] <;> simp <;> omega)
  simp only [OkAt, oppFn, Ok, Expr.denote, Var.get, IntOp.eval, CmpOp.eval, true_and, bits_one,
    bits_two, h1, h2]
  exact ⟨⟨hB, by omega⟩, fun _ => by omega, fun _ => by omega⟩

theorem srcFn_ok (L B : ℕ) (x : List ℤ × Bool) (hc : ∀ z ∈ x.1, z.natAbs + 1 ≤ B)
    (hB : 2 ≤ B) : OkAt L B srcFn x := by
  rcases x with ⟨col, b⟩
  rcases col with _ | ⟨s, _ | ⟨t, rest⟩⟩
  · simp [OkAt, srcFn, Ok, Expr.denote, Var.get]
  · simp only [List.mem_cons, forall_eq_or_imp] at hc
    cases b <;> simp only [OkAt, srcFn, Ok, ok_call, Expr.denote, Var.get, true_and,
      Bool.false_eq_true, ↓reduceIte, implies_true, true_implies, false_implies,
      Bool.true_eq_false, and_true] <;> exact oppFn_ok L B _ hc.1 hB
  · simp only [List.mem_cons, forall_eq_or_imp] at hc
    cases b <;> simp only [OkAt, srcFn, Ok, ok_call, Expr.denote, Var.get, true_and,
      Bool.false_eq_true, ↓reduceIte, implies_true, true_implies, false_implies,
      Bool.true_eq_false, and_true]
    · exact oppFn_ok L B _ hc.1 hB
    · exact oppFn_ok L B _ hc.2.1 hB

theorem tgtFn_ok (L B : ℕ) (x : List ℤ × Bool) : OkAt L B tgtFn x := by
  rcases x with ⟨col, b⟩
  rcases col with _ | ⟨s, _ | ⟨t, rest⟩⟩ <;> cases b <;>
    simp [OkAt, tgtFn, Ok, Expr.denote, Var.get]

theorem dirsFn_ok (L B : ℕ) (col : List ℤ) : OkAt L B dirsFn col := by
  cases col <;> simp [OkAt, dirsFn, Ok, Expr.denote, Var.get]

theorem length_dirsE (col : List ℤ) : (dirsE col).length ≤ 2 := by
  unfold dirsE; split_ifs <;> simp

/-- The numerical side conditions of one indexed edge record `(P, k, p, e)`. -/
def ArcInputOk (B : ℕ) (x : ℤ × ℤ × ℤ × EdgeIn) : Prop :=
  (∀ z ∈ x.2.2.2.1, z.natAbs + 1 ≤ B) ∧ bits x.1 ≤ B ∧ bits x.2.2.2.2.2.2 ≤ B ∧
    bits x.2.2.1 ≤ B ∧ bits (x.1 * x.2.2.2.2.2.2) ≤ B ∧
    bits (x.1 * x.2.2.2.2.2.2 + x.2.2.1) ≤ B

theorem arcOfDirFn_ok (L B : ℕ) (x : (ℤ × ℤ × ℤ × EdgeIn) × Bool) (h : ArcInputOk B x.1)
    (hB : 2 ≤ B) : OkAt L B arcOfDirFn x := by
  obtain ⟨hcol, hP, hc, hp, hPc, hPcp⟩ := h
  simp only [OkAt, arcOfDirFn, Ok, ok_call, Expr.denote, Var.get, IntOp.eval, true_and,
    and_true, bits_two]
  exact ⟨srcFn_ok L B _ hcol hB, tgtFn_ok L B _, ⟨⟨hP, hc⟩, hPc, hp⟩, hB, hPcp⟩

theorem edgeArcsFn_ok (L B : ℕ) (x : ℤ × ℤ × ℤ × EdgeIn) (h : ArcInputOk B x)
    (hB : 2 ≤ B) (hL : 2 ≤ L) : OkAt L B edgeArcsFn x := by
  simp only [OkAt, edgeArcsFn, Ok, ok_call, Expr.denote, Var.get, true_and, denote_call]
  refine ⟨dirsFn_ok L B _, mapWith_ok L B _ _ ?_ (fun b _ => arcOfDirFn_ok L B _ h hB)⟩
  rw [dirsFn_apply]
  exact (length_dirsE _).trans hL

theorem length_edgeArcs (P : ℤ) (x : ℤ × ℤ × EdgeIn) : (edgeArcs P x).length ≤ 2 := by
  rw [edgeArcs, List.length_map]; exact length_dirsE _

theorem arcsFn_ok (L B : ℕ) (x : ℤ × List EdgeIn) (hl : 2 * x.2.length ≤ L) (hLB : L + 2 ≤ B)
    (hL : 2 ≤ L) (h : ∀ y ∈ indexPow 0 1 x.2, ArcInputOk B (x.1, y)) :
    OkAt L B arcsFn x := by
  simp only [OkAt, arcsFn, Ok, ok_call, Expr.denote, Var.get, true_and, denote_call]
  refine ⟨indexPowFn_ok L B _ (by omega) hLB, ?_⟩
  rw [indexPowFn_apply]
  apply flatMapWith_ok
  · rw [length_indexPow]; omega
  · intro a ha
    refine ⟨edgeArcsFn_ok L B _ (h a ha) (by omega) hL, ?_⟩
    rw [edgeArcsFn_apply]; exact (length_edgeArcs _ _).trans hL
  · refine (length_flatMap_le _ _ 2 (fun a _ => ?_)).trans ?_
    · rw [edgeArcsFn_apply]; exact length_edgeArcs _ _
    · rw [length_indexPow]; omega

end MWIS.FunNetwork

end
