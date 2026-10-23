module

public import MWIS.FunLPBasic
public import Mathlib.Data.Nat.Size
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

/-!
# Closed `Fun` list utilities for the network program

Reversal, map and flat-map with a fixed context value, integer ranges, list
equality and indexed lookup. Each function has its meaning (`apply`) and a cost
bound.

Prepared 2026-10-23.
-/

@[expose] public section

namespace MWIS.FunNetwork

open MWIS.Fun MWIS.FunLP

/-! ## Reversal -/

/-- Reverse a list. -/
def rev (a : Ty) : Fn (.list a) (.list a) := .foldl v0 .nil (.cons v0 v1)

theorem foldl_cons_eq {α : Type*} (l acc : List α) :
    l.foldl (fun acc y => y :: acc) acc = l.reverse ++ acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons y l ih => simp [ih]

@[simp] theorem rev_apply (a : Ty) (l : List a.denote) : (rev a).apply l = l.reverse := by
  simp [rev, Fn.apply, Expr.denote, Var.get, foldl_cons_eq]

theorem rev_cost (a : Ty) (l : List a.denote) : (rev a).costAt l ≤ 5 * l.length + 3 := by
  have h := cost_foldl_le (Γ := [.list a]) v0 .nil (.cons v0 v1) (l, ()) (fun _ => True) 4
    trivial (fun acc y _ _ => ⟨trivial, by simp [Expr.cost, Var.index]⟩)
  calc (rev a).costAt l = (Expr.foldl (Γ := [.list a]) v0 .nil (.cons v0 v1)).cost (l, ()) := rfl
    _ ≤ _ := h
    _ ≤ _ := by simp only [Expr.cost, Var.index, Expr.denote, Var.get]; omega

/-! ## Map with a context value -/

/-- `mapWith f (c, l) = l.map (fun a => f (c, a))`. -/
def mapWith {γ α β : Ty} (f : Fn (.prod γ α) β) : Fn (.prod γ (.list α)) (.list β) :=
  call (rev β) (.foldl (.snd v0) .nil (.cons (call f (.pair (.fst v2) v0)) v1))

theorem foldl_cons_map {α β : Type*} (g : α → β) (l : List α) (acc : List β) :
    l.foldl (fun acc y => g y :: acc) acc = (l.map g).reverse ++ acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons y l ih => simp [ih]

theorem mapWith_inner {γ α β : Ty} (f : Fn (.prod γ α) β) (x : γ.denote × List α.denote) :
    (Expr.foldl (Γ := [.prod γ (.list α)]) (.snd v0) .nil
      (.cons (call f (.pair (.fst v2) v0)) v1)).denote (x, ()) =
      (x.2.map (fun a => f.apply (x.1, a))).reverse := by
  simp only [Expr.denote, Var.get, denote_call]
  have h := foldl_cons_map (fun a => f.apply (x.1, a)) x.2 []
  simpa using h

@[simp] theorem mapWith_apply {γ α β : Ty} (f : Fn (.prod γ α) β)
    (x : γ.denote × List α.denote) :
    (mapWith f).apply x = x.2.map (fun a => f.apply (x.1, a)) := by
  have h := mapWith_inner f x
  unfold mapWith
  simp only [Fn.apply] at h ⊢
  rw [denote_call, h]
  exact (rev_apply β _).trans (List.reverse_reverse _)

theorem mapWith_cost {γ α β : Ty} (f : Fn (.prod γ α) β) (x : γ.denote × List α.denote)
    (c0 : ℕ) (hf : ∀ a ∈ x.2, f.costAt (x.1, a) ≤ c0) :
    (mapWith f).costAt x ≤ (x.2.length + 1) * (c0 + 20) := by
  have hfold := cost_foldl_le (Γ := [.prod γ (.list α)]) (.snd v0) .nil
    (.cons (call f (.pair (.fst v2) v0)) v1) (x, ()) (fun _ => True) (c0 + 10) trivial
    (fun acc y hy _ => by
      refine ⟨trivial, ?_⟩
      simp only [Expr.cost, cost_call, Var.index, Expr.denote, Var.get]
      have := hf y hy
      omega)
  have hrev := rev_cost β ((x.2.map (fun a => f.apply (x.1, a))).reverse)
  simp only [List.length_reverse, List.length_map] at hrev
  have hs : (Expr.snd (Γ := [.prod γ (.list α)]) v0).cost (x, ()) = 2 := rfl
  have hn : (Expr.nil (Γ := [.prod γ (.list α)]) (a := β)).cost (x, ()) = 1 := rfl
  calc (mapWith f).costAt x = (Expr.foldl (Γ := [.prod γ (.list α)]) (.snd v0) .nil
        (.cons (call f (.pair (.fst v2) v0)) v1)).cost (x, ()) +
        (rev β).costAt ((x.2.map (fun a => f.apply (x.1, a))).reverse) + 1 := by
        unfold mapWith; simp only [Fn.costAt]; rw [cost_call, mapWith_inner]; rfl
    _ ≤ (2 + 1 + x.2.length * (c0 + 10 + 1) + 1) + (5 * x.2.length + 3) + 1 := by
        rw [hs, hn] at hfold; simp only [Expr.denote, Var.get] at hfold; omega
    _ ≤ _ := by nlinarith

/-! ## Flat map with a context value -/

/-- `flatMapWith f (c, l) = l.flatMap (fun a => f (c, a))`. -/
def flatMapWith {γ α β : Ty} (f : Fn (.prod γ α) (.list β)) :
    Fn (.prod γ (.list α)) (.list β) :=
  call (rev β) (.foldl (.snd v0) .nil (.foldl (call f (.pair (.fst v2) v0)) v1 (.cons v0 v1)))

theorem foldl_revAppend {α β : Type*} (g : α → List β) (l : List α) (acc : List β) :
    l.foldl (fun acc y => (g y).foldl (fun acc z => z :: acc) acc) acc =
      (l.flatMap g).reverse ++ acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons y l ih =>
    rw [List.foldl_cons, foldl_cons_eq, ih, List.flatMap_cons, List.reverse_append,
      List.append_assoc]

theorem flatMapWith_inner {γ α β : Ty} (f : Fn (.prod γ α) (.list β))
    (x : γ.denote × List α.denote) :
    (Expr.foldl (Γ := [.prod γ (.list α)]) (.snd v0) .nil
      (.foldl (call f (.pair (.fst v2) v0)) v1 (.cons v0 v1))).denote (x, ()) =
      (x.2.flatMap (fun a => f.apply (x.1, a))).reverse := by
  simp only [Expr.denote, Var.get, denote_call]
  have h := foldl_revAppend (fun a => f.apply (x.1, a)) x.2 []
  simpa using h

@[simp] theorem flatMapWith_apply {γ α β : Ty} (f : Fn (.prod γ α) (.list β))
    (x : γ.denote × List α.denote) :
    (flatMapWith f).apply x = x.2.flatMap (fun a => f.apply (x.1, a)) := by
  have h := flatMapWith_inner f x
  unfold flatMapWith
  simp only [Fn.apply] at h ⊢
  rw [denote_call, h]
  exact (rev_apply β _).trans (List.reverse_reverse _)

theorem flatMapWith_cost {γ α β : Ty} (f : Fn (.prod γ α) (.list β))
    (x : γ.denote × List α.denote) (c0 L : ℕ)
    (hf : ∀ a ∈ x.2, f.costAt (x.1, a) ≤ c0 ∧ (f.apply (x.1, a)).length ≤ L) :
    (flatMapWith f).costAt x ≤ (x.2.length + 1) * (c0 + 10 * L + 30) := by
  have hfold := cost_foldl_le (Γ := [.prod γ (.list α)]) (.snd v0) .nil
    (.foldl (call f (.pair (.fst v2) v0)) v1 (.cons v0 v1)) (x, ()) (fun _ => True)
    (c0 + 5 * L + 12) trivial
    (fun acc y hy _ => by
      refine ⟨trivial, ?_⟩
      obtain ⟨hc, hl⟩ := hf y hy
      have hin := cost_foldl_le (Γ := [α, .list β, .prod γ (.list α)])
        (call f (.pair (.fst v2) v0)) v1 (.cons v0 v1) (y, acc, x, ()) (fun _ => True) 4 trivial
        (fun _ _ _ _ => ⟨trivial, by simp [Expr.cost, Var.index]⟩)
      refine le_trans hin ?_
      rw [cost_call, denote_call]
      simp only [Expr.cost, Var.index, Expr.denote, Var.get]
      have hl' : ((f.apply (x.1, y))).length * (4 + 1) ≤ L * 5 := by nlinarith
      omega)
  have hlen : (x.2.flatMap (fun a => f.apply (x.1, a))).length ≤ x.2.length * L := by
    rw [List.length_flatMap]
    calc (x.2.map fun a => (f.apply (x.1, a)).length).sum ≤ (x.2.map fun _ => L).sum :=
          List.sum_le_sum (fun a ha => (hf a ha).2)
      _ = x.2.length * L := by simp
  have hrev := rev_cost β ((x.2.flatMap (fun a => f.apply (x.1, a))).reverse)
  simp only [List.length_reverse] at hrev
  have hs : (Expr.snd (Γ := [.prod γ (.list α)]) v0).cost (x, ()) = 2 := rfl
  have hn : (Expr.nil (Γ := [.prod γ (.list α)]) (a := β)).cost (x, ()) = 1 := rfl
  calc (flatMapWith f).costAt x = (Expr.foldl (Γ := [.prod γ (.list α)]) (.snd v0) .nil
        (.foldl (call f (.pair (.fst v2) v0)) v1 (.cons v0 v1))).cost (x, ()) +
        (rev β).costAt ((x.2.flatMap (fun a => f.apply (x.1, a))).reverse) + 1 := by
        unfold flatMapWith; simp only [Fn.costAt]; rw [cost_call, flatMapWith_inner]; rfl
    _ ≤ (2 + 1 + x.2.length * (c0 + 5 * L + 12 + 1) + 1) + (5 * (x.2.length * L) + 3) + 1 := by
        rw [hs, hn] at hfold; simp only [Expr.denote, Var.get] at hfold; omega
    _ ≤ _ := by nlinarith

/-! ## Integer ranges -/

/-- `range n = [0, 1, …, n - 1]`, empty for `n ≤ 0`. -/
def range : Fn .int (.list .int) :=
  .snd (.iter v0 (.pair v0 .nil)
    (.pair (.arith .sub (.fst v0) (.int 1)) (.cons (.arith .sub (.fst v0) (.int 1)) (.snd v0))))

/-- The step of the range iteration. -/
def rangeStep (s : ℤ × List ℤ) : ℤ × List ℤ := (s.1 - 1, (s.1 - 1) :: s.2)

theorem rangeStep_iterate (j : ℕ) (k : ℤ) (acc : List ℤ) :
    rangeStep^[j] (k, acc) =
      (k - j, ((List.range j).map (fun i : ℕ => k - (j : ℤ) + (i : ℤ))) ++ acc) := by
  induction j generalizing k acc with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply, show rangeStep (k, acc) = (k - 1, (k - 1) :: acc) from rfl,
      ih, List.range_succ, List.map_append, List.append_assoc]
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, Prod.mk.injEq]
    constructor
    · push_cast; ring
    · congr 1
      · apply List.map_congr_left; intro i _; push_cast; ring
      · congr 1; push_cast; ring

@[simp] theorem range_apply (n : ℤ) :
    range.apply n = (List.range n.toNat).map (fun i : ℕ => (i : ℤ)) := by
  have he : (fun s : ℤ × List ℤ => (s.1 - 1, (s.1 - 1) :: s.2)) = rangeStep := rfl
  simp only [range, Fn.apply, Expr.denote, Var.get, IntOp.eval, he]
  rw [rangeStep_iterate]
  simp only [List.append_nil]
  rcases le_or_gt 0 n with hn | hn
  · have h : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg hn
    congr 1; funext i; rw [h]; ring
  · have h : n.toNat = 0 := Int.toNat_eq_zero.mpr hn.le
    simp [h]

theorem range_cost (n : ℤ) (hn : 0 ≤ n) :
    range.costAt n ≤ (n.toNat + 1) * (4 * bits n + 30) := by
  have h := cost_iter_le_prefix (Γ := [.int]) v0 (.pair v0 .nil)
    (.pair (.arith .sub (.fst v0) (.int 1)) (.cons (.arith .sub (.fst v0) (.int 1)) (.snd v0)))
    (n, ()) (2 * bits n + 20) (fun j hj => by
      have he : (fun s : ℤ × List ℤ => (s.1 - 1, (s.1 - 1) :: s.2)) = rangeStep := rfl
      simp only [Expr.denote, Var.get, IntOp.eval, he] at hj ⊢
      rw [rangeStep_iterate]
      simp only [Expr.cost, Var.index, Expr.denote, Var.get, IntOp.charge]
      have hj' : (j : ℤ) < n := by
        have := Int.toNat_of_nonneg hn; omega
      have hb : bits (n - j) ≤ bits n := Nat.size_le_size (by omega)
      have h1 : bits (1 : ℤ) = 1 := by decide
      omega)
  have h2 := Nat.add_le_add_right h 1
  calc range.costAt n = (Expr.iter (Γ := [.int]) v0 (.pair v0 .nil)
        (.pair (.arith .sub (.fst v0) (.int 1))
          (.cons (.arith .sub (.fst v0) (.int 1)) (.snd v0)))).cost (n, ()) + 1 := rfl
    _ ≤ _ := h2
    _ ≤ _ := by
        simp only [Expr.cost, Var.index, Expr.denote, Var.get]
        nlinarith

/-! ## Equality of integer lists -/

/-- `eqList (a, b)` decides `a = b`. -/
def eqList : Fn (.prod (.list .int) (.list .int)) .bool :=
  .letE (.foldl (.fst v0) (.pair (.bool true) (.snd v0))
      (.listCase (.snd v1) (.pair (.bool false) .nil)
        (.pair (.ite (.fst v3) (.cmp .eq v2 v0) (.bool false)) v1)))
    (.listCase (.snd v0) (.fst v0) (.bool false))

/-- The step of the equality fold. -/
def eqStep (s : Bool × List ℤ) (a : ℤ) : Bool × List ℤ :=
  match s.2 with
  | [] => (false, [])
  | b :: bs => (s.1 && decide (a = b), bs)

theorem eqStep_fold (a b : List ℤ) (flag : Bool) :
    a.foldl eqStep (flag, b) =
      if a.length ≤ b.length then (flag && decide (a = b.take a.length), b.drop a.length)
      else (false, []) := by
  induction a generalizing b flag with
  | nil => simp
  | cons x a ih =>
    cases b with
    | nil =>
      simp only [List.foldl_cons, eqStep, List.length_cons, List.length_nil]
      have hf : ∀ l : List ℤ, l.foldl eqStep (false, []) = (false, []) := by
        intro l; induction l with
        | nil => rfl
        | cons _ l ih2 => simpa [eqStep] using ih2
      rw [hf]; simp
    | cons y b =>
      simp only [List.foldl_cons, eqStep, List.length_cons, ih]
      by_cases hl : a.length ≤ b.length
      · simp only [hl, ↓reduceIte, Nat.add_le_add_iff_right, List.take_succ_cons,
          List.drop_succ_cons, List.cons.injEq, Bool.and_assoc, Bool.decide_and]
      · simp [hl]

/-- The fold of `eqList`. -/
abbrev eqListFold : Expr [.prod (.list .int) (.list .int)] (.prod .bool (.list .int)) :=
  .foldl (.fst v0) (.pair (.bool true) (.snd v0))
    (.listCase (.snd v1) (.pair (.bool false) .nil)
      (.pair (.ite (.fst v3) (.cmp .eq v2 v0) (.bool false)) v1))

theorem eqListFold_denote (x : List ℤ × List ℤ) :
    eqListFold.denote (x, ()) = x.1.foldl eqStep (true, x.2) := by
  simp only [Expr.denote, Var.get, CmpOp.eval]
  congr 1
  funext acc y
  rcases acc with ⟨f, l⟩
  cases l <;> cases f <;> rfl

@[simp] theorem eqList_apply (x : List ℤ × List ℤ) : eqList.apply x = decide (x.1 = x.2) := by
  show (Expr.listCase (Γ := [.prod .bool (.list .int), .prod (.list .int) (.list .int)])
    (.snd v0) (.fst v0) (.bool false)).denote (eqListFold.denote (x, ()), x, ()) = _
  rw [eqListFold_denote, eqStep_fold]
  by_cases hl : x.1.length ≤ x.2.length
  · simp only [hl, ↓reduceIte, Bool.true_and]
    rcases hd : x.2.drop x.1.length with _ | ⟨z, zs⟩
    · have h := List.take_append_drop x.1.length x.2
      rw [hd, List.append_nil] at h
      simp only [Expr.denote, Var.get, hd, h]
    · simp only [Expr.denote, Var.get, hd]
      symm
      simp only [decide_eq_false_iff_not]
      intro heq
      have h1 := congrArg List.length hd
      rw [List.length_drop, heq] at h1
      simp at h1
  · simp only [hl, ↓reduceIte, Expr.denote, Var.get]
    symm
    simp only [decide_eq_false_iff_not]
    intro heq
    rw [heq] at hl
    exact hl le_rfl

theorem eqStep_bits (a b : List ℤ) (flag : Bool) (B : ℕ) (hb : ∀ z ∈ b, bits z ≤ B) :
    ∀ z ∈ (a.foldl eqStep (flag, b)).2, bits z ≤ B := by
  rw [eqStep_fold]
  split_ifs
  · intro z hz; exact hb z (List.mem_of_mem_drop hz)
  · simp

theorem eqList_cost (x : List ℤ × List ℤ) (B : ℕ) (ha : ∀ z ∈ x.1, bits z ≤ B)
    (hb : ∀ z ∈ x.2, bits z ≤ B) :
    eqList.costAt x ≤ (x.1.length + 1) * (2 * B + 30) := by
  have h := cost_foldl_le (Γ := [.prod (.list .int) (.list .int)]) (.fst v0)
    (.pair (.bool true) (.snd v0))
    (.listCase (.snd v1) (.pair (.bool false) .nil)
      (.pair (.ite (.fst v3) (.cmp .eq v2 v0) (.bool false)) v1)) (x, ())
    (fun st => ∀ z ∈ st.2, bits z ≤ B) (2 * B + 20) (by simpa [Expr.denote, Var.get] using hb)
    (fun acc y hy hP => by
      simp only [Expr.denote, Var.get] at hy
      have hyB := ha y hy
      rcases acc with ⟨f, l⟩
      cases l with
      | nil => simp [Expr.cost, Var.index, Expr.denote, Var.get]
      | cons z zs =>
        have hz := hP z (by simp)
        refine ⟨fun w hw => hP w (by simp [Expr.denote, Var.get] at hw; simp [hw]), ?_⟩
        cases f <;>
          simp only [Expr.cost, Var.index, Expr.denote, Var.get, CmpOp.charge, ↓reduceIte,
            Bool.false_eq_true] <;> linarith)
  have hl : (Expr.listCase (Γ := [.prod .bool (.list .int), .prod (.list .int) (.list .int)])
      (.snd v0) (.fst v0) (.bool false)).cost (eqListFold.denote (x, ()), x, ()) ≤ 5 := by
    simp only [Expr.cost, Var.index, Expr.denote, Var.get]
    split <;> linarith
  have h' : eqListFold.cost (x, ()) ≤ 2 + 4 + x.1.length * (2 * B + 20 + 1) + 1 := h
  have hc : eqList.costAt x = eqListFold.cost (x, ()) +
      (Expr.listCase (Γ := [.prod .bool (.list .int), .prod (.list .int) (.list .int)])
        (.snd v0) (.fst v0) (.bool false)).cost (eqListFold.denote (x, ()), x, ()) + 1 := rfl
  rw [hc]
  nlinarith

end MWIS.FunNetwork

end
