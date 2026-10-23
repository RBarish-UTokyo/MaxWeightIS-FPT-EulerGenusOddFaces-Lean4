module

public import MWIS.FunCoordinatesBase

/-!
# Indexed list access and first-index search in `Fun`

Closed `Fun` functions reading the entry of a list at an integer position, replacing it,
and finding the first position whose element satisfies a closed predicate. Each has an
exact denotation and an explicit cost bound in terms of the list length, the binary length
of the position, and the cost of the predicate.
-/

@[expose] public section

namespace MWIS.FunCoordinates

open MWIS.Fun MWIS.FunLP

/-! ## Integer positions -/

/-- The entry at an integer position, or `d` outside the list. -/
def getI {α : Type*} (l : List α) (d : α) (i : ℤ) : α :=
  if 0 ≤ i then l.getD i.toNat d else d

/-- Replace the entry at an integer position; positions outside the list change nothing. -/
def setI {α : Type*} (l : List α) (i : ℤ) (x : α) : List α :=
  if 0 ≤ i then l.set i.toNat x else l

/-- The integer code of an optional position: `-1` for none. -/
def optInt : Option ℕ → ℤ
  | none => -1
  | some i => i

theorem getI_natCast {α : Type*} (l : List α) (d : α) (i : ℕ) : getI l d i = l.getD i d := by
  simp [getI]

theorem setI_natCast {α : Type*} (l : List α) (i : ℕ) (x : α) : setI l i x = l.set i x := by
  simp [setI]

/-! ## Reading an entry -/

/-- The fold that reads the entry at position `i`: the state is the current position and
the value found so far. -/
def getStep {α : Type*} (i : ℤ) (s : ℤ × α) (x : α) : ℤ × α :=
  (s.1 + 1, if s.1 = i then x else s.2)

theorem getStep_fold {α : Type*} (i : ℤ) (l : List α) (k : ℤ) (acc : α) :
    l.foldl (getStep i) (k, acc) =
      (k + l.length, if k ≤ i ∧ i < k + l.length then l.getD (i - k).toNat acc else acc) := by
  induction l generalizing k acc with
  | nil => simp
  | cons x l ih =>
    simp only [List.foldl_cons, getStep, List.length_cons, Nat.cast_add, Nat.cast_one]
    rw [ih]
    refine Prod.ext (by simp; ring) ?_
    simp only
    by_cases hk : k = i
    · subst hk
      simp only [ite_true]
      by_cases hl : k + 1 ≤ k ∧ k < k + 1 + l.length
      · omega
      · simp only [if_neg hl, le_refl, true_and]
        rw [if_pos (by omega)]
        simp
    · simp only [if_neg hk]
      by_cases h1 : k + 1 ≤ i ∧ i < k + 1 + ↑l.length
      · rw [if_pos h1, if_pos (by omega)]
        have : (i - k).toNat = (i - (k + 1)).toNat + 1 := by omega
        rw [this]; simp
      · rw [if_neg h1]
        by_cases h2 : k ≤ i ∧ i < k + (↑l.length + 1)
        · exfalso; omega
        · rw [if_neg h2]

/-- The step expression of the reading folds. -/
def getStepE (a : Ty) : Expr [a, .prod .int a, .prod (.list a) .int] (.prod .int a) :=
  .pair (.arith .add (.fst v1) (.int 1)) (.ite (.cmp .eq (.fst v1) (.snd v2)) v0 (.snd v1))

theorem getStepE_denote (a : Ty) (l : List a.denote) (i : ℤ) :
    (fun acc y => (getStepE a).denote (y, acc, ((l, i), ()))) = getStep i := by
  funext acc y
  by_cases h : acc.1 = i <;> simp [getStepE, getStep, Expr.denote, Var.get, IntOp.eval, CmpOp.eval, h]

theorem getStepE_cost (a : Ty) (l : List a.denote) (i : ℤ) (acc : ℤ × a.denote) (y : a.denote) :
    (getStepE a).cost (y, acc, ((l, i), ())) ≤ 2 * bits acc.1 + bits i + 24 := by
  simp only [getStepE, Expr.cost, Var.index, Expr.denote, Var.get, IntOp.charge, CmpOp.charge,
    CmpOp.eval]
  have h1 : bits (1 : ℤ) = 1 := by decide
  by_cases h : acc.1 = i <;> simp only [h, decide_true, decide_false, ite_true, ite_false,
    Bool.false_eq_true] <;> omega

/-- Read the integer entry at a position (default `0`). -/
def getIntFn : Fn (.prod (.list .int) .int) .int :=
  .snd (.foldl (.fst v0) (.pair (.int 0) (.int 0)) (getStepE .int))

/-- Read the Boolean entry at a position (default `false`). -/
def getBoolFn : Fn (.prod (.list .bool) .int) .bool :=
  .snd (.foldl (.fst v0) (.pair (.int 0) (.bool false)) (getStepE .bool))

/-- Read the list entry at a position (default empty). -/
def getListFn (a : Ty) : Fn (.prod (.list (.list a)) .int) (.list a) :=
  .snd (.foldl (.fst v0) (.pair (.int 0) .nil) (getStepE (.list a)))

theorem getI_eq_fold {α : Type*} (l : List α) (d : α) (i : ℤ) :
    getI l d i = (l.foldl (getStep i) (0, d)).2 := by
  rw [getStep_fold]
  simp only [zero_add, sub_zero, getI]
  by_cases h : 0 ≤ i
  · rw [if_pos h]
    by_cases h2 : i < l.length
    · rw [if_pos ⟨h, h2⟩]
    · rw [if_neg (by omega)]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
  · rw [if_neg h, if_neg (by omega)]

@[simp] theorem getIntFn_apply (l : List ℤ) (i : ℤ) : getIntFn.apply (l, i) = getI l 0 i := by
  rw [getI_eq_fold, ← getStepE_denote .int l i]
  rfl

@[simp] theorem getBoolFn_apply (l : List Bool) (i : ℤ) :
    getBoolFn.apply (l, i) = getI l false i := by
  rw [getI_eq_fold, ← getStepE_denote .bool l i]
  rfl

@[simp] theorem getListFn_apply (a : Ty) (l : List (List a.denote)) (i : ℤ) :
    (getListFn a).apply (l, i) = getI l [] i := by
  rw [getI_eq_fold, ← getStepE_denote (.list a) l i]
  rfl

theorem get_cost_aux {a : Ty} (d : Expr [.prod (.list a) .int] a) (hd : ∀ env, d.cost env ≤ 3)
    (l : List a.denote) (i : ℤ) (β : ℕ) (hl : l.length < 2 ^ β) :
    (Expr.snd (Expr.foldl (.fst v0) (.pair (.int 0) d) (getStepE a))).cost ((l, i), ()) ≤
      (l.length + 1) * (2 * β + bits i + 34) := by
  have h := cost_foldl_le_prefix (Γ := [.prod (.list a) .int]) (.fst v0) (.pair (.int 0) d)
    (getStepE a) ((l, i), ()) (2 * β + bits i + 24) (by
      intro j hj
      refine (getStepE_cost a l i _ _).trans ?_
      simp only [Expr.denote, Var.get] at hj ⊢
      rw [getStepE_denote a l i, getStep_fold]
      have hb : bits (j : ℤ) ≤ β := by
        rw [cbits_natCast]; exact Nat.size_le.mpr (by omega)
      have hlen : ((l.take j).length : ℤ) = j := by simp; omega
      simp only [zero_add, hlen]
      omega)
  have hd' := hd ((l, i), ())
  change _ ≤ 2 + (1 + d.cost ((l, i), ()) + 1) + l.length * (2 * β + bits i + 24 + 1) + 1 at h
  change _ + 1 ≤ _
  nlinarith

theorem getIntFn_cost (l : List ℤ) (i : ℤ) (β : ℕ) (hl : l.length < 2 ^ β) :
    getIntFn.costAt (l, i) ≤ (l.length + 1) * (2 * β + bits i + 34) :=
  get_cost_aux (.int 0) (fun _ => by simp [Expr.cost]) l i β hl

theorem getBoolFn_cost (l : List Bool) (i : ℤ) (β : ℕ) (hl : l.length < 2 ^ β) :
    getBoolFn.costAt (l, i) ≤ (l.length + 1) * (2 * β + bits i + 34) :=
  get_cost_aux (a := .bool) (.bool false) (fun _ => by simp [Expr.cost]) l i β hl

theorem getListFn_cost (a : Ty) (l : List (List a.denote)) (i : ℤ) (β : ℕ)
    (hl : l.length < 2 ^ β) :
    (getListFn a).costAt (l, i) ≤ (l.length + 1) * (2 * β + bits i + 34) :=
  get_cost_aux (a := .list a) .nil (fun _ => by simp [Expr.cost]) l i β hl

/-- Read the integer pair at a position (default `(0, 0)`). -/
def getPairFn : Fn (.prod (.list (.prod .int .int)) .int) (.prod .int .int) :=
  .snd (.foldl (.fst v0) (.pair (.int 0) (.pair (.int 0) (.int 0))) (getStepE (.prod .int .int)))

@[simp] theorem getPairFn_apply (l : List (ℤ × ℤ)) (i : ℤ) :
    getPairFn.apply (l, i) = getI l (0, 0) i := by
  rw [getI_eq_fold, ← getStepE_denote (.prod .int .int) l i]
  rfl

theorem getPairFn_cost (l : List (ℤ × ℤ)) (i : ℤ) (β : ℕ) (hl : l.length < 2 ^ β) :
    getPairFn.costAt (l, i) ≤ (l.length + 1) * (2 * β + bits i + 34) :=
  get_cost_aux (a := .prod .int .int) (.pair (.int 0) (.int 0)) (fun _ => by simp [Expr.cost]) l i β hl

/-! ## List lemmas -/

theorem findIdx?_ofFn {α : Type*} {k : ℕ} (g : Fin k → α) (P : α → Bool) :
    (List.ofFn g).findIdx? P = ((List.finRange k).find? (fun i => P (g i))).map Fin.val := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.ofFn_succ, List.finRange_succ, List.findIdx?_cons, List.find?_cons, ih,
      List.find?_map]
    by_cases h : P (g 0)
    · simp [h]
    · simp only [h, Bool.false_eq_true, ite_false]
      cases hf : (List.finRange k).find? (fun i => P (g i.succ)) <;>
        simp [Function.comp_def, hf, Option.map_map]

theorem findSome?_eq_bind_find {α β : Type*} (f : α → Option β) (l : List α) :
    l.findSome? f = (l.find? fun x => (f x).isSome).bind f := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.findSome?_cons, List.find?_cons]
    cases hx : f x <;> simp [hx, ih]

theorem getI_ofFn {α : Type*} {k : ℕ} (g : Fin k → α) (d : α) (i : Fin k) :
    getI (List.ofFn g) d (i : ℤ) = g i := by
  rw [getI_natCast]
  simp [List.getD_eq_getElem?_getD]

/-! ## Mapping with positions -/

/-- The step of the positional map: the state is the current position and the reversed
output so far. -/
def mapIdxStepE {p a b : Ty} (f : Fn (.prod p (.prod .int a)) b) :
    Expr [a, .prod .int (.list b), .prod p (.list a)] (.prod .int (.list b)) :=
  .pair (.arith .add (.fst v1) (.int 1)) (.cons (call f (.pair (.fst v2) (.pair (.fst v1) v0))) (.snd v1))

/-- Map a closed function receiving the parameter, the position and the element. -/
def mapIdxFn {p a b : Ty} (f : Fn (.prod p (.prod .int a)) b) : Fn (.prod p (.list a)) (.list b) :=
  call (crevFn b) (.snd (.foldl (.snd v0) (.pair (.int 0) .nil) (mapIdxStepE f)))

theorem mapIdxStep_fold {α β : Type*} (g : ℤ → α → β) (l : List α) (k : ℤ) (acc : List β) :
    l.foldl (fun (s : ℤ × List β) y => (s.1 + 1, g s.1 y :: s.2)) (k, acc) =
      (k + l.length, (l.mapIdx fun j y => g (k + j) y).reverse ++ acc) := by
  induction l generalizing k acc with
  | nil => simp
  | cons x l ih =>
    simp only [List.foldl_cons]
    rw [ih]
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one, List.mapIdx_cons, Nat.cast_zero,
      add_zero, List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]
    refine Prod.ext (by ring) ?_
    have hf : (fun (j : ℕ) y => g (k + 1 + (j : ℤ)) y) = (fun (i : ℕ) y => g (k + ((i : ℤ) + 1)) y) := by
      funext j y; congr 1; ring
    simp only [hf]

@[simp] theorem mapIdxFn_apply {p a b : Ty} (f : Fn (.prod p (.prod .int a)) b) (q : p.denote)
    (l : List a.denote) :
    (mapIdxFn f).apply (q, l) = l.mapIdx fun j x => f.apply (q, (j : ℤ), x) := by
  have h := mapIdxStep_fold (fun (k : ℤ) x => f.apply (q, k, x)) l 0 []
  simp only [zero_add, List.append_nil] at h
  have hs : (fun acc y => (mapIdxStepE f).denote (y, acc, ((q, l), ()))) =
      fun (s : ℤ × List b.denote) y => (s.1 + 1, f.apply (q, s.1, y) :: s.2) := by
    funext acc y; simp [mapIdxStepE, Expr.denote, Var.get, IntOp.eval]
  rw [Fn.apply]
  simp only [mapIdxFn, denote_call, crevFn_apply]
  change ((List.foldl (fun acc y => (mapIdxStepE f).denote (y, acc, ((q, l), ()))) (0, []) l).2).reverse = _
  rw [hs, h]
  simp

/-! ## First position satisfying a predicate -/

/-- The step of the search: the state is the current position and the first position found
so far, or `-1`. -/
def findStepE {p a : Ty} (pred : Fn (.prod p a) .bool) :
    Expr [a, .prod .int .int, .prod p (.list a)] (.prod .int .int) :=
  .pair (.arith .add (.fst v1) (.int 1))
    (.ite (.cmp .lt (.snd v1) (.int 0))
      (.ite (call pred (.pair (.fst v2) v0)) (.fst v1) (.snd v1)) (.snd v1))

/-- The first position whose element satisfies the predicate, or `-1`. -/
def findIdxFn {p a : Ty} (pred : Fn (.prod p a) .bool) : Fn (.prod p (.list a)) .int :=
  .snd (.foldl (.snd v0) (.pair (.int 0) (.int (-1))) (findStepE pred))

theorem findStep_fold {α : Type*} (P : α → Bool) (l : List α) (k res : ℤ) (hk : 0 ≤ k) :
    l.foldl (fun (s : ℤ × ℤ) y => (s.1 + 1, if s.2 < 0 then (if P y then s.1 else s.2) else s.2))
        (k, res) =
      (k + l.length, if res < 0 then
        (match l.findIdx? P with | none => res | some j => k + j) else res) := by
  induction l generalizing k res with
  | nil => simp
  | cons x l ih =>
    simp only [List.foldl_cons]
    rw [ih (k + 1) _ (by omega)]
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one, List.findIdx?_cons]
    refine Prod.ext (by ring) ?_
    simp only
    by_cases hr : res < 0
    · by_cases hx : P x
      · simp only [hr, hx, ite_true]
        rw [if_neg (by omega)]
        simp
      · simp only [hr, hx, ite_true, Bool.false_eq_true, ite_false]
        cases l.findIdx? P with
        | none => simp
        | some j => simp; ring
    · simp [hr]

@[simp] theorem findIdxFn_apply {p a : Ty} (pred : Fn (.prod p a) .bool) (q : p.denote)
    (l : List a.denote) :
    (findIdxFn pred).apply (q, l) = optInt (l.findIdx? fun x => pred.apply (q, x)) := by
  have h := findStep_fold (fun x => pred.apply (q, x)) l 0 (-1) le_rfl
  have hs : (fun acc y => (findStepE pred).denote (y, acc, ((q, l), ()))) =
      fun (s : ℤ × ℤ) y => (s.1 + 1, if s.2 < 0 then (if pred.apply (q, y) then s.1 else s.2) else s.2) := by
    funext acc y
    by_cases h1 : acc.2 < 0 <;>
      simp [findStepE, Expr.denote, Var.get, IntOp.eval, CmpOp.eval, h1]
  rw [Fn.apply]
  change (List.foldl (fun acc y => (findStepE pred).denote (y, acc, ((q, l), ()))) (0, -1) l).2 = _
  rw [hs, h]
  simp only [show (-1 : ℤ) < 0 by norm_num, ite_true, zero_add]
  cases l.findIdx? fun x => pred.apply (q, x) <;> rfl

/-! ## Apply lemmas with unstructured arguments

These forms match an argument of any shape, so `simp` can use them inside larger programs. -/

@[simp] theorem getIntFn_apply' (x : (Ty.prod (.list .int) .int).denote) :
    getIntFn.apply x = getI x.1 0 x.2 := getIntFn_apply x.1 x.2

@[simp] theorem getBoolFn_apply' (x : (Ty.prod (.list .bool) .int).denote) :
    getBoolFn.apply x = getI x.1 false x.2 := getBoolFn_apply x.1 x.2

@[simp] theorem getPairFn_apply' (x : (Ty.prod (.list (.prod .int .int)) .int).denote) :
    getPairFn.apply x = getI x.1 (0, 0) x.2 := getPairFn_apply x.1 x.2

@[simp] theorem getListFn_apply' (a : Ty) (x : (Ty.prod (.list (.list a)) .int).denote) :
    (getListFn a).apply x = getI x.1 [] x.2 := getListFn_apply a x.1 x.2

@[simp] theorem mapIdxFn_apply' {p a b : Ty} (f : Fn (.prod p (.prod .int a)) b)
    (x : (Ty.prod p (.list a)).denote) :
    (mapIdxFn f).apply x = x.2.mapIdx fun j y => f.apply (x.1, (j : ℤ), y) :=
  mapIdxFn_apply f x.1 x.2

@[simp] theorem findIdxFn_apply' {p a : Ty} (pred : Fn (.prod p a) .bool)
    (x : (Ty.prod p (.list a)).denote) :
    (findIdxFn pred).apply x = optInt (x.2.findIdx? fun y => pred.apply (x.1, y)) :=
  findIdxFn_apply pred x.1 x.2

@[simp] theorem cmapFn_apply' {p a b : Ty} (f : Fn (.prod p a) b) (x : (Ty.prod p (.list a)).denote) :
    (cmapFn f).apply x = x.2.map fun y => f.apply (x.1, y) := cmapFn_apply f x.1 x.2

/-! ## Costs of mapping and searching -/

theorem bits_lt_pow {k : ℕ} {β : ℕ} (h : k < 2 ^ β) : bits (k : ℤ) ≤ β := by
  rw [cbits_natCast]; exact Nat.size_le.mpr h

theorem mapIdxFn_cost {p a b : Ty} (f : Fn (.prod p (.prod .int a)) b) (q : p.denote)
    (l : List a.denote) (β c : ℕ) (hl : l.length < 2 ^ β)
    (hc : ∀ j (hj : j < l.length), f.costAt (q, (j : ℤ), l[j]) ≤ c) :
    (mapIdxFn f).costAt (q, l) ≤ (l.length + 1) * (c + β + 40) := by
  unfold Fn.costAt mapIdxFn
  rw [cost_call]
  have hs : (fun acc y => (mapIdxStepE f).denote (y, acc, ((q, l), ()))) =
      fun (s : ℤ × List b.denote) y => (s.1 + 1, f.apply (q, s.1, y) :: s.2) := by
    funext acc y; simp [mapIdxStepE, Expr.denote, Var.get, IntOp.eval]
  have h := cost_foldl_le_prefix (Γ := [.prod p (.list a)]) (.snd v0) (.pair (.int 0) .nil)
    (mapIdxStepE f) ((q, l), ()) (c + β + 26) (by
      intro j hj
      have hj' : j < l.length := hj
      change (mapIdxStepE f).cost (l[j], ((l.take j).foldl
        (fun acc y => (mapIdxStepE f).denote (y, acc, ((q, l), ()))) (0, [])), ((q, l), ())) ≤ _
      rw [hs, mapIdxStep_fold (fun (k : ℤ) x => f.apply (q, k, x))]
      have hlen : ((l.take j).length : ℤ) = j := by simp; omega
      simp only [zero_add, hlen, mapIdxStepE, Expr.cost, Var.index, cost_call, Expr.denote,
        Var.get, IntOp.charge]
      have := hc j hj'
      have hb := bits_lt_pow (show j < 2 ^ β by omega)
      have h1 : bits (1 : ℤ) = 1 := by decide
      omega)
  change _ ≤ 2 + 3 + l.length * (c + β + 26 + 1) + 1 at h
  have hlen : ((l.foldl (fun acc y => (mapIdxStepE f).denote (y, acc, ((q, l), ())))
      (0, [])).2).length = l.length := by
    rw [hs, mapIdxStep_fold (fun (k : ℤ) x => f.apply (q, k, x))]; simp
  have hr := crevFn_cost b ((l.foldl (fun acc y => (mapIdxStepE f).denote (y, acc, ((q, l), ())))
      (0, [])).2)
  rw [hlen] at hr
  change (Expr.foldl (Γ := [.prod p (.list a)]) (.snd v0) (.pair (.int 0) .nil)
      (mapIdxStepE f)).cost ((q, l), ()) + 1 + (crevFn b).costAt
        ((l.foldl (fun acc y => (mapIdxStepE f).denote (y, acc, ((q, l), ()))) (0, [])).2) + 1 ≤ _
  nlinarith

theorem findIdxFn_cost {p a : Ty} (pred : Fn (.prod p a) .bool) (q : p.denote)
    (l : List a.denote) (β c : ℕ) (hβ : 1 ≤ β) (hl : l.length < 2 ^ β)
    (hc : ∀ x ∈ l, pred.costAt (q, x) ≤ c) :
    (findIdxFn pred).costAt (q, l) ≤ (l.length + 1) * (c + 2 * β + 40) := by
  unfold Fn.costAt findIdxFn
  have hs : (fun acc y => (findStepE pred).denote (y, acc, ((q, l), ()))) =
      fun (s : ℤ × ℤ) y => (s.1 + 1, if s.2 < 0 then (if pred.apply (q, y) then s.1 else s.2) else s.2) := by
    funext acc y
    by_cases h1 : acc.2 < 0 <;>
      simp [findStepE, Expr.denote, Var.get, IntOp.eval, CmpOp.eval, h1]
  have h := cost_foldl_le_prefix (Γ := [.prod p (.list a)]) (.snd v0) (.pair (.int 0) (.int (-1)))
    (findStepE pred) ((q, l), ()) (c + 2 * β + 30) (by
      intro j hj
      have hj' : j < l.length := hj
      change (findStepE pred).cost (l[j], ((l.take j).foldl
        (fun acc y => (findStepE pred).denote (y, acc, ((q, l), ()))) (0, -1)), ((q, l), ())) ≤ _
      rw [hs, findStep_fold _ _ _ _ le_rfl]
      have hlen : ((l.take j).length : ℤ) = j := by simp; omega
      have hb := bits_lt_pow (show j < 2 ^ β by omega)
      have hres : bits (match (l.take j).findIdx? (fun x => pred.apply (q, x)) with
            | none => -1 | some i => (i : ℤ)) ≤ β := by
        cases hf : (l.take j).findIdx? (fun x => pred.apply (q, x)) with
        | none =>
          simp only
          have : bits (-1 : ℤ) = 1 := by decide
          omega
        | some i =>
          simp only
          have hi := (List.findIdx?_eq_some_iff_getElem.mp hf).1
          simp only [List.length_take] at hi
          exact bits_lt_pow (by omega)
      have hcj := hc _ (List.getElem_mem hj')
      have hm1 : bits (-1 : ℤ) = 1 := by decide
      simp only [zero_add, hlen, if_pos (show (-1 : ℤ) < 0 by norm_num)]
      simp only [findStepE, Expr.cost, Var.index, cost_call, Expr.denote, Var.get, IntOp.charge,
        CmpOp.charge, CmpOp.eval]
      have h1 : bits (1 : ℤ) = 1 := by decide
      have h0 : bits (0 : ℤ) = 0 := by decide
      split_ifs <;> omega)
  change _ ≤ 2 + 3 + l.length * (c + 2 * β + 30 + 1) + 1 at h
  change (Expr.foldl (Γ := [.prod p (.list a)]) (.snd v0) (.pair (.int 0) (.int (-1)))
      (findStepE pred)).cost ((q, l), ()) + 1 ≤ _
  nlinarith

end MWIS.FunCoordinates

end
