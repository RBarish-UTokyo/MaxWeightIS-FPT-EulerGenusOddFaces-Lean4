module

public import MWIS.FunLPBasic
public import Mathlib.Data.Nat.Size
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Basic closed `Fun` functions on integers and integer lists

Each function comes with its meaning (`apply`) and an explicit cost bound in
terms of the binary lengths and list lengths of its arguments.
-/

@[expose] public section

namespace MWIS.FunLP

open MWIS.Fun

/-! ## Binary lengths -/

theorem bits_le_iff (x : ℤ) (w : ℕ) : bits x ≤ w ↔ x.natAbs < 2 ^ w := Nat.size_le

theorem natAbs_lt_of_bits (x : ℤ) : x.natAbs < 2 ^ bits x := Nat.lt_size_self _

theorem bits_mono {x y : ℤ} (h : x.natAbs ≤ y.natAbs) : bits x ≤ bits y :=
  Nat.size_le_size h

@[simp] theorem bits_neg (x : ℤ) : bits (-x) = bits x := by simp [bits]

@[simp] theorem bits_zero : bits 0 = 0 := by simp [bits]

theorem bits_add_le (x y : ℤ) : bits (x + y) ≤ max (bits x) (bits y) + 1 := by
  rw [bits_le_iff]
  have hx := natAbs_lt_of_bits x
  have hy := natAbs_lt_of_bits y
  have h1 : 2 ^ bits x ≤ 2 ^ max (bits x) (bits y) := Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
  have h2 : 2 ^ bits y ≤ 2 ^ max (bits x) (bits y) := Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
  have := Int.natAbs_add_le x y
  rw [pow_succ]
  omega

theorem bits_sub_le (x y : ℤ) : bits (x - y) ≤ max (bits x) (bits y) + 1 := by
  rw [sub_eq_add_neg]
  simpa using bits_add_le x (-y)

theorem bits_mul_le (x y : ℤ) : bits (x * y) ≤ bits x + bits y := by
  rw [bits_le_iff, Int.natAbs_mul, pow_add]
  exact Nat.mul_lt_mul'' (natAbs_lt_of_bits x) (natAbs_lt_of_bits y)

theorem bits_natCast (k : ℕ) : bits (k : ℤ) = k.size := by simp [bits]

theorem bits_le_of_natAbs_le {x : ℤ} {w : ℕ} (h : x.natAbs < 2 ^ w) : bits x ≤ w :=
  (bits_le_iff x w).mpr h

theorem bits_le_self_natAbs (x : ℤ) : bits x ≤ x.natAbs := by
  rw [bits_le_iff]; exact Nat.lt_two_pow_self

theorem bits_pow_two (k : ℕ) : bits ((2 : ℤ) ^ k) = k + 1 := by
  simp [bits, Int.natAbs_pow, Nat.size_pow]

theorem bits_pow_le (x : ℤ) (e : ℕ) : bits (x ^ e) ≤ e * bits x + 1 := by
  induction e with
  | zero => simp [bits]
  | succ e ih =>
    rw [pow_succ]
    have := bits_mul_le (x ^ e) x
    rw [Nat.succ_mul]
    omega

/-! ## Reversal -/

/-- Reverse a list. -/
def revFn (a : Ty) : Fn (.list a) (.list a) := .foldl v0 .nil (.cons v0 v1)

theorem foldl_cons_rev {α : Type*} (l acc : List α) :
    l.foldl (fun acc y => y :: acc) acc = l.reverse ++ acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons y l ih => simp [ih]

@[simp] theorem revFn_apply (a : Ty) (l : List a.denote) : (revFn a).apply l = l.reverse := by
  rw [Fn.apply]
  simp [revFn, Expr.denote, Var.get, foldl_cons_rev]

theorem revFn_cost (a : Ty) (l : List a.denote) : (revFn a).costAt l ≤ 6 * l.length + 3 := by
  unfold Fn.costAt revFn
  refine (cost_foldl_le (Γ := [.list a]) v0 .nil (.cons v0 v1) (l, ()) (fun _ => True) 4
    trivial (fun acc y _ _ => ⟨trivial, by simp [Expr.cost, Var.index]⟩)).trans ?_
  simp [Expr.cost, Var.index, Expr.denote, Var.get]
  omega

/-! ## Generic list combinators -/

theorem foldl_cons_map {α β : Type*} (f : α → β) (l : List α) (acc : List β) :
    l.foldl (fun acc y => f y :: acc) acc = (l.map f).reverse ++ acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons y l ih => simp [ih]

/-- Append two lists. -/
def appendFn (a : Ty) : Fn (.prod (.list a) (.list a)) (.list a) :=
  .foldl (call (revFn a) (.fst v0)) (.snd v0) (.cons v0 v1)

theorem appendFn_apply_mk (a : Ty) (l r : (Ty.list a).denote) :
    (appendFn a).apply (l, r) = l ++ r := by
  rw [Fn.apply]
  simp [appendFn, Expr.denote, Var.get, foldl_cons_rev]

@[simp] theorem appendFn_apply (a : Ty) (p : (Ty.prod (.list a) (.list a)).denote) :
    (appendFn a).apply p = p.1 ++ p.2 :=
  appendFn_apply_mk a p.1 p.2

theorem appendFn_cost (a : Ty) (l r : (Ty.list a).denote) :
    (appendFn a).costAt (l, r) ≤ 12 * l.length + 9 := by
  unfold Fn.costAt appendFn
  refine (cost_foldl_le (Γ := [.prod (.list a) (.list a)]) _ _ _ _ (fun _ => True) 4 trivial
    (fun _ _ _ _ => ⟨trivial, by simp [Expr.cost, Var.index]⟩)).trans ?_
  have := revFn_cost a l
  simp only [Expr.cost, cost_call, Var.index, Expr.denote, Var.get, denote_call, revFn_apply,
    List.length_reverse]
  omega

/-- Map a closed function with a fixed parameter over a list. -/
def mapFn {p a b : Ty} (f : Fn (.prod p a) b) : Fn (.prod p (.list a)) (.list b) :=
  call (revFn b) (.foldl (.snd v0) .nil (.cons (call f (.pair (.fst v2) v0)) v1))

theorem mapFn_apply_mk {p a b : Ty} (f : Fn (.prod p a) b) (q : p.denote) (l : (Ty.list a).denote) :
    (mapFn f).apply (q, l) = l.map (fun x => f.apply (q, x)) := by
  rw [Fn.apply]
  simp [mapFn, Expr.denote, Var.get, foldl_cons_map]

@[simp] theorem mapFn_apply {p a b : Ty} (f : Fn (.prod p a) b) (x : (Ty.prod p (.list a)).denote) :
    (mapFn f).apply x = x.2.map (fun y => f.apply (x.1, y)) :=
  mapFn_apply_mk f x.1 x.2

theorem mapFn_cost {p a b : Ty} (f : Fn (.prod p a) b) (q : p.denote) (l : (Ty.list a).denote)
    (c : ℕ) (hc : ∀ x ∈ l, f.costAt (q, x) ≤ c) :
    (mapFn f).costAt (q, l) ≤ (l.length + 1) * (c + 17) := by
  unfold Fn.costAt mapFn
  rw [cost_call]
  have h := cost_foldl_le (Γ := [.prod p (.list a)]) (.snd v0) .nil
    (.cons (call f (.pair (.fst v2) v0)) v1) ((q, l), ()) (fun _ => True) (c + 10) trivial
    (fun acc y hy _ => ⟨trivial, by
      simp only [Expr.cost, cost_call, Var.index, Expr.denote, Var.get]
      have := hc y hy
      omega⟩)
  have hr := revFn_cost b ((Expr.foldl (Γ := [.prod p (.list a)]) (.snd v0) .nil
    (.cons (call f (.pair (.fst v2) v0)) v1)).denote ((q, l), ()))
  simp only [Expr.cost, Var.index, Expr.denote, Var.get, denote_call, foldl_cons_map,
    List.length_append, List.length_reverse, List.length_map, List.length_nil] at h hr ⊢
  nlinarith

/-- Zip two lists with a closed function and a fixed parameter. The second
list is consumed while the first is traversed; the result has the length of
the shorter list. -/
def zipStepE {p a b c : Ty} (f : Fn (.prod p (.prod a b)) c) :
    Expr [a, .prod (.list b) (.list c), .prod p (.prod (.list a) (.list b))]
      (.prod (.list b) (.list c)) :=
  .listCase (.fst v1) v1 (.pair v1 (.cons (call f (.pair (.fst v4) (.pair v2 v0))) (.snd v3)))

def zipWithFn {p a b c : Ty} (f : Fn (.prod p (.prod a b)) c) :
    Fn (.prod p (.prod (.list a) (.list b))) (.list c) :=
  call (revFn c) (.snd (.foldl (.fst (.snd v0)) (.pair (.snd (.snd v0)) .nil) (zipStepE f)))

/-- The step of `zipWithFn`. -/
def zipStep {α β γ : Type*} (f : α → β → γ) (acc : List β × List γ) (x : α) :
    List β × List γ :=
  match acc.1 with
  | [] => acc
  | y :: ys => (ys, f x y :: acc.2)

theorem zipStep_nil {α β γ : Type*} (f : α → β → γ) (l : List α) (out : List γ) :
    l.foldl (zipStep f) ([], out) = ([], out) := by
  induction l with
  | nil => rfl
  | cons _ l ih => simpa [zipStep] using ih

theorem zip_fold {α β γ : Type*} (f : α → β → γ) (F : List β × List γ → α → List β × List γ)
    (hnil : ∀ o x, F ([], o) x = ([], o)) (hcons : ∀ y ys o x, F (y :: ys, o) x = (ys, f x y :: o))
    (l : List α) (r : List β) (out : List γ) :
    l.foldl F (r, out) = (r.drop l.length, (List.zipWith f l r).reverse ++ out) := by
  induction l generalizing r out with
  | nil => simp
  | cons x l ih =>
    cases r with
    | nil =>
      simp only [List.foldl_cons, hnil, List.zipWith_nil_right, List.reverse_nil, List.nil_append,
        List.drop_nil]
      clear ih
      induction l with
      | nil => rfl
      | cons _ l ih2 => simpa [hnil] using ih2
    | cons y ys => simp [hcons, ih, List.drop_succ_cons]

theorem zipStep_fold {α β γ : Type*} (f : α → β → γ) (l : List α) (r : List β) (out : List γ) :
    l.foldl (zipStep f) (r, out) = (r.drop l.length, (List.zipWith f l r).reverse ++ out) := by
  induction l generalizing r out with
  | nil => simp
  | cons x l ih =>
    cases r with
    | nil => simp [zipStep, zipStep_nil]
    | cons y ys => simp [zipStep, ih, List.drop_succ_cons]

theorem zipWithFn_apply_mk {p a b c : Ty} (f : Fn (.prod p (.prod a b)) c) (q : p.denote)
    (l : (Ty.list a).denote) (r : (Ty.list b).denote) :
    (zipWithFn f).apply (q, l, r) = List.zipWith (fun x y => f.apply (q, x, y)) l r := by
  have h := zipStep_fold (fun x y => f.apply (q, x, y)) l r []
  simp only [List.append_nil] at h
  rw [Fn.apply]
  simp only [zipWithFn, Expr.denote, Var.get, denote_call, revFn_apply]
  rw [zip_fold (fun x y => f.apply (q, x, y)) _ (fun o x => rfl)
    (fun y ys o x => by simp [zipStepE, Expr.denote, Var.get])]
  simp

@[simp] theorem zipWithFn_apply {p a b c : Ty} (f : Fn (.prod p (.prod a b)) c)
    (x : (Ty.prod p (.prod (.list a) (.list b))).denote) :
    (zipWithFn f).apply x = List.zipWith (fun y z => f.apply (x.1, y, z)) x.2.1 x.2.2 :=
  zipWithFn_apply_mk f x.1 x.2.1 x.2.2

theorem zipStep_reach {α β γ : Type*} (f : α → β → γ) (l : List α) (r : List β) (j : ℕ) :
    ((l.take j).foldl (zipStep f) (r, [])).1 = r.drop (l.take j).length := by
  rw [zipStep_fold]

theorem zipWithFn_cost {p a b c : Ty} (f : Fn (.prod p (.prod a b)) c) (q : p.denote)
    (l : (Ty.list a).denote) (r : (Ty.list b).denote) (C : ℕ)
    (hc : ∀ x ∈ l, ∀ y ∈ r, f.costAt (q, x, y) ≤ C) :
    (zipWithFn f).costAt (q, l, r) ≤ (l.length + 1) * (C + 60) := by
  unfold Fn.costAt zipWithFn
  rw [cost_call]
  have hfold := zip_fold (fun x y => f.apply (q, x, y))
    (fun acc z => (zipStepE f).denote (z, acc, (q, l, r), ())) (fun o x => rfl)
    (fun y ys o x => by simp [zipStepE, Expr.denote, Var.get])
  have hstep : ∀ (acc : List b.denote × List c.denote) (x : a.denote), x ∈ l →
      (∀ y ∈ acc.1, y ∈ r) → (zipStepE f).cost (x, acc, (q, l, r), ()) ≤ C + 40 := by
    rintro ⟨_ | ⟨y, ys⟩, o⟩ x hx hacc
    · simp [zipStepE, Expr.cost, Var.index, Expr.denote, Var.get]
    · have := hc x hx y (hacc y (by simp))
      simp only [zipStepE, Expr.cost, cost_call, Var.index, Expr.denote, Var.get]
      linarith
  have h := cost_foldl_le_prefix (Γ := [.prod p (.prod (.list a) (.list b))]) (.fst (.snd v0))
    (.pair (.snd (.snd v0)) .nil) (zipStepE f) ((q, l, r), ()) (C + 40) (by
      intro j hj
      apply hstep
      · simp only [Expr.denote, Var.get]; exact List.getElem_mem _
      · intro y hy
        simp only [Expr.denote, Var.get] at hy ⊢
        rw [hfold] at hy
        exact List.mem_of_mem_drop hy)
  have hr := revFn_cost c (((Expr.foldl (Γ := [.prod p (.prod (.list a) (.list b))])
    (.fst (.snd v0)) (.pair (.snd (.snd v0)) .nil) (zipStepE f)).denote ((q, l, r), ())).2)
  simp only [Expr.cost, Var.index, Expr.denote, Var.get] at h hr ⊢
  rw [hfold] at hr ⊢
  simp only [List.append_nil, List.length_reverse, List.length_zipWith] at hr ⊢
  have : min l.length r.length ≤ l.length := min_le_left _ _
  nlinarith

/-! ## Sums and dot products -/

/-- Sum of an integer list. -/
def sumFn : Fn (.list .int) .int := .foldl v0 (.int 0) (.arith .add v1 v0)

theorem foldl_add_eq_sum (l : List ℤ) (s : ℤ) : l.foldl (· + ·) s = s + l.sum := by
  induction l generalizing s with
  | nil => simp
  | cons x l ih => simp [ih, add_assoc]

@[simp] theorem sumFn_apply (l : List ℤ) : sumFn.apply l = l.sum := by
  rw [Fn.apply]
  have := foldl_add_eq_sum l 0
  simp only [zero_add] at this
  simpa [sumFn, Expr.denote, Var.get, IntOp.eval] using this

theorem sum_natAbs_le (l : List ℤ) (β : ℕ) (hl : ∀ y ∈ l, bits y ≤ β) :
    l.sum.natAbs ≤ l.length * 2 ^ β := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.sum_cons, List.length_cons]
    have h1 := ih (fun y hy => hl y (by simp [hy]))
    have h2 := (bits_le_iff x β).mp (hl x (by simp))
    have := Int.natAbs_add_le x l.sum
    rw [Nat.succ_mul]
    omega

/-- Partial sums of `L` integers of binary length at most `β` have length at most `β + L`. -/
theorem bits_sum_le (l : List ℤ) (β : ℕ) (hl : ∀ y ∈ l, bits y ≤ β) :
    bits l.sum ≤ β + l.length := by
  rw [bits_le_iff]
  calc l.sum.natAbs ≤ l.length * 2 ^ β := sum_natAbs_le l β hl
    _ < 2 ^ l.length * 2 ^ β :=
        Nat.mul_lt_mul_of_pos_right Nat.lt_two_pow_self (by positivity)
    _ = 2 ^ (β + l.length) := by rw [← pow_add, Nat.add_comm]

theorem sumFn_cost (l : List ℤ) (β : ℕ) (hl : ∀ y ∈ l, bits y ≤ β) :
    sumFn.costAt l ≤ (l.length + 1) * (2 * β + l.length + 10) := by
  unfold Fn.costAt sumFn
  have h := cost_foldl_le_prefix (Γ := [.list .int]) v0 (.int 0) (.arith .add v1 v0) (l, ())
    (2 * β + l.length + 6) (by
      intro j hj
      simp only [Expr.cost, Var.index, Expr.denote, Var.get, IntOp.charge]
      have hpre : ∀ y ∈ l.take j, bits y ≤ β := fun y hy => hl y (List.mem_of_mem_take hy)
      have hs := bits_sum_le (l.take j) β hpre
      have hf : (l.take j).foldl (fun acc y => IntOp.eval .add acc y) 0 = (l.take j).sum := by
        have := foldl_add_eq_sum (l.take j) 0
        simp only [zero_add] at this
        exact this
      rw [hf]
      have hx := hl l[j] (List.getElem_mem _)
      have : (l.take j).length ≤ l.length := by simp
      omega)
  simp only [Expr.cost, Var.index, Expr.denote, Var.get] at h ⊢
  nlinarith

/-- The dot product of two integer lists, truncated to the shorter length. -/
def dotL (a x : List ℤ) : ℤ := (List.zipWith (· * ·) a x).sum

/-- Multiply the two components of a pair. -/
def mulPairFn : Fn (.prod .unit (.prod .int .int)) .int := .arith .mul (.fst (.snd v0)) (.snd (.snd v0))

theorem mulPairFn_apply_mk (x y : Ty.int.denote) : mulPairFn.apply ((), x, y) = x * y := rfl

@[simp] theorem mulPairFn_apply (p : (Ty.prod .unit (.prod .int .int)).denote) :
    mulPairFn.apply p = p.2.1 * p.2.2 :=
  mulPairFn_apply_mk p.2.1 p.2.2

theorem mulPairFn_cost (x y : Ty.int.denote) : mulPairFn.costAt ((), x, y) = (bits x + 1) * (bits y + 1) + 7 := by
  simp [mulPairFn, Fn.costAt, Expr.cost, Var.index, IntOp.charge, Expr.denote, Var.get]
  ring

/-- Dot product: elementwise products, then their sum. -/
def dotFn : Fn (.prod (.list .int) (.list .int)) .int :=
  call sumFn (call (zipWithFn mulPairFn) (.pair .unit v0))

theorem dotFn_apply_mk (a x : (Ty.list .int).denote) : dotFn.apply (a, x) = dotL a x := by
  rw [Fn.apply]
  simp only [dotFn, Expr.denote, Var.get, denote_call, sumFn_apply, dotL]
  rw [zipWithFn_apply]
  rfl

@[simp] theorem dotFn_apply (p : (Ty.prod (.list .int) (.list .int)).denote) :
    dotFn.apply p = dotL p.1 p.2 :=
  dotFn_apply_mk p.1 p.2

theorem dotL_natAbs_le (a x : List ℤ) (β : ℕ) (ha : ∀ y ∈ a, bits y ≤ β)
    (hx : ∀ y ∈ x, bits y ≤ β) : ∀ z ∈ List.zipWith (· * ·) a x, bits z ≤ 2 * β := by
  intro z hz
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hz
  simp only [List.length_zipWith] at hi
  have hia : i < a.length := by omega
  have hix : i < x.length := by omega
  simp only [List.getElem_zipWith]
  have := bits_mul_le a[i] x[i]
  have h1 := ha _ (List.getElem_mem hia)
  have h2 := hx _ (List.getElem_mem hix)
  omega

/-- A bit-length bound for dot products. -/
theorem bits_dotL_le (a x : List ℤ) (β L : ℕ) (hL : a.length ≤ L)
    (ha : ∀ y ∈ a, bits y ≤ β) (hx : ∀ y ∈ x, bits y ≤ β) : bits (dotL a x) ≤ 2 * β + L := by
  have h := bits_sum_le _ _ (dotL_natAbs_le a x β ha hx)
  have : (List.zipWith (· * ·) a x).length ≤ L := by simp; omega
  unfold dotL
  omega

theorem dotFn_cost (a x : (Ty.list .int).denote) (β L : ℕ) (hL : a.length ≤ L)
    (ha : ∀ y ∈ a, bits y ≤ β) (hx : ∀ y ∈ x, bits y ≤ β) :
    dotFn.costAt (a, x) ≤ 4 * (L + 1) * (β + L + 10) ^ 2 := by
  unfold Fn.costAt dotFn
  rw [cost_call]
  have hz := zipWithFn_cost mulPairFn () a x ((β + 1) * (β + 1) + 7) (fun y hy z hz => by
    rw [mulPairFn_cost]
    have h1 := ha y hy
    have h2 := hx z hz
    have := Nat.mul_le_mul (Nat.succ_le_succ h1) (Nat.succ_le_succ h2)
    simp only [Nat.succ_eq_add_one] at this
    omega)
  have hs := sumFn_cost (List.zipWith (· * ·) a x) (2 * β) (dotL_natAbs_le a x β ha hx)
  have hlen : (List.zipWith (· * ·) a x).length ≤ L := by simp; omega
  simp only [Expr.cost, cost_call, Var.index, Expr.denote, Var.get, denote_call] at hz hs ⊢
  rw [zipWithFn_apply]
  set L' := (List.zipWith (· * ·) a x).length
  have hw : (List.zipWith (fun x y => mulPairFn.apply ((), x, y)) a x) = List.zipWith (· * ·) a x := rfl
  rw [hw]
  have h1 : (a.length + 1) * ((β + 1) * (β + 1) + 7 + 60) ≤ (L + 1) * (β + L + 10) ^ 2 := by
    apply Nat.mul_le_mul (by omega); nlinarith
  have h2 : (L' + 1) * (2 * (2 * β) + L' + 10) ≤ (L + 1) * (β + L + 10) ^ 2 := by
    apply Nat.mul_le_mul (by omega); nlinarith
  have h3 : 10 ≤ (L + 1) * (β + L + 10) ^ 2 := by nlinarith
  rw [Nat.mul_assoc]
  dsimp only [Ty.denote] at hz hs hlen h1 h2 h3 L' ⊢
  omega

/-! ## Zips, indexed maps and negation -/

/-- The pair of the two arguments. -/
def pairFn (a b : Ty) : Fn (.prod .unit (.prod a b)) (.prod a b) := .snd v0

theorem pairFn_apply_mk (a b : Ty) (x : a.denote) (y : b.denote) :
    (pairFn a b).apply ((), x, y) = (x, y) := rfl

@[simp] theorem pairFn_apply (a b : Ty) (p : (Ty.prod .unit (.prod a b)).denote) :
    (pairFn a b).apply p = p.2 :=
  pairFn_apply_mk a b p.2.1 p.2.2

theorem pairFn_cost (a b : Ty) (x : a.denote) (y : b.denote) :
    (pairFn a b).costAt ((), x, y) = 2 := rfl

/-- Zip two lists. -/
def zipFn (a b : Ty) : Fn (.prod (.list a) (.list b)) (.list (.prod a b)) :=
  call (zipWithFn (pairFn a b)) (.pair .unit v0)

theorem zipFn_apply_mk (a b : Ty) (l : (Ty.list a).denote) (r : (Ty.list b).denote) :
    (zipFn a b).apply (l, r) = l.zip r := by
  rw [Fn.apply]
  simp only [zipFn, Expr.denote, Var.get, denote_call]
  rw [zipWithFn_apply]
  rfl

@[simp] theorem zipFn_apply (a b : Ty) (p : (Ty.prod (.list a) (.list b)).denote) :
    (zipFn a b).apply p = p.1.zip p.2 :=
  zipFn_apply_mk a b p.1 p.2

theorem zipFn_cost (a b : Ty) (l : (Ty.list a).denote) (r : (Ty.list b).denote) :
    (zipFn a b).costAt (l, r) ≤ (l.length + 1) * 62 + 4 := by
  unfold Fn.costAt zipFn
  rw [cost_call]
  have := zipWithFn_cost (pairFn a b) () l r 2 (fun _ _ _ _ => by rw [pairFn_cost])
  simp only [Expr.cost, Var.index, Expr.denote, Var.get] at this ⊢
  omega

/-- The step of `mapIdxFn`: increment the index and cons the image. -/
def mapIdxStepE {p a b : Ty} (f : Fn (.prod p (.prod .int a)) b) :
    Expr [a, .prod .int (.list b), .prod p (.list a)] (.prod .int (.list b)) :=
  .pair (.arith .add (.fst v1) (.int 1)) (.cons (call f (.pair (.fst v2) (.pair (.fst v1) v0))) (.snd v1))

/-- Map with the position of each element. -/
def mapIdxFn {p a b : Ty} (f : Fn (.prod p (.prod .int a)) b) : Fn (.prod p (.list a)) (.list b) :=
  call (revFn b) (.snd (.foldl (.snd v0) (.pair (.int 0) .nil) (mapIdxStepE f)))

theorem mapIdx_fold {α β : Type*} (g : ℤ → α → β) (F : ℤ × List β → α → ℤ × List β)
    (hF : ∀ i o x, F (i, o) x = (i + 1, g i x :: o)) :
    ∀ (l : List α) (s : ℤ) (out : List β),
      l.foldl F (s, out) = (s + l.length, (l.mapIdx (fun i x => g (s + i) x)).reverse ++ out)
  | [], s, out => by simp
  | x :: l, s, out => by
    rw [List.foldl_cons, hF, mapIdx_fold g F hF l (s + 1) (g s x :: out)]
    simp only [List.length_cons, List.mapIdx_cons, List.reverse_cons, List.append_assoc,
      List.cons_append, List.nil_append, Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero]
    refine Prod.ext (by push_cast; ring) ?_
    simp only
    congr 2
    exact congrArg (fun h => List.mapIdx h l) (funext fun i => funext fun y => by
      congr 1; ring)

theorem mapIdxFn_apply_mk {p a b : Ty} (f : Fn (.prod p (.prod .int a)) b) (q : p.denote)
    (l : (Ty.list a).denote) :
    (mapIdxFn f).apply (q, l) = l.mapIdx (fun i x => f.apply (q, (i : ℤ), x)) := by
  rw [Fn.apply]
  simp only [mapIdxFn, Expr.denote, Var.get, denote_call, revFn_apply]
  rw [mapIdx_fold (fun i x => f.apply (q, i, x)) _
    (fun i o x => by simp [mapIdxStepE, Expr.denote, Var.get, IntOp.eval])]
  simp

@[simp] theorem mapIdxFn_apply {p a b : Ty} (f : Fn (.prod p (.prod .int a)) b) (x : (Ty.prod p (.list a)).denote) :
    (mapIdxFn f).apply x = x.2.mapIdx (fun i y => f.apply (x.1, (i : ℤ), y)) :=
  mapIdxFn_apply_mk f x.1 x.2

theorem mapIdxFn_cost {p a b : Ty} (f : Fn (.prod p (.prod .int a)) b) (q : p.denote)
    (l : (Ty.list a).denote) (C : ℕ) (hc : ∀ i < l.length, ∀ x ∈ l, f.costAt (q, (i : ℤ), x) ≤ C) :
    (mapIdxFn f).costAt (q, l) ≤ (l.length + 1) * (C + 3 * l.length + 40) := by
  unfold Fn.costAt mapIdxFn
  rw [cost_call]
  have hfold := mapIdx_fold (fun i x => f.apply (q, i, x))
    (fun acc z => (mapIdxStepE f).denote (z, acc, (q, l), ()))
    (fun i o x => by simp [mapIdxStepE, Expr.denote, Var.get, IntOp.eval])
  have h := cost_foldl_le_prefix (Γ := [.prod p (.list a)]) (.snd v0) (.pair (.int 0) .nil)
    (mapIdxStepE f) ((q, l), ()) (C + 3 * l.length + 30) (by
      intro j hj
      simp only [Expr.denote, Var.get] at hj ⊢
      rw [hfold]
      simp only [zero_add, List.length_take]
      have hjl : min j l.length = j := by omega
      rw [hjl]
      simp only [mapIdxStepE, Expr.cost, cost_call, Var.index, Expr.denote, Var.get, IntOp.charge]
      have hf := hc j hj l[j] (List.getElem_mem _)
      have hb : bits (j : ℤ) ≤ l.length := by
        have := bits_le_self_natAbs (j : ℤ); simp at this; omega
      have hb1 : bits (1 : ℤ) = 1 := by decide
      rw [hb1]
      omega)
  have hr := revFn_cost b (((Expr.foldl (Γ := [.prod p (.list a)]) (.snd v0) (.pair (.int 0) .nil)
    (mapIdxStepE f)).denote ((q, l), ())).2)
  simp only [Expr.cost, Var.index, Expr.denote, Var.get] at h hr ⊢
  rw [hfold] at hr ⊢
  simp only [List.append_nil, List.length_reverse, List.length_mapIdx] at hr ⊢
  nlinarith

/-- Negate every entry of an integer list. -/
def negEntryFn : Fn (.prod .unit .int) .int := .arith .sub (.int 0) (.snd v0)

def negFn : Fn (.list .int) (.list .int) := call (mapFn negEntryFn) (.pair .unit v0)

@[simp] theorem negFn_apply (l : List ℤ) : negFn.apply l = l.map (fun x => -x) := by
  rw [Fn.apply]
  simp only [negFn, Expr.denote, Var.get, denote_call]
  rw [mapFn_apply]
  simp [negEntryFn, Fn.apply, Expr.denote, Var.get, IntOp.eval]

theorem negFn_cost (l : List ℤ) (β : ℕ) (hl : ∀ y ∈ l, bits y ≤ β) :
    negFn.costAt l ≤ (l.length + 1) * (β + 30) + 4 := by
  unfold Fn.costAt negFn
  rw [cost_call]
  have := mapFn_cost negEntryFn () l (β + 8) (fun x hx => by
    have := hl x hx
    simp [negEntryFn, Fn.costAt, Expr.cost, Var.index, IntOp.charge, Expr.denote, Var.get]
    omega)
  simp only [Expr.cost, Var.index, Expr.denote, Var.get] at this ⊢
  nlinarith

end MWIS.FunLP

end
