module

public import MWIS.FunLPBasic
public import Mathlib.Tactic

/-!
# Basic list programs for the coordinate tables

Reversal, mapping with a fixed parameter and integer ranges, with exact denotations and
cost bounds. These are local copies of the corresponding generic programs, so that the
coordinate programs depend only on the `Fun` core and `MWIS.FunLPBasic`.
-/

@[expose] public section

namespace MWIS.FunCoordinates

open MWIS.Fun MWIS.FunLP

/-- The sixth variable. -/
abbrev v5 {Γ : List Ty} {a b c d e g : Ty} : Expr (a :: b :: c :: d :: e :: g :: Γ) g :=
  .var (.there (.there (.there (.there (.there .here)))))

/-- The seventh variable. -/
abbrev v6 {Γ : List Ty} {a b c d e g h : Ty} : Expr (a :: b :: c :: d :: e :: g :: h :: Γ) h :=
  .var (.there (.there (.there (.there (.there (.there .here))))))

theorem cbits_natCast (k : ℕ) : bits (k : ℤ) = k.size := by simp [bits]

/-- Reverse a list. -/
def crevFn (a : Ty) : Fn (.list a) (.list a) := .foldl v0 .nil (.cons v0 v1)

theorem cfoldl_cons_rev {α : Type*} (l acc : List α) :
    l.foldl (fun acc y => y :: acc) acc = l.reverse ++ acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons y l ih => simp [ih]

@[simp] theorem crevFn_apply (a : Ty) (l : List a.denote) : (crevFn a).apply l = l.reverse := by
  rw [Fn.apply]
  simp [crevFn, Expr.denote, Var.get, cfoldl_cons_rev]

theorem crevFn_cost (a : Ty) (l : List a.denote) : (crevFn a).costAt l ≤ 6 * l.length + 3 := by
  unfold Fn.costAt crevFn
  refine (cost_foldl_le (Γ := [.list a]) v0 .nil (.cons v0 v1) (l, ()) (fun _ => True) 4
    trivial (fun acc y _ _ => ⟨trivial, by simp [Expr.cost, Var.index]⟩)).trans ?_
  simp [Expr.cost, Var.index, Expr.denote, Var.get]
  omega

theorem cfoldl_cons_map {α β : Type*} (f : α → β) (l : List α) (acc : List β) :
    l.foldl (fun acc y => f y :: acc) acc = (l.map f).reverse ++ acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons y l ih => simp [ih]

/-- Map a closed function with a fixed parameter over a list. -/
def cmapFn {p a b : Ty} (f : Fn (.prod p a) b) : Fn (.prod p (.list a)) (.list b) :=
  call (crevFn b) (.foldl (.snd v0) .nil (.cons (call f (.pair (.fst v2) v0)) v1))

@[simp] theorem cmapFn_apply {p a b : Ty} (f : Fn (.prod p a) b) (q : p.denote) (l : (Ty.list a).denote) :
    (cmapFn f).apply (q, l) = l.map (fun x => f.apply (q, x)) := by
  rw [Fn.apply]
  simp [cmapFn, Expr.denote, Var.get, cfoldl_cons_map]

theorem cmapFn_cost {p a b : Ty} (f : Fn (.prod p a) b) (q : p.denote) (l : (Ty.list a).denote)
    (c : ℕ) (hc : ∀ x ∈ l, f.costAt (q, x) ≤ c) :
    (cmapFn f).costAt (q, l) ≤ (l.length + 1) * (c + 17) := by
  unfold Fn.costAt cmapFn
  rw [cost_call]
  have h := cost_foldl_le (Γ := [.prod p (.list a)]) (.snd v0) .nil
    (.cons (call f (.pair (.fst v2) v0)) v1) ((q, l), ()) (fun _ => True) (c + 10) trivial
    (fun acc y hy _ => ⟨trivial, by
      simp only [Expr.cost, cost_call, Var.index, Expr.denote, Var.get]
      have := hc y hy
      omega⟩)
  have hr := crevFn_cost b ((Expr.foldl (Γ := [.prod p (.list a)]) (.snd v0) .nil
    (.cons (call f (.pair (.fst v2) v0)) v1)).denote ((q, l), ()))
  simp only [Expr.cost, Var.index, Expr.denote, Var.get, denote_call, cfoldl_cons_map,
    List.length_append, List.length_reverse, List.length_map, List.length_nil] at h hr ⊢
  nlinarith

/-- `range n = [0, 1, …, n - 1]`, empty for `n ≤ 0`. -/
def crange : Fn .int (.list .int) :=
  .snd (.iter v0 (.pair v0 .nil)
    (.pair (.arith .sub (.fst v0) (.int 1)) (.cons (.arith .sub (.fst v0) (.int 1)) (.snd v0))))

/-- The step of the range iteration. -/
def crangeStep (s : ℤ × List ℤ) : ℤ × List ℤ := (s.1 - 1, (s.1 - 1) :: s.2)

theorem crangeStep_iterate (j : ℕ) (k : ℤ) (acc : List ℤ) :
    crangeStep^[j] (k, acc) =
      (k - j, ((List.range j).map (fun i : ℕ => k - (j : ℤ) + (i : ℤ))) ++ acc) := by
  induction j generalizing k acc with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply, show crangeStep (k, acc) = (k - 1, (k - 1) :: acc) from rfl,
      ih, List.range_succ, List.map_append, List.append_assoc]
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, Prod.mk.injEq]
    constructor
    · push_cast; ring
    · congr 1
      · apply List.map_congr_left; intro i _; push_cast; ring
      · congr 1; push_cast; ring

@[simp] theorem crange_apply (n : ℤ) :
    crange.apply n = (List.range n.toNat).map (fun i : ℕ => (i : ℤ)) := by
  have he : (fun s : ℤ × List ℤ => (s.1 - 1, (s.1 - 1) :: s.2)) = crangeStep := rfl
  simp only [crange, Fn.apply, Expr.denote, Var.get, IntOp.eval, he]
  rw [crangeStep_iterate]
  simp only [List.append_nil]
  rcases le_or_gt 0 n with hn | hn
  · have h : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg hn
    congr 1; funext i; rw [h]; ring
  · have h : n.toNat = 0 := Int.toNat_eq_zero.mpr hn.le
    simp [h]

theorem crange_cost (n : ℤ) (hn : 0 ≤ n) :
    crange.costAt n ≤ (n.toNat + 1) * (4 * bits n + 30) := by
  have h := cost_iter_le_prefix (Γ := [.int]) v0 (.pair v0 .nil)
    (.pair (.arith .sub (.fst v0) (.int 1)) (.cons (.arith .sub (.fst v0) (.int 1)) (.snd v0)))
    (n, ()) (2 * bits n + 20) (fun j hj => by
      have he : (fun s : ℤ × List ℤ => (s.1 - 1, (s.1 - 1) :: s.2)) = crangeStep := rfl
      simp only [Expr.denote, Var.get, IntOp.eval, he] at hj ⊢
      rw [crangeStep_iterate]
      simp only [Expr.cost, Var.index, Expr.denote, Var.get, IntOp.charge]
      have hj' : (j : ℤ) < n := by
        have := Int.toNat_of_nonneg hn; omega
      have hb : bits (n - j) ≤ bits n := Nat.size_le_size (by omega)
      have h1 : bits (1 : ℤ) = 1 := by decide
      omega)
  have h2 := Nat.add_le_add_right h 1
  calc crange.costAt n = (Expr.iter (Γ := [.int]) v0 (.pair v0 .nil)
        (.pair (.arith .sub (.fst v0) (.int 1))
          (.cons (.arith .sub (.fst v0) (.int 1)) (.snd v0)))).cost (n, ()) + 1 := rfl
    _ ≤ _ := h2
    _ ≤ _ := by
        simp only [Expr.cost, Var.index, Expr.denote, Var.get]
        nlinarith

end MWIS.FunCoordinates

end
