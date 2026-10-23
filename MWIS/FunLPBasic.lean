module

public import MWIS.Fun.Core
public import Mathlib.Data.List.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# Closed `Fun` functions and their composition

A closed function is an expression over a one-variable context. Appending
variables at the end of a context does not move the existing variables, so a
closed function can be embedded into any context without changing its meaning
or its cost. `call f x` evaluates `x` once, binds it, and runs `f` on it.

The file also proves generic cost bounds for left folds and bounded iteration
with an invariant on the accumulated state.
-/

@[expose] public section

namespace MWIS.Fun

/-! ## Appending variables at the end of a context -/

/-- Append two environments. -/
def Env.append {Γ : List Ty} : {Δ : List Ty} → Env Δ → Env Γ → Env (Δ ++ Γ)
  | [], _, g => g
  | _ :: _, (x, d), g => (x, Env.append d g)

@[simp] theorem Env.append_cons {Γ Δ : List Ty} {τ : Ty} (x : τ.denote) (d : Env Δ) (g : Env Γ) :
    Env.append (Δ := τ :: Δ) (x, d) g = (x, Env.append d g) := rfl

/-- A variable of `Δ` is a variable of `Δ ++ Γ` at the same position. -/
def Var.weakenTail {Γ : List Ty} : {Δ : List Ty} → {τ : Ty} → Var Δ τ → Var (Δ ++ Γ) τ
  | _, _, .here => .here
  | _, _, .there v => .there (Var.weakenTail v)

theorem Var.get_weakenTail {Γ : List Ty} {Δ : List Ty} {τ : Ty} (v : Var Δ τ)
    (d : Env Δ) (g : Env Γ) : (Var.weakenTail (Γ := Γ) v).get (Env.append d g) = v.get d := by
  induction v with
  | here => rfl
  | there v ih => exact ih d.2

theorem Var.index_weakenTail {Γ : List Ty} {Δ : List Ty} {τ : Ty} (v : Var Δ τ) :
    (Var.weakenTail (Γ := Γ) v).index = v.index := by
  induction v with
  | here => rfl
  | there v ih => simp [Var.weakenTail, Var.index, ih]

/-- Embed an expression over `Δ` into the context `Δ ++ Γ`. -/
def Expr.weakenTail {Γ : List Ty} : {Δ : List Ty} → {τ : Ty} → Expr Δ τ → Expr (Δ ++ Γ) τ
  | _, _, .var v => .var (Var.weakenTail v)
  | _, _, .int z => .int z
  | _, _, .bool b => .bool b
  | _, _, .unit => .unit
  | _, _, .arith op x y => .arith op x.weakenTail y.weakenTail
  | _, _, .cmp op x y => .cmp op x.weakenTail y.weakenTail
  | _, _, .ite c t e => .ite c.weakenTail t.weakenTail e.weakenTail
  | _, _, .pair x y => .pair x.weakenTail y.weakenTail
  | _, _, .fst p => .fst p.weakenTail
  | _, _, .snd p => .snd p.weakenTail
  | _, _, .nil => .nil
  | _, _, .cons x xs => .cons x.weakenTail xs.weakenTail
  | _, _, .listCase xs n c => .listCase xs.weakenTail n.weakenTail c.weakenTail
  | _, _, .foldl xs i s => .foldl xs.weakenTail i.weakenTail s.weakenTail
  | _, _, .iter c i s => .iter c.weakenTail i.weakenTail s.weakenTail
  | _, _, .letE x b => .letE x.weakenTail b.weakenTail
  | _, _, .treeCase t a b c d e f =>
      .treeCase t.weakenTail a.weakenTail b.weakenTail c.weakenTail d.weakenTail
        e.weakenTail f.weakenTail
  | _, _, .treeNil => .treeNil
  | _, _, .treeBit b t => .treeBit b.weakenTail t.weakenTail
  | _, _, .treeCons x t => .treeCons x.weakenTail t.weakenTail
  | _, _, .treePair x y => .treePair x.weakenTail y.weakenTail
  | _, _, .items t => .items t.weakenTail
  | _, _, .ofItems ts => .ofItems ts.weakenTail
  | _, _, .wordValue t => .wordValue t.weakenTail
  | _, _, .word w k => .word w.weakenTail k.weakenTail
  | _, _, .size x => .size x.weakenTail

theorem Expr.denote_weakenTail {Γ : List Ty} {Δ : List Ty} {τ : Ty} (e : Expr Δ τ) :
    ∀ (d : Env Δ) (g : Env Γ),
      (Expr.weakenTail (Γ := Γ) e).denote (Env.append d g) = e.denote d := by
  induction e with
  | var v => intro d g; exact Var.get_weakenTail v d g
  | int => intro d g; rfl
  | bool => intro d g; rfl
  | unit => intro d g; rfl
  | arith op x y ihx ihy => intro d g; simp only [Expr.weakenTail, Expr.denote, ihx, ihy]
  | cmp op x y ihx ihy => intro d g; simp only [Expr.weakenTail, Expr.denote, ihx, ihy]
  | ite c t e ihc iht ihe => intro d g; simp only [Expr.weakenTail, Expr.denote, ihc, iht, ihe]
  | pair x y ihx ihy => intro d g; simp only [Expr.weakenTail, Expr.denote, ihx, ihy]
  | fst p ih => intro d g; simp only [Expr.weakenTail, Expr.denote, ih]
  | snd p ih => intro d g; simp only [Expr.weakenTail, Expr.denote, ih]
  | nil => intro d g; rfl
  | cons x xs ihx ihxs => intro d g; simp only [Expr.weakenTail, Expr.denote, ihx, ihxs]
  | listCase xs n c ihxs ihn ihc =>
    intro d g
    simp only [Expr.weakenTail, Expr.denote, ihxs, ihn]
    split
    · rfl
    · exact ihc (_, _, d) g
  | foldl xs i s ihxs ihi ihs =>
    intro d g
    simp only [Expr.weakenTail, Expr.denote, ihxs, ihi]
    congr 1
    funext acc y
    exact ihs (y, acc, d) g
  | iter c i s ihc ihi ihs =>
    intro d g
    simp only [Expr.weakenTail, Expr.denote, ihc, ihi]
    congr 1
    funext st
    exact ihs (st, d) g
  | letE x b ihx ihb =>
    intro d g
    simp only [Expr.weakenTail, Expr.denote, ihx]
    exact ihb (_, d) g
  | treeCase t a b c dd e f iht iha ihb ihc ihd ihe ihf =>
    intro d g
    simp only [Expr.weakenTail, Expr.denote, iht, iha]
    split
    · rfl
    · exact ihb (_, _, d) g
    · exact ihc (_, _, d) g
    · exact ihd (_, _, d) g
    · exact ihe (_, d) g
    · exact ihf (_, _, d) g
  | treeNil => intro d g; rfl
  | treeBit b t ihb iht => intro d g; simp only [Expr.weakenTail, Expr.denote, ihb, iht]
  | treeCons x t ihx iht => intro d g; simp only [Expr.weakenTail, Expr.denote, ihx, iht]
  | treePair x y ihx ihy => intro d g; simp only [Expr.weakenTail, Expr.denote, ihx, ihy]
  | items t ih => intro d g; simp only [Expr.weakenTail, Expr.denote, ih]
  | ofItems ts ih => intro d g; simp only [Expr.weakenTail, Expr.denote, ih]
  | wordValue t ih => intro d g; simp only [Expr.weakenTail, Expr.denote, ih]
  | word w k ihw ihk => intro d g; simp only [Expr.weakenTail, Expr.denote, ihw, ihk]
  | size x ih => intro d g; simp only [Expr.weakenTail, Expr.denote, ih]

theorem Expr.cost_weakenTail {Γ : List Ty} {Δ : List Ty} {τ : Ty} (e : Expr Δ τ) :
    ∀ (d : Env Δ) (g : Env Γ),
      (Expr.weakenTail (Γ := Γ) e).cost (Env.append d g) = e.cost d := by
  induction e with
  | var v => intro d g; simp [Expr.weakenTail, Expr.cost, Var.index_weakenTail]
  | int => intro d g; rfl
  | bool => intro d g; rfl
  | unit => intro d g; rfl
  | arith op x y ihx ihy =>
    intro d g; simp only [Expr.weakenTail, Expr.cost, Expr.denote_weakenTail, ihx, ihy]
  | cmp op x y ihx ihy =>
    intro d g; simp only [Expr.weakenTail, Expr.cost, Expr.denote_weakenTail, ihx, ihy]
  | ite c t e ihc iht ihe =>
    intro d g; simp only [Expr.weakenTail, Expr.cost, Expr.denote_weakenTail, ihc, iht, ihe]
  | pair x y ihx ihy => intro d g; simp only [Expr.weakenTail, Expr.cost, ihx, ihy]
  | fst p ih => intro d g; simp only [Expr.weakenTail, Expr.cost, ih]
  | snd p ih => intro d g; simp only [Expr.weakenTail, Expr.cost, ih]
  | nil => intro d g; rfl
  | cons x xs ihx ihxs => intro d g; simp only [Expr.weakenTail, Expr.cost, ihx, ihxs]
  | listCase xs n c ihxs ihn ihc =>
    intro d g
    simp only [Expr.weakenTail, Expr.cost, Expr.denote_weakenTail, ihxs, ihn]
    split
    · rfl
    · exact congrArg (· + 1) (congrArg (_ + ·) (ihc (_, _, d) g))
  | @foldl Δ' a b xs i s ihxs ihi ihs =>
    intro d g
    simp only [Expr.weakenTail, Expr.cost, Expr.denote_weakenTail, ihxs, ihi]
    have hf : (fun (s1 : b.denote × ℕ) (y : a.denote) =>
        ((Expr.weakenTail (Γ := Γ) s).denote (y, s1.1, Env.append d g),
          s1.2 + (Expr.weakenTail (Γ := Γ) s).cost (y, s1.1, Env.append d g) + 1)) =
        (fun (s1 : b.denote × ℕ) (y : a.denote) =>
          (s.denote (y, s1.1, d), s1.2 + s.cost (y, s1.1, d) + 1)) := by
      funext s1 y
      rw [show ((y, s1.1, Env.append d g) : Env (a :: b :: (Δ' ++ Γ))) =
        Env.append (Δ := a :: b :: Δ') (y, s1.1, d) g from rfl,
        Expr.denote_weakenTail, ihs]
    rw [hf]
  | @iter Δ' b c i s ihc ihi ihs =>
    intro d g
    simp only [Expr.weakenTail, Expr.cost, Expr.denote_weakenTail, ihc, ihi]
    have hf : (fun (s1 : b.denote × ℕ) =>
        ((Expr.weakenTail (Γ := Γ) s).denote (s1.1, Env.append d g),
          s1.2 + (Expr.weakenTail (Γ := Γ) s).cost (s1.1, Env.append d g) + bits (c.denote d) + 1)) =
        (fun (s1 : b.denote × ℕ) =>
          (s.denote (s1.1, d), s1.2 + s.cost (s1.1, d) + bits (c.denote d) + 1)) := by
      funext s1
      rw [show ((s1.1, Env.append d g) : Env (b :: (Δ' ++ Γ))) =
        Env.append (Δ := b :: Δ') (s1.1, d) g from rfl,
        Expr.denote_weakenTail, ihs]
    rw [hf]
  | letE x b ihx ihb =>
    intro d g
    simp only [Expr.weakenTail, Expr.cost, Expr.denote_weakenTail, ihx]
    exact congrArg (· + 1) (congrArg (_ + ·) (ihb (_, d) g))
  | treeCase t a b c dd e f iht iha ihb ihc ihd ihe ihf =>
    intro d g
    simp only [Expr.weakenTail, Expr.cost, Expr.denote_weakenTail, iht, iha]
    split
    · rfl
    · exact congrArg (· + 1) (congrArg (_ + ·) (ihb (_, _, d) g))
    · exact congrArg (· + 1) (congrArg (_ + ·) (ihc (_, _, d) g))
    · exact congrArg (· + 1) (congrArg (_ + ·) (ihd (_, _, d) g))
    · exact congrArg (· + 1) (congrArg (_ + ·) (ihe (_, d) g))
    · exact congrArg (· + 1) (congrArg (_ + ·) (ihf (_, _, d) g))
  | treeNil => intro d g; rfl
  | treeBit b t ihb iht => intro d g; simp only [Expr.weakenTail, Expr.cost, ihb, iht]
  | treeCons x t ihx iht => intro d g; simp only [Expr.weakenTail, Expr.cost, ihx, iht]
  | treePair x y ihx ihy => intro d g; simp only [Expr.weakenTail, Expr.cost, ihx, ihy]
  | items t ih => intro d g; simp only [Expr.weakenTail, Expr.cost, Expr.denote_weakenTail, ih]
  | ofItems ts ih => intro d g; simp only [Expr.weakenTail, Expr.cost, Expr.denote_weakenTail, ih]
  | wordValue t ih =>
    intro d g; simp only [Expr.weakenTail, Expr.cost, Expr.denote_weakenTail, ih]
  | word w k ihw ihk =>
    intro d g; simp only [Expr.weakenTail, Expr.cost, Expr.denote_weakenTail, ihw, ihk]
  | size x ih => intro d g; simp only [Expr.weakenTail, Expr.cost, Expr.denote_weakenTail, ih]

end MWIS.Fun

namespace MWIS.FunLP

open MWIS.Fun

/-- A closed function of one argument. -/
abbrev Fn (σ τ : Ty) := Expr [σ] τ

/-! ## Calling closed functions -/

/-- Evaluate the argument once and run a closed function on it. -/
def call {Γ : List Ty} {σ τ : Ty} (f : Fn σ τ) (x : Expr Γ σ) : Expr Γ τ :=
  .letE x (Expr.weakenTail (Γ := Γ) f)

/-- Apply a closed function to a value. -/
def Fn.apply {σ τ : Ty} (f : Fn σ τ) (x : σ.denote) : τ.denote := f.denote (x, ())

/-- The cost of a closed function on a value. -/
def Fn.costAt {σ τ : Ty} (f : Fn σ τ) (x : σ.denote) : ℕ := f.cost (x, ())

@[simp] theorem denote_call {Γ : List Ty} {σ τ : Ty} (f : Fn σ τ) (x : Expr Γ σ)
    (env : Env Γ) : (call f x).denote env = f.apply (x.denote env) := by
  unfold call Fn.apply
  simp only [Expr.denote]
  exact Expr.denote_weakenTail f (x.denote env, ()) env

theorem cost_call {Γ : List Ty} {σ τ : Ty} (f : Fn σ τ) (x : Expr Γ σ) (env : Env Γ) :
    (call f x).cost env = x.cost env + f.costAt (x.denote env) + 1 := by
  unfold call Fn.costAt
  simp only [Expr.cost]
  exact congrArg (· + 1) (congrArg (_ + ·)
    (Expr.cost_weakenTail f ((x.denote env, ()) : Env [σ]) env))

/-- Compose closed functions. -/
def Fn.comp {σ τ ρ : Ty} (g : Fn τ ρ) (f : Fn σ τ) : Fn σ ρ := call g f

@[simp] theorem Fn.apply_comp {σ τ ρ : Ty} (g : Fn τ ρ) (f : Fn σ τ) (x : σ.denote) :
    (g.comp f).apply x = g.apply (f.apply x) := by
  simp [Fn.comp, Fn.apply]

theorem Fn.costAt_comp {σ τ ρ : Ty} (g : Fn τ ρ) (f : Fn σ τ) (x : σ.denote) :
    (g.comp f).costAt x = f.costAt x + g.costAt (f.apply x) + 1 := by
  simp only [Fn.comp, Fn.costAt]
  rw [cost_call]
  rfl

/-! ## Variables -/

/-- The innermost variable. -/
abbrev v0 {Γ : List Ty} {a : Ty} : Expr (a :: Γ) a := .var .here
/-- The second variable. -/
abbrev v1 {Γ : List Ty} {a b : Ty} : Expr (a :: b :: Γ) b := .var (.there .here)
/-- The third variable. -/
abbrev v2 {Γ : List Ty} {a b c : Ty} : Expr (a :: b :: c :: Γ) c := .var (.there (.there .here))
/-- The fourth variable. -/
abbrev v3 {Γ : List Ty} {a b c d : Ty} : Expr (a :: b :: c :: d :: Γ) d :=
  .var (.there (.there (.there .here)))
/-- The fifth variable. -/
abbrev v4 {Γ : List Ty} {a b c d e : Ty} : Expr (a :: b :: c :: d :: e :: Γ) e :=
  .var (.there (.there (.there (.there .here))))

/-- The sixth variable. -/
abbrev v5 {Γ : List Ty} {a b c d e f : Ty} : Expr (a :: b :: c :: d :: e :: f :: Γ) f :=
  .var (.there (.there (.there (.there (.there .here)))))
/-- The seventh variable. -/
abbrev v6 {Γ : List Ty} {a b c d e f g : Ty} : Expr (a :: b :: c :: d :: e :: f :: g :: Γ) g :=
  .var (.there (.there (.there (.there (.there (.there .here))))))
/-- The eighth variable. -/
abbrev v7 {Γ : List Ty} {a b c d e f g h : Ty} :
    Expr (a :: b :: c :: d :: e :: f :: g :: h :: Γ) h :=
  .var (.there (.there (.there (.there (.there (.there (.there .here)))))))
/-- The ninth variable. -/
abbrev v8 {Γ : List Ty} {a b c d e f g h i : Ty} :
    Expr (a :: b :: c :: d :: e :: f :: g :: h :: i :: Γ) i :=
  .var (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))

/-! ## Generic accumulation bounds -/

/-- A fold that adds a cost to a counter, under an invariant on the state. -/
theorem foldl_counter {α β : Type*} (F : β → α → β) (G : β → α → ℕ) (P : β → Prop)
    (c0 : ℕ) : ∀ (l : List α) (a : β) (c : ℕ), P a →
      (∀ b y, y ∈ l → P b → P (F b y) ∧ G b y ≤ c0) →
      (l.foldl (fun (s : β × ℕ) y => (F s.1 y, s.2 + G s.1 y + 1)) (a, c)).1 = l.foldl F a ∧
      (l.foldl (fun (s : β × ℕ) y => (F s.1 y, s.2 + G s.1 y + 1)) (a, c)).2 ≤
        c + l.length * (c0 + 1) ∧ P (l.foldl F a)
  | [], a, c, ha, _ => by simp [ha]
  | y :: l, a, c, ha, hs => by
    obtain ⟨hp, hg⟩ := hs a y (by simp) ha
    obtain ⟨h1, h2, h3⟩ := foldl_counter F G P c0 l (F a y) (c + G a y + 1) hp
      (fun b z hz hb => hs b z (by simp [hz]) hb)
    refine ⟨by simpa using h1, ?_, by simpa using h3⟩
    simp only [List.foldl_cons, List.length_cons]
    refine h2.trans ?_
    rw [Nat.succ_mul]
    omega

/-- Bounded iteration with a counter, under an invariant on the state. -/
theorem iterate_counter {β : Type*} (F : β → β) (G : β → ℕ) (extra : ℕ) (P : β → Prop)
    (c0 : ℕ) (hs : ∀ b, P b → P (F b) ∧ G b ≤ c0) : ∀ (N : ℕ) (a : β) (c : ℕ), P a →
      (Nat.iterate (fun (s : β × ℕ) => (F s.1, s.2 + G s.1 + extra + 1)) N (a, c)).1 =
        Nat.iterate F N a ∧
      (Nat.iterate (fun (s : β × ℕ) => (F s.1, s.2 + G s.1 + extra + 1)) N (a, c)).2 ≤
        c + N * (c0 + extra + 1) ∧ P (Nat.iterate F N a)
  | 0, a, c, ha => by simp [ha]
  | N + 1, a, c, ha => by
    obtain ⟨hp, hg⟩ := hs a ha
    obtain ⟨h1, h2, h3⟩ := iterate_counter F G extra P c0 hs N (F a) (c + G a + extra + 1) hp
    refine ⟨by simpa [Function.iterate_succ_apply] using h1, ?_,
      by simpa [Function.iterate_succ_apply] using h3⟩
    simp only [Function.iterate_succ_apply]
    refine h2.trans ?_
    rw [Nat.succ_mul]
    omega

/-- Unfold the cost of a fold into the generic counter form. -/
theorem cost_foldl {Γ : List Ty} {a b : Ty} (xs : Expr Γ (.list a)) (init : Expr Γ b)
    (step : Expr (a :: b :: Γ) b) (env : Env Γ) :
    (Expr.foldl xs init step).cost env = xs.cost env + init.cost env +
      ((xs.denote env).foldl
        (fun (s : b.denote × ℕ) y => ((fun acc z => step.denote (z, acc, env)) s.1 y,
          s.2 + (fun acc z => step.cost (z, acc, env)) s.1 y + 1))
        (init.denote env, 0)).2 + 1 := rfl

/-- Unfold the cost of an iteration into the generic counter form. -/
theorem cost_iter {Γ : List Ty} {b : Ty} (count : Expr Γ .int) (init : Expr Γ b)
    (step : Expr (b :: Γ) b) (env : Env Γ) :
    (Expr.iter count init step).cost env = count.cost env + init.cost env +
      (Nat.iterate
        (fun (s : b.denote × ℕ) => ((fun st => step.denote (st, env)) s.1,
          s.2 + (fun st => step.cost (st, env)) s.1 + bits (count.denote env) + 1))
        (count.denote env).toNat (init.denote env, 0)).2 + 1 := rfl

/-- A fold costs at most its parts plus a uniform bound per element. -/
theorem cost_foldl_le {Γ : List Ty} {a b : Ty} (xs : Expr Γ (.list a)) (init : Expr Γ b)
    (step : Expr (a :: b :: Γ) b) (env : Env Γ) (P : b.denote → Prop) (c0 : ℕ)
    (hinit : P (init.denote env))
    (hs : ∀ acc y, y ∈ xs.denote env → P acc →
      P (step.denote (y, acc, env)) ∧ step.cost (y, acc, env) ≤ c0) :
    (Expr.foldl xs init step).cost env ≤
      xs.cost env + init.cost env + (xs.denote env).length * (c0 + 1) + 1 := by
  rw [cost_foldl]; beta_reduce
  have h := (foldl_counter (fun acc z => step.denote (z, acc, env))
    (fun acc z => step.cost (z, acc, env)) P c0 (xs.denote env) (init.denote env) 0 hinit
    (fun acc y hy hp => hs acc y hy hp)).2.1
  omega

/-- The invariant of a fold holds for its value. -/
theorem foldl_invariant {Γ : List Ty} {a b : Ty} (xs : Expr Γ (.list a)) (init : Expr Γ b)
    (step : Expr (a :: b :: Γ) b) (env : Env Γ) (P : b.denote → Prop)
    (hinit : P (init.denote env))
    (hs : ∀ acc y, y ∈ xs.denote env → P acc → P (step.denote (y, acc, env))) :
    P ((Expr.foldl xs init step).denote env) := by
  have h := (foldl_counter (fun acc z => step.denote (z, acc, env))
    (fun _ _ => 0) P 0 (xs.denote env) (init.denote env) 0 hinit
    (fun acc y hy hp => ⟨hs acc y hy hp, le_rfl⟩)).2.2
  simpa [Expr.denote] using h

/-- An iteration costs at most its parts plus a uniform bound per round. -/
theorem cost_iter_le {Γ : List Ty} {b : Ty} (count : Expr Γ .int) (init : Expr Γ b)
    (step : Expr (b :: Γ) b) (env : Env Γ) (P : b.denote → Prop) (c0 : ℕ)
    (hinit : P (init.denote env))
    (hs : ∀ st, P st → P (step.denote (st, env)) ∧ step.cost (st, env) ≤ c0) :
    (Expr.iter count init step).cost env ≤
      count.cost env + init.cost env +
        (count.denote env).toNat * (c0 + bits (count.denote env) + 1) + 1 := by
  rw [cost_iter]; beta_reduce
  have h := (iterate_counter (fun st => step.denote (st, env)) (fun st => step.cost (st, env))
    (bits (count.denote env)) P c0 hs (count.denote env).toNat (init.denote env) 0 hinit).2.1
  omega

/-- The invariant of an iteration holds for its value. -/
theorem iter_invariant {Γ : List Ty} {b : Ty} (count : Expr Γ .int) (init : Expr Γ b)
    (step : Expr (b :: Γ) b) (env : Env Γ) (P : b.denote → Prop)
    (hinit : P (init.denote env))
    (hs : ∀ st, P st → P (step.denote (st, env))) :
    P ((Expr.iter count init step).denote env) := by
  have h := (iterate_counter (fun st => step.denote (st, env)) (fun _ => 0) 0 P 0
    (fun st hp => ⟨hs st hp, le_rfl⟩) (count.denote env).toNat (init.denote env) 0 hinit).2.2
  simpa [Expr.denote] using h

/-! ## Cost bounds indexed by the processed prefix -/

/-- A fold counter is bounded by a per-element bound at every reachable state. -/
theorem foldl_counter_prefix {α β : Type*} (F : β → α → β) (G : β → α → ℕ) (c0 : ℕ) :
    ∀ (l : List α) (a : β) (c : ℕ),
      (∀ j (hj : j < l.length), G ((l.take j).foldl F a) l[j] ≤ c0) →
      (l.foldl (fun (s : β × ℕ) y => (F s.1 y, s.2 + G s.1 y + 1)) (a, c)).2 ≤
        c + l.length * (c0 + 1)
  | [], a, c, _ => by simp
  | y :: l, a, c, hs => by
    have h0 := hs 0 (by simp)
    simp only [List.take_zero, List.foldl_nil, List.getElem_cons_zero] at h0
    have h := foldl_counter_prefix F G c0 l (F a y) (c + G a y + 1)
      (fun j hj => by
        have := hs (j + 1) (by simp; omega)
        simpa [List.getElem_cons_succ] using this)
    simp only [List.foldl_cons, List.length_cons]
    refine h.trans ?_
    rw [Nat.succ_mul]
    omega

/-- The value component of a fold counter is the plain fold. -/
theorem foldl_counter_value {α β : Type*} (F : β → α → β) (G : β → α → ℕ) :
    ∀ (l : List α) (a : β) (c : ℕ),
      (l.foldl (fun (s : β × ℕ) y => (F s.1 y, s.2 + G s.1 y + 1)) (a, c)).1 = l.foldl F a
  | [], _, _ => rfl
  | y :: l, a, c => by simp only [List.foldl_cons]; exact foldl_counter_value F G l _ _

/-- An iteration counter is bounded by a per-round bound at every reachable state. -/
theorem iterate_counter_prefix {β : Type*} (F : β → β) (G : β → ℕ) (extra c0 : ℕ) :
    ∀ (N : ℕ) (a : β) (c : ℕ), (∀ j < N, G (F^[j] a) ≤ c0) →
      (Nat.iterate (fun (s : β × ℕ) => (F s.1, s.2 + G s.1 + extra + 1)) N (a, c)).2 ≤
        c + N * (c0 + extra + 1)
  | 0, _, _, _ => by simp
  | N + 1, a, c, hs => by
    have h0 := hs 0 (by omega)
    simp only [Function.iterate_zero, id_eq] at h0
    have h := iterate_counter_prefix F G extra c0 N (F a) (c + G a + extra + 1)
      (fun j hj => by simpa [Function.iterate_succ_apply] using hs (j + 1) (by omega))
    simp only [Function.iterate_succ_apply]
    refine h.trans ?_
    rw [Nat.succ_mul]
    omega

/-- A fold costs at most its parts plus a per-element bound at every reachable state. -/
theorem cost_foldl_le_prefix {Γ : List Ty} {a b : Ty} (xs : Expr Γ (.list a)) (init : Expr Γ b)
    (step : Expr (a :: b :: Γ) b) (env : Env Γ) (c0 : ℕ)
    (hs : ∀ j (hj : j < (xs.denote env).length),
      step.cost ((xs.denote env)[j], ((xs.denote env).take j).foldl
        (fun acc y => step.denote (y, acc, env)) (init.denote env), env) ≤ c0) :
    (Expr.foldl xs init step).cost env ≤
      xs.cost env + init.cost env + (xs.denote env).length * (c0 + 1) + 1 := by
  rw [cost_foldl]; beta_reduce
  have h := foldl_counter_prefix (fun acc z => step.denote (z, acc, env))
    (fun acc z => step.cost (z, acc, env)) c0 (xs.denote env) (init.denote env) 0 hs
  omega

/-- An iteration costs at most its parts plus a per-round bound at every reachable state. -/
theorem cost_iter_le_prefix {Γ : List Ty} {b : Ty} (count : Expr Γ .int) (init : Expr Γ b)
    (step : Expr (b :: Γ) b) (env : Env Γ) (c0 : ℕ)
    (hs : ∀ j < (count.denote env).toNat,
      step.cost ((fun st => step.denote (st, env))^[j] (init.denote env), env) ≤ c0) :
    (Expr.iter count init step).cost env ≤
      count.cost env + init.cost env +
        (count.denote env).toNat * (c0 + bits (count.denote env) + 1) + 1 := by
  rw [cost_iter]; beta_reduce
  have h := iterate_counter_prefix (fun st => step.denote (st, env)) (fun st => step.cost (st, env))
    (bits (count.denote env)) c0 (count.denote env).toNat (init.denote env) 0 hs
  omega

end MWIS.FunLP

end
