module

public import MWIS.FunLPBasic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Syntactic cost bounds for `Fun` expressions with loops

`Ok L B e env` says that, along the evaluation of `e` in `env`, every fold runs
over a list of length at most `L`, every iteration count is at most `L`, and every
integer argument of an arithmetic operation, comparison, size computation or
iteration count has binary length at most `B`. Under `Ok`, the cost of `e` is at
most `bnd L B e`, a polynomial in `L` and `B` read off the syntax, and
`bnd L B e ≤ weight e * ((L + 1) * (2 * B + 2) ^ 2) ^ (depth e + 1)`, where
`weight e` and `depth e` are numerals computed from the syntax.

Prepared 2026-10-23.
-/

@[expose] public section

namespace MWIS.FunNetwork

open MWIS.Fun MWIS.FunLP

/-! ## Side conditions along folds and iterations -/

/-- `P` holds at every step of the fold of `F` from `b` over a list. -/
def FoldOK {α β : Type*} (F : β → α → β) (P : β → α → Prop) : β → List α → Prop
  | _, [] => True
  | b, y :: ys => P b y ∧ FoldOK F P (F b y) ys

/-- `P` holds at every state of `k` rounds of `F` from `b`. -/
def IterOK {β : Type*} (F : β → β) (P : β → Prop) : β → ℕ → Prop
  | _, 0 => True
  | b, k + 1 => P b ∧ IterOK F P (F b) k

theorem FoldOK.mono {α β : Type*} {F : β → α → β} {P Q : β → α → Prop}
    (hPQ : ∀ b y, P b y → Q b y) : ∀ {b : β} {l : List α}, FoldOK F P b l → FoldOK F Q b l
  | _, [], _ => trivial
  | _, _ :: _, h => ⟨hPQ _ _ h.1, FoldOK.mono hPQ h.2⟩

theorem IterOK.mono {β : Type*} {F : β → β} {P Q : β → Prop}
    (hPQ : ∀ b, P b → Q b) : ∀ {b : β} {k : ℕ}, IterOK F P b k → IterOK F Q b k
  | _, 0, _ => trivial
  | _, _ + 1, h => ⟨hPQ _ h.1, IterOK.mono hPQ h.2⟩

/-- A fold side condition from an invariant. -/
theorem FoldOK.of_inv {α β : Type*} (F : β → α → β) (P : β → α → Prop) (Inv : β → Prop) :
    ∀ (l : List α) (b : β), Inv b →
      (∀ c y, y ∈ l → Inv c → P c y ∧ Inv (F c y)) → FoldOK F P b l
  | [], _, _, _ => trivial
  | y :: l, b, hb, h =>
    ⟨(h b y (by simp) hb).1,
      FoldOK.of_inv F P Inv l (F b y) (h b y (by simp) hb).2
        (fun c z hz hc => h c z (by simp [hz]) hc)⟩

/-- A fold side condition from the actual prefixes. -/
theorem FoldOK.of_prefix {α β : Type*} (F : β → α → β) (P : β → α → Prop) :
    ∀ (l : List α) (b : β),
      (∀ (i : ℕ) (h : i < l.length), P ((l.take i).foldl F b) l[i]) → FoldOK F P b l
  | [], _, _ => trivial
  | y :: l, b, h =>
    ⟨by have := h 0 (by simp); rwa [List.take_zero, List.foldl_nil, List.getElem_cons_zero] at this,
      FoldOK.of_prefix F P l (F b y) (fun i hi => by
        have := h (i + 1) (by simp; omega)
        rwa [List.take_succ_cons, List.foldl_cons, List.getElem_cons_succ] at this)⟩

/-- An iteration side condition from an indexed invariant. -/
theorem IterOK.of_inv_aux {β : Type*} (F : β → β) (P : β → Prop) (Inv : ℕ → β → Prop) :
    ∀ (k j : ℕ) (b : β), Inv j b →
      (∀ i c, j ≤ i → i < j + k → Inv i c → P c ∧ Inv (i + 1) (F c)) → IterOK F P b k
  | 0, _, _, _, _ => trivial
  | k + 1, j, b, hb, h =>
    ⟨(h j b le_rfl (by omega) hb).1,
      IterOK.of_inv_aux F P Inv k (j + 1) (F b) (h j b le_rfl (by omega) hb).2
        (fun i c h1 h2 hc => h i c (by omega) (by omega) hc)⟩

theorem IterOK.of_inv {β : Type*} (F : β → β) (P : β → Prop) (Inv : ℕ → β → Prop)
    (k : ℕ) (b : β) (hb : Inv 0 b)
    (h : ∀ i c, i < k → Inv i c → P c ∧ Inv (i + 1) (F c)) : IterOK F P b k :=
  IterOK.of_inv_aux F P Inv k 0 b hb (fun i c _ h2 hc => h i c (by omega) hc)

theorem foldl_counter_le {α β : Type*} (F : β → α → β) (G : β → α → ℕ) (c : ℕ) :
    ∀ (l : List α) (a : β) (n : ℕ), FoldOK F (fun b y => G b y ≤ c) a l →
      (l.foldl (fun (s : β × ℕ) y => (F s.1 y, s.2 + G s.1 y + 1)) (a, n)).2 ≤
        n + l.length * (c + 1)
  | [], _, _, _ => by simp
  | y :: l, a, n, h => by
    have := foldl_counter_le F G c l (F a y) (n + G a y + 1) h.2
    have h1 := h.1
    simp only [List.foldl_cons, List.length_cons]
    calc _ ≤ _ := this
      _ ≤ _ := by rw [Nat.succ_mul]; omega

theorem iter_counter_le {β : Type*} (F : β → β) (G : β → ℕ) (e c : ℕ) :
    ∀ (k : ℕ) (a : β) (n : ℕ), IterOK F (fun b => G b ≤ c) a k →
      ((fun (s : β × ℕ) => (F s.1, s.2 + G s.1 + e + 1))^[k] (a, n)).2 ≤ n + k * (c + e + 1)
  | 0, _, _, _ => by simp
  | k + 1, a, n, h => by
    have := iter_counter_le F G e c k (F a) (n + G a + e + 1) h.2
    have h1 := h.1
    rw [Function.iterate_succ_apply]
    calc _ ≤ _ := this
      _ ≤ _ := by rw [Nat.succ_mul]; omega

/-! ## The side condition and the syntactic bound -/

/-- The side condition of the syntactic bound along an evaluation. Tree
operations are excluded. -/
def Ok (L B : ℕ) {Γ : List Ty} {τ : Ty} : Expr Γ τ → Env Γ → Prop
  | .var _, _ => True
  | .int _, _ => True
  | .bool _, _ => True
  | .unit, _ => True
  | .arith _ x y, env =>
      Ok L B x env ∧ Ok L B y env ∧ bits (x.denote env) ≤ B ∧ bits (y.denote env) ≤ B
  | .cmp _ x y, env =>
      Ok L B x env ∧ Ok L B y env ∧ bits (x.denote env) ≤ B ∧ bits (y.denote env) ≤ B
  | .ite c t e, env => Ok L B c env ∧ (c.denote env = true → Ok L B t env) ∧
      (c.denote env = false → Ok L B e env)
  | .pair x y, env => Ok L B x env ∧ Ok L B y env
  | .fst p, env => Ok L B p env
  | .snd p, env => Ok L B p env
  | .nil, _ => True
  | .cons x xs, env => Ok L B x env ∧ Ok L B xs env
  | .listCase xs onNil onCons, env =>
      Ok L B xs env ∧
        (match xs.denote env with
          | [] => Ok L B onNil env
          | y :: ys => Ok L B onCons (y, ys, env))
  | .foldl xs init step, env =>
      Ok L B xs env ∧ Ok L B init env ∧ (xs.denote env).length ≤ L ∧
        FoldOK (fun acc y => step.denote (y, acc, env)) (fun acc y => Ok L B step (y, acc, env))
          (init.denote env) (xs.denote env)
  | .iter count init step, env =>
      Ok L B count env ∧ Ok L B init env ∧ (count.denote env).toNat ≤ L ∧
        bits (count.denote env) ≤ B ∧
        IterOK (fun st => step.denote (st, env)) (fun st => Ok L B step (st, env))
          (init.denote env) (count.denote env).toNat
  | .letE x body, env => Ok L B x env ∧ Ok L B body (x.denote env, env)
  | .treeCase _ _ _ _ _ _ _, _ => False
  | .treeNil, _ => False
  | .treeBit _ _, _ => False
  | .treeCons _ _, _ => False
  | .treePair _ _, _ => False
  | .items _, _ => False
  | .ofItems _, _ => False
  | .wordValue _, _ => False
  | .word _ _, _ => False
  | .size x, env => Ok L B x env ∧ bits (x.denote env) ≤ B

/-- The syntactic cost bound. -/
def bnd (L B : ℕ) {Γ : List Ty} {τ : Ty} : Expr Γ τ → ℕ
  | .var v => v.index + 1
  | .int _ => 1
  | .bool _ => 1
  | .unit => 1
  | .arith _ x y => bnd L B x + bnd L B y + (2 * B + 1) ^ 2 + 1
  | .cmp _ x y => bnd L B x + bnd L B y + (2 * B + 1) + 1
  | .ite c t e => bnd L B c + bnd L B t + bnd L B e + 1
  | .pair x y => bnd L B x + bnd L B y + 1
  | .fst p => bnd L B p + 1
  | .snd p => bnd L B p + 1
  | .nil => 1
  | .cons x xs => bnd L B x + bnd L B xs + 1
  | .listCase xs onNil onCons => bnd L B xs + bnd L B onNil + bnd L B onCons + 1
  | .foldl xs init step => bnd L B xs + bnd L B init + L * (bnd L B step + 1) + 1
  | .iter count init step =>
      bnd L B count + bnd L B init + L * (bnd L B step + B + 1) + 1
  | .letE x body => bnd L B x + bnd L B body + 1
  | .treeCase _ _ _ _ _ _ _ => 0
  | .treeNil => 0
  | .treeBit _ _ => 0
  | .treeCons _ _ => 0
  | .treePair _ _ => 0
  | .items _ => 0
  | .ofItems _ => 0
  | .wordValue _ => 0
  | .word _ _ => 0
  | .size x => bnd L B x + B + 1

theorem charge_le (op : IntOp) (x y : ℤ) (B : ℕ) (hx : bits x ≤ B) (hy : bits y ≤ B) :
    op.charge x y ≤ (2 * B + 1) ^ 2 := by
  cases op <;> simp only [IntOp.charge]
  · nlinarith
  · nlinarith
  · have := Nat.mul_le_mul (Nat.add_le_add_right hx 1) (Nat.add_le_add_right hy 1)
    nlinarith
  · exact Nat.pow_le_pow_left (by omega) 2
  · exact Nat.pow_le_pow_left (by omega) 2

/-- **The syntactic bound.** -/
theorem cost_le_bnd (L B : ℕ) {Γ : List Ty} {τ : Ty} (e : Expr Γ τ) :
    ∀ env, Ok L B e env → e.cost env ≤ bnd L B e := by
  induction e with
  | var v => intro env _; simp [Expr.cost, bnd]
  | int => intro env _; simp [Expr.cost, bnd]
  | bool => intro env _; simp [Expr.cost, bnd]
  | unit => intro env _; simp [Expr.cost, bnd]
  | arith op x y ihx ihy =>
    intro env h
    obtain ⟨hx, hy, bx, bY⟩ := h
    have h1 := ihx env hx
    have h2 := ihy env hy
    have h3 := charge_le op _ _ B bx bY
    simp only [Expr.cost, bnd]
    omega
  | cmp op x y ihx ihy =>
    intro env h
    obtain ⟨hx, hy, bx, bY⟩ := h
    have h1 := ihx env hx
    have h2 := ihy env hy
    simp only [Expr.cost, bnd, CmpOp.charge]
    omega
  | ite c t e ihc iht ihe =>
    intro env h
    obtain ⟨hc, ht, he⟩ := h
    have h1 := ihc env hc
    simp only [Expr.cost, bnd]
    cases hcv : c.denote env
    · have := ihe env (he hcv); simp only [Bool.false_eq_true, ↓reduceIte]; omega
    · have := iht env (ht hcv); simp only [↓reduceIte]; omega
  | pair x y ihx ihy =>
    intro env h
    have h1 := ihx env h.1
    have h2 := ihy env h.2
    simp only [Expr.cost, bnd]; omega
  | fst p ih => intro env h; have := ih env h; simp only [Expr.cost, bnd]; omega
  | snd p ih => intro env h; have := ih env h; simp only [Expr.cost, bnd]; omega
  | nil => intro env _; simp [Expr.cost, bnd]
  | cons x xs ihx ihxs =>
    intro env h
    have h1 := ihx env h.1
    have h2 := ihxs env h.2
    simp only [Expr.cost, bnd]; omega
  | listCase xs n c ihxs ihn ihc =>
    intro env h
    obtain ⟨hxs, hb⟩ := h
    have h1 := ihxs env hxs
    simp only [Expr.cost, bnd]
    split at hb
    · rename_i heq
      rw [heq]
      have := ihn env hb; dsimp only; omega
    · rename_i y ys heq
      rw [heq]
      have := ihc _ hb; dsimp only; omega
  | foldl xs i s ihxs ihi ihs =>
    intro env h
    obtain ⟨hxs, hi, hlen, hf⟩ := h
    have h1 := ihxs env hxs
    have h2 := ihi env hi
    have h3 := foldl_counter_le (fun acc y => s.denote (y, acc, env))
      (fun acc y => s.cost (y, acc, env)) (bnd L B s) (xs.denote env) (i.denote env) 0
      (FoldOK.mono (fun b y hb => ihs _ hb) hf)
    have h4 : (xs.denote env).length * (bnd L B s + 1) ≤ L * (bnd L B s + 1) :=
      Nat.mul_le_mul_right _ hlen
    simp only [Expr.cost, bnd]
    omega
  | iter c i s ihc ihi ihs =>
    intro env h
    obtain ⟨hc, hi, hk, hbits, hf⟩ := h
    have h1 := ihc env hc
    have h2 := ihi env hi
    have h3 := iter_counter_le (fun st => s.denote (st, env)) (fun st => s.cost (st, env))
      (bits (c.denote env)) (bnd L B s) (c.denote env).toNat (i.denote env) 0
      (IterOK.mono (fun b hb => ihs _ hb) hf)
    have h4 : (c.denote env).toNat * (bnd L B s + bits (c.denote env) + 1) ≤
        L * (bnd L B s + B + 1) := Nat.mul_le_mul hk (by omega)
    simp only [Expr.cost, bnd]
    omega
  | letE x b ihx ihb =>
    intro env h
    have h1 := ihx env h.1
    have h2 := ihb _ h.2
    simp only [Expr.cost, bnd]; omega
  | treeCase => intro env h; exact h.elim
  | treeNil => intro env h; exact h.elim
  | treeBit => intro env h; exact h.elim
  | treeCons => intro env h; exact h.elim
  | treePair => intro env h; exact h.elim
  | items => intro env h; exact h.elim
  | ofItems => intro env h; exact h.elim
  | wordValue => intro env h; exact h.elim
  | word => intro env h; exact h.elim
  | size x ih =>
    intro env h
    have h1 := ih env h.1
    have h2 := h.2
    simp only [Expr.cost, bnd]; omega

/-! ## Weakening -/

theorem bnd_weakenTail (L B : ℕ) {Γ : List Ty} {Δ : List Ty} {τ : Ty} (e : Expr Δ τ) :
    bnd L B (Expr.weakenTail (Γ := Γ) e) = bnd L B e := by
  induction e with
  | var v => simp [Expr.weakenTail, bnd, Var.index_weakenTail]
  | arith op x y ihx ihy => simp only [Expr.weakenTail, bnd, ihx, ihy]
  | cmp op x y ihx ihy => simp only [Expr.weakenTail, bnd, ihx, ihy]
  | ite c t e ihc iht ihe => simp only [Expr.weakenTail, bnd, ihc, iht, ihe]
  | pair x y ihx ihy => simp only [Expr.weakenTail, bnd, ihx, ihy]
  | fst p ih => simp only [Expr.weakenTail, bnd, ih]
  | snd p ih => simp only [Expr.weakenTail, bnd, ih]
  | cons x xs ihx ihxs => simp only [Expr.weakenTail, bnd, ihx, ihxs]
  | listCase xs n c ihxs ihn ihc => simp only [Expr.weakenTail, bnd, ihxs, ihn, ihc]
  | foldl xs i s ihxs ihi ihs => simp only [Expr.weakenTail, bnd, ihxs, ihi, ihs]
  | iter c i s ihc ihi ihs => simp only [Expr.weakenTail, bnd, ihc, ihi, ihs]
  | letE x b ihx ihb => simp only [Expr.weakenTail, bnd, ihx, ihb]
  | size x ih => simp only [Expr.weakenTail, bnd, ih]
  | _ => rfl

theorem ok_weakenTail (L B : ℕ) {Γ : List Ty} {Δ : List Ty} {τ : Ty} (e : Expr Δ τ) :
    ∀ (d : Env Δ) (g : Env Γ),
      Ok L B (Expr.weakenTail (Γ := Γ) e) (Env.append d g) ↔ Ok L B e d := by
  induction e with
  | var v => intro d g; simp [Expr.weakenTail, Ok]
  | int => intro d g; simp [Expr.weakenTail, Ok]
  | bool => intro d g; simp [Expr.weakenTail, Ok]
  | unit => intro d g; simp [Expr.weakenTail, Ok]
  | arith op x y ihx ihy =>
    intro d g; simp only [Expr.weakenTail, Ok, Expr.denote_weakenTail, ihx, ihy]
  | cmp op x y ihx ihy =>
    intro d g; simp only [Expr.weakenTail, Ok, Expr.denote_weakenTail, ihx, ihy]
  | ite c t e ihc iht ihe =>
    intro d g; simp only [Expr.weakenTail, Ok, Expr.denote_weakenTail, ihc, iht, ihe]
  | pair x y ihx ihy => intro d g; simp only [Expr.weakenTail, Ok, ihx, ihy]
  | fst p ih => intro d g; simp only [Expr.weakenTail, Ok, ih]
  | snd p ih => intro d g; simp only [Expr.weakenTail, Ok, ih]
  | nil => intro d g; simp [Expr.weakenTail, Ok]
  | cons x xs ihx ihxs => intro d g; simp only [Expr.weakenTail, Ok, ihx, ihxs]
  | listCase xs n c ihxs ihn ihc =>
    intro d g
    simp only [Expr.weakenTail, Ok, Expr.denote_weakenTail, ihxs, ihn]
    split
    · rfl
    · exact and_congr_right' (ihc (_, _, d) g)
  | @foldl Δ' a b xs i s ihxs ihi ihs =>
    intro d g
    simp only [Expr.weakenTail, Ok, Expr.denote_weakenTail, ihxs, ihi]
    have hF : (fun (acc : b.denote) (y : a.denote) =>
        (Expr.weakenTail (Γ := Γ) s).denote (y, acc, Env.append d g)) =
        (fun acc y => s.denote (y, acc, d)) := by
      funext acc y
      rw [show ((y, acc, Env.append d g) : Env (a :: b :: (Δ' ++ Γ))) =
        Env.append (Δ := a :: b :: Δ') (y, acc, d) g from rfl, Expr.denote_weakenTail]
    have hP : (fun (acc : b.denote) (y : a.denote) =>
        Ok L B (Expr.weakenTail (Γ := Γ) s) (y, acc, Env.append d g)) =
        (fun acc y => Ok L B s (y, acc, d)) := by
      funext acc y
      rw [show ((y, acc, Env.append d g) : Env (a :: b :: (Δ' ++ Γ))) =
        Env.append (Δ := a :: b :: Δ') (y, acc, d) g from rfl]
      exact propext (ihs _ g)
    rw [hF, hP]
  | @iter Δ' b c i s ihc ihi ihs =>
    intro d g
    simp only [Expr.weakenTail, Ok, Expr.denote_weakenTail, ihc, ihi]
    have hF : (fun (st : b.denote) => (Expr.weakenTail (Γ := Γ) s).denote (st, Env.append d g)) =
        (fun st => s.denote (st, d)) := by
      funext st
      rw [show ((st, Env.append d g) : Env (b :: (Δ' ++ Γ))) =
        Env.append (Δ := b :: Δ') (st, d) g from rfl, Expr.denote_weakenTail]
    have hP : (fun (st : b.denote) => Ok L B (Expr.weakenTail (Γ := Γ) s) (st, Env.append d g)) =
        (fun st => Ok L B s (st, d)) := by
      funext st
      rw [show ((st, Env.append d g) : Env (b :: (Δ' ++ Γ))) =
        Env.append (Δ := b :: Δ') (st, d) g from rfl]
      exact propext (ihs _ g)
    rw [hF, hP]
  | letE x b ihx ihb =>
    intro d g
    simp only [Expr.weakenTail, Ok, Expr.denote_weakenTail, ihx]
    exact and_congr_right' (ihb (_, d) g)
  | treeCase => intro d g; simp [Expr.weakenTail, Ok]
  | treeNil => intro d g; simp [Expr.weakenTail, Ok]
  | treeBit => intro d g; simp [Expr.weakenTail, Ok]
  | treeCons => intro d g; simp [Expr.weakenTail, Ok]
  | treePair => intro d g; simp [Expr.weakenTail, Ok]
  | items => intro d g; simp [Expr.weakenTail, Ok]
  | ofItems => intro d g; simp [Expr.weakenTail, Ok]
  | wordValue => intro d g; simp [Expr.weakenTail, Ok]
  | word => intro d g; simp [Expr.weakenTail, Ok]
  | size x ih => intro d g; simp only [Expr.weakenTail, Ok, Expr.denote_weakenTail, ih]

/-! ## Closed functions -/

/-- The side condition of a closed function at an argument. -/
def OkAt (L B : ℕ) {σ τ : Ty} (f : Fn σ τ) (x : σ.denote) : Prop := Ok L B f (x, ())

theorem costAt_le_bnd (L B : ℕ) {σ τ : Ty} (f : Fn σ τ) (x : σ.denote) (h : OkAt L B f x) :
    f.costAt x ≤ bnd L B f := cost_le_bnd L B f (x, ()) h

@[simp] theorem ok_call (L B : ℕ) {Γ : List Ty} {σ τ : Ty} (f : Fn σ τ) (x : Expr Γ σ)
    (env : Env Γ) : Ok L B (call f x) env ↔ Ok L B x env ∧ OkAt L B f (x.denote env) := by
  unfold call OkAt
  simp only [Ok]
  exact and_congr_right' (ok_weakenTail L B f ((x.denote env, ()) : Env [σ]) env)

@[simp] theorem bnd_call (L B : ℕ) {Γ : List Ty} {σ τ : Ty} (f : Fn σ τ) (x : Expr Γ σ) :
    bnd L B (call f x) = bnd L B x + bnd L B f + 1 := by
  unfold call
  simp only [bnd, bnd_weakenTail]

/-! ## A closed form -/

/-- The weight of an expression: its number of nodes, with variables counted by
their position and loops counted twice. -/
def weight {Γ : List Ty} {τ : Ty} : Expr Γ τ → ℕ
  | .var v => v.index + 1
  | .int _ => 1
  | .bool _ => 1
  | .unit => 1
  | .arith _ x y => weight x + weight y + 1
  | .cmp _ x y => weight x + weight y + 1
  | .ite c t e => weight c + weight t + weight e + 1
  | .pair x y => weight x + weight y + 1
  | .fst p => weight p + 1
  | .snd p => weight p + 1
  | .nil => 1
  | .cons x xs => weight x + weight xs + 1
  | .listCase xs onNil onCons => weight xs + weight onNil + weight onCons + 1
  | .foldl xs init step => weight xs + weight init + weight step + 2
  | .iter count init step => weight count + weight init + weight step + 2
  | .letE x body => weight x + weight body + 1
  | .treeCase _ _ _ _ _ _ _ => 0
  | .treeNil => 0
  | .treeBit _ _ => 0
  | .treeCons _ _ => 0
  | .treePair _ _ => 0
  | .items _ => 0
  | .ofItems _ => 0
  | .wordValue _ => 0
  | .word _ _ => 0
  | .size x => weight x + 1

/-- The loop nesting depth of an expression. -/
def depth {Γ : List Ty} {τ : Ty} : Expr Γ τ → ℕ
  | .var _ => 0
  | .int _ => 0
  | .bool _ => 0
  | .unit => 0
  | .arith _ x y => max (depth x) (depth y)
  | .cmp _ x y => max (depth x) (depth y)
  | .ite c t e => max (depth c) (max (depth t) (depth e))
  | .pair x y => max (depth x) (depth y)
  | .fst p => depth p
  | .snd p => depth p
  | .nil => 0
  | .cons x xs => max (depth x) (depth xs)
  | .listCase xs onNil onCons => max (depth xs) (max (depth onNil) (depth onCons))
  | .foldl xs init step => max (max (depth xs) (depth init)) (depth step + 1)
  | .iter count init step => max (max (depth count) (depth init)) (depth step + 1)
  | .letE x body => max (depth x) (depth body)
  | .treeCase _ _ _ _ _ _ _ => 0
  | .treeNil => 0
  | .treeBit _ _ => 0
  | .treeCons _ _ => 0
  | .treePair _ _ => 0
  | .items _ => 0
  | .ofItems _ => 0
  | .wordValue _ => 0
  | .word _ _ => 0
  | .size x => depth x

theorem weight_weakenTail {Γ : List Ty} {Δ : List Ty} {τ : Ty} (e : Expr Δ τ) :
    weight (Expr.weakenTail (Γ := Γ) e) = weight e := by
  induction e with
  | var v => simp [Expr.weakenTail, weight, Var.index_weakenTail]
  | arith op x y ihx ihy => simp only [Expr.weakenTail, weight, ihx, ihy]
  | cmp op x y ihx ihy => simp only [Expr.weakenTail, weight, ihx, ihy]
  | ite c t e ihc iht ihe => simp only [Expr.weakenTail, weight, ihc, iht, ihe]
  | pair x y ihx ihy => simp only [Expr.weakenTail, weight, ihx, ihy]
  | fst p ih => simp only [Expr.weakenTail, weight, ih]
  | snd p ih => simp only [Expr.weakenTail, weight, ih]
  | cons x xs ihx ihxs => simp only [Expr.weakenTail, weight, ihx, ihxs]
  | listCase xs n c ihxs ihn ihc => simp only [Expr.weakenTail, weight, ihxs, ihn, ihc]
  | foldl xs i s ihxs ihi ihs => simp only [Expr.weakenTail, weight, ihxs, ihi, ihs]
  | iter c i s ihc ihi ihs => simp only [Expr.weakenTail, weight, ihc, ihi, ihs]
  | letE x b ihx ihb => simp only [Expr.weakenTail, weight, ihx, ihb]
  | size x ih => simp only [Expr.weakenTail, weight, ih]
  | _ => rfl

theorem depth_weakenTail {Γ : List Ty} {Δ : List Ty} {τ : Ty} (e : Expr Δ τ) :
    depth (Expr.weakenTail (Γ := Γ) e) = depth e := by
  induction e with
  | arith op x y ihx ihy => simp only [Expr.weakenTail, depth, ihx, ihy]
  | cmp op x y ihx ihy => simp only [Expr.weakenTail, depth, ihx, ihy]
  | ite c t e ihc iht ihe => simp only [Expr.weakenTail, depth, ihc, iht, ihe]
  | pair x y ihx ihy => simp only [Expr.weakenTail, depth, ihx, ihy]
  | fst p ih => simp only [Expr.weakenTail, depth, ih]
  | snd p ih => simp only [Expr.weakenTail, depth, ih]
  | cons x xs ihx ihxs => simp only [Expr.weakenTail, depth, ihx, ihxs]
  | listCase xs n c ihxs ihn ihc => simp only [Expr.weakenTail, depth, ihxs, ihn, ihc]
  | foldl xs i s ihxs ihi ihs => simp only [Expr.weakenTail, depth, ihxs, ihi, ihs]
  | iter c i s ihc ihi ihs => simp only [Expr.weakenTail, depth, ihc, ihi, ihs]
  | letE x b ihx ihb => simp only [Expr.weakenTail, depth, ihx, ihb]
  | size x ih => simp only [Expr.weakenTail, depth, ih]
  | _ => rfl

@[simp] theorem weight_call {Γ : List Ty} {σ τ : Ty} (f : Fn σ τ) (x : Expr Γ σ) :
    weight (call f x) = weight x + weight f + 1 := by
  unfold call; simp only [weight, weight_weakenTail]

@[simp] theorem depth_call {Γ : List Ty} {σ τ : Ty} (f : Fn σ τ) (x : Expr Γ σ) :
    depth (call f x) = max (depth x) (depth f) := by
  unfold call; simp only [depth, depth_weakenTail]

theorem pow_mono_aux {K a b : ℕ} (hK : 1 ≤ K) (h : a ≤ b) : K ^ a ≤ K ^ b :=
  Nat.pow_le_pow_right hK h

/-- **Closed form of the syntactic bound.** -/
theorem bnd_le_weight (L B : ℕ) {Γ : List Ty} {τ : Ty} (e : Expr Γ τ) :
    bnd L B e ≤ weight e * ((L + 1) * (2 * B + 2) ^ 2) ^ (depth e + 1) := by
  set K := (L + 1) * (2 * B + 2) ^ 2 with hKdef
  have hK1 : 1 ≤ K := by
    have : 1 ≤ (2 * B + 2) ^ 2 := Nat.one_le_pow _ _ (by omega)
    nlinarith
  have hKL : L ≤ K := by
    have : 1 ≤ (2 * B + 2) ^ 2 := Nat.one_le_pow _ _ (by omega)
    nlinarith
  have hKB : (2 * B + 1) ^ 2 + 1 ≤ K := by
    have : (2 * B + 1) ^ 2 + 1 ≤ (2 * B + 2) ^ 2 := by
      have e : (2 * B + 2) ^ 2 = (2 * B + 1) ^ 2 + (4 * B + 3) := by ring
      omega
    nlinarith
  have hKB' : B + 1 ≤ K := by nlinarith
  have hp : ∀ a b, a ≤ b → K ^ a ≤ K ^ b := fun a b h => pow_mono_aux hK1 h
  have hK : ∀ a, K ≤ K ^ (a + 1) := fun a => by
    simpa using hp 1 (a + 1) (by omega)
  have lift : ∀ (w x d d' : ℕ), x ≤ w * K ^ (d + 1) → d ≤ d' → x ≤ w * K ^ (d' + 1) :=
    fun w x d d' hx hd => hx.trans (Nat.mul_le_mul_left _ (hp _ _ (by omega)))
  induction e with
  | var v => simp only [bnd, weight, depth]; nlinarith [hK 0]
  | int => simp only [bnd, weight, depth]; nlinarith [hK 0]
  | bool => simp only [bnd, weight, depth]; nlinarith [hK 0]
  | unit => simp only [bnd, weight, depth]; nlinarith [hK 0]
  | nil => simp only [bnd, weight, depth]; nlinarith [hK 0]
  | arith op x y ihx ihy =>
    simp only [bnd, weight, depth]
    have h1 := lift _ _ _ (max (depth x) (depth y)) ihx (le_max_left _ _)
    have h2 := lift _ _ _ (max (depth x) (depth y)) ihy (le_max_right _ _)
    have h3 := hK (max (depth x) (depth y))
    nlinarith
  | cmp op x y ihx ihy =>
    simp only [bnd, weight, depth]
    have h1 := lift _ _ _ (max (depth x) (depth y)) ihx (le_max_left _ _)
    have h2 := lift _ _ _ (max (depth x) (depth y)) ihy (le_max_right _ _)
    have h3 := hK (max (depth x) (depth y))
    have : 2 * B + 1 + 1 ≤ K := by nlinarith
    nlinarith
  | ite c t e ihc iht ihe =>
    simp only [bnd, weight, depth]
    set D := max (depth c) (max (depth t) (depth e))
    have h1 := lift _ _ _ D ihc (le_max_left _ _)
    have h2 := lift _ _ _ D iht (le_trans (le_max_left _ _) (le_max_right _ _))
    have h3 := lift _ _ _ D ihe (le_trans (le_max_right _ _) (le_max_right _ _))
    have h4 := hK D
    nlinarith
  | pair x y ihx ihy =>
    simp only [bnd, weight, depth]
    have h1 := lift _ _ _ (max (depth x) (depth y)) ihx (le_max_left _ _)
    have h2 := lift _ _ _ (max (depth x) (depth y)) ihy (le_max_right _ _)
    have h3 := hK (max (depth x) (depth y))
    nlinarith
  | fst p ih => simp only [bnd, weight, depth]; have := hK (depth p); nlinarith
  | snd p ih => simp only [bnd, weight, depth]; have := hK (depth p); nlinarith
  | cons x y ihx ihy =>
    simp only [bnd, weight, depth]
    have h1 := lift _ _ _ (max (depth x) (depth y)) ihx (le_max_left _ _)
    have h2 := lift _ _ _ (max (depth x) (depth y)) ihy (le_max_right _ _)
    have h3 := hK (max (depth x) (depth y))
    nlinarith
  | listCase c t e ihc iht ihe =>
    simp only [bnd, weight, depth]
    set D := max (depth c) (max (depth t) (depth e))
    have h1 := lift _ _ _ D ihc (le_max_left _ _)
    have h2 := lift _ _ _ D iht (le_trans (le_max_left _ _) (le_max_right _ _))
    have h3 := lift _ _ _ D ihe (le_trans (le_max_right _ _) (le_max_right _ _))
    have h4 := hK D
    nlinarith
  | foldl xs i s ihxs ihi ihs =>
    simp only [bnd, weight, depth]
    set D := max (max (depth xs) (depth i)) (depth s + 1)
    have h1 := lift _ _ _ D ihxs (le_trans (le_max_left _ _) (le_max_left _ _))
    have h2 := lift _ _ _ D ihi (le_trans (le_max_right _ _) (le_max_left _ _))
    have hd : depth s + 1 ≤ D := le_max_right _ _
    have h4 := hK D
    have h5 : L * (bnd L B s + 1) ≤ (weight s + 1) * K ^ (D + 1) := by
      have e1 : bnd L B s + 1 ≤ (weight s + 1) * K ^ (depth s + 1) := by
        have := Nat.one_le_pow (depth s + 1) K hK1
        nlinarith
      calc L * (bnd L B s + 1) ≤ K * ((weight s + 1) * K ^ (depth s + 1)) :=
            Nat.mul_le_mul hKL e1
        _ = (weight s + 1) * K ^ (depth s + 1 + 1) := by ring
        _ ≤ (weight s + 1) * K ^ (D + 1) :=
            Nat.mul_le_mul_left _ (hp _ _ (by omega))
    nlinarith
  | iter c i s ihc ihi ihs =>
    simp only [bnd, weight, depth]
    set D := max (max (depth c) (depth i)) (depth s + 1)
    have h1 := lift _ _ _ D ihc (le_trans (le_max_left _ _) (le_max_left _ _))
    have h2 := lift _ _ _ D ihi (le_trans (le_max_right _ _) (le_max_left _ _))
    have hd : depth s + 1 ≤ D := le_max_right _ _
    have h4 := hK D
    have h5 : L * (bnd L B s + B + 1) ≤ (weight s + 1) * K ^ (D + 1) := by
      have e1 : bnd L B s + B + 1 ≤ (weight s + 1) * K ^ (depth s + 1) := by
        have := hK (depth s)
        nlinarith
      calc L * (bnd L B s + B + 1) ≤ K * ((weight s + 1) * K ^ (depth s + 1)) :=
            Nat.mul_le_mul hKL e1
        _ = (weight s + 1) * K ^ (depth s + 1 + 1) := by ring
        _ ≤ (weight s + 1) * K ^ (D + 1) :=
            Nat.mul_le_mul_left _ (hp _ _ (by omega))
    nlinarith
  | letE x y ihx ihy =>
    simp only [bnd, weight, depth]
    have h1 := lift _ _ _ (max (depth x) (depth y)) ihx (le_max_left _ _)
    have h2 := lift _ _ _ (max (depth x) (depth y)) ihy (le_max_right _ _)
    have h3 := hK (max (depth x) (depth y))
    nlinarith
  | size x ih =>
    simp only [bnd, weight, depth]
    have := hK (depth x)
    nlinarith
  | treeCase => simp [bnd]
  | treeNil => simp [bnd]
  | treeBit => simp [bnd]
  | treeCons => simp [bnd]
  | treePair => simp [bnd]
  | items => simp [bnd]
  | ofItems => simp [bnd]
  | wordValue => simp [bnd]
  | word => simp [bnd]

/-- **Cost of a closed function in closed form.** -/
theorem costAt_le_weight (L B : ℕ) {σ τ : Ty} (f : Fn σ τ) (x : σ.denote) (h : OkAt L B f x) :
    f.costAt x ≤ weight f * ((L + 1) * (2 * B + 2) ^ 2) ^ (depth f + 1) :=
  (costAt_le_bnd L B f x h).trans (bnd_le_weight L B f)

end MWIS.FunNetwork

end
