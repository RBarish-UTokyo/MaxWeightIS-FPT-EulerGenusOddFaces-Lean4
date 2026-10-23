module

public import MWIS.Fun.InterpCases

/-!
# The `Fun` interpreter: constructors with binders

`letE`, `listCase`, `foldl`, `iter` and `treeCase` extend the stored
environment by cons cells before evaluating their bodies. Folds and bounded
iterations use the fold procedure and the binary-recursion iteration with the
eval-step procedure.
-/

@[expose] public section

namespace MWIS.Fun.Interp

open MWIS.PointerMemory MWIS.RegisterMachine MWIS.Fun.Arith

variable {p : ℕ} {code : Code p} {d : Procedures p} {Γ : List Ty}

theorem envAt_cons {a : Ty} {h : Heap} {q : Ptr} {v : a.denote} {env : Env Γ} :
    EnvAt (a :: Γ) h q (v, env) ↔ TreeAt h q (.cons (rep a v) (envTree Γ env)) := Iff.rfl

theorem spec_letE (hm : d.Matches code) {a b : Ty} {x : Expr Γ a} {body : Expr (a :: Γ) b}
    (hx : EvalSpec code d x) (hb : EvalSpec code d body) : EvalSpec code d (.letE x body) := by
  intro env h hh ep envp he henv
  simp only [Expr.encode] at he
  refine Yields.le (B := 10 + (10 * (21 + 1) + (10 + (1 + 2 * 2 + K * x.cost env +
    (8 + (1 + 2 * 2 + K * body.cost (x.denote env, env) + 3)))))) ?_
    (by simp only [Expr.cost]; unfold K; omega)
  refine enter hm (k := 21) (by omega) he fun regs pp h0 h1 h3 tp => ?_
  refine Yields.loadPair (by rsimp [h3]) tp fun xp bp tx tb => ?_
  refine Yields.call (by rsimp [h1]) (hx env hh tx henv) fun m1 v1 r1 => ?_
  obtain ⟨e1, vm1, q1, rfl, t1⟩ := r1
  refine Yields.allocCons vm1 (by rsimp) (by rsimp [h1]) t1 (henv.mono e1) fun e2 v2 t2 => ?_
  refine Yields.call (by rsimp) (hb (x.denote env, env) v2 ((tb.mono e1).mono e2) t2)
    fun m3 v3 r3 => ?_
  obtain ⟨e3, vm3, q3, rfl, t3⟩ := r3
  exact Yields.ret ⟨e1.trans (e2.trans e3), vm3, q3, by rsimp, t3⟩ (by simp)

theorem spec_listCase (hm : d.Matches code) {a b : Ty} {xs : Expr Γ (.list a)}
    {onNil : Expr Γ b} {onCons : Expr (a :: .list a :: Γ) b}
    (hxs : EvalSpec code d xs) (hn : EvalSpec code d onNil) (hc : EvalSpec code d onCons) :
    EvalSpec code d (.listCase xs onNil onCons) := by
  intro env h hh ep envp he henv
  simp only [Expr.encode] at he
  have hcost : (Expr.listCase xs onNil onCons).cost env = xs.cost env +
      (match xs.denote env with
        | [] => onNil.cost env
        | y :: ys => onCons.cost (y, ys, env)) + 1 := rfl
  have hden : (Expr.listCase xs onNil onCons).denote env =
      (match xs.denote env with
        | [] => onNil.denote env
        | y :: ys => onCons.denote (y, ys, env)) := rfl
  cases hv : xs.denote env with
  | nil =>
    rw [hv] at hcost hden
    dsimp only at hcost hden
    refine Yields.le (B := 10 + (10 * (18 + 1) + (10 + (1 + 2 * 2 + K * xs.cost env +
      (10 + (10 + (1 + 2 * 2 + K * onNil.cost env + 3))))))) ?_
      (by rw [hcost]; unfold K; omega)
    rw [hden]
    refine enter hm (k := 18) (by omega) he fun regs pp h0 h1 h3 tp => ?_
    refine Yields.loadPair (by rsimp [h3]) tp fun xp rp tx tr => ?_
    refine Yields.call (by rsimp [h1]) (hxs env hh tx henv) fun m1 v1 r1 => ?_
    obtain ⟨e1, vm1, q1, rfl, t1⟩ := r1
    rw [hv] at t1
    refine Yields.loadPair (by rsimp) (tr.mono e1) fun np cp tn tc => ?_
    refine Yields.loadNil (ptr := q1) (by rsimp) (by simpa [rep, Tree.ofList] using t1) ?_
    refine Yields.call (by rsimp [h1]) (hn env vm1 tn (henv.mono e1)) fun m2 v2 r2 => ?_
    obtain ⟨e2, vm2, q2, rfl, t2⟩ := r2
    exact Yields.ret ⟨e1.trans e2, vm2, q2, by rsimp, t2⟩ (by simp)
  | cons y ys =>
    rw [hv] at hcost hden
    dsimp only at hcost hden
    refine Yields.le (B := 10 + (10 * (18 + 1) + (10 + (1 + 2 * 2 + K * xs.cost env +
      (10 + (10 + (8 + (8 + (1 + 2 * 2 + K * onCons.cost (y, ys, env) + 3))))))))) ?_
      (by rw [hcost]; unfold K; omega)
    rw [hden]
    refine enter hm (k := 18) (by omega) he fun regs pp h0 h1 h3 tp => ?_
    refine Yields.loadPair (by rsimp [h3]) tp fun xp rp tx tr => ?_
    refine Yields.call (by rsimp [h1]) (hxs env hh tx henv) fun m1 v1 r1 => ?_
    obtain ⟨e1, vm1, q1, rfl, t1⟩ := r1
    rw [hv] at t1
    refine Yields.loadPair (by rsimp) (tr.mono e1) fun np cp tn tc => ?_
    refine Yields.loadCons (ptr := q1) (by rsimp) (by simpa [rep, Tree.ofList] using t1)
      fun yp ysp ty tys => ?_
    refine Yields.allocCons vm1 (a := ysp) (by rsimp) (by rsimp [h1]) (x := rep (.list a) ys)
      (by simpa [rep] using tys) (henv.mono e1) fun e2 v2 t2 => ?_
    refine Yields.allocCons v2 (by rsimp) (by rsimp) (ty.mono e2) t2 fun e3 v3 t3 => ?_
    refine Yields.call (by rsimp) (hc (y, ys, env) v3 ((tc.mono e2).mono e3) t3)
      fun m4 v4 r4 => ?_
    obtain ⟨e4, vm4, q4, rfl, t4⟩ := r4
    exact Yields.ret ⟨e1.trans (e2.trans (e3.trans e4)), vm4, q4, by rsimp, t4⟩ (by simp)

/-! ## Folds -/

/-- The charge of a left fold. -/
def foldCost {σ α : Type*} (f : σ → α → σ) (g : σ → α → ℕ) : List α → σ → ℕ
  | [], _ => 0
  | y :: ys, s => g s y + foldCost f g ys (f s y)

theorem foldl_pair {σ α : Type*} (f : σ → α → σ) (g : σ → α → ℕ) :
    ∀ (xs : List α) (s : σ) (c : ℕ),
      xs.foldl (fun (q : σ × ℕ) y => (f q.1 y, q.2 + g q.1 y + 1)) (s, c) =
        (xs.foldl f s, c + foldCost f (fun s y => g s y + 1) xs s) := by
  intro xs
  induction xs with
  | nil => intro s c; simp [foldCost]
  | cons y ys ih => intro s c; simp only [List.foldl_cons, ih, foldCost]; ext <;> simp; ring

theorem fold_spec (hm : d.Matches code) {a b : Ty} {step : Expr (a :: b :: Γ) b}
    (hs : EvalSpec code d step) (env : Env Γ) :
    ∀ (xs : List a.denote) (acc : b.denote) {h : Heap}, Valid h → ∀ {lp ap sp envp : Ptr},
      TreeAt h lp (rep (.list a) xs) → TreeAt h ap (rep b acc) → TreeAt h sp step.encode →
      EnvAt Γ h envp env →
      Yields code h (initialRegisters [.pointer lp, .pointer ap, .pointer sp, .pointer envp])
        (code d.fold)
        (K * foldCost (fun s y => step.denote (y, s, env)) (fun s y => step.cost (y, s, env) + 1)
          xs acc + 13)
        (Returns h (rep b (xs.foldl (fun s y => step.denote (y, s, env)) acc))) := by
  intro xs
  induction xs with
  | nil =>
    intro acc h hh lp ap sp envp tl ta ts te
    rw [hm.fold]
    refine Yields.le (B := 10 + 3) ?_ (by simp)
    refine Yields.loadNil (ptr := lp) (by rsimp) (by simpa [rep, Tree.ofList] using tl) ?_
    exact Yields.ret ⟨Extends.refl h, hh, ap, by rsimp, ta⟩ (by simp)
  | cons y ys ih =>
    intro acc h hh lp ap sp envp tl ta ts te
    rw [hm.fold]
    refine Yields.le (B := 10 + (8 + (8 + (1 + 2 * 2 + K * step.cost (y, acc, env) +
      (1 + 2 * 4 + (K * foldCost (fun s y => step.denote (y, s, env))
        (fun s y => step.cost (y, s, env) + 1) ys (step.denote (y, acc, env)) + 13) + 3))))) ?_
      (by simp only [foldCost]; unfold K; ring_nf; omega)
    refine Yields.loadCons (ptr := lp) (by rsimp) (by simpa [rep, Tree.ofList] using tl)
      fun yp ysp ty tys => ?_
    refine Yields.allocCons hh (by rsimp) (by rsimp) ta te fun e1 v1 t1 => ?_
    refine Yields.allocCons v1 (by rsimp) (by rsimp) (ty.mono e1) t1 fun e2 v2 t2 => ?_
    refine Yields.call (by rsimp) (hs (y, acc, env) v2 ((ts.mono e1).mono e2) t2)
      fun m3 v3 r3 => ?_
    obtain ⟨e3, vm3, q3, rfl, t3⟩ := r3
    have e123 := e1.trans (e2.trans e3)
    refine Yields.call (by rsimp)
      (ih (step.denote (y, acc, env)) vm3 (lp := ysp) (by simpa [rep] using tys.mono e123) t3
        (ts.mono e123) (te.mono e123)) fun m4 v4 r4 => ?_
    obtain ⟨e4, vm4, q4, rfl, t4⟩ := r4
    exact Yields.ret ⟨e123.trans e4, vm4, q4, by rsimp, by simpa using t4⟩ (by simp)

theorem spec_foldl (hm : d.Matches code) {a b : Ty} {xs : Expr Γ (.list a)} {init : Expr Γ b}
    {step : Expr (a :: b :: Γ) b} (hxs : EvalSpec code d xs) (hi : EvalSpec code d init)
    (hs : EvalSpec code d step) : EvalSpec code d (.foldl xs init step) := by
  intro env h hh ep envp he henv
  simp only [Expr.encode] at he
  have hc : (Expr.foldl xs init step).cost env = xs.cost env + init.cost env +
      foldCost (fun s y => step.denote (y, s, env)) (fun s y => step.cost (y, s, env) + 1)
        (xs.denote env) (init.denote env) + 1 := by
    simp only [Expr.cost]
    rw [foldl_pair (fun s y => step.denote (y, s, env)) (fun s y => step.cost (y, s, env))]
    simp
  refine Yields.le (B := 10 + (10 * (19 + 1) + (10 + (1 + 2 * 2 + K * xs.cost env +
    (10 + (1 + 2 * 2 + K * init.cost env + (1 + 2 * 4 + (K * foldCost
      (fun s y => step.denote (y, s, env)) (fun s y => step.cost (y, s, env) + 1)
      (xs.denote env) (init.denote env) + 13) + 3))))))) ?_
    (by rw [hc]; unfold K; ring_nf; omega)
  refine enter hm (k := 19) (by omega) he fun regs pp h0 h1 h3 tp => ?_
  refine Yields.loadPair (by rsimp [h3]) tp fun xp rp tx tr => ?_
  refine Yields.call (by rsimp [h1]) (hxs env hh tx henv) fun m1 v1 r1 => ?_
  obtain ⟨e1, vm1, q1, rfl, t1⟩ := r1
  refine Yields.loadPair (by rsimp) (tr.mono e1) fun ip sp ti ts => ?_
  refine Yields.call (by rsimp [h1]) (hi env vm1 ti (henv.mono e1)) fun m2 v2 r2 => ?_
  obtain ⟨e2, vm2, q2, rfl, t2⟩ := r2
  refine Yields.call (by rsimp [h1]) (fold_spec hm hs env (xs.denote env) (init.denote env) vm2
    (t1.mono e2) t2 (ts.mono e2) ((henv.mono e1).mono e2)) fun m3 v3 r3 => ?_
  obtain ⟨e3, vm3, q3, rfl, t3⟩ := r3
  exact Yields.ret ⟨e1.trans (e2.trans e3), vm3, q3, by rsimp,
    by simpa [Expr.denote] using t3⟩ (by simp)

/-! ## Bounded iteration -/

theorem rounds_mul {σ : Type*} (f : σ → σ) (g : σ → ℕ) (c : ℕ) :
    ∀ n s, rounds f (fun s => c * g s) n s = c * rounds f g n s := by
  intro n; induction n with
  | zero => simp [rounds]
  | succ n ih => intro s; simp only [rounds, ih]; ring

theorem iterate_pair' {σ : Type*} (f : σ → σ) (g : σ → ℕ) (c : ℕ) :
    ∀ (n : ℕ) (s : σ) (c0 : ℕ),
      Nat.iterate (fun (x : σ × ℕ) => (f x.1, x.2 + g x.1 + c + 1)) n (s, c0) =
        (f^[n] s, c0 + rounds f (fun s => g s + c + 1) n s) := by
  intro n
  induction n with
  | zero => intro s c0; simp [rounds]
  | succ n ih =>
    intro s c0
    rw [Function.iterate_succ_apply, ih, Function.iterate_succ_apply]
    simp [rounds]; ring

theorem evalStep_spec (hm : d.Matches code) {b : Ty} {step : Expr (b :: Γ) b}
    (hs : EvalSpec code d step) (env : Env Γ) (s : b.denote) {h : Heap} (hh : Valid h)
    {dp sp : Ptr} (hd : TreeAt h dp (.pair step.encode (envTree Γ env)))
    (hsp : TreeAt h sp (rep b s)) :
    Yields code h (initialRegisters [.pointer dp, .pointer sp]) (code d.evalStep)
      (K * step.cost (s, env) + 26)
      (StateOut (fun h q s => TreeAt h q (rep b s)) h (step.denote (s, env))) := by
  rw [hm.evalStep]
  refine Yields.le (B := 10 + (8 + (1 + 2 * 2 + K * step.cost (s, env) + 3))) ?_ (by omega)
  refine Yields.loadPair (by rsimp) hd fun stp envp tst tenv => ?_
  refine Yields.allocCons hh (by rsimp) (by rsimp) hsp tenv fun e1 v1 t1 => ?_
  refine Yields.call (by rsimp) (hs (s, env) v1 (tst.mono e1) t1) fun m2 v2 r2 => ?_
  obtain ⟨e2, vm2, q2, rfl, t2⟩ := r2
  exact Yields.ret ⟨e1.trans e2, vm2, q2, by rsimp, t2⟩ (by simp)

theorem spec_iter (hm : d.Matches code) {b : Ty} {count : Expr Γ .int} {init : Expr Γ b}
    {step : Expr (b :: Γ) b} (hcnt : EvalSpec code d count) (hi : EvalSpec code d init)
    (hs : EvalSpec code d step) : EvalSpec code d (.iter count init step) := by
  intro env h hh ep envp he henv
  simp only [Expr.encode] at he
  set n := (count.denote env).natAbs with hn
  set f := fun s => step.denote (s, env) with hf
  set G := fun s => step.cost (s, env) with hG
  have hc : (Expr.iter count init step).cost env = count.cost env + init.cost env +
      rounds f (fun s => G s + bits (count.denote env) + 1) (count.denote env).toNat
        (init.denote env) + 1 := by
    simp only [Expr.cost]
    rw [iterate_pair' f G (bits (count.denote env))]
    dsimp only
    rw [zero_add]
  have h2 := two_pow_length_le n
  have hR : rounds f (fun s => (K * G s + 26) + 5) n (init.denote env) + 43 * (2 ^ (n.bits.length + 1) - 1)
      + 300 ≤ K * rounds f (fun s => G s + bits (count.denote env) + 1) n (init.denote env) + K := by
    have e1 : rounds f (fun s => (K * G s + 26) + 5) n (init.denote env) =
        K * rounds f G n (init.denote env) + 31 * n := by
      rw [show (fun s => (K * G s + 26) + 5) = (fun s => K * G s + 31) by funext s; ring,
        rounds_add_const, rounds_mul]
    have e2 : rounds f (fun s => G s + bits (count.denote env) + 1) n (init.denote env) =
        rounds f G n (init.denote env) + (bits (count.denote env) + 1) * n := by
      rw [show (fun s => G s + bits (count.denote env) + 1) =
        (fun s => G s + (bits (count.denote env) + 1)) by funext s; ring, rounds_add_const]
    rw [e1, e2]; unfold K
    have : (bits (count.denote env) + 1) * n ≥ n := Nat.le_mul_of_pos_left n (by omega)
    omega
  refine Yields.le (B := 10 + (10 * (20 + 1) + (10 + (1 + 2 * 2 + K * count.cost env +
    (10 + (1 + 2 * 2 + K * init.cost env + (10 + (3 + (if count.denote env < 0 then 3 else
      (8 + (1 + 2 * 3 +
      (rounds f (fun s => (K * G s + 26) + 5) n (init.denote env) +
        43 * (2 ^ (n.bits.length + 1) - 1)) + 3))))))))))) ?_ (by
      rw [hc]
      by_cases hneg : count.denote env < 0
      · have : (count.denote env).toNat = 0 := Int.toNat_eq_zero.mpr hneg.le
        rw [if_pos hneg, this]; simp only [rounds]; unfold K; omega
      · have : (count.denote env).toNat = n := by
          rw [hn]; exact (Int.toNat_of_nonneg (not_lt.mp hneg)).symm ▸ (Int.natAbs_of_nonneg (not_lt.mp hneg)).symm ▸ rfl
        rw [if_neg hneg, this]; unfold K at hR ⊢; omega)
  refine enter hm (k := 20) (by omega) he fun regs pp h0 h1 h3 tp => ?_
  refine Yields.loadPair (by rsimp [h3]) tp fun cp rp tcnt tr => ?_
  refine Yields.call (by rsimp [h1]) (hcnt env hh tcnt henv) fun m1 v1 r1 => ?_
  obtain ⟨e1, vm1, q1, rfl, t1⟩ := r1
  refine Yields.loadPair (by rsimp) (tr.mono e1) fun ip sp ti ts => ?_
  refine Yields.call (by rsimp [h1]) (hi env vm1 ti (henv.mono e1)) fun m2 v2 r2 => ?_
  obtain ⟨e2, vm2, q2, rfl, t2⟩ := r2
  refine Yields.loadBit (by rsimp) (t1.mono e2) fun mp tm => ?_
  by_cases hneg : count.denote env < 0
  · rw [if_pos hneg]
    refine Yields.branch (b := true) (by rsimp [hneg]) ?_
    refine Yields.ret ⟨e1.trans e2, vm2, q2, by rsimp, ?_⟩ (by simp)
    simp only [Expr.denote]
    rw [show (count.denote env).toNat = 0 from Int.toNat_eq_zero.mpr hneg.le]
    simpa using t2
  · rw [if_neg hneg]
    refine Yields.branch (b := false) (by rsimp [hneg]) ?_
    refine Yields.allocPair vm2 (by rsimp) (by rsimp [h1]) (ts.mono e2) ((henv.mono e1).mono e2)
      fun e3 v3 t3 => ?_
    have hit := iter_compiled code d.iter d.evalStep hm.iter (fun h q s => TreeAt h q (rep b s))
      f (fun s => K * G s + 26) (h0 := m2 ++ [.pair sp envp]) (dp := m2.length)
      (fun s h' vh' he' sp' hsp' => evalStep_spec hm hs env s vh' (t3.mono he') hsp')
      n.bits (init.denote env) v3 (Extends.refl _) (tm.mono e3) (t2.mono e3)
    rw [lval_bits] at hit
    refine Yields.call (by rsimp) hit fun m4 v4 r4 => ?_
    obtain ⟨e4, vm4, q4, rfl, t4⟩ := r4
    refine Yields.ret ⟨e1.trans (e2.trans (e3.trans e4)), vm4, q4, by rsimp, ?_⟩ (by simp)
    simp only [Expr.denote]
    rw [show (count.denote env).toNat = n by
      rw [hn]; exact (Int.toNat_of_nonneg (not_lt.mp hneg)).symm ▸ (Int.natAbs_of_nonneg (not_lt.mp hneg)).symm ▸ rfl]
    exact t4

/-! ## Tree inspection -/

theorem spec_treeCase (hm : d.Matches code) {b : Ty} {t : Expr Γ .tree} {onNil : Expr Γ b}
    {onBit : Expr (.bool :: .tree :: Γ) b} {onCons : Expr (.tree :: .tree :: Γ) b}
    {onFork : Expr (.tree :: .tree :: Γ) b} {onBucket : Expr (.tree :: Γ) b}
    {onPair : Expr (.tree :: .tree :: Γ) b}
    (ht : EvalSpec code d t) (hn : EvalSpec code d onNil) (hb : EvalSpec code d onBit)
    (hc : EvalSpec code d onCons) (hf : EvalSpec code d onFork)
    (hk : EvalSpec code d onBucket) (hp : EvalSpec code d onPair) :
    EvalSpec code d (.treeCase t onNil onBit onCons onFork onBucket onPair) := by
  intro env h hh ep envp he henv
  simp only [Expr.encode] at he
  have hcost : (Expr.treeCase t onNil onBit onCons onFork onBucket onPair).cost env =
      t.cost env + (match t.denote env with
          | .nil => onNil.cost env
          | .bit b u => onBit.cost (b, u, env)
          | .cons u v => onCons.cost (u, v, env)
          | .fork u v => onFork.cost (u, v, env)
          | .bucket u => onBucket.cost (u, env)
          | .pair u v => onPair.cost (u, v, env)) + 1 := rfl
  have hden : (Expr.treeCase t onNil onBit onCons onFork onBucket onPair).denote env =
      (match t.denote env with
          | .nil => onNil.denote env
          | .bit b u => onBit.denote (b, u, env)
          | .cons u v => onCons.denote (u, v, env)
          | .fork u v => onFork.denote (u, v, env)
          | .bucket u => onBucket.denote (u, env)
          | .pair u v => onPair.denote (u, v, env)) := rfl
  refine Yields.le (B := 10 + (10 * (22 + 1) + (10 + (1 + 2 * 2 + K * t.cost env +
    (10 + (10 + (10 + (10 + (10 + (10 + (match t.denote env with
          | .nil => 1 + 2 * 2 + K * onNil.cost env + 3
          | .bit b u => 8 + (8 + (8 + (1 + 2 * 2 + K * onBit.cost (b, u, env) + 3)))
          | .cons u v => 8 + (8 + (1 + 2 * 2 + K * onCons.cost (u, v, env) + 3))
          | .fork u v => 8 + (8 + (1 + 2 * 2 + K * onFork.cost (u, v, env) + 3))
          | .bucket u => 8 + (1 + 2 * 2 + K * onBucket.cost (u, env) + 3)
          | .pair u v => 8 + (8 + (1 + 2 * 2 + K * onPair.cost (u, v, env) + 3))))))))))))) ?_
    (by
      rw [hcost]
      cases t.denote env <;> (simp only []; unfold K; omega))
  rw [hden]
  refine enter hm (k := 22) (by omega) he fun regs pp h0 h1 h3 tp => ?_
  refine Yields.loadPair (by rsimp [h3]) tp fun tp' rp tt tr => ?_
  refine Yields.call (by rsimp [h1]) (ht env hh tt henv) fun m1 v1 r1 => ?_
  obtain ⟨e1, vm1, q1, rfl, t1⟩ := r1
  have henv1 := henv.mono e1
  refine Yields.loadPair (by rsimp) (tr.mono e1) fun np r0 tn tr0 => ?_
  refine Yields.loadPair (by rsimp) tr0 fun bp r1' tb tr1 => ?_
  refine Yields.loadPair (by rsimp) tr1 fun cp r2' tc tr2 => ?_
  refine Yields.loadPair (by rsimp) tr2 fun fp r3' tf tr3 => ?_
  refine Yields.loadPair (by rsimp) tr3 fun kp pp' tk tpp => ?_
  generalize t.denote env = T at t1 ⊢
  cases T with
  | nil =>
    dsimp only
    refine Yields.loadNil (ptr := q1) (by rsimp) t1 ?_
    refine Yields.call (by rsimp [h1]) (hn env vm1 tn henv1) fun m2 v2 r2 => ?_
    obtain ⟨e2, vm2, q2, rfl, t2⟩ := r2
    exact Yields.ret ⟨e1.trans e2, vm2, q2, by rsimp, t2⟩ (by simp)
  | bit bv u =>
    dsimp only
    refine Yields.loadBit (ptr := q1) (by rsimp) t1 fun up tu => ?_
    refine Yields.allocBit vm1 (b := bv) (by rsimp) (by rsimp) (TreeAt.zero vm1) fun e2 v2 t2 => ?_
    refine Yields.allocCons v2 (by rsimp) (by rsimp [h1]) (tu.mono e2) (henv1.mono e2)
      fun e3 v3 t3 => ?_
    refine Yields.allocCons v3 (by rsimp) (by rsimp) (t2.mono e3) t3 fun e4 v4 t4 => ?_
    refine Yields.call (by rsimp) (hb (bv, u, env) v4 (((tb.mono e2).mono e3).mono e4) t4)
      fun m5 v5 r5 => ?_
    obtain ⟨e5, vm5, q5, rfl, t5⟩ := r5
    exact Yields.ret ⟨e1.trans (e2.trans (e3.trans (e4.trans e5))), vm5, q5, by rsimp, t5⟩
      (by simp)
  | cons u v =>
    dsimp only
    refine Yields.loadCons (ptr := q1) (by rsimp) t1 fun up vp tu tv => ?_
    refine Yields.allocCons vm1 (by rsimp) (by rsimp [h1]) tv henv1 fun e2 v2 t2 => ?_
    refine Yields.allocCons v2 (by rsimp) (by rsimp) (tu.mono e2) t2 fun e3 v3 t3 => ?_
    refine Yields.call (by rsimp) (hc (u, v, env) v3 ((tc.mono e2).mono e3) t3)
      fun m4 v4 r4 => ?_
    obtain ⟨e4, vm4, q4, rfl, t4⟩ := r4
    exact Yields.ret ⟨e1.trans (e2.trans (e3.trans e4)), vm4, q4, by rsimp, t4⟩ (by simp)
  | fork u v =>
    dsimp only
    refine Yields.loadFork (ptr := q1) (by rsimp) t1 fun up vp tu tv => ?_
    refine Yields.allocCons vm1 (by rsimp) (by rsimp [h1]) tv henv1 fun e2 v2 t2 => ?_
    refine Yields.allocCons v2 (by rsimp) (by rsimp) (tu.mono e2) t2 fun e3 v3 t3 => ?_
    refine Yields.call (by rsimp) (hf (u, v, env) v3 ((tf.mono e2).mono e3) t3)
      fun m4 v4 r4 => ?_
    obtain ⟨e4, vm4, q4, rfl, t4⟩ := r4
    exact Yields.ret ⟨e1.trans (e2.trans (e3.trans e4)), vm4, q4, by rsimp, t4⟩ (by simp)
  | bucket u =>
    dsimp only
    refine Yields.loadBucket (ptr := q1) (by rsimp) t1 fun up tu => ?_
    refine Yields.allocCons vm1 (by rsimp) (by rsimp [h1]) tu henv1 fun e2 v2 t2 => ?_
    refine Yields.call (by rsimp) (hk (u, env) v2 (tk.mono e2) t2) fun m3 v3 r3 => ?_
    obtain ⟨e3, vm3, q3, rfl, t3⟩ := r3
    exact Yields.ret ⟨e1.trans (e2.trans e3), vm3, q3, by rsimp, t3⟩ (by simp)
  | pair u v =>
    dsimp only
    refine Yields.loadPair (ptr := q1) (by rsimp) t1 fun up vp tu tv => ?_
    refine Yields.allocCons vm1 (by rsimp) (by rsimp [h1]) tv henv1 fun e2 v2 t2 => ?_
    refine Yields.allocCons v2 (by rsimp) (by rsimp) (tu.mono e2) t2 fun e3 v3 t3 => ?_
    refine Yields.call (by rsimp) (hp (u, v, env) v3 ((tpp.mono e2).mono e3) t3)
      fun m4 v4 r4 => ?_
    obtain ⟨e4, vm4, q4, rfl, t4⟩ := r4
    exact Yields.ret ⟨e1.trans (e2.trans (e3.trans e4)), vm4, q4, by rsimp, t4⟩ (by simp)

end MWIS.Fun.Interp

end
