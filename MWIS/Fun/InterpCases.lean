module

public import MWIS.Fun.Interp

/-!
# The `Fun` interpreter: constructors without binders

For each expression constructor that binds no variables, the eval procedure
meets `EvalSpec` provided its subexpressions do.
-/

@[expose] public section

namespace MWIS.Fun.Interp

open MWIS.PointerMemory MWIS.RegisterMachine MWIS.Fun.Arith

variable {p : ℕ} {code : Code p} {d : Procedures p} {Γ : List Ty}

theorem spec_var (hm : d.Matches code) {τ : Ty} (v : Var Γ τ) : EvalSpec code d (.var v) := by
  intro env h hh ep envp he henv
  simp only [Expr.encode] at he
  refine Yields.le (B := 10 + (10 * (0 + 1) + (1 + 2 * 2 + 30 * (v.index + 1) + 3))) ?_
    (by simp only [Expr.cost, K]; omega)
  refine enter hm (k := 0) (by omega) he fun regs pp h0 h1 h3 tp => ?_
  refine Yields.call (by rsimp [h3, h1]) (lookup_compiled code d.lookup hm.lookup v env tp henv)
    fun mid vals hv => ?_
  obtain ⟨rfl, q, rfl, tq⟩ := hv
  exact Yields.ret ⟨Extends.refl _, hh, q, by rsimp, by simpa [Expr.denote] using tq⟩ (by simp)

theorem spec_lit {τ : Ty} (hm : d.Matches code) {k : ℕ} (hk' : k < 4)
    (e : Expr Γ τ) (val : τ.denote) (henc : e.encode = node k (rep τ val))
    (hden : ∀ env : Env Γ, e.denote env = val) (hcost : ∀ env : Env Γ, e.cost env = 1)
    (hleaf : leaf d k = .ret [.register 3]) : EvalSpec code d e := by
  intro env h hh ep envp he henv
  rw [henc] at he
  refine Yields.le (B := 10 + (10 * (k + 1) + 3)) ?_ (by rw [hcost]; unfold K; omega)
  refine enter hm (by omega) he fun regs pp h0 h1 h3 tp => ?_
  rw [hleaf]
  exact Yields.ret ⟨Extends.refl _, hh, pp, by rsimp [h3], by rw [hden]; exact tp⟩ (by simp)

theorem spec_int (hm : d.Matches code) (z : ℤ) : EvalSpec code d (Γ := Γ) (.int z) :=
  spec_lit hm (k := 1) (by omega) _ (τ := .int) z rfl (fun _ => rfl) (fun _ => rfl) rfl

theorem spec_bool (hm : d.Matches code) (b : Bool) : EvalSpec code d (Γ := Γ) (.bool b) :=
  spec_lit hm (k := 2) (by omega) _ (τ := .bool) b rfl (fun _ => rfl) (fun _ => rfl) rfl

theorem spec_unit (hm : d.Matches code) : EvalSpec code d (Γ := Γ) .unit :=
  spec_lit hm (k := 3) (by omega) _ (τ := .unit) () rfl (fun _ => rfl) (fun _ => rfl) rfl

/-- A binary leaf: both subexpressions are evaluated, then a fixed procedure
combines the two stored values. -/
theorem spec_bin {a b τ : Ty} (hm : d.Matches code) {k : ℕ} (hk : k < 32) (proc : Fin p)
    (hleaf : leaf d k = binLeaf d.eval proc) (e : Expr Γ τ) (x : Expr Γ a) (y : Expr Γ b)
    (henc : e.encode = node k (.pair x.encode y.encode)) (hx : EvalSpec code d x)
    (hy : EvalSpec code d y) (charge : Env Γ → ℕ)
    (hcost : ∀ env, e.cost env = x.cost env + y.cost env + charge env + 1)
    (hbound : ∀ env, 10 * (k + 1) + 128 + 1000 * (charge env + 1) ≤ K * (charge env + 1))
    (hproc : ∀ env {h : Heap}, Valid h → ∀ {px py : Ptr}, TreeAt h px (rep a (x.denote env)) →
      TreeAt h py (rep b (y.denote env)) →
      Yields code h (initialRegisters [.pointer px, .pointer py]) (code proc)
        (1000 * (charge env + 1)) (Returns h (rep τ (e.denote env)))) :
    EvalSpec code d e := by
  intro env h hh ep envp he henv
  rw [henc] at he
  have hb := hbound env
  refine Yields.le (B := 10 + (10 * (k + 1) + (10 + (1 + 2 * 2 + K * x.cost env +
    (1 + 2 * 2 + K * y.cost env + (1 + 2 * 2 + 1000 * (charge env + 1) + 3)))))) ?_
    (by rw [hcost]; nlinarith)
  refine enter hm hk he fun regs pp h0 h1 h3 tp => ?_
  rw [hleaf]
  refine Yields.loadPair (by rsimp [h3]) tp fun xp yp tx ty => ?_
  refine Yields.call (by rsimp [h1]) (hx env hh tx henv) fun m1 v1 r1 => ?_
  obtain ⟨e1, vm1, q1, rfl, t1⟩ := r1
  refine Yields.call (by rsimp [h1]) (hy env vm1 (ty.mono e1) (henv.mono e1)) fun m2 v2 r2 => ?_
  obtain ⟨e2, vm2, q2, rfl, t2⟩ := r2
  refine Yields.call (by rsimp) (hproc env vm2 (t1.mono e2) t2) fun m3 v3 r3 => ?_
  obtain ⟨e3, vm3, q3, rfl, t3⟩ := r3
  exact Yields.ret ⟨e1.trans (e2.trans e3), vm3, q3, by rsimp, t3⟩ (by simp)

theorem spec_arith (hm : d.Matches code) (op : IntOp) {x y : Expr Γ .int}
    (hx : EvalSpec code d x) (hy : EvalSpec code d y) : EvalSpec code d (.arith op x y) :=
  spec_bin hm (k := op.tag) (by cases op <;> decide) (d.arith.intOp op) (by cases op <;> rfl) _ x y
    rfl hx hy (fun env => op.charge (x.denote env) (y.denote env)) (fun _ => rfl)
    (fun env => by have : op.tag ≤ 8 := by cases op <;> decide
                   unfold K; omega)
    (fun env h hh px py tx ty => (intOp_compiled hm.arith op _ _ hh tx ty).le (by omega))

theorem spec_cmp (hm : d.Matches code) (op : CmpOp) {x y : Expr Γ .int}
    (hx : EvalSpec code d x) (hy : EvalSpec code d y) : EvalSpec code d (.cmp op x y) :=
  spec_bin hm (k := op.tag) (by cases op <;> decide) (d.arith.cmpOp op) (by cases op <;> rfl) _ x y
    rfl hx hy (fun env => op.charge (x.denote env) (y.denote env)) (fun _ => rfl)
    (fun env => by have : op.tag ≤ 11 := by cases op <;> decide
                   unfold K; omega)
    (fun env h hh px py tx ty => (icmp_compiled hm.arith op _ _ hh tx ty).le (by omega))

theorem spec_word (hm : d.Matches code) {w k : Expr Γ .int}
    (hw : EvalSpec code d w) (hk : EvalSpec code d k) : EvalSpec code d (.word w k) := by
  refine spec_bin hm (k := 30) (by omega) d.word rfl _ w k rfl hw hk
    (fun env => (w.denote env).toNat + bits (k.denote env))
    (fun _ => by simp only [Expr.cost]; omega)
    (fun env => by unfold K; omega) ?_
  intro env h hh px py tx ty
  exact (word_compiled code d.word d.iterW d.wordStep hm.word hm.iterW hm.wordStep _ _ hh tx ty).le
    (by omega)

/-- Both subexpressions are evaluated, then a cell over the two results is
allocated. -/
theorem spec_alloc {a b τ : Ty} (hm : d.Matches code) {k : ℕ} (hk : k < 32) (cell : CellExpr)
    (hleaf : leaf d k = allocLeaf d.eval cell) (e : Expr Γ τ) (x : Expr Γ a) (y : Expr Γ b)
    (henc : e.encode = node k (.pair x.encode y.encode)) (hx : EvalSpec code d x)
    (hy : EvalSpec code d y)
    (hcost : ∀ env, e.cost env = x.cost env + y.cost env + 1)
    (hbound : 10 * (k + 1) + 60 ≤ K)
    (halloc : ∀ env {h : Heap} (regs : Registers), Valid h → ∀ {px py : Ptr},
      regs 6 = .pointer px → regs 7 = .pointer py →
      TreeAt h px (rep a (x.denote env)) → TreeAt h py (rep b (y.denote env)) →
      Yields code h regs (.allocate 8 cell (.ret [.register 8])) 11
        (Returns h (rep τ (e.denote env)))) :
    EvalSpec code d e := by
  intro env h hh ep envp he henv
  rw [henc] at he
  refine Yields.le (B := 10 + (10 * (k + 1) + (10 + (1 + 2 * 2 + K * x.cost env +
    (1 + 2 * 2 + K * y.cost env + 11))))) ?_ (by rw [hcost]; nlinarith)
  refine enter hm hk he fun regs pp h0 h1 h3 tp => ?_
  rw [hleaf]
  refine Yields.loadPair (by rsimp [h3]) tp fun xp yp tx ty => ?_
  refine Yields.call (by rsimp [h1]) (hx env hh tx henv) fun m1 v1 r1 => ?_
  obtain ⟨e1, vm1, q1, rfl, t1⟩ := r1
  refine Yields.call (by rsimp [h1]) (hy env vm1 (ty.mono e1) (henv.mono e1)) fun m2 v2 r2 => ?_
  obtain ⟨e2, vm2, q2, rfl, t2⟩ := r2
  exact (halloc env _ vm2 (by rsimp) (by rsimp) (t1.mono e2) t2).mono (by omega)
    fun out outs ho => ⟨e1.trans (e2.trans ho.1), ho.2⟩

theorem alloc_pair_ret {h : Heap} (regs : Registers) (hh : Valid h) {px py : Ptr} {x y : Tree}
    (h6 : regs 6 = .pointer px) (h7 : regs 7 = .pointer py) (tx : TreeAt h px x)
    (ty : TreeAt h py y) :
    Yields code h regs (.allocate 8 (.pair (.register 6) (.register 7)) (.ret [.register 8])) 11
      (Returns h (.pair x y)) := by
  refine Yields.le (B := 8 + 3) ?_ (by omega)
  refine Yields.allocPair hh (by rsimp [h6]) (by rsimp [h7]) tx ty fun e2 v2 t2 => ?_
  exact Yields.ret ⟨e2, v2, h.length, by rsimp, t2⟩ (by simp)

theorem alloc_cons_ret {h : Heap} (regs : Registers) (hh : Valid h) {px py : Ptr} {x y : Tree}
    (h6 : regs 6 = .pointer px) (h7 : regs 7 = .pointer py) (tx : TreeAt h px x)
    (ty : TreeAt h py y) :
    Yields code h regs (.allocate 8 (.cons (.register 6) (.register 7)) (.ret [.register 8])) 11
      (Returns h (.cons x y)) := by
  refine Yields.le (B := 8 + 3) ?_ (by omega)
  refine Yields.allocCons hh (by rsimp [h6]) (by rsimp [h7]) tx ty fun e2 v2 t2 => ?_
  exact Yields.ret ⟨e2, v2, h.length, by rsimp, t2⟩ (by simp)

theorem spec_pair (hm : d.Matches code) {a b : Ty} {x : Expr Γ a} {y : Expr Γ b}
    (hx : EvalSpec code d x) (hy : EvalSpec code d y) : EvalSpec code d (.pair x y) :=
  spec_alloc hm (k := 13) (by omega) _ rfl _ x y rfl hx hy (fun _ => rfl) (by unfold K; omega)
    (fun env h regs hh px py h6 h7 tx ty => by
      simpa [Expr.denote, rep] using alloc_pair_ret regs hh h6 h7 tx ty)

theorem spec_cons (hm : d.Matches code) {a : Ty} {x : Expr Γ a} {xs : Expr Γ (.list a)}
    (hx : EvalSpec code d x) (hy : EvalSpec code d xs) : EvalSpec code d (.cons x xs) :=
  spec_alloc hm (k := 17) (by omega) _ rfl _ x xs rfl hx hy (fun _ => rfl) (by unfold K; omega)
    (fun env h regs hh px py h6 h7 tx ty => by
      simpa [Expr.denote, rep, Tree.ofList] using alloc_cons_ret regs hh h6 h7 tx ty)

theorem spec_treeCons (hm : d.Matches code) {x t : Expr Γ .tree}
    (hx : EvalSpec code d x) (hy : EvalSpec code d t) : EvalSpec code d (.treeCons x t) :=
  spec_alloc hm (k := 25) (by omega) _ rfl _ x t rfl hx hy (fun _ => rfl) (by unfold K; omega)
    (fun env h regs hh px py h6 h7 tx ty => by
      simpa [Expr.denote, rep] using alloc_cons_ret regs hh h6 h7 tx ty)

theorem spec_treePair (hm : d.Matches code) {x y : Expr Γ .tree}
    (hx : EvalSpec code d x) (hy : EvalSpec code d y) : EvalSpec code d (.treePair x y) :=
  spec_alloc hm (k := 26) (by omega) _ rfl _ x y rfl hx hy (fun _ => rfl) (by unfold K; omega)
    (fun env h regs hh px py h6 h7 tx ty => by
      simpa [Expr.denote, rep] using alloc_pair_ret regs hh h6 h7 tx ty)

theorem spec_treeBit (hm : d.Matches code) {b : Expr Γ .bool} {t : Expr Γ .tree}
    (hb : EvalSpec code d b) (ht : EvalSpec code d t) : EvalSpec code d (.treeBit b t) := by
  intro env h hh ep envp he henv
  simp only [Expr.encode] at he
  refine Yields.le (B := 10 + (10 * (24 + 1) + (10 + (1 + 2 * 2 + K * b.cost env +
    (1 + 2 * 2 + K * t.cost env + (10 + 11)))))) ?_ (by simp only [Expr.cost]; unfold K; omega)
  refine enter hm (k := 24) (by omega) he fun regs pp h0 h1 h3 tp => ?_
  refine Yields.loadPair (by rsimp [h3]) tp fun bp tp' tb tt => ?_
  refine Yields.call (by rsimp [h1]) (hb env hh tb henv) fun m1 v1 r1 => ?_
  obtain ⟨e1, vm1, q1, rfl, t1⟩ := r1
  refine Yields.call (by rsimp [h1]) (ht env vm1 (tt.mono e1) (henv.mono e1)) fun m2 v2 r2 => ?_
  obtain ⟨e2, vm2, q2, rfl, t2⟩ := r2
  refine Yields.loadBit (by rsimp) (t1.mono e2) fun _ _ => ?_
  refine Yields.le (B := 8 + 3) ?_ (by omega)
  refine Yields.allocBit vm2 (b := b.denote env) (by rsimp) (by rsimp) t2 fun e3 v3 t3 => ?_
  exact Yields.ret ⟨e1.trans (e2.trans e3), v3, m2.length, by rsimp,
    by simpa [Expr.denote, rep] using t3⟩ (by simp)

/-- One subexpression is evaluated and passed to a fixed procedure. -/
theorem spec_un {a τ : Ty} (hm : d.Matches code) {k : ℕ} (hk : k < 32) (proc : Fin p)
    (hleaf : leaf d k = unLeaf d.eval proc) (e : Expr Γ τ) (x : Expr Γ a)
    (henc : e.encode = node k x.encode) (hx : EvalSpec code d x) (charge : Env Γ → ℕ)
    (hcost : ∀ env, e.cost env = x.cost env + charge env + 1)
    (hbound : ∀ env, 10 * (k + 1) + 30 + 1000 * charge env ≤ K * (charge env + 1))
    (hproc : ∀ env {h : Heap}, Valid h → ∀ {px : Ptr}, TreeAt h px (rep a (x.denote env)) →
      Yields code h (initialRegisters [.pointer px]) (code proc)
        (1000 * (charge env + 1)) (Returns h (rep τ (e.denote env)))) :
    EvalSpec code d e := by
  intro env h hh ep envp he henv
  rw [henc] at he
  have hb := hbound env
  refine Yields.le (B := 10 + (10 * (k + 1) + (1 + 2 * 2 + K * x.cost env +
    (1 + 2 * 1 + 1000 * (charge env + 1) + 3)))) ?_ (by rw [hcost]; unfold K at *; nlinarith)
  refine enter hm hk he fun regs pp h0 h1 h3 tp => ?_
  rw [hleaf]
  refine Yields.call (by rsimp [h3, h1]) (hx env hh tp henv) fun m1 v1 r1 => ?_
  obtain ⟨e1, vm1, q1, rfl, t1⟩ := r1
  refine Yields.call (by rsimp) (hproc env vm1 t1) fun m2 v2 r2 => ?_
  obtain ⟨e2, vm2, q2, rfl, t2⟩ := r2
  exact Yields.ret ⟨e1.trans e2, vm2, q2, by rsimp, t2⟩ (by simp)

theorem spec_size (hm : d.Matches code) {x : Expr Γ .int} (hx : EvalSpec code d x) :
    EvalSpec code d (.size x) :=
  spec_un hm (k := 31) (by omega) d.arith.isize rfl _ x rfl hx (fun env => bits (x.denote env))
    (fun _ => rfl) (fun env => by unfold K; omega)
    (fun env h hh px tx => isize_compiled hm.arith _ hh tx)

theorem spec_items (hm : d.Matches code) {t : Expr Γ .tree} (ht : EvalSpec code d t) :
    EvalSpec code d (.items t) :=
  spec_un hm (k := 27) (by omega) d.items rfl _ t rfl ht (fun env => (t.denote env).spine)
    (fun _ => rfl) (fun env => by unfold K; omega)
    (fun env h hh px tx => by
      have := items_compiled code d.items hm.items (t.denote env) hh tx
      refine this.mono (by omega) fun out outs ho => ?_
      simpa [Expr.denote, rep] using ho)

theorem spec_wordValue (hm : d.Matches code) {t : Expr Γ .tree} (ht : EvalSpec code d t) :
    EvalSpec code d (.wordValue t) :=
  spec_un hm (k := 29) (by omega) d.skip rfl _ t rfl ht
    (fun env => (t.denote env).bitList.length) (fun _ => rfl) (fun env => by unfold K; omega)
    (fun env h hh px tx => by
      have := skip_compiled code d.skip d.rev hm.skip hm.rev (t.denote env) hh tx
      exact this.mono (by omega) fun out outs ho => ho)

theorem spec_ofItems (hm : d.Matches code) {ts : Expr Γ (.list .tree)}
    (ht : EvalSpec code d ts) : EvalSpec code d (.ofItems ts) := by
  intro env h hh ep envp he henv
  simp only [Expr.encode] at he
  refine Yields.le (B := 10 + (10 * (28 + 1) + (1 + 2 * 2 + K * ts.cost env + 3))) ?_
    (by simp only [Expr.cost]; unfold K; omega)
  refine enter hm (k := 28) (by omega) he fun regs pp h0 h1 h3 tp => ?_
  refine Yields.call (by rsimp [h3, h1]) (ht env hh tp henv) fun m1 v1 r1 => ?_
  obtain ⟨e1, vm1, q1, rfl, t1⟩ := r1
  exact Yields.ret ⟨e1, vm1, q1, by rsimp, by simpa [Expr.denote, rep] using t1⟩ (by simp)

theorem spec_proj {a b τ : Ty} (hm : d.Matches code) {k : ℕ} (hk : k < 32) (r : Register)
    (hleaf : leaf d k = projLeaf d.eval r) (e : Expr Γ τ) (x : Expr Γ (.prod a b))
    (henc : e.encode = node k x.encode) (hx : EvalSpec code d x)
    (hcost : ∀ env, e.cost env = x.cost env + 1) (hbound : 10 * (k + 1) + 30 ≤ K)
    (hpick : ∀ env (regs : Registers) (u v : Ptr), regs 5 = .pointer u → regs 6 = .pointer v →
      ∀ {h : Heap}, TreeAt h u (rep a (x.denote env).1) → TreeAt h v (rep b (x.denote env).2) →
      ∃ q, values regs [.register r] = [.pointer q] ∧ TreeAt h q (rep τ (e.denote env))) :
    EvalSpec code d e := by
  intro env h hh ep envp he henv
  rw [henc] at he
  refine Yields.le (B := 10 + (10 * (k + 1) + (1 + 2 * 2 + K * x.cost env + (10 + 3)))) ?_
    (by rw [hcost]; nlinarith)
  refine enter hm hk he fun regs pp h0 h1 h3 tp => ?_
  rw [hleaf]
  refine Yields.call (by rsimp [h3, h1]) (hx env hh tp henv) fun m1 v1 r1 => ?_
  obtain ⟨e1, vm1, q1, rfl, t1⟩ := r1
  refine Yields.loadPair (by rsimp) t1 fun u v tu tv => ?_
  obtain ⟨q, hq, tq⟩ := hpick env (loaded (bindResults regs [4] [.pointer q1]) 5 6 15 u v false)
    u v (by rsimp) (by rsimp) tu tv
  exact Yields.ret ⟨e1, vm1, q, hq, tq⟩ (by simp)

theorem spec_fst (hm : d.Matches code) {a b : Ty} {x : Expr Γ (.prod a b)}
    (hx : EvalSpec code d x) : EvalSpec code d (.fst x) :=
  spec_proj hm (k := 14) (by omega) 5 rfl _ x rfl hx (fun _ => rfl) (by unfold K; omega)
    (fun env regs u v h5 _ _ tu _ => ⟨u, by rsimp [h5], tu⟩)

theorem spec_snd (hm : d.Matches code) {a b : Ty} {x : Expr Γ (.prod a b)}
    (hx : EvalSpec code d x) : EvalSpec code d (.snd x) :=
  spec_proj hm (k := 15) (by omega) 6 rfl _ x rfl hx (fun _ => rfl) (by unfold K; omega)
    (fun env regs u v _ h6 _ _ tv => ⟨v, by rsimp [h6], tv⟩)

theorem spec_nullary {τ : Ty} (hm : d.Matches code) {k : ℕ} (hk : k < 32) (e : Expr Γ τ)
    (henc : e.encode = node k .nil) (hden : ∀ env, rep τ (e.denote env) = .nil)
    (hcost : ∀ env, e.cost env = 1) (hleaf : leaf d k = .ret [.null]) (hbound : 10 * (k + 1) + 13 ≤ K) :
    EvalSpec code d e := by
  intro env h hh ep envp he henv
  rw [henc] at he
  refine Yields.le (B := 10 + (10 * (k + 1) + 3)) ?_ (by rw [hcost]; omega)
  refine enter hm hk he fun regs pp h0 h1 h3 tp => ?_
  rw [hleaf]
  exact Yields.ret ⟨Extends.refl _, hh, 0, by rsimp, by rw [hden]; exact TreeAt.zero hh⟩ (by simp)

theorem spec_nil (hm : d.Matches code) {a : Ty} : EvalSpec code d (Γ := Γ) (.nil (a := a)) :=
  spec_nullary hm (k := 16) (by omega) _ rfl (fun _ => rfl) (fun _ => rfl) rfl (by unfold K; omega)

theorem spec_treeNil (hm : d.Matches code) : EvalSpec code d (Γ := Γ) .treeNil :=
  spec_nullary hm (k := 23) (by omega) _ rfl (fun _ => rfl) (fun _ => rfl) rfl (by unfold K; omega)

theorem spec_ite (hm : d.Matches code) {τ : Ty} {c : Expr Γ .bool} {t e : Expr Γ τ}
    (hc : EvalSpec code d c) (ht : EvalSpec code d t) (he' : EvalSpec code d e) :
    EvalSpec code d (.ite c t e) := by
  intro env h hh ep envp he henv
  simp only [Expr.encode] at he
  refine Yields.le (B := 10 + (10 * (12 + 1) + (10 + (1 + 2 * 2 + K * c.cost env +
    (10 + (10 + (3 + (1 + 2 * 2 + K * (if c.denote env then t.cost env else e.cost env) +
      3)))))))) ?_ (by simp only [Expr.cost]; unfold K; omega)
  refine enter hm (k := 12) (by omega) he fun regs pp h0 h1 h3 tp => ?_
  refine Yields.loadPair (by rsimp [h3]) tp fun cp rp tc tr => ?_
  refine Yields.call (by rsimp [h1]) (hc env hh tc henv) fun m1 v1 r1 => ?_
  obtain ⟨e1, vm1, q1, rfl, t1⟩ := r1
  refine Yields.loadBit (by rsimp) t1 fun _ _ => ?_
  refine Yields.loadPair (by rsimp) (tr.mono e1) fun tp2 ep2 tt te => ?_
  cases hcd : c.denote env
  · refine Yields.branch (b := false) (by rsimp [hcd]) ?_
    refine Yields.call (by rsimp [h1]) (he' env vm1 te (henv.mono e1)) fun m2 v2 r2 => ?_
    obtain ⟨e2, vm2, q2, rfl, t2⟩ := r2
    exact Yields.ret ⟨e1.trans e2, vm2, q2, by rsimp, by simpa [Expr.denote, hcd] using t2⟩
      (by simp)
  · refine Yields.branch (b := true) (by rsimp [hcd]) ?_
    refine Yields.call (by rsimp [h1]) (ht env vm1 tt (henv.mono e1)) fun m2 v2 r2 => ?_
    obtain ⟨e2, vm2, q2, rfl, t2⟩ := r2
    exact Yields.ret ⟨e1.trans e2, vm2, q2, by rsimp, by simpa [Expr.denote, hcd] using t2⟩
      (by simp)

end MWIS.Fun.Interp

end
