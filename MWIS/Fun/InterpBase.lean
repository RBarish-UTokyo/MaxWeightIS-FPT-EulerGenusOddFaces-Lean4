module

public import MWIS.Fun.ArithOps

/-!
# Building blocks of the `Fun` interpreter

Fixed procedures used by the interpreter: dispatch on a unary constructor tag,
variable lookup in a stored environment, binary-recursion iteration with an
arbitrary step procedure (performing `n` rounds in `O(n)` calls for a count
with `log n` digits), copying a cons spine, reading a big-endian bit chain as an
integer, and writing the fixed-width word of an integer.
-/

@[expose] public section

namespace MWIS.Fun.Interp

open MWIS.PointerMemory MWIS.RegisterMachine MWIS.Fun.Arith

variable {p : ℕ}

/-! ## Dispatch on a unary tag -/

/-- Follow the tag chain in register 2; the `j`-th leaf runs when the chain has
`j` bit cells. -/
def switch (leaves : ℕ → Command p) : ℕ → ℕ → Command p
  | _, 0 => .fail
  | k, n + 1 => .load (.register 2) 2 15 14 { CompiledTrie.failCases with
      nil := leaves k, bit := switch leaves (k + 1) n }

/-- The registers agree outside the dispatch scratch registers 2, 14 and 15. -/
def Agree (regs regs' : Registers) : Prop :=
  ∀ r : Register, r ≠ 2 → r ≠ 14 → r ≠ 15 → regs' r = regs r

theorem Agree.trans {a b c : Registers} (hab : Agree a b) (hbc : Agree b c) : Agree a c :=
  fun r h2 h14 h15 => (hbc r h2 h14 h15).trans (hab r h2 h14 h15)

theorem agree_loaded (regs : Registers) (a b : Ptr) (f : Bool) :
    Agree regs (loaded regs 2 15 14 a b f) := by
  intro r h2 h14 h15
  simp [loaded, Function.update_apply, h2, h14, h15]

theorem Yields.switch {code : Code p} {leaves : ℕ → Command p} {B : ℕ}
    {P : Heap → List Value → Prop} :
    ∀ (j k n : ℕ) {h : Heap} {regs : Registers} {tp : Ptr}, j < n →
      regs 2 = .pointer tp → TreeAt h tp (unary j) →
      (∀ regs', Agree regs regs' → Yields code h regs' (leaves (k + j)) B P) →
      Yields code h regs (switch leaves k n) (10 * (j + 1) + B) P := by
  intro j
  induction j with
  | zero =>
    intro k n h regs tp hn h2 ht rest
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    refine Yields.le (B := 10 + B) ?_ (by omega)
    exact Yields.loadNil (by rsimp [h2]) ht (rest _ (agree_loaded _ _ _ _))
  | succ j ih =>
    intro k n h regs tp hn h2 ht rest
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    refine Yields.le (B := 10 + (10 * (j + 1) + B)) ?_ (by omega)
    refine Yields.loadBit (by rsimp [h2]) ht fun q tq => ?_
    exact ih (k + 1) n (by omega) (by rsimp) tq fun regs' ha =>
      by simpa [Nat.add_assoc, Nat.add_comm 1 j] using
        rest regs' ((agree_loaded _ _ _ _).trans ha)

/-! ## Variable lookup -/

/-- Arguments 0 = unary index, 1 = environment; result: the indexed value. -/
def lookupBody (self : Fin p) : Command p :=
  .load (.register 0) 2 15 3 { CompiledTrie.failCases with
    nil := .load (.register 1) 4 5 15 { CompiledTrie.failCases with cons := .ret [.register 4] }
    bit := .load (.register 1) 4 5 15 { CompiledTrie.failCases with
      cons := .call self [.register 2, .register 5] [6] (.ret [.register 6]) } }

theorem lookup_compiled (code : Code p) (self : Fin p) (hself : code self = lookupBody self) :
    ∀ {Γ : List Ty} {τ : Ty} (v : Var Γ τ) (env : Env Γ) {h : Heap} {ip envp : Ptr},
      TreeAt h ip (unary v.index) → EnvAt Γ h envp env →
      Yields code h (initialRegisters [.pointer ip, .pointer envp]) (code self)
        (30 * (v.index + 1))
        (fun out outs => out = h ∧ ∃ q, outs = [.pointer q] ∧ TreeAt h q (rep τ (v.get env))) := by
  intro Γ τ v
  induction v with
  | here =>
    intro env h ip envp hi he
    rw [hself]
    refine Yields.le (B := 10 + (10 + 3)) ?_ (by simp [Var.index])
    refine Yields.loadNil (by rsimp) hi ?_
    exact Yields.loadCons (by rsimp) he fun a q ta _ =>
      Yields.ret ⟨rfl, a, by rsimp, ta⟩ (by simp)
  | there v ih =>
    intro env h ip envp hi he
    rw [hself]
    refine Yields.le (B := 10 + (10 + (1 + 2 * 2 + 30 * (v.index + 1) + 3))) ?_
      (by simp [Var.index]; omega)
    refine Yields.loadBit (by rsimp) hi fun q tq => ?_
    refine Yields.loadCons (by rsimp) he fun a q2 _ tq2 => ?_
    refine Yields.call (by rsimp) (ih env.2 tq tq2) fun mid vals hv => ?_
    obtain ⟨rfl, q3, rfl, t3⟩ := hv
    exact Yields.ret ⟨rfl, q3, by rsimp, t3⟩ (by simp)

/-! ## Rounds of an iteration -/

/-- The total charge `Σ_{i<n} g (f^[i] s)` of `n` rounds. -/
def rounds {σ : Type*} (f : σ → σ) (g : σ → ℕ) : ℕ → σ → ℕ
  | 0, _ => 0
  | n + 1, s => g s + rounds f g n (f s)

theorem rounds_add {σ : Type*} (f : σ → σ) (g : σ → ℕ) (a b : ℕ) (s : σ) :
    rounds f g (a + b) s = rounds f g a s + rounds f g b (f^[a] s) := by
  induction a generalizing s with
  | zero => simp [rounds]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega, rounds, rounds, ih, Function.iterate_succ_apply]
    omega

theorem rounds_mono {σ : Type*} (f : σ → σ) {g g' : σ → ℕ} (hg : ∀ s, g s ≤ g' s) :
    ∀ n s, rounds f g n s ≤ rounds f g' n s := by
  intro n
  induction n with
  | zero => simp [rounds]
  | succ n ih => intro s; simp only [rounds]; have := hg s; have := ih (f s); omega

theorem rounds_add_const {σ : Type*} (f : σ → σ) (g : σ → ℕ) (c : ℕ) :
    ∀ n s, rounds f (fun s => g s + c) n s = rounds f g n s + c * n := by
  intro n
  induction n with
  | zero => simp [rounds]
  | succ n ih => intro s; simp only [rounds, ih]; ring

/-- The accumulated cost of `Nat.iterate` on pairs is the sum of the rounds. -/
theorem iterate_pair {σ : Type*} (f : σ → σ) (g : σ → ℕ) :
    ∀ (n : ℕ) (s : σ) (c : ℕ),
      Nat.iterate (fun (x : σ × ℕ) => (f x.1, x.2 + g x.1)) n (s, c) =
        (f^[n] s, c + rounds f g n s) := by
  intro n
  induction n with
  | zero => intro s c; simp [rounds]
  | succ n ih =>
    intro s c
    rw [Function.iterate_succ_apply, ih, Function.iterate_succ_apply]
    simp [rounds]; ring

/-! ## Binary-recursion iteration -/

/-- Arguments 0 = count digits, 1 = data, 2 = state; result: the state after
`count` calls of `step` on `[data, state]`. -/
def iterBody (self step : Fin p) : Command p :=
  .load (.register 0) 3 15 4 { CompiledTrie.failCases with
    nil := .ret [.register 2]
    bit := .call self [.register 3, .register 1, .register 2] [5]
      (.call self [.register 3, .register 1, .register 5] [6]
        (.branch (.register 4)
          (.call step [.register 1, .register 6] [7] (.ret [.register 7]))
          (.ret [.register 6]))) }

/-- A stored state satisfying a representation property, on a valid heap
extending `h`. -/
def StateOut {σ : Type*} (StateAt : Heap → Ptr → σ → Prop) (h : Heap) (s : σ)
    (out : Heap) (outs : List Value) : Prop :=
  Extends h out ∧ Valid out ∧ ∃ q, outs = [.pointer q] ∧ StateAt out q s

theorem iter_compiled (code : Code p) (self step : Fin p) (hself : code self = iterBody self step)
    {σ : Type*} (StateAt : Heap → Ptr → σ → Prop) (f : σ → σ) (g : σ → ℕ) {h0 : Heap} {dp : Ptr}
    (hstep : ∀ (s : σ) {h : Heap}, Valid h → Extends h0 h → ∀ {sp : Ptr}, StateAt h sp s →
      Yields code h (initialRegisters [.pointer dp, .pointer sp]) (code step) (g s)
        (StateOut StateAt h (f s))) :
    ∀ (l : List Bool) (s : σ) {h : Heap}, Valid h → Extends h0 h → ∀ {lp sp : Ptr},
      TreeAt h lp (Tree.chain l) → StateAt h sp s →
      Yields code h (initialRegisters [.pointer lp, .pointer dp, .pointer sp]) (code self)
        (rounds f (fun s => g s + 5) (lval l) s + 43 * (2 ^ (l.length + 1) - 1))
        (StateOut StateAt h (f^[lval l] s)) := by
  intro l
  induction l with
  | nil =>
    intro s h hh he lp sp hl hs
    rw [hself]
    refine Yields.le (B := 10 + 3) ?_ (by simp [rounds])
    refine Yields.loadChain hh (by rsimp) hl fun _ _ => ?_
    rw [if_pos rfl]
    exact Yields.ret ⟨Extends.refl h, hh, sp, by rsimp, by simpa [lval] using hs⟩ (by simp)
  | cons b l ih =>
    intro s h hh he lp sp hl hs
    rw [hself]
    have hpow : 43 * (2 ^ (l.length + 1 + 1) - 1) =
        2 * (43 * (2 ^ (l.length + 1) - 1)) + 43 := by
      have : 1 ≤ 2 ^ (l.length + 1) := Nat.one_le_two_pow
      rw [pow_succ]; omega
    have hsplit : rounds f (fun s => g s + 5) (lval (b :: l)) s =
        rounds f (fun s => g s + 5) (lval l) s +
          rounds f (fun s => g s + 5) (lval l) (f^[lval l] s) +
          (if b then g (f^[lval l + lval l] s) + 5 else 0) := by
      rw [lval_cons]
      cases b
      · simp only [dg_false, zero_add, Bool.false_eq_true, ↓reduceIte, add_zero]
        rw [two_mul, rounds_add]
      · simp only [dg_true, ↓reduceIte]
        rw [show 1 + 2 * lval l = (lval l + lval l) + 1 by omega, rounds_add, rounds_add,
          Function.iterate_add_apply]
        conv_lhs => rw [show 1 = 0 + 1 from rfl]
        simp only [rounds, add_zero]
        try rw [← Function.iterate_add_apply]
        try ring
    refine Yields.le (B := 10 + (1 + 2 * 3 +
      (rounds f (fun s => g s + 5) (lval l) s + 43 * (2 ^ (l.length + 1) - 1)) +
      (1 + 2 * 3 + (rounds f (fun s => g s + 5) (lval l) (f^[lval l] s) +
        43 * (2 ^ (l.length + 1) - 1)) +
      (3 + (if b then 1 + 2 * 2 + g (f^[lval l + lval l] s) + 3 else 3))))) ?_
      (by rw [hsplit, List.length_cons, hpow]; split_ifs <;> omega)
    refine Yields.loadChain hh (by rsimp) hl fun q tq => ?_
    rw [if_neg (by simp)]
    simp only [List.tail_cons, List.headD_cons] at tq ⊢
    refine Yields.call (by rsimp) (ih s hh he tq hs) fun mid vals hv => ?_
    obtain ⟨hm1, vm1, q1, rfl, t1⟩ := hv
    refine Yields.call (by rsimp) (ih (f^[lval l] s) vm1 (he.trans hm1) (tq.mono hm1) t1)
      fun mid2 vals2 hv2 => ?_
    obtain ⟨hm2, vm2, q2, rfl, t2⟩ := hv2
    have hval : f^[lval (b :: l)] s =
        if b then f (f^[lval l + lval l] s) else f^[lval l + lval l] s := by
      rw [lval_cons]; cases b
      · simp [two_mul]
      · simp only [dg_true, ↓reduceIte]
        rw [show 1 + 2 * lval l = (lval l + lval l) + 1 by omega, Function.iterate_succ_apply']
    have hval2 : f^[lval l] (f^[lval l] s) = f^[lval l + lval l] s := by
      rw [Function.iterate_add_apply]
    rw [hval2] at t2
    cases b
    · refine Yields.branch (b := false) (by rsimp) ?_
      refine Yields.ret ⟨hm1.trans hm2, vm2, q2, by rsimp, ?_⟩ (by simp)
      simpa [hval] using t2
    · refine Yields.branch (b := true) (by rsimp) ?_
      refine Yields.call (by rsimp)
        (hstep (f^[lval l + lval l] s) vm2 (he.trans (hm1.trans hm2)) t2) fun mid3 vals3 hv3 => ?_
      obtain ⟨hm3, vm3, q3, rfl, t3⟩ := hv3
      refine Yields.ret ⟨hm1.trans (hm2.trans hm3), vm3, q3, by rsimp, ?_⟩ (by simp)
      simpa [hval] using t3

/-- The binary-recursion overhead for a normalized count `n ≥ 0`. -/
theorem two_pow_length_le (n : ℕ) : 2 ^ (n.bits.length + 1) ≤ 4 * n + 2 := by
  rw [bits_length]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have := Nat.lt_size_self n
    have h2 : 2 ^ n.size ≤ 2 * n := by
      have hs : 2 ^ (n.size - 1) ≤ n := by
        have := Nat.size_pos.mpr hn
        exact (Nat.lt_size.mp (by omega))
      calc 2 ^ n.size = 2 * 2 ^ (n.size - 1) := by
            rw [← pow_succ']; congr 1; have := Nat.size_pos.mpr hn; omega
        _ ≤ 2 * n := by omega
    rw [pow_succ]; omega

end MWIS.Fun.Interp

end
