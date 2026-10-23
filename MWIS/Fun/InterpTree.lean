module

public import MWIS.Fun.InterpBase

/-!
# Tree conversions of the `Fun` interpreter

Copying a cons spine into a list, reading a big-endian bit chain as a stored
integer, and writing the fixed-width big-endian word of an integer.
-/

@[expose] public section

namespace MWIS.Fun.Interp

open MWIS.PointerMemory MWIS.RegisterMachine MWIS.Fun.Arith

variable {p : ℕ}

/-! ## Cons spines -/

/-- Argument 0 = tree; result: a copy of its cons spine ending in a nil cell. -/
def itemsBody (self : Fin p) : Command p :=
  .load (.register 0) 1 2 15 ⟨.ret [.null], .ret [.null],
    .call self [.register 2] [3] (.allocate 4 (.cons (.register 1) (.register 3)) (.ret [.register 4])),
    .ret [.null], .ret [.null], .ret [.null]⟩

theorem items_compiled (code : Code p) (self : Fin p) (hself : code self = itemsBody self) :
    ∀ (t : Tree) {h : Heap}, Valid h → ∀ {tp : Ptr}, TreeAt h tp t →
      Yields code h (initialRegisters [.pointer tp]) (code self) (30 * (t.spine + 1))
        (Returns h (Tree.ofList t.items)) := by
  intro t
  induction t with
  | nil =>
    intro h hh tp ht; rw [hself]
    refine Yields.le (B := 10 + 3) ?_ (by simp [Tree.spine, Tree.bitList])
    exact Yields.loadNil (by rsimp) ht (Yields.ret ⟨Extends.refl h, hh, 0, by rsimp,
      by simpa [Tree.items, Tree.ofList] using TreeAt.zero hh⟩ (by simp))
  | bit b u _ =>
    intro h hh tp ht; rw [hself]
    refine Yields.le (B := 10 + 3) ?_ (by simp [Tree.spine, Tree.bitList])
    exact Yields.loadBit (by rsimp) ht fun _ _ => Yields.ret ⟨Extends.refl h, hh, 0, by rsimp,
      by simpa [Tree.items, Tree.ofList] using TreeAt.zero hh⟩ (by simp)
  | fork a u _ _ =>
    intro h hh tp ht; rw [hself]
    refine Yields.le (B := 10 + 3) ?_ (by simp [Tree.spine, Tree.bitList])
    exact Yields.loadFork (by rsimp) ht fun _ _ _ _ => Yields.ret ⟨Extends.refl h, hh, 0,
      by rsimp, by simpa [Tree.items, Tree.ofList] using TreeAt.zero hh⟩ (by simp)
  | bucket u _ =>
    intro h hh tp ht; rw [hself]
    refine Yields.le (B := 10 + 3) ?_ (by simp [Tree.spine, Tree.bitList])
    exact Yields.loadBucket (by rsimp) ht fun _ _ => Yields.ret ⟨Extends.refl h, hh, 0, by rsimp,
      by simpa [Tree.items, Tree.ofList] using TreeAt.zero hh⟩ (by simp)
  | pair a u _ _ =>
    intro h hh tp ht; rw [hself]
    refine Yields.le (B := 10 + 3) ?_ (by simp [Tree.spine, Tree.bitList])
    exact Yields.loadPair (by rsimp) ht fun _ _ _ _ => Yields.ret ⟨Extends.refl h, hh, 0,
      by rsimp, by simpa [Tree.items, Tree.ofList] using TreeAt.zero hh⟩ (by simp)
  | cons a u _ ihu =>
    intro h hh tp ht; rw [hself]
    refine Yields.le (B := 10 + (1 + 2 * 1 + 30 * (u.spine + 1) + (8 + 3))) ?_
      (by simp [Tree.spine]; omega)
    refine Yields.loadCons (by rsimp) ht fun ap up ta tu => ?_
    refine Yields.callTree (by rsimp) (ihu hh tu) fun mid q hm vm tq => ?_
    refine Yields.allocCons vm (by rsimp) (by rsimp) (ta.mono hm) tq fun e2 v2 t2 => ?_
    exact Yields.ret ⟨hm.trans e2, v2, mid.length, by rsimp,
      by simpa [Tree.items, Tree.ofList] using t2⟩ (by simp)

/-! ## Reading a big-endian word -/

theorem lval_append (l₁ l₂ : List Bool) : lval (l₁ ++ l₂) = lval l₁ + 2 ^ l₁.length * lval l₂ := by
  induction l₁ with
  | nil => simp [lval]
  | cons b l ih => simp only [List.cons_append, lval_cons, ih, List.length_cons, pow_succ]; ring

theorem foldl_bits (l : List Bool) (a : ℕ) :
    l.foldl (fun a b => 2 * a + if b then 1 else 0) a = 2 ^ l.length * a + lval l.reverse := by
  induction l generalizing a with
  | nil => simp [lval]
  | cons b l ih =>
    rw [List.foldl_cons, ih, List.reverse_cons, lval_append, List.length_cons, List.length_reverse]
    simp only [lval, add_zero]
    cases b <;> simp [pow_succ] <;> ring

theorem wordValue_eq (t : Tree) : t.wordValue = lval t.bitList.reverse := by
  unfold Tree.wordValue; rw [foldl_bits]; simp

theorem norm_reverse_true (l : List Bool) : Norm (true :: l).reverse := by
  intro hne; simp

/-- Argument 0 = tree, 1 = accumulated digits; result: the reversed bit chain
of the tree followed by the accumulated digits. -/
def revBody (self : Fin p) : Command p :=
  .load (.register 0) 2 15 3 ⟨.ret [.register 1],
    .allocate 4 (.bit (.register 3) (.register 1))
      (.call self [.register 2, .register 4] [5] (.ret [.register 5])),
    .ret [.register 1], .ret [.register 1], .ret [.register 1], .ret [.register 1]⟩

theorem rev_compiled (code : Code p) (self : Fin p) (hself : code self = revBody self) :
    ∀ (t : Tree) (acc : List Bool) {h : Heap}, Valid h → ∀ {tp ap : Ptr}, TreeAt h tp t →
      TreeAt h ap (Tree.chain acc) →
      Yields code h (initialRegisters [.pointer tp, .pointer ap]) (code self)
        (30 * (t.bitList.length + 1)) (Returns h (Tree.chain (t.bitList.reverse ++ acc))) := by
  intro t
  induction t with
  | bit b u ihu =>
    intro acc h hh tp ap ht ha; rw [hself]
    refine Yields.le (B := 10 + (8 + (1 + 2 * 2 + 30 * (u.bitList.length + 1) + 3))) ?_
      (by simp [Tree.bitList]; omega)
    refine Yields.loadBit (by rsimp) ht fun up tu => ?_
    refine Yields.allocBit hh (b := b) (by rsimp) (by rsimp) ha fun e2 v2 t2 => ?_
    refine Yields.call (by rsimp) (ihu (b :: acc) v2 (tp := up) (ap := h.length) (tu.mono e2)
      (by simpa using t2))
      fun mid vals hv => ?_
    obtain ⟨hm, vm, q, rfl, tq⟩ := hv
    exact Yields.ret ⟨e2.trans hm, vm, q, by rsimp, by simpa [Tree.bitList] using tq⟩ (by simp)
  | nil =>
    intro acc h hh tp ap ht ha; rw [hself]
    refine Yields.le (B := 10 + 3) ?_ (by simp [Tree.spine, Tree.bitList])
    exact Yields.loadNil (by rsimp) ht (Yields.ret ⟨Extends.refl h, hh, ap, by rsimp,
      by simpa [Tree.bitList] using ha⟩ (by simp))
  | cons a u _ _ =>
    intro acc h hh tp ap ht ha; rw [hself]
    refine Yields.le (B := 10 + 3) ?_ (by simp [Tree.spine, Tree.bitList])
    exact Yields.loadCons (by rsimp) ht fun _ _ _ _ => Yields.ret ⟨Extends.refl h, hh, ap,
      by rsimp, by simpa [Tree.bitList] using ha⟩ (by simp)
  | fork a u _ _ =>
    intro acc h hh tp ap ht ha; rw [hself]
    refine Yields.le (B := 10 + 3) ?_ (by simp [Tree.spine, Tree.bitList])
    exact Yields.loadFork (by rsimp) ht fun _ _ _ _ => Yields.ret ⟨Extends.refl h, hh, ap,
      by rsimp, by simpa [Tree.bitList] using ha⟩ (by simp)
  | bucket u _ =>
    intro acc h hh tp ap ht ha; rw [hself]
    refine Yields.le (B := 10 + 3) ?_ (by simp [Tree.spine, Tree.bitList])
    exact Yields.loadBucket (by rsimp) ht fun _ _ => Yields.ret ⟨Extends.refl h, hh, ap,
      by rsimp, by simpa [Tree.bitList] using ha⟩ (by simp)
  | pair a u _ _ =>
    intro acc h hh tp ap ht ha; rw [hself]
    refine Yields.le (B := 10 + 3) ?_ (by simp [Tree.spine, Tree.bitList])
    exact Yields.loadPair (by rsimp) ht fun _ _ _ _ => Yields.ret ⟨Extends.refl h, hh, ap,
      by rsimp, by simpa [Tree.bitList] using ha⟩ (by simp)

/-- The zero integer as a sign cell over the empty cell. -/
def zeroCell : Command p := .allocate 4 (.bit (.flag false) .null) (.ret [.register 4])

theorem Yields.zeroCell {code : Code p} {h : Heap} (hh : Valid h) {regs : Registers} :
    Yields code h regs zeroCell 11 (Returns h (reprInt 0)) := by
  refine Yields.le (B := 8 + 3) ?_ (by omega)
  refine Yields.allocBit hh (b := false) (by rsimp) (by rsimp) (TreeAt.zero hh) fun e2 v2 t2 => ?_
  exact Yields.ret ⟨e2, v2, h.length, by rsimp, by simpa [reprInt] using t2⟩ (by simp)

/-- Argument 0 = tree; result: the stored integer value of its big-endian bit
chain. Leading zero bits are skipped and the rest is reversed. -/
def skipBody (self rev : Fin p) : Command p :=
  .load (.register 0) 1 15 2 ⟨zeroCell,
    .branch (.register 2)
      (.call rev [.register 0, .null] [3]
        (.allocate 4 (.bit (.flag false) (.register 3)) (.ret [.register 4])))
      (.call self [.register 1] [3] (.ret [.register 3])),
    zeroCell, zeroCell, zeroCell, zeroCell⟩

theorem skip_compiled (code : Code p) (self rev : Fin p) (hself : code self = skipBody self rev)
    (hrev : code rev = revBody rev) :
    ∀ (t : Tree) {h : Heap}, Valid h → ∀ {tp : Ptr}, TreeAt h tp t →
      Yields code h (initialRegisters [.pointer tp]) (code self) (50 * (t.bitList.length + 1))
        (Returns h (reprInt (t.wordValue : ℤ))) := by
  have hz : ∀ (t : Tree), t.bitList = [] → reprInt (t.wordValue : ℤ) = reprInt 0 := by
    intro t ht; rw [wordValue_eq, ht]; simp [lval]
  intro t
  induction t with
  | bit b u ihu =>
    intro h hh tp ht; rw [hself]
    cases b
    · refine Yields.le (B := 10 + (3 + (1 + 2 * 1 + 50 * (u.bitList.length + 1) + 3))) ?_
        (by simp [Tree.bitList]; omega)
      refine Yields.loadBit (by rsimp) ht fun up tu => ?_
      refine Yields.branch (b := false) (by rsimp) ?_
      refine Yields.call (by rsimp) (ihu hh tu) fun mid vals hv => ?_
      obtain ⟨hm, vm, q, rfl, tq⟩ := hv
      refine Yields.ret ⟨hm, vm, q, by rsimp, ?_⟩ (by simp)
      have : (Tree.bit false u).wordValue = u.wordValue := by
        simp [Tree.wordValue, Tree.bitList]
      rw [this]; exact tq
    · refine Yields.le (B := 10 + (3 + (1 + 2 * 2 + 30 * ((Tree.bit true u).bitList.length + 1) +
          (8 + 3)))) ?_ (by simp [Tree.bitList]; omega)
      refine Yields.loadBit (by rsimp) ht fun up tu => ?_
      refine Yields.branch (b := true) (by rsimp) ?_
      refine Yields.call (by rsimp) (rev_compiled code rev hrev _ [] hh ht (TreeAt.zero hh))
        fun mid vals hv => ?_
      obtain ⟨hm, vm, q, rfl, tq⟩ := hv
      refine Yields.allocBit vm (b := false) (by rsimp) (by rsimp) tq fun e2 v2 t2 => ?_
      refine Yields.ret ⟨hm.trans e2, v2, mid.length, by rsimp, ?_⟩ (by simp)
      have hn := norm_reverse_true u.bitList
      have hv : (Tree.bit true u).wordValue = lval (true :: u.bitList).reverse := by
        rw [wordValue_eq]; rfl
      rw [hv, reprInt_natCast, ← norm_eq_bits hn]
      simpa [Tree.bitList] using t2
  | nil =>
    intro h hh tp ht; rw [hself, hz _ rfl]
    refine Yields.le (B := 10 + 11) ?_ (by simp [Tree.spine, Tree.bitList])
    exact Yields.loadNil (by rsimp) ht (Yields.zeroCell hh)
  | cons a u _ _ =>
    intro h hh tp ht; rw [hself, hz _ rfl]
    refine Yields.le (B := 10 + 11) ?_ (by simp [Tree.spine, Tree.bitList])
    exact Yields.loadCons (by rsimp) ht fun _ _ _ _ => Yields.zeroCell hh
  | fork a u _ _ =>
    intro h hh tp ht; rw [hself, hz _ rfl]
    refine Yields.le (B := 10 + 11) ?_ (by simp [Tree.spine, Tree.bitList])
    exact Yields.loadFork (by rsimp) ht fun _ _ _ _ => Yields.zeroCell hh
  | bucket u _ =>
    intro h hh tp ht; rw [hself, hz _ rfl]
    refine Yields.le (B := 10 + 11) ?_ (by simp [Tree.spine, Tree.bitList])
    exact Yields.loadBucket (by rsimp) ht fun _ _ => Yields.zeroCell hh
  | pair a u _ _ =>
    intro h hh tp ht; rw [hself, hz _ rfl]
    refine Yields.le (B := 10 + 11) ?_ (by simp [Tree.spine, Tree.bitList])
    exact Yields.loadPair (by rsimp) ht fun _ _ _ _ => Yields.zeroCell hh

/-! ## Writing a fixed-width word -/

theorem testBit_lval (l : List Bool) (i : ℕ) : (lval l).testBit i = l.getD i false := by
  induction l generalizing i with
  | nil => simp [lval]
  | cons b l ih =>
    cases i with
    | zero => cases b <;> simp [lval, Nat.testBit_zero] <;> omega
    | succ i =>
      rw [Nat.testBit_succ, lval_cons]
      have : (dg b + 2 * lval l) / 2 = lval l := by cases b <;> simp <;> omega
      rw [this, ih]; simp

theorem testBit_bits (k i : ℕ) : k.testBit i = k.bits.getD i false := by
  conv_lhs => rw [← lval_bits k]
  exact testBit_lval _ _

/-- The state after `i` rounds of writing the word of `k`: the low `i` bits and
the unread digits. -/
def WordState (k : ℕ) (h : Heap) (q : Ptr) (i : ℕ) : Prop :=
  TreeAt h q (.pair (Tree.word i k) (Tree.chain (k.bits.drop i)))

/-- Arguments 0 = unused, 1 = state; one round of writing a word. -/
def wordStepBody : Command p :=
  .load (.register 1) 2 3 15 { CompiledTrie.failCases with
    pair := .load (.register 3) 4 15 5 { CompiledTrie.failCases with
      nil := .allocate 6 (.bit (.register 5) (.register 2))
        (.allocate 7 (.pair (.register 6) (.register 4)) (.ret [.register 7]))
      bit := .allocate 6 (.bit (.register 5) (.register 2))
        (.allocate 7 (.pair (.register 6) (.register 4)) (.ret [.register 7])) } }

theorem wordStep_compiled (code : Code p) (self : Fin p) (hself : code self = wordStepBody)
    (k i : ℕ) {h : Heap} (hh : Valid h) {dp sp : Ptr} (hs : WordState k h sp i) :
    Yields code h (initialRegisters [.pointer dp, .pointer sp]) (code self) 50
      (StateOut (WordState k) h (Nat.succ i)) := by
  rw [hself]
  refine Yields.le (B := 10 + (10 + (8 + (8 + 3)))) ?_ (by omega)
  refine Yields.loadPair (by rsimp) hs fun wp rp tw tr => ?_
  refine Yields.loadChain hh (by rsimp) tr fun q tq => ?_
  have hd : (k.bits.drop i).headD false = k.testBit i := by
    rw [testBit_bits]
    rcases Nat.lt_or_ge i k.bits.length with hi | hi
    · rw [List.drop_eq_getElem_cons hi]; simp [hi]
    · rw [List.drop_eq_nil_of_le hi]; simp [hi]
  have ht : (k.bits.drop i).tail = k.bits.drop (i + 1) := by
    rw [List.tail_drop]
  rw [ht] at tq
  have body : Yields code h (loaded (loaded (initialRegisters [.pointer dp, .pointer sp]) 2 3 15
      wp rp false) 4 15 5 q 0 ((k.bits.drop i).headD false))
      (.allocate 6 (.bit (.register 5) (.register 2))
        (.allocate 7 (.pair (.register 6) (.register 4)) (.ret [.register 7]))) (8 + (8 + 3))
      (StateOut (WordState k) h (Nat.succ i)) := by
    refine Yields.allocBit hh (b := k.testBit i)
      (by rsimp; rw [testBit_bits, List.getD_eq_getElem?_getD]) (by rsimp) tw fun e2 v2 t2 => ?_
    refine Yields.allocPair v2 (by rsimp) (by rsimp) t2 (tq.mono e2) fun e3 v3 t3 => ?_
    exact Yields.ret ⟨e2.trans e3, v3, (h ++ [Cell.bit (k.testBit i) wp]).length, by rsimp,
      by simpa [WordState, Tree.word] using t3⟩
      (by simp)
  by_cases hn : k.bits.drop i = []
  · rw [if_pos hn]; exact body
  · rw [if_neg hn]; exact body

/-- Arguments 0 = width integer, 1 = value integer; result: the big-endian word
of width `max w 0` holding the low bits of `|k|`. -/
def wordBody (iterW : Fin p) : Command p :=
  .load (.register 0) 2 15 3 { CompiledTrie.failCases with
    bit := .branch (.register 3) (.ret [.null])
      (.load (.register 1) 4 15 5 { CompiledTrie.failCases with
        bit := .allocate 6 (.pair .null (.register 4))
          (.call iterW [.register 2, .null, .register 6] [7]
            (.load (.register 7) 8 9 15 { CompiledTrie.failCases with
              pair := .ret [.register 8] })) }) }

theorem rounds_const {σ : Type*} (f : σ → σ) (c : ℕ) :
    ∀ n s, rounds f (fun _ => c) n s = c * n := by
  intro n; induction n with
  | zero => simp [rounds]
  | succ n ih => intro s; simp only [rounds, ih]; ring

theorem word_compiled (code : Code p) (self iterW step : Fin p) (hself : code self = wordBody iterW)
    (hiter : code iterW = iterBody iterW step) (hstep : code step = wordStepBody)
    (w k : ℤ) {h : Heap} (hh : Valid h) {wp kp : Ptr}
    (hw : TreeAt h wp (reprInt w)) (hk : TreeAt h kp (reprInt k)) :
    Yields code h (initialRegisters [.pointer wp, .pointer kp]) (code self)
      (300 * (w.toNat + 1)) (Returns h (Tree.word w.toNat k.natAbs)) := by
  rw [hself]
  have h2 := two_pow_length_le w.natAbs
  have hbound : 10 + (3 + (10 + (8 + (1 + 2 * 3 + (55 * w.natAbs +
      43 * (2 ^ (w.natAbs.bits.length + 1) - 1)) + (10 + 3))))) ≤ 300 * (w.toNat + 1) ∨ w < 0 := by
    by_cases hw0 : w < 0
    · exact Or.inr hw0
    · left
      have : w.toNat = w.natAbs := by omega
      rw [this]; omega
  by_cases hw0 : w < 0
  · refine Yields.le (B := 10 + (3 + 3)) ?_ (by omega)
    refine Yields.loadBit (by rsimp) hw fun mw tmw => ?_
    refine Yields.branch (b := true) (by rsimp [hw0]) ?_
    refine Yields.ret ⟨Extends.refl h, hh, 0, by rsimp, ?_⟩ (by simp)
    rw [show w.toNat = 0 by omega]; exact TreeAt.zero hh
  · refine Yields.le (B := 10 + (3 + (10 + (8 + (1 + 2 * 3 + (55 * w.natAbs +
      43 * (2 ^ (w.natAbs.bits.length + 1) - 1)) + (10 + 3)))))) ?_
      (by rcases hbound with hb | hb; exact hb; exact absurd hb hw0)
    refine Yields.loadBit (by rsimp) hw fun mw tmw => ?_
    refine Yields.branch (b := false) (by rsimp [hw0]) ?_
    refine Yields.loadBit (by rsimp) hk fun mk tmk => ?_
    refine Yields.allocPair hh (by rsimp) (by rsimp) (TreeAt.zero hh) tmk fun e2 v2 t2 => ?_
    have hit := iter_compiled code iterW step hiter (WordState k.natAbs) Nat.succ (fun _ => 50)
      (h0 := h) (dp := 0)
      (fun s h' vh' _ sp hs => wordStep_compiled code step hstep k.natAbs s vh' hs)
      w.natAbs.bits 0 v2 e2 (tmw.mono e2) (by simpa [WordState, Tree.word] using t2)
    rw [lval_bits] at hit
    refine Yields.call (by rsimp) (hit.le (B' := 55 * w.natAbs +
      43 * (2 ^ (w.natAbs.bits.length + 1) - 1)) (by rw [rounds_const])) fun mid vals hv => ?_
    obtain ⟨hm, vm, q, rfl, tq⟩ := hv
    have hn : Nat.succ^[w.natAbs] 0 = w.toNat := by
      rw [Nat.succ_iterate]; omega
    rw [hn] at tq
    refine Yields.loadPair (by rsimp) tq fun a r ta _ => ?_
    exact Yields.ret ⟨e2.trans hm, vm, a, by rsimp, ta⟩ (by simp)

end MWIS.Fun.Interp

end
