module

public import MWIS.Fun.HeapExec
public import MWIS.Fun.ArithSpec

/-!
# Register procedures on stored digit chains

Fixed procedures on least-significant-first digit chains: ripple-carry
addition, comparison, trimmed subtraction, length comparison, shift-and-add
multiplication, restoring division and binary length. Each procedure refines
the corresponding function of `MWIS.Fun.ArithSpec`, with an event bound linear
in the digit counts (quadratic for multiplication and division).
-/

@[expose] public section

namespace MWIS.Fun.Arith

open MWIS.PointerMemory MWIS.RegisterMachine MWIS.EfficientSearch

variable {p : ℕ}

/-- Evaluate register lookups after loads, updates and calls. -/
syntax "rsimp" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| rsimp) => `(tactic| (set_option linter.unusedSimpArgs false in
      simp [loaded, Atom.eval, initialRegisters, values, bindResults, Function.update_apply,
        CellExpr.eval, Value.asPointer, Value.asFlag]))
  | `(tactic| rsimp [$args,*]) => `(tactic| (set_option linter.unusedSimpArgs false in
      simp [loaded, Atom.eval, initialRegisters, values, bindResults, Function.update_apply,
        CellExpr.eval, Value.asPointer, Value.asFlag, $args,*]))

/-! ## Branching on three flags -/

/-- Branch on three flag registers to the leaf indexed by their values. -/
def branch3 (r1 r2 r3 : Register) (leaf : Bool → Bool → Bool → Command p) : Command p :=
  .branch (.register r1)
    (.branch (.register r2) (.branch (.register r3) (leaf true true true) (leaf true true false))
      (.branch (.register r3) (leaf true false true) (leaf true false false)))
    (.branch (.register r2) (.branch (.register r3) (leaf false true true) (leaf false true false))
      (.branch (.register r3) (leaf false false true) (leaf false false false)))

theorem Yields.branch3 {code : Code p} {h : Heap} {regs : Registers} {r1 r2 r3 : Register}
    {leaf : Bool → Bool → Bool → Command p} {a b c : Bool} {B : ℕ}
    {P : Heap → List Value → Prop}
    (h1 : regs r1 = .flag a) (h2 : regs r2 = .flag b) (h3 : regs r3 = .flag c)
    (rest : Yields code h regs (leaf a b c) B P) :
    Yields code h regs (branch3 r1 r2 r3 leaf) (9 + B) P := by
  have e1 : (Atom.register r1).eval regs = .flag a := h1
  have e2 : (Atom.register r2).eval regs = .flag b := h2
  have e3 : (Atom.register r3).eval regs = .flag c := h3
  cases a <;> cases b <;> cases c <;>
    exact (Yields.branch e1 (Yields.branch e2 (Yields.branch e3 rest))).le (by omega)

/-! ## Addition -/

def addLeaf (self : Fin p) (a b c : Bool) : Command p :=
  .call self [.register 3, .register 5, .flag (Bits.fullAdd a b c).2] [7]
    (.allocate 8 (.bit (.flag (Bits.fullAdd a b c).1) (.register 7)) (.ret [.register 8]))

def addBase : Command p :=
  .branch (.register 2) (.allocate 7 (.bit (.flag true) .null) (.ret [.register 7])) (.ret [.null])

/-- Arguments 0 = first chain, 1 = second chain, 2 = carry flag. -/
def addBody (self : Fin p) : Command p :=
  .load (.register 0) 3 15 4 { CompiledTrie.failCases with
    nil := .load (.register 1) 5 15 6 { CompiledTrie.failCases with
      nil := addBase, bit := branch3 4 6 2 (addLeaf self) }
    bit := .load (.register 1) 5 15 6 { CompiledTrie.failCases with
      nil := branch3 4 6 2 (addLeaf self), bit := branch3 4 6 2 (addLeaf self) } }

/-- Event budget of the adder. -/
def addBudget (la lb : ℕ) : ℕ := 60 * (la + lb + 1)

theorem add_compiled (code : Code p) (self : Fin p) (hself : code self = addBody self)
    (la lb : List Bool) (c : Bool) {h : Heap} (hh : Valid h) {ap bp : Ptr}
    (ha : TreeAt h ap (Tree.chain la)) (hb : TreeAt h bp (Tree.chain lb)) :
    Yields code h (initialRegisters [.pointer ap, .pointer bp, .flag c]) (code self)
      (addBudget la.length lb.length) (Returns h (Tree.chain (addL la lb c))) := by
  rw [hself]
  have hrec : ¬(la = [] ∧ lb = []) → ∀ qa qb, TreeAt h qa (Tree.chain la.tail) →
      TreeAt h qb (Tree.chain lb.tail) →
      Yields code h (loaded (loaded (initialRegisters [.pointer ap, .pointer bp, .flag c])
        3 15 4 qa 0 (la.headD false)) 5 15 6 qb 0 (lb.headD false))
        (branch3 4 6 2 (addLeaf self)) (60 * (la.length + lb.length) + 40)
        (Returns h (Tree.chain (addL la lb c))) := by
    intro hne qa qb hqa hqb
    have ih := add_compiled code self hself la.tail lb.tail
      (Bits.fullAdd (la.headD false) (lb.headD false) c).2 hh hqa hqb
    have hlt := tail_lt hne
    refine Yields.le (B := 9 + (7 + addBudget la.tail.length lb.tail.length + 11)) ?_
      (by unfold addBudget; omega)
    refine Yields.branch3 (a := la.headD false) (b := lb.headD false) (c := c) ?_ ?_ ?_ ?_
    · rsimp
    · rsimp
    · rsimp
    refine Yields.callTree ?_ ih fun mid q hm vm tq => ?_
    · rsimp
    refine Yields.le (B := 8 + 3) ?_ (by omega)
    refine Yields.allocBit vm (b := (Bits.fullAdd (la.headD false) (lb.headD false) c).1) ?_ ?_ tq
      fun e2 v2 t2 => ?_
    · rsimp
    · rsimp
    refine Yields.ret ⟨hm.trans e2, v2, mid.length, ?_, ?_⟩ (by simp)
    · rsimp
    · rw [addL, dif_neg hne]
      simpa [Tree.chain] using t2
  refine Yields.le (B := 10 + (60 * (la.length + lb.length) + 50)) ?_
    (by unfold addBudget; omega)
  refine Yields.loadChain hh ?_ ha fun qa hqa => ?_
  · rsimp
  by_cases hla : la = []
  · subst hla
    simp only [↓reduceIte]
    refine Yields.le (B := 10 + (60 * lb.length + 40)) ?_ (by simp; omega)
    refine Yields.loadChain hh ?_ hb fun qb hqb => ?_
    · rsimp
    by_cases hlb : lb = []
    · subst hlb
      simp only [↓reduceIte]
      refine Yields.le (B := 3 + 11) ?_ (by omega)
      cases c
      · refine Yields.branch (b := false) ?_ ?_
        · rsimp
        refine Yields.ret ⟨Extends.refl h, hh, 0, ?_, by rw [addL]; exact TreeAt.zero hh⟩
          (by simp)
        rsimp
      · refine Yields.branch (b := true) ?_ ?_
        · rsimp
        refine Yields.le (B := 8 + 3) ?_ (by omega)
        refine Yields.allocBit hh (b := true) ?_ ?_ (TreeAt.zero hh) fun e2 v2 t2 => ?_
        · rsimp
        · rsimp
        refine Yields.ret ⟨e2, v2, h.length, ?_, by rw [addL]; simpa [Tree.chain] using t2⟩ (by simp)
        rsimp
    · rw [if_neg hlb]
      simpa using hrec (by simp [hlb]) qa qb hqa hqb
  · simp only [hla, ↓reduceIte]
    refine Yields.le (B := 10 + (60 * (la.length + lb.length) + 40)) ?_ (by omega)
    refine Yields.loadChain hh ?_ hb fun qb hqb => ?_
    · rsimp
    by_cases hlb : lb = []
    · rw [if_pos hlb]
      exact hrec (by simp [hla]) qa qb hqa hqb
    · rw [if_neg hlb]
      exact hrec (by simp [hla]) qa qb hqa hqb
termination_by la.length + lb.length
decreasing_by all_goals exact tail_lt ‹_›

/-! ## Two-chain recursion skeleton -/

/-- Load the two argument chains (registers 0 and 1); run `base` when both are
empty and `rec` otherwise, with tails in registers 3, 5 and head digits in 4, 6. -/
def twoChain (base rec : Command p) : Command p :=
  .load (.register 0) 3 15 4 { CompiledTrie.failCases with
    nil := .load (.register 1) 5 15 6 { CompiledTrie.failCases with nil := base, bit := rec }
    bit := .load (.register 1) 5 15 6 { CompiledTrie.failCases with nil := rec, bit := rec } }

theorem Yields.twoChain {code : Code p} {h : Heap} (hh : Valid h) {regs : Registers}
    {base rec : Command p} {ap bp : Ptr} {la lb : List Bool}
    (h0 : regs 0 = .pointer ap) (h1 : regs 1 = .pointer bp)
    (ha : TreeAt h ap (Tree.chain la)) (hb : TreeAt h bp (Tree.chain lb))
    {B : ℕ} {P : Heap → List Value → Prop}
    (hbase : la = [] → lb = [] → ∀ qa qb,
      Yields code h (loaded (loaded regs 3 15 4 qa 0 false) 5 15 6 qb 0 false) base B P)
    (hrec : ¬(la = [] ∧ lb = []) → ∀ qa qb, TreeAt h qa (Tree.chain la.tail) →
      TreeAt h qb (Tree.chain lb.tail) →
      Yields code h (loaded (loaded regs 3 15 4 qa 0 (la.headD false)) 5 15 6 qb 0
        (lb.headD false)) rec B P) :
    Yields code h regs (twoChain base rec) (20 + B) P := by
  refine Yields.le (B := 10 + (10 + B)) ?_ (by omega)
  refine Yields.loadChain hh (by simp [Atom.eval, h0]) ha fun qa hqa => ?_
  by_cases hla : la = []
  · subst hla
    rw [if_pos rfl]
    refine Yields.loadChain hh (by rsimp; exact h1) hb fun qb hqb => ?_
    by_cases hlb : lb = []
    · subst hlb; rw [if_pos rfl]; exact hbase rfl rfl qa qb
    · rw [if_neg hlb]; simpa using hrec (by simp [hlb]) qa qb hqa hqb
  · rw [if_neg hla]
    refine Yields.loadChain hh (by rsimp; exact h1) hb fun qb hqb => ?_
    by_cases hlb : lb = []
    · rw [if_pos hlb]; exact hrec (by simp [hla]) qa qb hqa hqb
    · rw [if_neg hlb]; exact hrec (by simp [hla]) qa qb hqa hqb

/-! ## Comparison -/

def cmpHead : Command p :=
  .branch (.register 4)
    (.branch (.register 6) (.ret [.flag false, .flag true]) (.ret [.flag false, .flag false]))
    (.branch (.register 6) (.ret [.flag true, .flag false]) (.ret [.flag false, .flag true]))

/-- Arguments 0, 1 = chains; results: strictly-less flag and equality flag. -/
def cmpBody (self : Fin p) : Command p :=
  twoChain (.ret [.flag false, .flag true])
    (.call self [.register 3, .register 5] [7, 8]
      (.branch (.register 8) cmpHead (.ret [.register 7, .flag false])))

def cmpBudget (la lb : ℕ) : ℕ := 50 * (la + lb + 1)

/-- The comparison leaves the heap unchanged and returns the two flags. -/
def CmpOut (h : Heap) (r : Bool × Bool) (out : Heap) (outs : List Value) : Prop :=
  out = h ∧ outs = [.flag r.1, .flag r.2]

theorem cmp_compiled (code : Code p) (self : Fin p) (hself : code self = cmpBody self)
    (la lb : List Bool) {h : Heap} (hh : Valid h) {ap bp : Ptr}
    (ha : TreeAt h ap (Tree.chain la)) (hb : TreeAt h bp (Tree.chain lb)) :
    Yields code h (initialRegisters [.pointer ap, .pointer bp]) (code self)
      (cmpBudget la.length lb.length) (CmpOut h (cmpL la lb)) := by
  rw [hself]
  refine Yields.le (B := 20 + (50 * (la.length + lb.length) + 30)) ?_
    (by unfold cmpBudget; omega)
  refine Yields.twoChain hh (by rsimp) (by rsimp) ha hb ?_ ?_
  · intro hla hlb qa qb
    subst hla hlb
    refine Yields.ret ⟨rfl, ?_⟩ (by simp)
    rw [cmpL, dif_pos ⟨rfl, rfl⟩]; rsimp
  · intro hne qa qb hqa hqb
    have ih := cmp_compiled code self hself la.tail lb.tail hh hqa hqb
    have hlt := tail_lt hne
    refine Yields.le (B := 1 + 2 * 2 + cmpBudget la.tail.length lb.tail.length + 14) ?_
      (by unfold cmpBudget; omega)
    refine Yields.call (by rsimp) ih fun mid vals hv => ?_
    obtain ⟨rfl, rfl⟩ := hv
    have hc : cmpL la lb = if (cmpL la.tail lb.tail).2 then
        (!(la.headD false) && lb.headD false, la.headD false == lb.headD false)
        else ((cmpL la.tail lb.tail).1, false) := by rw [cmpL, dif_neg hne]
    cases ht : (cmpL la.tail lb.tail).2
    · refine Yields.le (B := 3 + 5) ?_ (by omega)
      refine Yields.branch (b := false) (by rsimp [ht]) ?_
      refine Yields.ret ⟨rfl, ?_⟩ (by simp)
      rw [hc, ht]; rsimp
    · refine Yields.le (B := 3 + (3 + (3 + 5))) ?_ (by omega)
      refine Yields.branch (b := true) (by rsimp [ht]) ?_
      rw [hc, ht]
      simp only [↓reduceIte]
      cases ha4 : la.headD false <;> cases hb4 : lb.headD false
      · refine Yields.branch (b := false) (by rsimp [ha4]) ?_
        refine Yields.branch (b := false) (by rsimp [hb4]) ?_
        exact Yields.ret ⟨rfl, by rsimp⟩ (by simp)
      · refine Yields.branch (b := false) (by rsimp [ha4]) ?_
        refine Yields.branch (b := true) (by rsimp [hb4]) ?_
        exact Yields.ret ⟨rfl, by rsimp⟩ (by simp)
      · refine Yields.branch (b := true) (by rsimp [ha4]) ?_
        refine Yields.branch (b := false) (by rsimp [hb4]) ?_
        exact Yields.ret ⟨rfl, by rsimp⟩ (by simp)
      · refine Yields.branch (b := true) (by rsimp [ha4]) ?_
        refine Yields.branch (b := true) (by rsimp [hb4]) ?_
        exact Yields.ret ⟨rfl, by rsimp⟩ (by simp)
termination_by la.length + lb.length
decreasing_by exact tail_lt ‹_›

/-! ## Trimmed subtraction -/

def subLeaf (self : Fin p) (a b br : Bool) : Command p :=
  .call self [.register 3, .register 5, .flag (subDigit a b br).2] [7, 8]
    (cond (subDigit a b br).1
      (.allocate 9 (.bit (.flag true) (.register 7)) (.ret [.register 9, .flag false]))
      (.branch (.register 8) (.ret [.null, .flag true])
        (.allocate 9 (.bit (.flag false) (.register 7)) (.ret [.register 9, .flag false]))))

/-- Arguments 0, 1 = chains, 2 = borrow; results: difference chain and zero flag. -/
def subBody (self : Fin p) : Command p :=
  twoChain (.ret [.null, .flag true]) (branch3 4 6 2 (subLeaf self))

def subBudget (la lb : ℕ) : ℕ := 70 * (la + lb + 1)

/-- A stored chain and a flag. -/
def ChainFlag (h : Heap) (r : List Bool × Bool) (out : Heap) (outs : List Value) : Prop :=
  Extends h out ∧ Valid out ∧ ∃ q, outs = [.pointer q, .flag r.2] ∧ TreeAt out q (Tree.chain r.1)

theorem sub_compiled (code : Code p) (self : Fin p) (hself : code self = subBody self)
    (la lb : List Bool) (br : Bool) {h : Heap} (hh : Valid h) {ap bp : Ptr}
    (ha : TreeAt h ap (Tree.chain la)) (hb : TreeAt h bp (Tree.chain lb)) :
    Yields code h (initialRegisters [.pointer ap, .pointer bp, .flag br]) (code self)
      (subBudget la.length lb.length) (ChainFlag h (subL la lb br)) := by
  rw [hself]
  refine Yields.le (B := 20 + (70 * (la.length + lb.length) + 50)) ?_
    (by unfold subBudget; omega)
  refine Yields.twoChain hh (by rsimp) (by rsimp) ha hb ?_ ?_
  · intro hla hlb qa qb
    subst hla hlb
    refine Yields.ret ⟨Extends.refl h, hh, 0, ?_, ?_⟩ (by simp)
    · rw [subL, dif_pos ⟨rfl, rfl⟩]; rsimp
    · rw [subL, dif_pos ⟨rfl, rfl⟩]; exact TreeAt.zero hh
  · intro hne qa qb hqa hqb
    have hlt := tail_lt hne
    have ih := sub_compiled code self hself la.tail lb.tail
      (subDigit (la.headD false) (lb.headD false) br).2 hh hqa hqb
    have hs : subL la lb br =
        if (subL la.tail lb.tail (subDigit (la.headD false) (lb.headD false) br).2).2 &&
          !(subDigit (la.headD false) (lb.headD false) br).1 then ([], true)
        else ((subDigit (la.headD false) (lb.headD false) br).1 ::
          (subL la.tail lb.tail (subDigit (la.headD false) (lb.headD false) br).2).1, false) := by
      rw [subL, dif_neg hne]
    refine Yields.le (B := 9 + (1 + 2 * 3 + subBudget la.tail.length lb.tail.length + 20)) ?_
      (by unfold subBudget; omega)
    refine Yields.branch3 (a := la.headD false) (b := lb.headD false) (c := br)
      (by rsimp) (by rsimp) (by rsimp) ?_
    refine Yields.call (by rsimp) ih fun mid vals hv => ?_
    obtain ⟨hm, vm, q, rfl, tq⟩ := hv
    try simp only [subLeaf]
    cases hd : (subDigit (la.headD false) (lb.headD false) br).1
    · simp only [cond_false]
      cases hz : (subL la.tail lb.tail (subDigit (la.headD false) (lb.headD false) br).2).2
      · refine Yields.le (B := 3 + (8 + 5)) ?_ (by omega)
        refine Yields.branch (b := false) (by rsimp [hz]) ?_
        refine Yields.allocBit vm (b := false) (by rsimp) (by rsimp) tq fun e2 v2 t2 => ?_
        refine Yields.ret ⟨hm.trans e2, v2, mid.length, by rw [hs, hd, hz]; rsimp, ?_⟩ (by simp)
        rw [hs, hd, hz]; simpa [Tree.chain] using t2
      · refine Yields.le (B := 3 + 5) ?_ (by omega)
        refine Yields.branch (b := true) (by rsimp [hz]) ?_
        refine Yields.ret ⟨hm, vm, 0, ?_, ?_⟩ (by simp)
        · rw [hs, hd, hz]; rsimp
        · rw [hs, hd, hz]; exact TreeAt.zero vm
    · simp only [cond_true]
      refine Yields.le (B := 8 + 5) ?_ (by omega)
      refine Yields.allocBit vm (b := true) (by rsimp) (by rsimp) tq fun e2 v2 t2 => ?_
      refine Yields.ret ⟨hm.trans e2, v2, mid.length, ?_, ?_⟩ (by simp)
      · rw [hs, hd]; rsimp
      · rw [hs, hd]; simpa [Tree.chain] using t2
termination_by la.length + lb.length
decreasing_by exact tail_lt ‹_›

/-! ## Length comparison -/

/-- Arguments 0, 1 = chains; result: whether the first has at most as many digits. -/
def lenLeBody (self : Fin p) : Command p :=
  .load (.register 0) 3 15 4 { CompiledTrie.failCases with
    nil := .ret [.flag true]
    bit := .load (.register 1) 5 15 6 { CompiledTrie.failCases with
      nil := .ret [.flag false]
      bit := .call self [.register 3, .register 5] [7] (.ret [.register 7]) } }

def lenLeBudget (la : ℕ) : ℕ := 40 * (la + 1)

theorem lenLe_compiled (code : Code p) (self : Fin p) (hself : code self = lenLeBody self)
    (la lb : List Bool) {h : Heap} (hh : Valid h) {ap bp : Ptr}
    (ha : TreeAt h ap (Tree.chain la)) (hb : TreeAt h bp (Tree.chain lb)) :
    Yields code h (initialRegisters [.pointer ap, .pointer bp]) (code self)
      (lenLeBudget la.length)
      (fun out outs => out = h ∧ outs = [.flag (decide (la.length ≤ lb.length))]) := by
  rw [hself]
  refine Yields.le (B := 10 + (40 * la.length + 30)) ?_ (by unfold lenLeBudget; omega)
  refine Yields.loadChain hh (by rsimp) ha fun qa hqa => ?_
  by_cases hla : la = []
  · subst hla; rw [if_pos rfl]
    exact Yields.ret ⟨rfl, by rsimp⟩ (by simp)
  · rw [if_neg hla]
    obtain ⟨a, as, rfl⟩ := List.exists_cons_of_ne_nil hla
    simp only [List.tail_cons] at hqa
    refine Yields.le (B := 10 + (40 * as.length + 60)) ?_ (by simp only [List.length_cons]; omega)
    refine Yields.loadChain hh (by rsimp) hb fun qb hqb => ?_
    by_cases hlb : lb = []
    · subst hlb; rw [if_pos rfl]
      exact Yields.ret ⟨rfl, by rsimp⟩ (by simp)
    · rw [if_neg hlb]
      obtain ⟨b, bs, rfl⟩ := List.exists_cons_of_ne_nil hlb
      try simp only [List.tail_cons] at hqb
      have ih := lenLe_compiled code self hself as bs hh hqa hqb
      refine Yields.le (B := 1 + 2 * 2 + lenLeBudget as.length + 3) ?_
        (by unfold lenLeBudget; omega)
      refine Yields.call (by rsimp) ih fun mid vals hv => ?_
      obtain ⟨rfl, rfl⟩ := hv
      exact Yields.ret ⟨rfl, by rsimp⟩ (by simp)
termination_by la.length
decreasing_by all_goals (simp_all; try omega)

/-! ## Multiplication -/

/-- Arguments 0, 1 = chains; result: the product chain `mulL`, recursing on the
first argument. -/
def mulBody (self add : Fin p) : Command p :=
  .load (.register 0) 3 15 4 { CompiledTrie.failCases with
    nil := .ret [.null]
    bit := .call self [.register 3, .register 1] [5]
      (.load (.register 5) 6 15 7 { CompiledTrie.failCases with
        nil := .branch (.register 4) (.ret [.register 1]) (.ret [.null])
        bit := .allocate 8 (.bit (.flag false) (.register 5))
          (.branch (.register 4)
            (.call add [.register 8, .register 1, .flag false] [9] (.ret [.register 9]))
            (.ret [.register 8])) }) }

def mulBudget (la lb : ℕ) : ℕ := 200 * (la + 1) * (la + lb + 1)

theorem mulBudget_succ (n m : ℕ) :
    mulBudget (n + 1) m = mulBudget n m + 200 * (2 * n + m + 3) := by unfold mulBudget; ring

theorem mul_compiled (code : Code p) (self add : Fin p) (hself : code self = mulBody self add)
    (hadd : code add = addBody add)
    (la lb : List Bool) {h : Heap} (hh : Valid h) {ap bp : Ptr}
    (ha : TreeAt h ap (Tree.chain la)) (hb : TreeAt h bp (Tree.chain lb)) :
    Yields code h (initialRegisters [.pointer ap, .pointer bp]) (code self)
      (mulBudget la.length lb.length) (Returns h (Tree.chain (mulL la lb))) := by
  rw [hself]
  have h10 : 10 ≤ mulBudget la.length lb.length := by
    unfold mulBudget; nlinarith
  refine Yields.le (B := 10 + (mulBudget la.length lb.length - 10)) ?_ (by omega)
  refine Yields.loadChain hh (by rsimp) ha fun qa hqa => ?_
  by_cases hla : la = []
  · subst hla; rw [if_pos rfl]
    refine Yields.ret ⟨Extends.refl h, hh, 0, by rsimp, by simp [mulL]; exact TreeAt.zero hh⟩
      (by unfold mulBudget; simp; omega)
  · rw [if_neg hla]
    obtain ⟨a, as, rfl⟩ := List.exists_cons_of_ne_nil hla
    simp only [List.headD_cons, List.tail_cons] at hqa ⊢
    have ih := mul_compiled code self add hself hadd as lb hh hqa hb
    have hpl := mulL_length as lb
    have hsucc := mulBudget_succ as.length lb.length
    refine Yields.le (B := 1 + 2 * 2 + mulBudget as.length lb.length +
        (10 + (8 + (3 + (1 + 2 * 3 + addBudget (as.length * 2 + lb.length + 1) lb.length + 3)))))
      ?_ (by simp only [List.length_cons, hsucc]; unfold addBudget; omega)
    refine Yields.callTree (by rsimp) ih fun mid q hm vm tq => ?_
    refine Yields.loadChain vm (by rsimp) tq fun q2 _ => ?_
    by_cases hp : mulL as lb = []
    · rw [if_pos hp]
      cases a
      · refine Yields.le (B := 3 + 3) ?_ (by omega)
        refine Yields.branch (b := false) (by rsimp) ?_
        refine Yields.ret ⟨hm, vm, 0, by rsimp, ?_⟩ (by simp)
        simp only [mulL, Bool.false_eq_true, ↓reduceIte, hp, shiftL]
        exact TreeAt.zero vm
      · refine Yields.le (B := 3 + 3) ?_ (by omega)
        refine Yields.branch (b := true) (by rsimp) ?_
        refine Yields.ret ⟨hm, vm, bp, by rsimp, ?_⟩ (by simp)
        simp only [mulL, ↓reduceIte, hp, shiftL, and_self, addL_nil_left]
        exact hb.mono hm
    · rw [if_neg hp]
      have hs : shiftL false (mulL as lb) = false :: mulL as lb := by simp [shiftL, hp]
      refine Yields.allocBit vm (b := false) (by rsimp) (by rsimp) tq fun e2 v2 t2 => ?_
      cases a
      · refine Yields.le (B := 3 + 3) ?_ (by omega)
        refine Yields.branch (b := false) (by rsimp) ?_
        refine Yields.ret ⟨hm.trans e2, v2, mid.length, by rsimp, ?_⟩ (by simp)
        simp only [mulL, Bool.false_eq_true, ↓reduceIte, hs]
        simpa [Tree.chain] using t2
      · refine Yields.branch (b := true) (by rsimp) ?_
        have hadd' := add_compiled code add hadd (false :: mulL as lb) lb false v2
          (by simpa [Tree.chain] using t2) (hb.mono (hm.trans e2))
        have hlen : (false :: mulL as lb).length ≤ as.length * 2 + lb.length + 1 := by
          simp; omega
        refine Yields.callTree (by rsimp) (hadd'.le (B' := addBudget (as.length * 2 + lb.length + 1)
            lb.length) (by unfold addBudget; omega)) fun mid2 q3 hm2 vm2 tq2 => ?_
        refine Yields.ret ⟨hm.trans (e2.trans hm2), vm2, q3, by rsimp, ?_⟩ (by simp)
        simp only [mulL, ↓reduceIte, hs]
        exact tq2
termination_by la.length
decreasing_by all_goals (simp_all; try omega)

/-! ## Division -/

def divShiftQ (r : Register) (dst : Register) (next : Command p) : Command p :=
  .load (.register r) 12 15 13 { CompiledTrie.failCases with
    nil := .copy dst .null next
    bit := .allocate dst (.bit (.flag false) (.register r)) next }

def divCont (cmp sub : Fin p) : Command p :=
  .call cmp [.register 9, .register 1] [10, 11]
    (.branch (.register 10)
      (divShiftQ 5 14 (.ret [.register 14, .register 9]))
      (.allocate 14 (.bit (.flag true) (.register 5))
        (.call sub [.register 9, .register 1, .flag false] [15, 12]
          (.ret [.register 14, .register 15]))))

/-- Arguments 0 = dividend chain, 1 = divisor chain; results: quotient and
remainder chains of `divmodL`. -/
def divBody (self cmp sub : Fin p) : Command p :=
  .load (.register 0) 3 15 4 { CompiledTrie.failCases with
    nil := .ret [.null, .null]
    bit := .call self [.register 3, .register 1] [5, 6]
      (.load (.register 6) 7 15 8 { CompiledTrie.failCases with
        nil := .branch (.register 4)
          (.allocate 9 (.bit (.flag true) (.register 6)) (divCont cmp sub))
          (.copy 9 .null (divCont cmp sub))
        bit := .allocate 9 (.bit (.register 4) (.register 6)) (divCont cmp sub) }) }

def divBudget (la lb : ℕ) : ℕ := 400 * (la + 1) * (lb + 2)

/-- Two stored chains. -/
def TwoChains (h : Heap) (r : List Bool × List Bool) (out : Heap) (outs : List Value) : Prop :=
  Extends h out ∧ Valid out ∧ ∃ q s, outs = [.pointer q, .pointer s] ∧
    TreeAt out q (Tree.chain r.1) ∧ TreeAt out s (Tree.chain r.2)

theorem divCont_yields (code : Code p) (cmp sub : Fin p) (hcmp : code cmp = cmpBody cmp)
    (hsub : code sub = subBody sub) {h : Heap} (hh : Valid h) {regs : Registers}
    {bp qp rp : Ptr} {lb lq lr : List Bool} (h1 : regs 1 = .pointer bp) (h5 : regs 5 = .pointer qp)
    (h9 : regs 9 = .pointer rp) (hb : TreeAt h bp (Tree.chain lb))
    (hq : TreeAt h qp (Tree.chain lq)) (hr : TreeAt h rp (Tree.chain lr)) :
    Yields code h regs (divCont cmp sub)
      (60 + cmpBudget lr.length lb.length + subBudget lr.length lb.length)
      (TwoChains h (if (cmpL lr lb).1 then (shiftL false lq, lr)
        else (shiftL true lq, (subL lr lb false).1))) := by
  have hc := cmp_compiled code cmp hcmp lr lb hh hr hb
  refine Yields.le (B := 1 + 2 * 2 + cmpBudget lr.length lb.length +
    (26 + subBudget lr.length lb.length)) ?_ (by omega)
  refine Yields.call (by rsimp [h9, h1]) hc fun mid vals hv => ?_
  obtain ⟨hmid, rfl⟩ := hv
  rw [hmid]
  cases hlt : (cmpL lr lb).1
  · refine Yields.le (B := 3 + (8 + (1 + 2 * 3 + subBudget lr.length lb.length + 5))) ?_
      (by omega)
    refine Yields.branch (b := false) (by rsimp [hlt]) ?_
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine Yields.allocBit hh (b := true) (by rsimp) (by rsimp [h5]) hq fun e2 v2 t2 => ?_
    have hs := sub_compiled code sub hsub lr lb false v2 (hr.mono e2) (hb.mono e2)
    refine Yields.call (by rsimp [h9, h1]) hs fun mid2 vals2 hv2 => ?_
    obtain ⟨hm2, vm2, s2, rfl, ts2⟩ := hv2
    refine Yields.ret ⟨e2.trans hm2, vm2, h.length, s2, by rsimp, ?_, ts2⟩ (by simp)
    simpa [shiftL, Tree.chain] using t2.mono hm2
  · refine Yields.le (B := 3 + (10 + 13)) ?_ (by omega)
    refine Yields.branch (b := true) (by rsimp [hlt]) ?_
    simp only [↓reduceIte]
    refine Yields.loadChain hh (by rsimp [h5]) hq fun _ _ => ?_
    by_cases hlq : lq = []
    · subst hlq; rw [if_pos rfl]
      refine Yields.le (B := 3 + 5) ?_ (by omega)
      refine Yields.copy ?_
      refine Yields.ret ⟨Extends.refl h, hh, 0, rp, by rsimp [h9], ?_, hr⟩ (by simp)
      simpa [shiftL, Tree.chain] using TreeAt.zero hh
    · rw [if_neg hlq]
      refine Yields.le (B := 8 + 5) ?_ (by omega)
      refine Yields.allocBit hh (b := false) (by rsimp) (by rsimp [h5]) hq fun e2 v2 t2 => ?_
      refine Yields.ret ⟨e2, v2, h.length, rp, by rsimp [h9], ?_, hr.mono e2⟩ (by simp)
      simpa [shiftL, hlq, Tree.chain] using t2

theorem div_compiled (code : Code p) (self cmp sub : Fin p)
    (hself : code self = divBody self cmp sub) (hcmp : code cmp = cmpBody cmp)
    (hsub : code sub = subBody sub)
    (la lb : List Bool) (hbn : Norm lb) (hbp : 0 < lval lb) {h : Heap} (hh : Valid h)
    {ap bp : Ptr} (ha : TreeAt h ap (Tree.chain la)) (hb : TreeAt h bp (Tree.chain lb)) :
    Yields code h (initialRegisters [.pointer ap, .pointer bp]) (code self)
      (divBudget la.length lb.length) (TwoChains h (divmodL la lb)) := by
  rw [hself]
  refine Yields.le (B := 10 + (divBudget la.length lb.length - 10)) ?_
    (by unfold divBudget; have : 10 ≤ 400 * (la.length + 1) * (lb.length + 2) := by nlinarith
        omega)
  refine Yields.loadChain hh (by rsimp) ha fun qa hqa => ?_
  by_cases hla : la = []
  · subst hla; rw [if_pos rfl]
    refine Yields.ret ⟨Extends.refl h, hh, 0, 0, by rsimp, ?_, ?_⟩
      (by unfold divBudget; simp; omega)
    · simpa [divmodL, Tree.chain] using TreeAt.zero hh
    · simpa [divmodL, Tree.chain] using TreeAt.zero hh
  · rw [if_neg hla]
    obtain ⟨x, as, rfl⟩ := List.exists_cons_of_ne_nil hla
    simp only [List.headD_cons, List.tail_cons] at hqa ⊢
    have ih := div_compiled code self cmp sub hself hcmp hsub as lb hbn hbp hh hqa hb
    have hrl := divmodL_rem_length as hbn hbp
    have hr2 : (shiftL x (divmodL as lb).2).length ≤ lb.length + 1 := by
      have := shiftL_length x (divmodL as lb).2; omega
    have hbudget : 1 + 2 * 2 + divBudget as.length lb.length + (10 + (3 + (8 +
        (60 + cmpBudget (lb.length + 1) lb.length + subBudget (lb.length + 1) lb.length))))
        ≤ divBudget (as.length + 1) lb.length - 10 := by
      unfold divBudget cmpBudget subBudget
      have h1 : 400 * (as.length + 1 + 1) * (lb.length + 2) =
          400 * (as.length + 1) * (lb.length + 2) + 400 * (lb.length + 2) := by ring
      omega
    refine Yields.le (B := 1 + 2 * 2 + divBudget as.length lb.length + (10 + (3 + (8 +
        (60 + cmpBudget (lb.length + 1) lb.length + subBudget (lb.length + 1) lb.length)))))
      ?_ (by simpa using hbudget)
    refine Yields.call (by rsimp) ih fun mid vals hv => ?_
    obtain ⟨hm, vm, q, r, rfl, tq, tr⟩ := hv
    have hcont : ∀ {h' : Heap} {regs : Registers} {rp : Ptr}, Valid h' → Extends mid h' →
        regs 1 = .pointer bp → regs 5 = .pointer q → regs 9 = .pointer rp →
        TreeAt h' rp (Tree.chain (shiftL x (divmodL as lb).2)) →
        Yields code h' regs (divCont cmp sub)
          (60 + cmpBudget (lb.length + 1) lb.length + subBudget (lb.length + 1) lb.length)
          (TwoChains h (divmodL (x :: as) lb)) := by
      intro h' regs rp vh' he' r1 r5 r9 trp
      have hy := divCont_yields code cmp sub hcmp hsub vh' r1 r5 r9 ((hb.mono hm).mono he')
        (tq.mono he') trp
      refine hy.mono (by unfold cmpBudget subBudget; omega) fun out outs ho => ?_
      obtain ⟨ho1, ho2, rest⟩ := ho
      refine ⟨hm.trans (he'.trans ho1), ho2, ?_⟩
      rw [divmodL]
      exact rest
    refine Yields.loadChain vm (by rsimp) tr fun _ _ => ?_
    by_cases hr : (divmodL as lb).2 = []
    · rw [if_pos hr]
      cases x
      · refine Yields.le (B := 3 + (3 + (60 + cmpBudget (lb.length + 1) lb.length +
          subBudget (lb.length + 1) lb.length))) ?_ (by omega)
        refine Yields.branch (b := false) (by rsimp) ?_
        refine Yields.copy (hcont (rp := 0) vm (Extends.refl _) (by rsimp) (by rsimp) (by rsimp) ?_)
        rw [hr]; simpa [shiftL, Tree.chain] using TreeAt.zero vm
      · refine Yields.branch (b := true) (by rsimp) ?_
        refine Yields.allocBit vm (b := true) (by rsimp) (by rsimp) tr fun e2 v2 t2 =>
          hcont (rp := mid.length) v2 e2 (by rsimp) (by rsimp) (by rsimp) ?_
        rw [hr] at t2 ⊢; simpa [shiftL, Tree.chain] using t2
    · rw [if_neg hr]
      refine Yields.le (B := 8 + (60 + cmpBudget (lb.length + 1) lb.length +
          subBudget (lb.length + 1) lb.length)) ?_ (by omega)
      refine Yields.allocBit vm (b := x) (by rsimp) (by rsimp) tr fun e2 v2 t2 =>
        hcont (rp := mid.length) v2 e2 (by rsimp) (by rsimp) (by rsimp) ?_
      simpa [shiftL, hr, Tree.chain] using t2
termination_by la.length
decreasing_by all_goals (simp_all; try omega)

/-! ## Halving a chain and its binary length -/

/-- Argument 0 = chain; results: a chain of `⌊length/2⌋` zero digits and the
parity of the length. -/
def halveBody (self : Fin p) : Command p :=
  .load (.register 0) 3 15 4 { CompiledTrie.failCases with
    nil := .ret [.null, .flag false]
    bit := .load (.register 3) 5 15 6 { CompiledTrie.failCases with
      nil := .ret [.null, .flag true]
      bit := .call self [.register 5] [7, 8]
        (.allocate 9 (.bit (.flag false) (.register 7)) (.ret [.register 9, .register 8])) } }

def halveBudget (l : ℕ) : ℕ := 40 * (l + 1)

theorem halve_compiled (code : Code p) (self : Fin p) (hself : code self = halveBody self)
    (l : List Bool) {h : Heap} (hh : Valid h) {ap : Ptr} (ha : TreeAt h ap (Tree.chain l)) :
    Yields code h (initialRegisters [.pointer ap]) (code self) (halveBudget l.length)
      (ChainFlag h (List.replicate (l.length / 2) false, decide (l.length % 2 = 1))) := by
  rw [hself]
  refine Yields.le (B := 10 + (40 * l.length + 30)) ?_ (by unfold halveBudget; omega)
  refine Yields.loadChain hh (by rsimp) ha fun q1 hq1 => ?_
  by_cases hl : l = []
  · subst hl; rw [if_pos rfl]
    exact Yields.ret ⟨Extends.refl h, hh, 0, by rsimp, by simpa using TreeAt.zero hh⟩ (by simp)
  · rw [if_neg hl]
    obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hl
    simp only [List.tail_cons] at hq1
    refine Yields.le (B := 10 + (40 * t.length + 20)) ?_ (by simp; omega)
    refine Yields.loadChain hh (by rsimp) hq1 fun q2 hq2 => ?_
    by_cases ht : t = []
    · subst ht; rw [if_pos rfl]
      exact Yields.ret ⟨Extends.refl h, hh, 0, by rsimp, by simpa using TreeAt.zero hh⟩ (by simp)
    · rw [if_neg ht]
      obtain ⟨b, u, rfl⟩ := List.exists_cons_of_ne_nil ht
      simp only [List.tail_cons] at hq2
      have ih := halve_compiled code self hself u hh hq2
      refine Yields.le (B := 1 + 2 * 1 + halveBudget u.length + (8 + 5)) ?_
        (by unfold halveBudget; simp; omega)
      refine Yields.call (by rsimp) ih fun mid vals hv => ?_
      obtain ⟨hm, vm, q, rfl, tq⟩ := hv
      refine Yields.allocBit vm (b := false) (by rsimp) (by rsimp) tq fun e2 v2 t2 => ?_
      refine Yields.ret ⟨hm.trans e2, v2, mid.length, ?_, ?_⟩ (by simp)
      · rsimp; omega
      · have : (u.length + 1 + 1) / 2 = u.length / 2 + 1 := by omega
        simp only [List.length_cons, this, List.replicate_succ]
        simpa [Tree.chain] using t2
termination_by l.length
decreasing_by all_goals simp_all

/-- Argument 0 = chain; result: the digit chain of its length. -/
def sizeBody (self halve : Fin p) : Command p :=
  .load (.register 0) 3 15 4 { CompiledTrie.failCases with
    nil := .ret [.null]
    bit := .call halve [.register 0] [5, 6]
      (.call self [.register 5] [7]
        (.allocate 8 (.bit (.register 6) (.register 7)) (.ret [.register 8]))) }

def sizeBudget (l : ℕ) : ℕ := 200 * l + 30

theorem bits_halve (L : ℕ) (hL : 0 < L) :
    L.bits = decide (L % 2 = 1) :: (L / 2).bits := by
  rcases Nat.even_or_odd' L with ⟨k, rfl | rfl⟩
  · have hk : k ≠ 0 := by omega
    rw [Nat.bit0_bits k hk]
    have h1 : 2 * k / 2 = k := by omega
    have h2 : 2 * k % 2 = 0 := by omega
    rw [h1, h2]; rfl
  · rw [Nat.bit1_bits k]
    have h1 : (2 * k + 1) / 2 = k := by omega
    have h2 : (2 * k + 1) % 2 = 1 := by omega
    rw [h1, h2]; rfl

theorem size_compiled (code : Code p) (self halve : Fin p)
    (hself : code self = sizeBody self halve) (hhalve : code halve = halveBody halve)
    (l : List Bool) {h : Heap} (hh : Valid h) {ap : Ptr} (ha : TreeAt h ap (Tree.chain l)) :
    Yields code h (initialRegisters [.pointer ap]) (code self) (sizeBudget l.length)
      (Returns h (Tree.chain l.length.bits)) := by
  rw [hself]
  refine Yields.le (B := 10 + (sizeBudget l.length - 10)) ?_ (by unfold sizeBudget; omega)
  refine Yields.loadChain hh (by rsimp) ha fun _ _ => ?_
  by_cases hl : l = []
  · subst hl; rw [if_pos rfl]
    exact Yields.ret ⟨Extends.refl h, hh, 0, by rsimp, by simpa using TreeAt.zero hh⟩
      (by unfold sizeBudget; simp)
  · rw [if_neg hl]
    have hpos : 0 < l.length := List.length_pos_iff.mpr hl
    have hv := halve_compiled code halve hhalve l hh ha
    refine Yields.le (B := 1 + 2 * 1 + halveBudget l.length +
      (1 + 2 * 1 + sizeBudget (l.length / 2) + (8 + 3))) ?_
      (by unfold halveBudget sizeBudget; omega)
    refine Yields.call (by rsimp) hv fun mid vals hv => ?_
    obtain ⟨hm, vm, q, rfl, tq⟩ := hv
    have ih := size_compiled code self halve hself hhalve
      (List.replicate (l.length / 2) false) vm tq
    rw [List.length_replicate] at ih
    refine Yields.callTree (by rsimp) ih fun mid2 q2 hm2 vm2 tq2 => ?_
    refine Yields.allocBit vm2 (b := decide (l.length % 2 = 1)) (by rsimp) (by rsimp) tq2
      fun e3 v3 t3 => ?_
    refine Yields.ret ⟨hm.trans (hm2.trans e3), v3, mid2.length, by rsimp, ?_⟩ (by simp)
    rw [bits_halve _ hpos]
    simpa [Tree.chain] using t3
termination_by l.length
decreasing_by
  rw [List.length_replicate]
  have : 0 < l.length := List.length_pos_iff.mpr hl
  omega

end MWIS.Fun.Arith

end
