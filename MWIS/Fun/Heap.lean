module

public import MWIS.Fun.Core
public import MWIS.RegisterFlagKeys
public import MWIS.CompiledTrie
public import Mathlib.Data.Nat.Bits

/-!
# Heap representations of `Fun` values and expressions

Every `Fun` value, environment and expression is stored as an immutable cell
tree. `TreeAt h p t` says that the cells reachable from address `p` have exactly
the shape of `t`; subtrees may be shared. Integers are a sign cell over the
least-significant-first binary digits of the absolute value (`Nat.bits`, so the
chain is normalized and has exactly `bits z` cells); booleans are a bit cell;
pairs are pair cells; lists are cons spines ending in a nil cell; raw trees are
stored as themselves. An expression is a pair cell of a unary constructor tag
and its payload.
-/

@[expose] public section

namespace MWIS.Fun

open MWIS.PointerMemory MWIS.RegisterMachine

/-! ## Exact cell trees -/

/-- The cells reachable from `p` form exactly the tree `t`. -/
inductive TreeAt (h : Heap) : Ptr → Tree → Prop
  | nil {p : Ptr} (cell : h[p]? = some .nil) : TreeAt h p .nil
  | bit {p q : Ptr} {b : Bool} {t : Tree} (cell : h[p]? = some (.bit b q))
      (tail : TreeAt h q t) : TreeAt h p (.bit b t)
  | cons {p a q : Ptr} {x t : Tree} (cell : h[p]? = some (.cons a q))
      (head : TreeAt h a x) (tail : TreeAt h q t) : TreeAt h p (.cons x t)
  | fork {p a q : Ptr} {x t : Tree} (cell : h[p]? = some (.fork a q))
      (left : TreeAt h a x) (right : TreeAt h q t) : TreeAt h p (.fork x t)
  | bucket {p q : Ptr} {t : Tree} (cell : h[p]? = some (.bucket q))
      (items : TreeAt h q t) : TreeAt h p (.bucket t)
  | pair {p a q : Ptr} {x t : Tree} (cell : h[p]? = some (.pair a q))
      (first : TreeAt h a x) (second : TreeAt h q t) : TreeAt h p (.pair x t)

theorem TreeAt.mono {a b : Heap} (hab : Extends a b) {p : Ptr} {t : Tree}
    (h : TreeAt a p t) : TreeAt b p t := by
  induction h with
  | nil c => exact .nil (hab.lookup c)
  | bit c _ ih => exact .bit (hab.lookup c) ih
  | cons c _ _ ih1 ih2 => exact .cons (hab.lookup c) ih1 ih2
  | fork c _ _ ih1 ih2 => exact .fork (hab.lookup c) ih1 ih2
  | bucket c _ ih => exact .bucket (hab.lookup c) ih
  | pair c _ _ ih1 ih2 => exact .pair (hab.lookup c) ih1 ih2

theorem lookup_allocated {h : Heap} {p : Ptr} {c : Cell} (hc : h[p]? = some c) :
    p < h.length := (List.getElem?_eq_some_iff.mp hc).1

theorem TreeAt.allocated {h : Heap} {p : Ptr} {t : Tree} (ht : TreeAt h p t) :
    p < h.length := by
  cases ht <;> exact lookup_allocated (by assumption)

/-- The shared empty cell at address zero. -/
theorem TreeAt.zero {h : Heap} (hh : Valid h) : TreeAt h 0 .nil := .nil hh.1

/-! ## Allocation -/

/-- One allocation of a cell whose fields are allocated. -/
theorem alloc {h : Heap} (hh : Valid h) (c : Cell) (hc : ∀ q ∈ c.references, q < h.length) :
    Extends h (h ++ [c]) ∧ Valid (h ++ [c]) ∧ (h ++ [c])[h.length]? = some c := by
  have hs := safe_allocate h hh c hc
  refine ⟨hs.1, hs.2.1, ?_⟩
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp

theorem alloc_bitT {h : Heap} (hh : Valid h) (b : Bool) {q : Ptr} {t : Tree}
    (ht : TreeAt h q t) :
    Extends h (h ++ [.bit b q]) ∧ Valid (h ++ [.bit b q]) ∧
      TreeAt (h ++ [.bit b q]) h.length (.bit b t) := by
  obtain ⟨he, hv, hc⟩ := alloc hh (.bit b q) (by
    intro x hx; simp only [Cell.references, List.mem_singleton] at hx; exact hx ▸ ht.allocated)
  exact ⟨he, hv, .bit hc (ht.mono he)⟩

theorem alloc_consT {h : Heap} (hh : Valid h) {a q : Ptr} {x t : Tree}
    (ha : TreeAt h a x) (ht : TreeAt h q t) :
    Extends h (h ++ [.cons a q]) ∧ Valid (h ++ [.cons a q]) ∧
      TreeAt (h ++ [.cons a q]) h.length (.cons x t) := by
  obtain ⟨he, hv, hc⟩ := alloc hh (.cons a q) (by
    intro y hy; simp only [Cell.references, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact ha.allocated
    · exact ht.allocated)
  exact ⟨he, hv, .cons hc (ha.mono he) (ht.mono he)⟩

theorem alloc_pairT {h : Heap} (hh : Valid h) {a q : Ptr} {x t : Tree}
    (ha : TreeAt h a x) (ht : TreeAt h q t) :
    Extends h (h ++ [.pair a q]) ∧ Valid (h ++ [.pair a q]) ∧
      TreeAt (h ++ [.pair a q]) h.length (.pair x t) := by
  obtain ⟨he, hv, hc⟩ := alloc hh (.pair a q) (by
    intro y hy; simp only [Cell.references, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact ha.allocated
    · exact ht.allocated)
  exact ⟨he, hv, .pair hc (ha.mono he) (ht.mono he)⟩

/-! ## Binary digit chains -/

/-- A chain of bit cells holding the given bits, ending in a nil cell. -/
def Tree.chain : List Bool → Tree
  | [] => .nil
  | b :: bs => .bit b (Tree.chain bs)

@[simp] theorem Tree.chain_nil : Tree.chain [] = .nil := rfl
@[simp] theorem Tree.chain_cons (b : Bool) (l : List Bool) :
    Tree.chain (b :: l) = .bit b (Tree.chain l) := rfl

/-- The value of a least-significant-first digit list. -/
def lval : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * lval bs

/-- A digit list is normalized when it is empty or its last digit is one. -/
def Norm (l : List Bool) : Prop := ∀ hne : l ≠ [], l.getLast hne = true

theorem Norm.nil : Norm [] := fun h => absurd rfl h

theorem Norm.tail {b : Bool} {l : List Bool} (h : Norm (b :: l)) : Norm l := by
  intro hne
  have := h (List.cons_ne_nil _ _)
  rwa [List.getLast_cons hne] at this

theorem Norm.cons {b : Bool} {l : List Bool} (h : Norm l) (hb : l = [] → b = true) :
    Norm (b :: l) := by
  intro _
  by_cases hl : l = []
  · subst hl; simpa using hb rfl
  · rw [List.getLast_cons hl]; exact h hl

theorem Norm.single_true {l : List Bool} (h : Norm (false :: l)) : l ≠ [] := by
  rintro rfl; simpa using h (List.cons_ne_nil _ _)

theorem lval_pos {l : List Bool} (h : Norm l) (hne : l ≠ []) : 0 < lval l := by
  induction l with
  | nil => exact absurd rfl hne
  | cons b l ih =>
    by_cases hl : l = []
    · subst hl; have := h (List.cons_ne_nil _ _); simp at this; simp [lval, this]
    · have := ih h.tail hl; simp only [lval]; omega

/-- A normalized digit list is the binary expansion of its value. -/
theorem norm_eq_bits {l : List Bool} (h : Norm l) : l = (lval l).bits := by
  induction l with
  | nil => simp [lval]
  | cons b l ih =>
    have hl := ih h.tail
    cases b with
    | true =>
      simp only [lval, ↓reduceIte]
      rw [show 1 + 2 * lval l = 2 * lval l + 1 by omega, Nat.bit1_bits, ← hl]
    | false =>
      have hne := h.single_true
      have hp := lval_pos h.tail hne
      simp only [lval, Bool.false_eq_true, ↓reduceIte, zero_add]
      rw [Nat.bit0_bits _ (by omega), ← hl]

theorem lval_bits (n : ℕ) : lval n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [lval]
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn]
    cases b <;> simp [lval, ih, Nat.bit] <;> omega

theorem bits_norm (n : ℕ) : Norm n.bits := by
  induction n using Nat.binaryRec' with
  | zero => exact Norm.nil
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn]
    refine ih.cons fun h => hn ?_
    have := congrArg lval h
    rw [lval_bits] at this
    simpa [lval] using this

theorem bits_length (n : ℕ) : n.bits.length = n.size := Nat.size_eq_bits_len n

/-- Normalized lists with equal values are equal. -/
theorem norm_ext {l l' : List Bool} (h : Norm l) (h' : Norm l') (hv : lval l = lval l') :
    l = l' := by rw [norm_eq_bits h, norm_eq_bits h', hv]

/-! ## Values, environments and expressions -/

/-- The stored integer: a sign cell over the digit chain of the absolute value. -/
def reprInt (z : ℤ) : Tree := .bit (decide (z < 0)) (Tree.chain z.natAbs.bits)

/-- The cell tree of a value. -/
def rep : (τ : Ty) → τ.denote → Tree
  | .int, z => reprInt z
  | .bool, b => .bit b .nil
  | .unit, _ => .nil
  | .tree, t => t
  | .prod a b, x => .pair (rep a x.1) (rep b x.2)
  | .list a, xs => Tree.ofList (xs.map (rep a))

/-- The value `v` of type `τ` is stored at `p`. -/
def ValAt (τ : Ty) (h : Heap) (p : Ptr) (v : τ.denote) : Prop := TreeAt h p (rep τ v)

/-- The cell tree of an environment: a cons spine of its values. -/
def envTree : (Γ : List Ty) → Env Γ → Tree
  | [], _ => .nil
  | τ :: Γ, e => .cons (rep τ e.1) (envTree Γ e.2)

/-- The environment `env` is stored at `p`. -/
def EnvAt (Γ : List Ty) (h : Heap) (p : Ptr) (env : Env Γ) : Prop :=
  TreeAt h p (envTree Γ env)

theorem ValAt.mono {τ : Ty} {a b : Heap} (hab : Extends a b) {p : Ptr} {v : τ.denote}
    (h : ValAt τ a p v) : ValAt τ b p v := TreeAt.mono hab h

theorem EnvAt.mono {Γ : List Ty} {a b : Heap} (hab : Extends a b) {p : Ptr} {env : Env Γ}
    (h : EnvAt Γ a p env) : EnvAt Γ b p env := TreeAt.mono hab h

/-- A unary chain of `k` bit cells: the constructor tag of an expression node. -/
def unary : ℕ → Tree
  | 0 => .nil
  | k + 1 => .bit false (unary k)

/-- An expression node with tag `k`. -/
def node (k : ℕ) (payload : Tree) : Tree := .pair (unary k) payload

/-- Tag offset of an integer operation. -/
def IntOp.tag : IntOp → ℕ
  | .add => 4 | .sub => 5 | .mul => 6 | .div => 7 | .mod => 8

/-- Tag offset of a comparison. -/
def CmpOp.tag : CmpOp → ℕ
  | .lt => 9 | .le => 10 | .eq => 11

/-- The stored form of an expression. -/
def Expr.encode {Γ : List Ty} {τ : Ty} : Expr Γ τ → Tree
  | .var v => node 0 (unary v.index)
  | .int z => node 1 (reprInt z)
  | .bool b => node 2 (.bit b .nil)
  | .unit => node 3 .nil
  | .arith op x y => node op.tag (.pair x.encode y.encode)
  | .cmp op x y => node op.tag (.pair x.encode y.encode)
  | .ite c t e => node 12 (.pair c.encode (.pair t.encode e.encode))
  | .pair x y => node 13 (.pair x.encode y.encode)
  | .fst p => node 14 p.encode
  | .snd p => node 15 p.encode
  | .nil => node 16 .nil
  | .cons x xs => node 17 (.pair x.encode xs.encode)
  | .listCase xs n c => node 18 (.pair xs.encode (.pair n.encode c.encode))
  | .foldl xs i s => node 19 (.pair xs.encode (.pair i.encode s.encode))
  | .iter n i s => node 20 (.pair n.encode (.pair i.encode s.encode))
  | .letE x b => node 21 (.pair x.encode b.encode)
  | .treeCase t a b c d e f => node 22 (.pair t.encode (.pair a.encode (.pair b.encode
      (.pair c.encode (.pair d.encode (.pair e.encode f.encode))))))
  | .treeNil => node 23 .nil
  | .treeBit b t => node 24 (.pair b.encode t.encode)
  | .treeCons x t => node 25 (.pair x.encode t.encode)
  | .treePair x y => node 26 (.pair x.encode y.encode)
  | .items t => node 27 t.encode
  | .ofItems ts => node 28 ts.encode
  | .wordValue t => node 29 t.encode
  | .word w k => node 30 (.pair w.encode k.encode)
  | .size x => node 31 x.encode

end MWIS.Fun

end
