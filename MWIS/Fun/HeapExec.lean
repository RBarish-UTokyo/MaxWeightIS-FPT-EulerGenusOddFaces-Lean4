module

public import MWIS.Fun.Heap

/-!
# Execution lemmas for stored trees

`Yields code h regs cmd B P` says that the command, started on heap `h` with
registers `regs`, returns within `B` events with a final heap and output values
satisfying `P`. The lemmas below compose loads of cells of known tree shape,
branches, allocations, calls and returns. Register contents after a load are
explicit updates, so that later register lookups reduce by `simp`.
-/

@[expose] public section

namespace MWIS.Fun

open MWIS.PointerMemory MWIS.RegisterMachine

variable {p : ℕ}

/-- Some run of the command returns within `B` events, with final heap and
outputs satisfying `P`. -/
def Yields (code : Code p) (h : Heap) (regs : Registers) (cmd : Command p) (B : ℕ)
    (P : Heap → List Value → Prop) : Prop :=
  ∃ out outs, P out outs ∧ Within code h regs cmd outs out B

theorem Yields.mono {code : Code p} {h : Heap} {regs : Registers} {cmd : Command p}
    {B B' : ℕ} {P P' : Heap → List Value → Prop} (hy : Yields code h regs cmd B P)
    (hB : B ≤ B') (hP : ∀ out outs, P out outs → P' out outs) :
    Yields code h regs cmd B' P' := by
  obtain ⟨out, outs, hp, hw⟩ := hy
  exact ⟨out, outs, hP _ _ hp, hw.mono hB⟩

theorem Yields.le {code : Code p} {h : Heap} {regs : Registers} {cmd : Command p}
    {B B' : ℕ} {P : Heap → List Value → Prop} (hy : Yields code h regs cmd B P)
    (hB : B ≤ B') : Yields code h regs cmd B' P := hy.mono hB (fun _ _ x => x)

theorem Yields.ret {code : Code p} {h : Heap} {regs : Registers} {outs : List Atom}
    {B : ℕ} {P : Heap → List Value → Prop} (hp : P h (values regs outs))
    (hB : 1 + 2 * outs.length ≤ B) : Yields code h regs (.ret outs) B P :=
  ⟨h, _, hp, (Within.ret code h regs outs).mono hB⟩

theorem Yields.copy {code : Code p} {h : Heap} {regs : Registers} {dst : Register}
    {src : Atom} {next : Command p} {B : ℕ} {P : Heap → List Value → Prop}
    (rest : Yields code h (Function.update regs dst (src.eval regs)) next B P) :
    Yields code h regs (.copy dst src next) (3 + B) P := by
  obtain ⟨out, outs, hp, hw⟩ := rest
  exact ⟨out, outs, hp, Within.copy hw⟩

theorem Yields.branch {code : Code p} {h : Heap} {regs : Registers} {test : Atom} {b : Bool}
    {yes no : Command p} {B : ℕ} {P : Heap → List Value → Prop}
    (ht : test.eval regs = .flag b) (rest : Yields code h regs (if b then yes else no) B P) :
    Yields code h regs (.branch test yes no) (3 + B) P := by
  obtain ⟨out, outs, hp, hw⟩ := rest
  exact ⟨out, outs, hp, Within.branch ht hw⟩

theorem Yields.load {code : Code p} {h : Heap} {regs : Registers} {address : Atom}
    {ptr : Ptr} {c : Cell} {first second bit : Register} {branches : Cases (Command p)}
    {B : ℕ} {P : Heap → List Value → Prop}
    (ha : address.eval regs = .pointer ptr) (hc : h[ptr]? = some c)
    (rest : Yields code h (loadRegisters regs first second bit c) (branches.select c) B P) :
    Yields code h regs (.load address first second bit branches) (10 + B) P := by
  obtain ⟨out, outs, hp, hw⟩ := rest
  exact ⟨out, outs, hp, Within.load ha hc hw⟩

theorem Yields.allocate {code : Code p} {h : Heap} {regs : Registers} {dst : Register}
    {expr : CellExpr} {c : Cell} {next : Command p} {B : ℕ} {P : Heap → List Value → Prop}
    (he : expr.eval regs = some c)
    (rest : Yields code (h ++ [c]) (Function.update regs dst (.pointer h.length)) next B P) :
    Yields code h regs (.allocate dst expr next) (4 + 2 * expr.args.length + B) P := by
  obtain ⟨out, outs, hp, hw⟩ := rest
  exact ⟨out, outs, hp, Within.allocate he hw⟩

theorem Yields.call {code : Code p} {h : Heap} {regs : Registers} {procedure : Fin p}
    {arguments : List Atom} {args : List Value} {results : List Register} {next : Command p}
    {cb rb : ℕ} {Q P : Heap → List Value → Prop}
    (hargs : values regs arguments = args)
    (body : Yields code h (initialRegisters args) (code procedure) cb Q)
    (rest : ∀ mid vals, Q mid vals → Yields code mid (bindResults regs results vals) next rb P) :
    Yields code h regs (.call procedure arguments results next)
      (1 + 2 * arguments.length + cb + rb) P := by
  obtain ⟨mid, vals, hq, hw⟩ := body
  obtain ⟨out, outs, hp, hw'⟩ := rest mid vals hq
  exact ⟨out, outs, hp, Within.call (hargs ▸ hw) hw'⟩

/-! ## Loads of cells of known shape -/

/-- Registers after loading pointer fields `a`, `b` and flag `f`. -/
def loaded (regs : Registers) (first second bit : Register) (a b : Ptr) (f : Bool) :
    Registers :=
  Function.update (Function.update (Function.update regs first (.pointer a)) second (.pointer b))
    bit (.flag f)

/-- Load a digit chain: the tail and the head digit, defaulting to the shared
empty cell and `false` at the end of the chain. -/
theorem Yields.loadChain {code : Code p} {h : Heap} (hh : Valid h) {regs : Registers}
    {address : Atom} {ptr : Ptr} {l : List Bool} (ha : address.eval regs = .pointer ptr)
    (hl : TreeAt h ptr (Tree.chain l)) {first second bit : Register} {X Y : Command p}
    {B : ℕ} {P : Heap → List Value → Prop}
    (rest : ∀ q, TreeAt h q (Tree.chain l.tail) →
      Yields code h (loaded regs first second bit q 0 (l.headD false))
        (if l = [] then X else Y) B P) :
    Yields code h regs
      (.load address first second bit { CompiledTrie.failCases with nil := X, bit := Y })
      (10 + B) P := by
  cases l with
  | nil =>
    cases hl with
    | nil cell => exact Yields.load ha cell (rest 0 (TreeAt.zero hh))
  | cons b l =>
    cases hl with
    | bit cell tail =>
      exact Yields.load ha cell (by
        have := rest _ tail; simp only [List.cons_ne_nil, ↓reduceIte] at this; exact this)

/-- Load a bit cell. -/
theorem Yields.loadBit {code : Code p} {h : Heap} {regs : Registers}
    {address : Atom} {ptr : Ptr} {b : Bool} {t : Tree} (ha : address.eval regs = .pointer ptr)
    (hl : TreeAt h ptr (.bit b t)) {first second bit : Register} {branches : Cases (Command p)}
    {B : ℕ} {P : Heap → List Value → Prop}
    (rest : ∀ q, TreeAt h q t →
      Yields code h (loaded regs first second bit q 0 b) branches.bit B P) :
    Yields code h regs (.load address first second bit branches) (10 + B) P := by
  cases hl with
  | bit cell tail => exact Yields.load ha cell (rest _ tail)

/-- Load a pair cell. -/
theorem Yields.loadPair {code : Code p} {h : Heap} {regs : Registers}
    {address : Atom} {ptr : Ptr} {x y : Tree} (ha : address.eval regs = .pointer ptr)
    (hl : TreeAt h ptr (.pair x y)) {first second bit : Register} {branches : Cases (Command p)}
    {B : ℕ} {P : Heap → List Value → Prop}
    (rest : ∀ a q, TreeAt h a x → TreeAt h q y →
      Yields code h (loaded regs first second bit a q false) branches.pair B P) :
    Yields code h regs (.load address first second bit branches) (10 + B) P := by
  cases hl with
  | pair cell first second => exact Yields.load ha cell (rest _ _ first second)

/-- Load a cons cell. -/
theorem Yields.loadCons {code : Code p} {h : Heap} {regs : Registers}
    {address : Atom} {ptr : Ptr} {x y : Tree} (ha : address.eval regs = .pointer ptr)
    (hl : TreeAt h ptr (.cons x y)) {first second bit : Register} {branches : Cases (Command p)}
    {B : ℕ} {P : Heap → List Value → Prop}
    (rest : ∀ a q, TreeAt h a x → TreeAt h q y →
      Yields code h (loaded regs first second bit a q false) branches.cons B P) :
    Yields code h regs (.load address first second bit branches) (10 + B) P := by
  cases hl with
  | cons cell first second => exact Yields.load ha cell (rest _ _ first second)

/-- Load a fork cell. -/
theorem Yields.loadFork {code : Code p} {h : Heap} {regs : Registers}
    {address : Atom} {ptr : Ptr} {x y : Tree} (ha : address.eval regs = .pointer ptr)
    (hl : TreeAt h ptr (.fork x y)) {first second bit : Register} {branches : Cases (Command p)}
    {B : ℕ} {P : Heap → List Value → Prop}
    (rest : ∀ a q, TreeAt h a x → TreeAt h q y →
      Yields code h (loaded regs first second bit a q false) branches.fork B P) :
    Yields code h regs (.load address first second bit branches) (10 + B) P := by
  cases hl with
  | fork cell first second => exact Yields.load ha cell (rest _ _ first second)

/-- Load a bucket cell. -/
theorem Yields.loadBucket {code : Code p} {h : Heap} {regs : Registers}
    {address : Atom} {ptr : Ptr} {t : Tree} (ha : address.eval regs = .pointer ptr)
    (hl : TreeAt h ptr (.bucket t)) {first second bit : Register} {branches : Cases (Command p)}
    {B : ℕ} {P : Heap → List Value → Prop}
    (rest : ∀ q, TreeAt h q t →
      Yields code h (loaded regs first second bit q 0 false) branches.bucket B P) :
    Yields code h regs (.load address first second bit branches) (10 + B) P := by
  cases hl with
  | bucket cell items => exact Yields.load ha cell (rest _ items)

/-- Load a nil cell. -/
theorem Yields.loadNil {code : Code p} {h : Heap} {regs : Registers}
    {address : Atom} {ptr : Ptr} (ha : address.eval regs = .pointer ptr)
    (hl : TreeAt h ptr .nil) {first second bit : Register} {branches : Cases (Command p)}
    {B : ℕ} {P : Heap → List Value → Prop}
    (rest : Yields code h (loaded regs first second bit 0 0 false) branches.nil B P) :
    Yields code h regs (.load address first second bit branches) (10 + B) P := by
  cases hl with
  | nil cell => exact Yields.load ha cell rest

/-! ## Allocations over stored trees -/

/-- Allocate a bit cell over a stored tail and continue. -/
theorem Yields.allocBit {code : Code p} {h : Heap} (hh : Valid h) {regs : Registers}
    {dst : Register} {fa ta : Atom} {b : Bool} {q : Ptr} {t : Tree}
    (hf : fa.eval regs = .flag b) (htl : ta.eval regs = .pointer q) (ht : TreeAt h q t)
    {next : Command p} {B : ℕ} {P : Heap → List Value → Prop}
    (rest : Extends h (h ++ [.bit b q]) → Valid (h ++ [.bit b q]) →
      TreeAt (h ++ [.bit b q]) h.length (.bit b t) →
      Yields code (h ++ [.bit b q]) (Function.update regs dst (.pointer h.length)) next B P) :
    Yields code h regs (.allocate dst (.bit fa ta) next) (8 + B) P := by
  obtain ⟨he, hv, hn⟩ := alloc_bitT hh b ht
  have := Yields.allocate (dst := dst) (expr := .bit fa ta) (c := .bit b q) (next := next)
    (by simp [CellExpr.eval, hf, htl, Value.asFlag, Value.asPointer]) (rest he hv hn)
  simpa [CellExpr.args] using this

/-- Allocate a pair cell over stored fields and continue. -/
theorem Yields.allocPair {code : Code p} {h : Heap} (hh : Valid h) {regs : Registers}
    {dst : Register} {fa ta : Atom} {a q : Ptr} {x t : Tree}
    (hf : fa.eval regs = .pointer a) (htl : ta.eval regs = .pointer q)
    (hx : TreeAt h a x) (ht : TreeAt h q t)
    {next : Command p} {B : ℕ} {P : Heap → List Value → Prop}
    (rest : Extends h (h ++ [.pair a q]) → Valid (h ++ [.pair a q]) →
      TreeAt (h ++ [.pair a q]) h.length (.pair x t) →
      Yields code (h ++ [.pair a q]) (Function.update regs dst (.pointer h.length)) next B P) :
    Yields code h regs (.allocate dst (.pair fa ta) next) (8 + B) P := by
  obtain ⟨he, hv, hn⟩ := alloc_pairT hh hx ht
  have := Yields.allocate (dst := dst) (expr := .pair fa ta) (c := .pair a q) (next := next)
    (by simp [CellExpr.eval, hf, htl, Value.asPointer]) (rest he hv hn)
  simpa [CellExpr.args] using this

/-- Allocate a cons cell over stored fields and continue. -/
theorem Yields.allocCons {code : Code p} {h : Heap} (hh : Valid h) {regs : Registers}
    {dst : Register} {fa ta : Atom} {a q : Ptr} {x t : Tree}
    (hf : fa.eval regs = .pointer a) (htl : ta.eval regs = .pointer q)
    (hx : TreeAt h a x) (ht : TreeAt h q t)
    {next : Command p} {B : ℕ} {P : Heap → List Value → Prop}
    (rest : Extends h (h ++ [.cons a q]) → Valid (h ++ [.cons a q]) →
      TreeAt (h ++ [.cons a q]) h.length (.cons x t) →
      Yields code (h ++ [.cons a q]) (Function.update regs dst (.pointer h.length)) next B P) :
    Yields code h regs (.allocate dst (.cons fa ta) next) (8 + B) P := by
  obtain ⟨he, hv, hn⟩ := alloc_consT hh hx ht
  have := Yields.allocate (dst := dst) (expr := .cons fa ta) (c := .cons a q) (next := next)
    (by simp [CellExpr.eval, hf, htl, Value.asPointer]) (rest he hv hn)
  simpa [CellExpr.args] using this

/-! ## Results that are one stored tree -/

/-- The run returns one pointer to a stored copy of `t`, on a valid heap
extending `h`. -/
def Returns (h : Heap) (t : Tree) (out : Heap) (outs : List Value) : Prop :=
  Extends h out ∧ Valid out ∧ ∃ q, outs = [.pointer q] ∧ TreeAt out q t

/-- Combine a callee returning one stored tree with a continuation. -/
theorem Yields.callTree {code : Code p} {h : Heap} {regs : Registers} {procedure : Fin p}
    {arguments : List Atom} {args : List Value} {result : Register} {next : Command p}
    {cb rb : ℕ} {t : Tree} {P : Heap → List Value → Prop}
    (hargs : values regs arguments = args)
    (body : Yields code h (initialRegisters args) (code procedure) cb (Returns h t))
    (rest : ∀ mid q, Extends h mid → Valid mid → TreeAt mid q t →
      Yields code mid (Function.update regs result (.pointer q)) next rb P) :
    Yields code h regs (.call procedure arguments [result] next)
      (1 + 2 * arguments.length + cb + rb) P :=
  Yields.call hargs body (by
    rintro mid vals ⟨he, hv, q, rfl, ht⟩
    simpa [bindResults] using rest mid q he hv ht)

/-- Transport the starting heap of a `Returns` property along `Extends`. -/
theorem Returns.of_extends {h h' out : Heap} {t : Tree} {outs : List Value}
    (he : Extends h h') (hr : Returns h' t out outs) : Returns h t out outs :=
  ⟨he.trans hr.1, hr.2⟩

end MWIS.Fun

end
