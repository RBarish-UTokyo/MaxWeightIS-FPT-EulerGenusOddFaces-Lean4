module

public import MWIS.FPTRunFun
public import MWIS.Fun.HeapExec

/-!
# Building a constant tree

`buildBody t` is a straight-line procedure body that allocates a fresh copy of
the constant tree `t` and returns a pointer to it. It visits `t` in postorder
and keeps the result of the last finished subtree in register 1. Before the
second child of a two-field node is built, the pointer to the first child is
pushed onto a stack of cons cells on the heap, whose top is held in register 0;
afterwards it is popped into register 2. Register 3 receives the unused flag of
the popped cell. No other register is used and no procedure is called.

The body is defined by structural recursion on the tree, so an equation
`code build = buildBody t` for a fixed `t` holds by `rfl`.

`build_compiled` proves the contract `FPTRunFun.BuildsTree code build t
(buildBudget t)` with the linear budget `buildBudget t = 26 * t.size + 3`.
-/

@[expose] public section

namespace MWIS.FPTBuild

open MWIS.PointerMemory MWIS.RegisterMachine MWIS.Fun

variable {p : ℕ}

/-! ## The procedure body -/

/-- The load cases of a pop: the stack cells are cons cells. -/
def popCases (next : Command p) : Cases (Command p) :=
  { nil := .fail, bit := .fail, cons := next, fork := .fail, bucket := .fail, pair := .fail }

/-- A two-field node: build the first child, push it, build the second child,
pop the first child, and allocate the node cell. -/
def binary (first second : Command p → Command p) (mk : Atom → Atom → CellExpr)
    (next : Command p) : Command p :=
  first (.allocate 0 (.cons (.register 1) (.register 0))
    (second (.load (.register 0) 2 0 3
      (popCases (.allocate 1 (mk (.register 2) (.register 1)) next)))))

/-- Allocate a copy of `t`, leave its pointer in register 1, and continue with
`next`. -/
def build : Tree → Command p → Command p
  | .nil, next => .allocate 1 .nil next
  | .bit b t, next => build t (.allocate 1 (.bit (.flag b) (.register 1)) next)
  | .cons x y, next => binary (build x) (build y) .cons next
  | .fork x y, next => binary (build x) (build y) .fork next
  | .bucket t, next => build t (.allocate 1 (.bucket (.register 1)) next)
  | .pair x y, next => binary (build x) (build y) .pair next

/-- The builder procedure of the constant tree `t`. -/
def buildBody (t : Tree) : Command p := build t (.ret [.register 1])

/-- The event budget of the builder of `t`. -/
def buildBudget (t : Tree) : ℕ := 26 * t.size + 3

/-! ## Correctness -/

/-- The continuation contract of a builder fragment `bt` for the tree `t`: started
with a stack pointer `s` in register 0, it allocates a copy of `t`, leaves its
pointer in register 1, restores register 0, and continues. -/
def Builds (code : Code p) (t : Tree) (bt : Command p → Command p) : Prop :=
  ∀ {next : Command p} {B : ℕ} {P : Heap → List Value → Prop} {h : Heap} {regs : Registers}
    {s : Ptr}, Valid h → regs 0 = .pointer s → s < h.length →
    (∀ h' q (regs' : Registers), Extends h h' → Valid h' → TreeAt h' q t →
      regs' 0 = .pointer s → regs' 1 = .pointer q → Yields code h' regs' next B P) →
    Yields code h regs (bt next) (26 * t.size + B) P

theorem builds_unary (code : Code p) {t node : Tree} {bt : Command p → Command p}
    (ht : Builds code t bt) (e : CellExpr) (c : Ptr → Cell) (hargs : e.args.length ≤ 11)
    (heval : ∀ (regs : Registers) (q : Ptr), regs 1 = .pointer q → e.eval regs = some (c q))
    (hrefs : ∀ q, (c q).references = [q])
    (hnode : ∀ (h : Heap) (a q : Ptr), h[a]? = some (c q) → TreeAt h q t → TreeAt h a node)
    (hsize : node.size = t.size + 1) :
    Builds code node (fun next => bt (.allocate 1 e next)) := by
  intro next B P h regs s hh h0 hs hk
  refine Yields.le (ht (B := 4 + 2 * e.args.length + B) hh h0 hs
    fun h1 q r1 e1 v1 t1 r10 r11 => ?_) (by rw [hsize]; omega)
  obtain ⟨e2, v2, c2⟩ := alloc v1 (c q) (by
    intro y hy; rw [hrefs, List.mem_singleton] at hy; exact hy ▸ t1.allocated)
  refine Yields.allocate (heval r1 q r11) (hk _ _ _ (e1.trans e2) v2
    (hnode _ _ _ c2 (t1.mono e2)) ?_ (by simp))
  rw [Function.update_of_ne (by decide), r10]

theorem builds_binary (code : Code p) {x y node : Tree} {bx byy : Command p → Command p}
    (hx : Builds code x bx) (hy : Builds code y byy) (mk : Atom → Atom → CellExpr)
    (c : Ptr → Ptr → Cell)
    (hargs : (mk (.register 2) (.register 1)).args.length = 2)
    (heval : ∀ (regs : Registers) (a q : Ptr), regs 2 = .pointer a → regs 1 = .pointer q →
      (mk (.register 2) (.register 1)).eval regs = some (c a q))
    (hrefs : ∀ a q, (c a q).references = [a, q])
    (hnode : ∀ (h : Heap) (r a q : Ptr), h[r]? = some (c a q) → TreeAt h a x → TreeAt h q y →
      TreeAt h r node)
    (hsize : node.size = x.size + y.size + 1) :
    Builds code node (binary bx byy mk) := by
  intro next B P h regs s hh h0 hs hk
  refine Yields.le (hx (B := 8 + (26 * y.size + (10 + (8 + B)))) hh h0 hs
    fun h1 qx r1 e1 v1 t1 r10 r11 => ?_) (by rw [hsize]; omega)
  have hs1 : s < h1.length := lt_of_lt_of_le hs e1.length_le
  obtain ⟨e2, v2, c2⟩ := alloc v1 (.cons qx s) (by
    intro z hz
    simp only [Cell.references, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · exact t1.allocated
    · exact hs1)
  refine Yields.le (Yields.allocate (B := 26 * y.size + (10 + (8 + B))) (c := .cons qx s) (by simp [CellExpr.eval, Atom.eval, r10, r11,
    Value.asPointer]) ?_) (by simp [CellExpr.args])
  refine hy (s := h1.length) v2 (by simp) (by simp)
    fun h3 qy r3 e3 v3 t3 r30 r31 => ?_
  refine Yields.load (ptr := h1.length) (c := .cons qx s) (by simp [Atom.eval, r30])
    (e3.lookup c2) ?_
  have hl2 : loadRegisters r3 2 0 3 (.cons qx s) 2 = .pointer qx := by
    simp [loadRegisters, decoded]
  have hl1 : loadRegisters r3 2 0 3 (.cons qx s) 1 = .pointer qy := by
    simp [loadRegisters, decoded, r31]
  have hl0 : loadRegisters r3 2 0 3 (.cons qx s) 0 = .pointer s := by
    simp [loadRegisters, decoded]
  obtain ⟨e4, v4, c4⟩ := alloc v3 (c qx qy) (by
    intro z hz
    rw [hrefs] at hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · exact ((t1.mono e2).mono e3).allocated
    · exact t3.allocated)
  have e14 := e1.trans (e2.trans (e3.trans e4))
  refine Yields.le (Yields.allocate (B := B) (heval _ qx qy hl2 hl1) (hk _ _ _ e14 v4
    (hnode _ _ _ _ c4 (((t1.mono e2).mono e3).mono e4) (t3.mono e4)) ?_ (by simp)))
    (by rw [hargs])
  rw [Function.update_of_ne (by decide), hl0]

/-- Every builder fragment meets its contract. -/
theorem build_builds (code : Code p) (t : Tree) : Builds code t (build t) := by
  induction t with
  | nil =>
    intro next B P h regs s hh h0 hs hk
    obtain ⟨e1, v1, c1⟩ := alloc hh .nil (by simp [Cell.references])
    refine Yields.le (Yields.allocate (c := .nil) (by simp [CellExpr.eval])
      (hk _ _ _ e1 v1 (.nil c1) ?_ (by simp))) (by simp [CellExpr.args, Tree.size])
    rw [Function.update_of_ne (by decide), h0]
  | bit b t ih =>
    exact builds_unary code ih (.bit (.flag b) (.register 1)) (fun q => .bit b q)
      (by simp [CellExpr.args])
      (fun regs q hq => by simp [CellExpr.eval, Atom.eval, hq, Value.asPointer, Value.asFlag])
      (fun _ => rfl) (fun _ _ _ hc ht => .bit hc ht) rfl
  | cons x y ihx ihy =>
    exact builds_binary code ihx ihy .cons (fun a q => .cons a q) rfl
      (fun regs a q ha hq => by simp [CellExpr.eval, Atom.eval, ha, hq, Value.asPointer])
      (fun _ _ => rfl) (fun _ _ _ _ hc ha hq => .cons hc ha hq) rfl
  | fork x y ihx ihy =>
    exact builds_binary code ihx ihy .fork (fun a q => .fork a q) rfl
      (fun regs a q ha hq => by simp [CellExpr.eval, Atom.eval, ha, hq, Value.asPointer])
      (fun _ _ => rfl) (fun _ _ _ _ hc ha hq => .fork hc ha hq) rfl
  | bucket t ih =>
    exact builds_unary code ih (.bucket (.register 1)) (fun q => .bucket q)
      (by simp [CellExpr.args])
      (fun regs q hq => by simp [CellExpr.eval, Atom.eval, hq, Value.asPointer])
      (fun _ => rfl) (fun _ _ _ hc ht => .bucket hc ht) rfl
  | pair x y ihx ihy =>
    exact builds_binary code ihx ihy .pair (fun a q => .pair a q) rfl
      (fun regs a q ha hq => by simp [CellExpr.eval, Atom.eval, ha, hq, Value.asPointer])
      (fun _ _ => rfl) (fun _ _ _ _ hc ha hq => .pair hc ha hq) rfl

/-- **The builder.** The procedure `buildBody t` returns a pointer to a fresh copy
of `t` within `buildBudget t` events. -/
theorem build_compiled (code : Code p) (build : Fin p) (t : Tree)
    (hbuild : code build = buildBody t) :
    FPTRunFun.BuildsTree code build t (buildBudget t) := by
  intro h hh
  have hy : Yields code h (initialRegisters []) (code build) (buildBudget t) (Returns h t) := by
    rw [hbuild]
    exact build_builds code t hh (by simp [initialRegisters]) (lookup_allocated hh.1)
      fun h' q regs' e' v' t' _ r1 =>
        Yields.ret ⟨e', v', q, by simp [values, Atom.eval, r1], t'⟩ (by simp)
  obtain ⟨out, outs, ⟨he, hv, q, rfl, hq⟩, hw⟩ := hy
  exact ⟨out, q, he, hv, hq, hw⟩

/-! ## The wrappers with built programs -/

/-- The constants stage, with the stored program built by `buildBody`. -/
theorem constsSpec_built (code : Code p) (self build eval : Fin p)
    (hself : code self = FPTRunFun.wrap2Body build eval) {K : ℕ}
    (heval : FPTRunFun.EvalSpec code eval K)
    (hbuild : code build = buildBody FPTRunFun.constsProg.encode) :
    FPTRegister.ConstsSpec code self
      (FPTRunFun.constsBudget K (buildBudget FPTRunFun.constsProg.encode)) :=
  FPTRunFun.constsSpec code self build eval hself heval
    (build_compiled code build _ hbuild)

/-- The numerical stage, with the stored program built by `buildBody`. -/
theorem funStageSpec_built (code : Code p) (self build eval : Fin p)
    (hself : code self = FPTRunFun.wrap5Body build eval) {K : ℕ}
    (heval : FPTRunFun.EvalSpec code eval K)
    (prog : Expr [.tree, .tree, .tree, .tree, .tree] .tree)
    (hbuild : code build = buildBody prog.encode) {coords : FPTRegister.CoordFn}
    {pb : ℕ → ℕ → RegisterComponentSolve.HardBudget}
    (hprog : FPTRunFun.ProgFunStage prog coords pb) :
    FPTRegister.FunStageSpec code self coords
      (FPTRunFun.stageBudget K (buildBudget prog.encode) pb) :=
  FPTRunFun.funStageSpec code self build eval hself heval prog
    (build_compiled code build _ hbuild) hprog

end MWIS.FPTBuild

end
