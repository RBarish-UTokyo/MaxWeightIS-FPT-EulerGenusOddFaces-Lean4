module

public import MWIS.Fun.InterpTree

/-!
# The `Fun` interpreter: procedures

The interpreter is a fixed table of procedures. The entry procedure `eval`
receives a stored expression and a stored environment. It loads the root pair
of the expression, follows its unary tag to one of 32 leaves, evaluates the
subexpressions by recursive calls, and performs the operation of the node.
Folds, bounded iterations and tree conversions use the procedures of
`MWIS.Fun.InterpBase` and `MWIS.Fun.InterpTree`; integer operations use
`MWIS.Fun.ArithOps`.
-/

@[expose] public section

namespace MWIS.Fun.Interp

open MWIS.PointerMemory MWIS.RegisterMachine MWIS.Fun.Arith

variable {p : ℕ}

/-- The procedures of the interpreter. -/
structure Procedures (p : ℕ) where
  arith : Arith.Procedures p
  eval : Fin p
  lookup : Fin p
  fold : Fin p
  iter : Fin p
  evalStep : Fin p
  items : Fin p
  rev : Fin p
  skip : Fin p
  wordStep : Fin p
  iterW : Fin p
  word : Fin p

/-! ## Procedure bodies -/

/-- Arguments 0 = list, 1 = accumulator, 2 = step expression, 3 = environment. -/
def foldBody (self eval : Fin p) : Command p :=
  .load (.register 0) 4 5 15 { CompiledTrie.failCases with
    nil := .ret [.register 1]
    cons := .allocate 6 (.cons (.register 1) (.register 3))
      (.allocate 7 (.cons (.register 4) (.register 6))
        (.call eval [.register 2, .register 7] [8]
          (.call self [.register 5, .register 8, .register 2, .register 3] [9]
            (.ret [.register 9])))) }

/-- Arguments 0 = pair of step expression and environment, 1 = state. -/
def evalStepBody (eval : Fin p) : Command p :=
  .load (.register 0) 2 3 15 { CompiledTrie.failCases with
    pair := .allocate 4 (.cons (.register 1) (.register 3))
      (.call eval [.register 2, .register 4] [5] (.ret [.register 5])) }

/-- A leaf evaluating both components of the payload pair and combining them
with procedure `proc`. -/
def binLeaf (eval proc : Fin p) : Command p :=
  .load (.register 3) 4 5 15 { CompiledTrie.failCases with
    pair := .call eval [.register 4, .register 1] [6]
      (.call eval [.register 5, .register 1] [7]
        (.call proc [.register 6, .register 7] [8] (.ret [.register 8]))) }

/-- A leaf evaluating both components of the payload pair and allocating a cell. -/
def allocLeaf (eval : Fin p) (cell : CellExpr) : Command p :=
  .load (.register 3) 4 5 15 { CompiledTrie.failCases with
    pair := .call eval [.register 4, .register 1] [6]
      (.call eval [.register 5, .register 1] [7]
        (.allocate 8 cell (.ret [.register 8]))) }

/-- A leaf evaluating the payload and passing it to procedure `proc`. -/
def unLeaf (eval proc : Fin p) : Command p :=
  .call eval [.register 3, .register 1] [4] (.call proc [.register 4] [5] (.ret [.register 5]))

def iteLeaf (eval : Fin p) : Command p :=
  .load (.register 3) 4 5 15 { CompiledTrie.failCases with
    pair := .call eval [.register 4, .register 1] [6]
      (.load (.register 6) 7 15 8 { CompiledTrie.failCases with
        bit := .load (.register 5) 9 10 15 { CompiledTrie.failCases with
          pair := .branch (.register 8)
            (.call eval [.register 9, .register 1] [11] (.ret [.register 11]))
            (.call eval [.register 10, .register 1] [11] (.ret [.register 11])) } }) }

def projLeaf (eval : Fin p) (r : Register) : Command p :=
  .call eval [.register 3, .register 1] [4]
    (.load (.register 4) 5 6 15 { CompiledTrie.failCases with pair := .ret [.register r] })

def listCaseLeaf (eval : Fin p) : Command p :=
  .load (.register 3) 4 5 15 { CompiledTrie.failCases with
    pair := .call eval [.register 4, .register 1] [6]
      (.load (.register 5) 7 8 15 { CompiledTrie.failCases with
        pair := .load (.register 6) 9 10 15 { CompiledTrie.failCases with
          nil := .call eval [.register 7, .register 1] [11] (.ret [.register 11])
          cons := .allocate 12 (.cons (.register 10) (.register 1))
            (.allocate 13 (.cons (.register 9) (.register 12))
              (.call eval [.register 8, .register 13] [11] (.ret [.register 11]))) } }) }

def foldLeaf (eval fold : Fin p) : Command p :=
  .load (.register 3) 4 5 15 { CompiledTrie.failCases with
    pair := .call eval [.register 4, .register 1] [6]
      (.load (.register 5) 7 8 15 { CompiledTrie.failCases with
        pair := .call eval [.register 7, .register 1] [9]
          (.call fold [.register 6, .register 9, .register 8, .register 1] [10]
            (.ret [.register 10])) }) }

def iterLeaf (eval iter : Fin p) : Command p :=
  .load (.register 3) 4 5 15 { CompiledTrie.failCases with
    pair := .call eval [.register 4, .register 1] [6]
      (.load (.register 5) 7 8 15 { CompiledTrie.failCases with
        pair := .call eval [.register 7, .register 1] [9]
          (.load (.register 6) 10 15 11 { CompiledTrie.failCases with
            bit := .branch (.register 11) (.ret [.register 9])
              (.allocate 12 (.pair (.register 8) (.register 1))
                (.call iter [.register 10, .register 12, .register 9] [13]
                  (.ret [.register 13]))) }) }) }

def letLeaf (eval : Fin p) : Command p :=
  .load (.register 3) 4 5 15 { CompiledTrie.failCases with
    pair := .call eval [.register 4, .register 1] [6]
      (.allocate 7 (.cons (.register 6) (.register 1))
        (.call eval [.register 5, .register 7] [8] (.ret [.register 8]))) }

/-- Bind two loaded children and evaluate the branch expression in `r`. -/
def bindTwo (eval : Fin p) (r : Register) : Command p :=
  .allocate 3 (.cons (.register 14) (.register 1))
    (.allocate 4 (.cons (.register 13) (.register 3))
      (.call eval [.register r, .register 4] [5] (.ret [.register 5])))

def treeCaseLeaf (eval : Fin p) : Command p :=
  .load (.register 3) 4 5 15 { CompiledTrie.failCases with
    pair := .call eval [.register 4, .register 1] [6]
      (.load (.register 5) 7 8 15 { CompiledTrie.failCases with
        pair := .load (.register 8) 8 9 15 { CompiledTrie.failCases with
          pair := .load (.register 9) 9 10 15 { CompiledTrie.failCases with
            pair := .load (.register 10) 10 11 15 { CompiledTrie.failCases with
              pair := .load (.register 11) 11 12 15 { CompiledTrie.failCases with
                pair := .load (.register 6) 13 14 15 {
                  nil := .call eval [.register 7, .register 1] [4] (.ret [.register 4])
                  bit := .allocate 2 (.bit (.register 15) .null)
                    (.allocate 3 (.cons (.register 13) (.register 1))
                      (.allocate 4 (.cons (.register 2) (.register 3))
                        (.call eval [.register 8, .register 4] [5] (.ret [.register 5]))))
                  cons := bindTwo eval 9
                  fork := bindTwo eval 10
                  bucket := .allocate 4 (.cons (.register 13) (.register 1))
                    (.call eval [.register 11, .register 4] [5] (.ret [.register 5]))
                  pair := bindTwo eval 12 } } } } } }) }

def treeBitLeaf (eval : Fin p) : Command p :=
  .load (.register 3) 4 5 15 { CompiledTrie.failCases with
    pair := .call eval [.register 4, .register 1] [6]
      (.call eval [.register 5, .register 1] [7]
        (.load (.register 6) 8 15 9 { CompiledTrie.failCases with
          bit := .allocate 10 (.bit (.register 9) (.register 7)) (.ret [.register 10]) })) }

/-- The 32 leaves of the dispatch, indexed by constructor tag. -/
def leaf (d : Procedures p) : ℕ → Command p
  | 0 => .call d.lookup [.register 3, .register 1] [4] (.ret [.register 4])
  | 1 => .ret [.register 3]
  | 2 => .ret [.register 3]
  | 3 => .ret [.register 3]
  | 4 => binLeaf d.eval (d.arith.intOp .add)
  | 5 => binLeaf d.eval (d.arith.intOp .sub)
  | 6 => binLeaf d.eval (d.arith.intOp .mul)
  | 7 => binLeaf d.eval (d.arith.intOp .div)
  | 8 => binLeaf d.eval (d.arith.intOp .mod)
  | 9 => binLeaf d.eval (d.arith.cmpOp .lt)
  | 10 => binLeaf d.eval (d.arith.cmpOp .le)
  | 11 => binLeaf d.eval (d.arith.cmpOp .eq)
  | 12 => iteLeaf d.eval
  | 13 => allocLeaf d.eval (.pair (.register 6) (.register 7))
  | 14 => projLeaf d.eval 5
  | 15 => projLeaf d.eval 6
  | 16 => .ret [.null]
  | 17 => allocLeaf d.eval (.cons (.register 6) (.register 7))
  | 18 => listCaseLeaf d.eval
  | 19 => foldLeaf d.eval d.fold
  | 20 => iterLeaf d.eval d.iter
  | 21 => letLeaf d.eval
  | 22 => treeCaseLeaf d.eval
  | 23 => .ret [.null]
  | 24 => treeBitLeaf d.eval
  | 25 => allocLeaf d.eval (.cons (.register 6) (.register 7))
  | 26 => allocLeaf d.eval (.pair (.register 6) (.register 7))
  | 27 => unLeaf d.eval d.items
  | 28 => .call d.eval [.register 3, .register 1] [4] (.ret [.register 4])
  | 29 => unLeaf d.eval d.skip
  | 30 => binLeaf d.eval d.word
  | 31 => unLeaf d.eval d.arith.isize
  | _ => .fail

/-- Arguments 0 = expression, 1 = environment; result: the value. -/
def evalBody (d : Procedures p) : Command p :=
  .load (.register 0) 2 3 15 { CompiledTrie.failCases with pair := switch (leaf d) 0 32 }

/-- The bodies of all interpreter procedures. -/
structure Procedures.Matches (d : Procedures p) (code : Code p) : Prop where
  arith : d.arith.Matches code
  eval : code d.eval = evalBody d
  lookup : code d.lookup = lookupBody d.lookup
  fold : code d.fold = foldBody d.fold d.eval
  iter : code d.iter = iterBody d.iter d.evalStep
  evalStep : code d.evalStep = evalStepBody d.eval
  items : code d.items = itemsBody d.items
  rev : code d.rev = revBody d.rev
  skip : code d.skip = skipBody d.skip d.rev
  wordStep : code d.wordStep = wordStepBody
  iterW : code d.iterW = iterBody d.iterW d.wordStep
  word : code d.word = wordBody d.iterW

/-! ## The specification -/

/-- The interpreter constant: every expression is evaluated within `K` times
its cost. -/
def K : ℕ := 2048

/-- The eval procedure evaluates `e` in every stored environment within
`K * e.cost env` events. -/
def EvalSpec (code : Code p) (d : Procedures p) {Γ : List Ty} {τ : Ty} (e : Expr Γ τ) : Prop :=
  ∀ (env : Env Γ) {h : Heap}, Valid h → ∀ {ep envp : Ptr}, TreeAt h ep e.encode →
    EnvAt Γ h envp env →
    Yields code h (initialRegisters [.pointer ep, .pointer envp]) (code d.eval)
      (K * e.cost env) (Returns h (rep τ (e.denote env)))

/-- Entering the eval procedure on a node with tag `k`: the leaf sees the
expression, environment and payload pointers in registers 0, 1 and 3. -/
theorem enter {code : Code p} {d : Procedures p} (hm : d.Matches code) {k : ℕ} (hk : k < 32)
    {payload : Tree} {h : Heap} {ep envp : Ptr} (he : TreeAt h ep (node k payload)) {B : ℕ}
    {P : Heap → List Value → Prop}
    (rest : ∀ (regs : Registers) (pp : Ptr), regs 0 = .pointer ep → regs 1 = .pointer envp →
      regs 3 = .pointer pp → TreeAt h pp payload → Yields code h regs (leaf d k) B P) :
    Yields code h (initialRegisters [.pointer ep, .pointer envp]) (code d.eval)
      (10 + (10 * (k + 1) + B)) P := by
  rw [hm.eval]
  refine Yields.loadPair (by rsimp) he fun tp pp tt tpp => ?_
  refine Yields.switch k 0 32 hk (by rsimp) tt fun regs' ha => ?_
  rw [Nat.zero_add]
  refine rest regs' pp ?_ ?_ ?_ tpp
  · rw [ha 0 (by decide) (by decide) (by decide)]; rsimp
  · rw [ha 1 (by decide) (by decide) (by decide)]; rsimp
  · rw [ha 3 (by decide) (by decide) (by decide)]; rsimp

end MWIS.Fun.Interp

end
