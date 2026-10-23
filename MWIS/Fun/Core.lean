module

public import Mathlib.Data.Int.Basic
public import Mathlib.Data.Nat.Size
public import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# A small total first-order language with an explicit cost

`Fun` is the intermediate language in which the new numerical stages of the
fixed-parameter program are written. A program is a typed expression. Its
meaning is the total function `Expr.denote`, and its cost is `Expr.cost`,
defined by the same structural recursion. The cost charges every syntax node,
the position of every variable lookup, every element of every fold and every
round of every bounded iteration, and every arithmetic operation by the binary
lengths of its actual arguments.

The language has no general recursion: lists are processed by left folds and
loops are bounded iterations with an explicit integer count. It also has a type
of raw heap trees, whose values are the cell structures of the register machine,
so that data stored by earlier register procedures can be read and written.

The register interpreter in `MWIS.Fun.Interpreter` executes every expression
within a fixed multiple of its cost. This file contains no machine code.
-/

@[expose] public section

namespace MWIS.Fun

/-! ## Types and values -/

/-- Raw immutable cell trees, mirroring `PointerMemory.Cell`. -/
inductive Tree where
  | nil
  | bit (value : Bool) (tail : Tree)
  | cons (head tail : Tree)
  | fork (left right : Tree)
  | bucket (items : Tree)
  | pair (first second : Tree)
  deriving DecidableEq, Repr, Inhabited

/-- The types of `Fun`. -/
inductive Ty where
  | int
  | bool
  | unit
  | tree
  | prod (a b : Ty)
  | list (a : Ty)
  deriving DecidableEq, Repr

/-- The Lean type denoted by a `Fun` type. -/
@[reducible] def Ty.denote : Ty → Type
  | .int => ℤ
  | .bool => Bool
  | .unit => Unit
  | .tree => Tree
  | .prod a b => a.denote × b.denote
  | .list a => List a.denote

/-- Typed de Bruijn variables. -/
inductive Var : List Ty → Ty → Type where
  | here {Γ : List Ty} {τ : Ty} : Var (τ :: Γ) τ
  | there {Γ : List Ty} {σ τ : Ty} (v : Var Γ τ) : Var (σ :: Γ) τ

/-- The position of a variable in its context. -/
def Var.index {Γ : List Ty} {τ : Ty} : Var Γ τ → ℕ
  | .here => 0
  | .there v => v.index + 1

/-- Environments: one value for every type of the context. -/
@[reducible] def Env : List Ty → Type
  | [] => Unit
  | τ :: Γ => τ.denote × Env Γ

/-- Read a variable from an environment. -/
def Var.get {Γ : List Ty} {τ : Ty} : Var Γ τ → Env Γ → τ.denote
  | .here, env => env.1
  | .there v, env => v.get env.2

/-! ## Primitive operations -/

/-- Integer operations. Division and remainder are Euclidean (`Int.ediv`,
`Int.emod`); division by zero returns zero and the remainder is the dividend. -/
inductive IntOp where
  | add | sub | mul | div | mod
  deriving DecidableEq, Repr

/-- Integer comparisons. -/
inductive CmpOp where
  | lt | le | eq
  deriving DecidableEq, Repr

/-- Meaning of an integer operation. -/
def IntOp.eval : IntOp → ℤ → ℤ → ℤ
  | .add, x, y => x + y
  | .sub, x, y => x - y
  | .mul, x, y => x * y
  | .div, x, y => x / y
  | .mod, x, y => x % y

/-- Meaning of a comparison. -/
def CmpOp.eval : CmpOp → ℤ → ℤ → Bool
  | .lt, x, y => decide (x < y)
  | .le, x, y => decide (x ≤ y)
  | .eq, x, y => decide (x = y)

/-- Binary length of the absolute value of an integer. -/
def bits (x : ℤ) : ℕ := x.natAbs.size

/-- Charge of an integer operation on its actual arguments: linear in the
binary lengths for addition and subtraction, and the product of the lengths for
multiplication; division and remainder are charged the square of the total
length. -/
def IntOp.charge : IntOp → ℤ → ℤ → ℕ
  | .add, x, y => bits x + bits y + 1
  | .sub, x, y => bits x + bits y + 1
  | .mul, x, y => (bits x + 1) * (bits y + 1)
  | .div, x, y => (bits x + bits y + 1) ^ 2
  | .mod, x, y => (bits x + bits y + 1) ^ 2

/-- Charge of a comparison: linear in the binary lengths. -/
def CmpOp.charge (_ : CmpOp) (x y : ℤ) : ℕ := bits x + bits y + 1

/-! ## Raw trees as data -/

namespace Tree

/-- Number of cells of a tree. -/
def size : Tree → ℕ
  | .nil => 1
  | .bit _ t => t.size + 1
  | .cons a t => a.size + t.size + 1
  | .fork l r => l.size + r.size + 1
  | .bucket t => t.size + 1
  | .pair a b => a.size + b.size + 1

/-- The items of a cons spine; the spine ends at the first non-cons cell. -/
def items : Tree → List Tree
  | .cons a t => a :: t.items
  | _ => []

/-- The length of a cons spine. -/
def spine : Tree → ℕ
  | .cons _ t => t.spine + 1
  | _ => 0

/-- The bits of a bit chain, most significant first; the chain ends at the
first non-bit cell. -/
def bitList : Tree → List Bool
  | .bit b t => b :: t.bitList
  | _ => []

/-- The natural number written by a bit chain, most significant bit first. -/
def wordValue (t : Tree) : ℕ :=
  t.bitList.foldl (fun a b => 2 * a + if b then 1 else 0) 0

/-- A cons spine of the given items, ending in `nil`. -/
def ofList : List Tree → Tree
  | [] => .nil
  | a :: as => .cons a (ofList as)

/-- The fixed-width big-endian word of the `w` low bits of `k`, ending in `nil`. -/
def word : ℕ → ℕ → Tree
  | 0, _ => .nil
  | w + 1, k => .bit (k.testBit w) (word w k)

end Tree

/-! ## Expressions -/

/-- Typed expressions over a context of variable types. In binders, the newly
bound variables come first: `listCase` binds the head and then the tail, `foldl`
binds the element and then the accumulator, and `iter` binds the state. -/
inductive Expr : List Ty → Ty → Type where
  | var {Γ : List Ty} {τ : Ty} (v : Var Γ τ) : Expr Γ τ
  | int {Γ : List Ty} (z : ℤ) : Expr Γ .int
  | bool {Γ : List Ty} (b : Bool) : Expr Γ .bool
  | unit {Γ : List Ty} : Expr Γ .unit
  | arith {Γ : List Ty} (op : IntOp) (x y : Expr Γ .int) : Expr Γ .int
  | cmp {Γ : List Ty} (op : CmpOp) (x y : Expr Γ .int) : Expr Γ .bool
  | ite {Γ : List Ty} {τ : Ty} (c : Expr Γ .bool) (t e : Expr Γ τ) : Expr Γ τ
  | pair {Γ : List Ty} {a b : Ty} (x : Expr Γ a) (y : Expr Γ b) : Expr Γ (.prod a b)
  | fst {Γ : List Ty} {a b : Ty} (p : Expr Γ (.prod a b)) : Expr Γ a
  | snd {Γ : List Ty} {a b : Ty} (p : Expr Γ (.prod a b)) : Expr Γ b
  | nil {Γ : List Ty} {a : Ty} : Expr Γ (.list a)
  | cons {Γ : List Ty} {a : Ty} (x : Expr Γ a) (xs : Expr Γ (.list a)) : Expr Γ (.list a)
  | listCase {Γ : List Ty} {a b : Ty} (xs : Expr Γ (.list a)) (onNil : Expr Γ b)
      (onCons : Expr (a :: .list a :: Γ) b) : Expr Γ b
  | foldl {Γ : List Ty} {a b : Ty} (xs : Expr Γ (.list a)) (init : Expr Γ b)
      (step : Expr (a :: b :: Γ) b) : Expr Γ b
  | iter {Γ : List Ty} {b : Ty} (count : Expr Γ .int) (init : Expr Γ b)
      (step : Expr (b :: Γ) b) : Expr Γ b
  | letE {Γ : List Ty} {a b : Ty} (x : Expr Γ a) (body : Expr (a :: Γ) b) : Expr Γ b
  /-- Inspect the root cell of a tree. The bit case binds the bit and the tail;
  the cons, fork and pair cases bind the two children (first child first); the
  bucket case binds its child. -/
  | treeCase {Γ : List Ty} {b : Ty} (t : Expr Γ .tree) (onNil : Expr Γ b)
      (onBit : Expr (.bool :: .tree :: Γ) b) (onCons : Expr (.tree :: .tree :: Γ) b)
      (onFork : Expr (.tree :: .tree :: Γ) b) (onBucket : Expr (.tree :: Γ) b)
      (onPair : Expr (.tree :: .tree :: Γ) b) : Expr Γ b
  | treeNil {Γ : List Ty} : Expr Γ .tree
  | treeBit {Γ : List Ty} (b : Expr Γ .bool) (t : Expr Γ .tree) : Expr Γ .tree
  | treeCons {Γ : List Ty} (x t : Expr Γ .tree) : Expr Γ .tree
  | treePair {Γ : List Ty} (x y : Expr Γ .tree) : Expr Γ .tree
  /-- The items of a cons spine. -/
  | items {Γ : List Ty} (t : Expr Γ .tree) : Expr Γ (.list .tree)
  /-- A cons spine of tree items. -/
  | ofItems {Γ : List Ty} (ts : Expr Γ (.list .tree)) : Expr Γ .tree
  /-- The value of a big-endian bit chain. -/
  | wordValue {Γ : List Ty} (t : Expr Γ .tree) : Expr Γ .int
  /-- The big-endian word of width `max w 0` holding the low bits of `|k|`. -/
  | word {Γ : List Ty} (w k : Expr Γ .int) : Expr Γ .tree
  /-- The binary length `Nat.size |x|` of an integer. -/
  | size {Γ : List Ty} (x : Expr Γ .int) : Expr Γ .int

namespace Expr

/-- The meaning of an expression. -/
def denote {Γ : List Ty} {τ : Ty} : Expr Γ τ → Env Γ → τ.denote
  | .var v, env => v.get env
  | .int z, _ => z
  | .bool b, _ => b
  | .unit, _ => ()
  | .arith op x y, env => op.eval (x.denote env) (y.denote env)
  | .cmp op x y, env => op.eval (x.denote env) (y.denote env)
  | .ite c t e, env => if c.denote env then t.denote env else e.denote env
  | .pair x y, env => (x.denote env, y.denote env)
  | .fst p, env => (p.denote env).1
  | .snd p, env => (p.denote env).2
  | .nil, _ => []
  | .cons x xs, env => x.denote env :: xs.denote env
  | .listCase xs onNil onCons, env =>
      match xs.denote env with
      | [] => onNil.denote env
      | y :: ys => onCons.denote (y, ys, env)
  | .foldl xs init step, env =>
      (xs.denote env).foldl (fun acc y => step.denote (y, acc, env)) (init.denote env)
  | .iter count init step, env =>
      Nat.iterate (fun s => step.denote (s, env)) (count.denote env).toNat (init.denote env)
  | .letE x body, env => body.denote (x.denote env, env)
  | .treeCase t onNil onBit onCons onFork onBucket onPair, env =>
      match t.denote env with
      | .nil => onNil.denote env
      | .bit b u => onBit.denote (b, u, env)
      | .cons u v => onCons.denote (u, v, env)
      | .fork u v => onFork.denote (u, v, env)
      | .bucket u => onBucket.denote (u, env)
      | .pair u v => onPair.denote (u, v, env)
  | .treeNil, _ => .nil
  | .treeBit b t, env => .bit (b.denote env) (t.denote env)
  | .treeCons x t, env => .cons (x.denote env) (t.denote env)
  | .treePair x y, env => .pair (x.denote env) (y.denote env)
  | .items t, env => (t.denote env).items
  | .ofItems ts, env => Tree.ofList (ts.denote env)
  | .wordValue t, env => ((t.denote env).wordValue : ℤ)
  | .word w k, env => Tree.word (w.denote env).toNat (k.denote env).natAbs
  | .size x, env => (bits (x.denote env) : ℤ)

/-- The cost of evaluating an expression in an environment. Every node costs
one unit; a variable additionally costs its position; folds and iterations
charge every round; integer operations charge their argument lengths; tree
conversions charge the cells they traverse or create. -/
def cost {Γ : List Ty} {τ : Ty} : Expr Γ τ → Env Γ → ℕ
  | .var v, _ => v.index + 1
  | .int _, _ => 1
  | .bool _, _ => 1
  | .unit, _ => 1
  | .arith op x y, env =>
      x.cost env + y.cost env + op.charge (x.denote env) (y.denote env) + 1
  | .cmp op x y, env =>
      x.cost env + y.cost env + op.charge (x.denote env) (y.denote env) + 1
  | .ite c t e, env =>
      c.cost env + (if c.denote env then t.cost env else e.cost env) + 1
  | .pair x y, env => x.cost env + y.cost env + 1
  | .fst p, env => p.cost env + 1
  | .snd p, env => p.cost env + 1
  | .nil, _ => 1
  | .cons x xs, env => x.cost env + xs.cost env + 1
  | .listCase xs onNil onCons, env =>
      xs.cost env +
        (match xs.denote env with
          | [] => onNil.cost env
          | y :: ys => onCons.cost (y, ys, env)) + 1
  | .foldl xs init step, env =>
      xs.cost env + init.cost env +
        ((xs.denote env).foldl
          (fun (s : _ × ℕ) y => (step.denote (y, s.1, env), s.2 + step.cost (y, s.1, env) + 1))
          (init.denote env, 0)).2 + 1
  | .iter count init step, env =>
      count.cost env + init.cost env +
        (Nat.iterate
          (fun (s : _ × ℕ) => (step.denote (s.1, env),
            s.2 + step.cost (s.1, env) + bits (count.denote env) + 1))
          (count.denote env).toNat (init.denote env, 0)).2 + 1
  | .letE x body, env => x.cost env + body.cost (x.denote env, env) + 1
  | .treeCase t onNil onBit onCons onFork onBucket onPair, env =>
      t.cost env +
        (match t.denote env with
          | .nil => onNil.cost env
          | .bit b u => onBit.cost (b, u, env)
          | .cons u v => onCons.cost (u, v, env)
          | .fork u v => onFork.cost (u, v, env)
          | .bucket u => onBucket.cost (u, env)
          | .pair u v => onPair.cost (u, v, env)) + 1
  | .treeNil, _ => 1
  | .treeBit b t, env => b.cost env + t.cost env + 1
  | .treeCons x t, env => x.cost env + t.cost env + 1
  | .treePair x y, env => x.cost env + y.cost env + 1
  | .items t, env => t.cost env + (t.denote env).spine + 1
  | .ofItems ts, env => ts.cost env + (ts.denote env).length + 1
  | .wordValue t, env => t.cost env + (t.denote env).bitList.length + 1
  | .word w k, env =>
      w.cost env + k.cost env + (w.denote env).toNat + bits (k.denote env) + 1
  | .size x, env => x.cost env + bits (x.denote env) + 1

end Expr

/-- Euclidean division is Lean's integer division. -/
example (x y : ℤ) : IntOp.eval .div x y = Int.ediv x y := rfl

end MWIS.Fun

end
