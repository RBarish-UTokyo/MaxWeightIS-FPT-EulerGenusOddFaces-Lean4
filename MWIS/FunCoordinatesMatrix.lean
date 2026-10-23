module

public import MWIS.FunCoordinatesElim
public import MWIS.TreeCotree

/-!
# The face equations and their elimination in `Fun`

A signed column is encoded by the integer codes `2k + 1 + [b]` of its stubs `(k, b)`.
`actInitFn` computes the flags of the non-tree edges from the encoded tree, `matrixFn` the
matrix of `TreeCotree.columnState`, and `freeFn` runs `f` encoded elimination steps and
returns the flags of the free edges `TreeCotree.free`.
-/

@[expose] public section

namespace MWIS.FunCoordinates

open MWIS.Fun MWIS.FunLP MWIS.TreeCotree

/-! ## Encodings -/

variable {f : ℕ}

/-- The code of a signed stub: `2k + 1` for `(k, false)` and `2k + 2` for `(k, true)`. -/
def stubCodeC (s : Walks.Stub (Fin f)) : ℤ := 2 * (s.1 : ℕ) + 1 + if s.2 then 1 else 0

/-- The codes of the stubs of a column. -/
def columnCodeC : Walks.Column (Fin f) → List ℤ
  | .zero => []
  | .one s => [stubCodeC s]
  | .two s t => [stubCodeC s, stubCodeC t]

/-! ## Programs -/

/-- `(_, _) ↦ true`. -/
def trueFn (a : Ty) : Fn (.prod .unit a) .bool := .bool true

/-- `(T, edges)`: the flags of the edges that are not tree edges. -/
def actInitFn : Fn (.prod (.list (.prod .int .int)) (.list (.prod .int .int))) (.list .bool) :=
  .foldl (.fst v0) (call (cmapFn (trueFn (.prod .int .int))) (.pair .unit (.snd v0)))
    (call clearFn (.pair (.snd v0) v1))

/-- The value at row `r` of the stub with code `c`. -/
def stubValE : Expr [.int, .int, .prod (.list .int) .int] .int :=
  .ite (.cmp .eq (.arith .div (.arith .sub v0 (.int 1)) (.int 2)) (.snd v2))
    (.ite (.cmp .eq (.arith .mod (.arith .sub v0 (.int 1)) (.int 2)) (.int 1)) (.int 1) (.int (-1)))
    (.int 0)

/-- `(codes, r)`: the entry at row `r` of the encoded column. -/
def colValFn : Fn (.prod (.list .int) .int) .int :=
  .foldl (.fst v0) (.int 0) (.arith .add v1 stubValE)

/-- `((act, r), (k, codes))`: the matrix entry at row `r` and column `k`. -/
def entryItem : Fn (.prod (.prod (.list .bool) .int) (.prod .int (.list .int))) .int :=
  .ite (call getBoolFn (.pair (.fst (.fst v0)) (.fst (.snd v0))))
    (call colValFn (.pair (.snd (.snd v0)) (.snd (.fst v0)))) (.int 0)

/-- `((act, cols), r)`: row `r` of the matrix. -/
def rowFn : Fn (.prod (.prod (.list .bool) (.list (.list .int))) .int) (.list .int) :=
  call (mapIdxFn entryItem) (.pair (.pair (.fst (.fst v0)) (.snd v0)) (.snd (.fst v0)))

/-- `(act, (cols, f))`: the matrix of the face equations on the active columns. -/
def matrixFn : Fn (.prod (.list .bool) (.prod (.list (.list .int)) .int)) (.list (.list .int)) :=
  call (cmapFn rowFn) (.pair (.pair (.fst v0) (.fst (.snd v0))) (call crange (.snd (.snd v0))))

/-- The argument of the elimination: tree code, edges, column codes and face count. -/
abbrev ElimArg : Ty :=
  .prod (.list (.prod .int .int)) (.prod (.list (.prod .int .int)) (.prod (.list (.list .int)) .int))

/-- The initial encoded state. -/
def elimInit : Expr [.list .bool, ElimArg] ElimTy :=
  .pair (call (cmapFn (trueFn .int)) (.pair .unit (call crange (.snd (.snd (.snd v1))))))
    (.pair v0 (call matrixFn (.pair v0 (.snd (.snd v1)))))

/-- The flags of the free edges. -/
def freeFn : Fn ElimArg (.list .bool) :=
  .letE (call actInitFn (.pair (.fst v0) (.fst (.snd v0))))
    (.fst (.snd (.iter (.snd (.snd (.snd v1))) elimInit (call elimStepFn v0))))

/-! ## Denotations -/

/-- The value of a stub code at a row. -/
def stubVal (r c : ℤ) : ℤ := if (c - 1) / 2 = r then (if (c - 1) % 2 = 1 then 1 else -1) else 0

/-- The value of an encoded column at a row. -/
def colVal (codes : List ℤ) (r : ℤ) : ℤ := codes.foldl (fun acc c => acc + stubVal r c) 0

@[simp] theorem colValFn_apply (x : (Ty.prod (.list .int) .int).denote) :
    colValFn.apply x = colVal x.1 x.2 := by
  rw [Fn.apply]
  simp only [colValFn, colVal, Expr.denote, Var.get]
  congr 1
  funext acc c
  by_cases h1 : (c - 1) / 2 = x.2 <;> by_cases h2 : (c - 1) % 2 = 1 <;>
    simp [stubValE, stubVal, Expr.denote, Var.get, IntOp.eval, CmpOp.eval, h1, h2]

theorem actInitFn_apply (x : (Ty.prod (.list (.prod .int .int)) (.list (.prod .int .int))).denote) :
    actInitFn.apply x = x.1.foldl (fun acc p => clearS p.2 acc) (x.2.map fun _ => true) := by
  rw [Fn.apply]
  simp only [actInitFn, Expr.denote, Var.get, denote_call, cmapFn_apply', clearFn_apply]
  rfl

@[simp] theorem entryItem_apply
    (x : (Ty.prod (.prod (.list .bool) .int) (.prod .int (.list .int))).denote) :
    entryItem.apply x = if getI x.1.1 false x.2.1 then colVal x.2.2 x.1.2 else 0 := by
  rw [Fn.apply]
  simp only [entryItem, Expr.denote, Var.get, denote_call, getBoolFn_apply', colValFn_apply]

@[simp] theorem rowFn_apply (x : (Ty.prod (.prod (.list .bool) (.list (.list .int))) .int).denote) :
    rowFn.apply x = x.1.2.mapIdx fun k codes => if getI x.1.1 false k then colVal codes x.2 else 0 := by
  rw [Fn.apply]
  simp only [rowFn, Expr.denote, Var.get, denote_call, mapIdxFn_apply', entryItem_apply]

theorem matrixFn_apply (x : (Ty.prod (.list .bool) (.prod (.list (.list .int)) .int)).denote) :
    matrixFn.apply x = (List.range x.2.2.toNat).map fun r : ℕ =>
      x.2.1.mapIdx fun k codes => if getI x.1 false k then colVal codes r else 0 := by
  rw [Fn.apply]
  simp only [matrixFn, Expr.denote, Var.get, denote_call, cmapFn_apply', rowFn_apply,
    crange_apply, List.map_map]
  rfl

/-- The encoded initial state. -/
def initS (x : ElimArg.denote) : List Bool × List Bool × List (List ℤ) :=
  let act := x.1.foldl (fun acc p => clearS p.2 acc) (x.2.1.map fun _ => true)
  ((List.range x.2.2.2.toNat).map fun _ => true, act,
    (List.range x.2.2.2.toNat).map fun r : ℕ =>
      x.2.2.1.mapIdx fun k codes => if getI act false k then colVal codes r else 0)

theorem freeFn_apply (x : ElimArg.denote) :
    freeFn.apply x = (stepS^[x.2.2.2.toNat] (initS x)).2.1 := by
  rw [Fn.apply]
  simp only [freeFn, elimInit, Expr.denote, Var.get, denote_call, cmapFn_apply', crange_apply,
    List.map_map, elimStepFn_apply, actInitFn_apply, matrixFn_apply]
  rfl

/-! ## Agreement with the face equations -/

theorem stubVal_code (s : Walks.Stub (Fin f)) (r : Fin f) :
    stubVal ((r : ℕ) : ℤ) (stubCodeC s) = Walks.potential (some s) r := by
  obtain ⟨k, b⟩ := s
  unfold stubVal stubCodeC Walks.potential
  by_cases hk : r = k
  · subst hk
    cases b <;> simp [Walks.signValue] <;> omega
  · have hk' : ((k : ℕ) : ℤ) ≠ ((r : ℕ) : ℤ) := fun h => hk (Fin.ext (by exact_mod_cast h.symm))
    have : ¬ (2 * ((k : ℕ) : ℤ) + 1 + (if b then 1 else 0) - 1) / 2 = ((r : ℕ) : ℤ) := by
      cases b <;> simp <;> omega
    simp only [this, ite_false, hk]

theorem colVal_code (col : Walks.Column (Fin f)) (r : Fin f) :
    colVal (columnCodeC col) ((r : ℕ) : ℤ) = Walks.columnVector col r := by
  cases col with
  | zero => simp [colVal, columnCodeC, Walks.columnVector]
  | one s => simp [colVal, columnCodeC, Walks.columnVector, stubVal_code]
  | two s t => simp [colVal, columnCodeC, Walks.columnVector, stubVal_code]

variable {m n : ℕ} (left right : Fin m → Fin n) (C : Fin m → Walks.Column (Fin f))

/-- The column codes of a family of columns. -/
def colList : List (List ℤ) := List.ofFn fun e => columnCodeC (C e)

theorem clearFold_ofFn (g : Fin m → Bool) (s : List (Fin n × Fin m)) :
    (treeCode s).foldl (fun acc p => clearS p.2 acc) (List.ofFn g) =
      List.ofFn fun e => g e && decide (e ∉ s.map Prod.snd) := by
  induction s generalizing g with
  | nil => simp [treeCode]
  | cons p s ih =>
    simp only [treeCode, List.map_cons, List.foldl_cons] at ih ⊢
    rw [clearS_ofFn, ih]
    congr 1
    funext e
    by_cases h : e = p.2 <;> simp [h]

theorem actInit_eq (root : Fin n) :
    (treeCode (tree left right root)).foldl (fun acc p => clearS p.2 acc)
        ((edgeList left right).map fun _ => true) =
      List.ofFn fun e => decide (e ∈ nonTree left right root) := by
  have : (edgeList left right).map (fun _ => true) = List.ofFn fun _ : Fin m => true := by
    simp [edgeList, List.map_ofFn, Function.comp_def]
  rw [this, clearFold_ofFn]
  congr 1
  funext e
  simp [nonTree, treeEdges]

theorem initS_eq (root : Fin n) :
    initS (treeCode (tree left right root), (edgeList left right, (colList C, (f : ℤ)))) =
      encS (columnState C (nonTree left right root)) := by
  unfold initS encS columnState
  simp only [actInit_eq, Int.toNat_natCast, Finset.mem_univ, decide_true, Prod.mk.injEq]
  refine ⟨?_, trivial, ?_⟩
  · apply List.ext_getElem (by simp)
    intro k h1 h2
    simp
  · apply List.ext_getElem (by simp)
    intro r h1 h2
    simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn, colList, mapIdx_ofFn]
    congr 1
    funext e
    rw [show (((e : ℕ) : ℤ)) = ((e : ℕ) : ℤ) from rfl, getI_ofFn]
    simp only [decide_eq_true_eq]
    split_ifs
    · have := colVal_code (C e) ⟨r, by simpa using h1⟩
      simpa using this
    · rfl

/-- The free-edge flags. -/
def freeList (root : Fin n) : List Bool :=
  List.ofFn fun e => decide (e ∈ free left right C root)

/-- **The elimination program computes the free edges.** -/
theorem freeFn_free (root : Fin n) :
    freeFn.apply (treeCode (tree left right root), (edgeList left right, (colList C, (f : ℤ)))) =
      freeList left right C root := by
  rw [freeFn_apply]
  simp only [Int.toNat_natCast]
  rw [initS_eq, run_enc]
  rfl

end MWIS.FunCoordinates

end
