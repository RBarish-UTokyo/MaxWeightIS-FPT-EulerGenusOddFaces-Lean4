module

public import MWIS.FunCoordinatesLib
public import MWIS.TreeCotreeSearch

/-!
# The spanning-tree search in `Fun`

The graph is given as the list of integer endpoint pairs `(left e, right e)` of its edges in
edge order. `treeFn` runs `n` growth steps from the root and returns the discovered
`(vertex, edge)` pairs in discovery order. Its value is exactly the integer code of
`TreeCotree.tree left right root`.
-/

@[expose] public section

namespace MWIS.FunCoordinates

open MWIS.Fun MWIS.FunLP MWIS.TreeCotree

/-! ## Encodings -/

variable {m n : ℕ}

/-- The endpoint pairs of the edges, in edge order. -/
def edgeList (left right : Fin m → Fin n) : List (ℤ × ℤ) :=
  List.ofFn fun e => ((left e : ℤ), (right e : ℤ))

/-- The discovered flags of the vertices. -/
def discList (root : Fin n) (s : List (Fin n × Fin m)) : List Bool :=
  List.ofFn fun v : Fin n => decide (v ∈ discovered root s)

/-- The integer code of a growth sequence. -/
def treeCode (s : List (Fin n × Fin m)) : List (ℤ × ℤ) :=
  s.map fun p => ((p.1 : ℤ), (p.2 : ℤ))

/-! ## Programs -/

/-- `(root, k) ↦ k = root`. -/
def eqRootFn : Fn (.prod .int .int) .bool := .cmp .eq (.snd v0) (.fst v0)

/-- `(disc, (l, r))`: exactly one endpoint is discovered. -/
def frontierPred : Fn (.prod (.list .bool) (.prod .int .int)) .bool :=
  .ite (call getBoolFn (.pair (.fst v0) (.fst (.snd v0))))
    (.ite (call getBoolFn (.pair (.fst v0) (.snd (.snd v0)))) (.bool false) (.bool true))
    (call getBoolFn (.pair (.fst v0) (.snd (.snd v0))))

/-- `(v, (k, b)) ↦ k = v ∨ b`. -/
def setTrueItem : Fn (.prod .int (.prod .int .bool)) .bool :=
  .ite (.cmp .eq (.fst (.snd v0)) (.fst v0)) (.bool true) (.snd (.snd v0))

/-- Mark vertex `v` discovered. -/
def setTrueFn : Fn (.prod .int (.list .bool)) (.list .bool) := mapIdxFn setTrueItem

/-- The argument of the search: the edge list, the vertex count and the root. -/
abbrev SearchArg : Ty := .prod (.list (.prod .int .int)) (.prod .int .int)

/-- The search state: discovered flags and the reversed discovery list. -/
abbrev SearchState : Ty := .prod (.list .bool) (.list (.prod .int .int))

/-- The initial state: only the root is discovered. -/
def searchInit : Expr [SearchArg] SearchState :=
  .pair (call (cmapFn eqRootFn) (.pair (.snd (.snd v0)) (call crange (.fst (.snd v0)))))
    .nil

/-- One growth step. -/
def searchStep : Expr [SearchState, SearchArg] SearchState :=
  .letE (call (findIdxFn frontierPred) (.pair (.fst v0) (.fst v1)))
    (.ite (.cmp .lt v0 (.int 0)) v1
      (.letE (call getPairFn (.pair (.fst v2) v0))
        (.letE (.ite (call getBoolFn (.pair (.fst v2) (.fst v0))) (.snd v0) (.fst v0))
          (.pair (call setTrueFn (.pair v0 (.fst v3))) (.cons (.pair v0 v2) (.snd v3))))))

/-- The spanning-tree search. -/
def treeFn : Fn SearchArg (.list (.prod .int .int)) :=
  call (crevFn (.prod .int .int)) (.snd (.iter (.fst (.snd v0)) searchInit searchStep))

/-! ## Denotations -/

/-- The Boolean exclusive-or computed by the frontier predicate. -/
def frontierB (disc : List Bool) (lr : ℤ × ℤ) : Bool :=
  if getI disc false lr.1 then !getI disc false lr.2 else getI disc false lr.2

@[simp] theorem frontierPred_apply (x : (Ty.prod (.list .bool) (.prod .int .int)).denote) :
    frontierPred.apply x = frontierB x.1 x.2 := by
  rw [Fn.apply]
  simp only [frontierPred, frontierB, Expr.denote, Var.get, denote_call, getBoolFn_apply']
  cases getI x.1 false x.2.1 <;> cases getI x.1 false x.2.2 <;> rfl

@[simp] theorem setTrueFn_apply (x : (Ty.prod .int (.list .bool)).denote) :
    setTrueFn.apply x = x.2.mapIdx fun k b => if (k : ℤ) = x.1 then true else b := by
  rw [setTrueFn, mapIdxFn_apply']
  congr 1
  funext k b
  rw [Fn.apply]
  by_cases h : (k : ℤ) = x.1 <;> simp [setTrueItem, Expr.denote, Var.get, CmpOp.eval, h]

/-- The growth step on encoded states. -/
def stepSpec (edges : List (ℤ × ℤ)) (st : List Bool × List (ℤ × ℤ)) :
    List Bool × List (ℤ × ℤ) :=
  let e := optInt (edges.findIdx? (frontierB st.1))
  if e < 0 then st else
    let lr := getI edges (0, 0) e
    let v := if getI st.1 false lr.1 then lr.2 else lr.1
    (st.1.mapIdx (fun k b => if (k : ℤ) = v then true else b), (v, e) :: st.2)

theorem searchStep_denote (arg : List (ℤ × ℤ) × ℤ × ℤ) :
    (fun st => searchStep.denote (st, (arg, ()))) = stepSpec arg.1 := by
  funext st
  simp only [searchStep, stepSpec, Expr.denote, Var.get, denote_call, findIdxFn_apply',
    frontierPred_apply, getPairFn_apply', getBoolFn_apply', setTrueFn_apply, CmpOp.eval]
  by_cases h : optInt (List.findIdx? (frontierB st.1) arg.1) < 0
  · simp [h]
  · simp only [h, decide_false, Bool.false_eq_true, ite_false]

theorem searchInit_denote (arg : List (ℤ × ℤ) × ℤ × ℤ) :
    searchInit.denote (arg, ()) =
      ((List.range arg.2.1.toNat).map (fun i : ℕ => decide ((i : ℤ) = arg.2.2)), []) := by
  simp only [searchInit, Expr.denote, Var.get, denote_call, cmapFn_apply', crange_apply,
    List.map_map]
  try congr 1
  try (apply List.map_congr_left; intro i _; simp [Fn.apply, eqRootFn, Expr.denote, Var.get, CmpOp.eval])

theorem treeFn_apply (arg : List (ℤ × ℤ) × ℤ × ℤ) :
    treeFn.apply arg = ((stepSpec arg.1)^[arg.2.1.toNat]
      ((List.range arg.2.1.toNat).map (fun i : ℕ => decide ((i : ℤ) = arg.2.2)), [])).2.reverse := by
  rw [Fn.apply]
  simp only [treeFn, denote_call, crevFn_apply, Expr.denote, Var.get]
  rw [searchStep_denote, searchInit_denote]

/-! ## Agreement with the tree search -/

variable (left right : Fin m → Fin n)

theorem frontierB_edge (root : Fin n) (s : List (Fin n × Fin m)) (e : Fin m) :
    frontierB (discList root s) ((left e : ℤ), (right e : ℤ)) =
      (frontierEdge left right root s e).isSome := by
  unfold frontierB discList frontierEdge
  rw [getI_ofFn, getI_ofFn]
  by_cases h1 : left e ∈ discovered root s <;> by_cases h2 : right e ∈ discovered root s <;>
    simp [h1, h2]

theorem stepSpec_grow (root : Fin n) (s : List (Fin n × Fin m)) :
    stepSpec (edgeList left right) (discList root s, (treeCode s).reverse) =
      (discList root (grow left right root s), (treeCode (grow left right root s)).reverse) := by
  have hfind : (edgeList left right).findIdx? (frontierB (discList root s)) =
      ((List.finRange m).find? (fun e => (frontierEdge left right root s e).isSome)).map
        Fin.val := by
    rw [edgeList, findIdx?_ofFn]
    congr 2
    funext e
    exact frontierB_edge left right root s e
  have hfr : frontier left right root s =
      ((List.finRange m).find? (fun e => (frontierEdge left right root s e).isSome)).bind
        (frontierEdge left right root s) := findSome?_eq_bind_find _ _
  unfold stepSpec grow
  simp only [hfind]
  cases hf : (List.finRange m).find? (fun e => (frontierEdge left right root s e).isSome) with
  | none =>
    rw [hfr, hf]
    simp [optInt]
  | some e =>
    have he := List.find?_some hf
    rw [hfr, hf]
    simp only [Option.map_some, optInt, Option.bind_some]
    have hpos : ¬ ((e : ℕ) : ℤ) < 0 := by omega
    simp only [hpos, ite_false]
    simp only [edgeList, getI_ofFn]
    unfold frontierEdge at he ⊢
    simp only [discList, getI_ofFn]
    by_cases h1 : left e ∈ discovered root s <;> by_cases h2 : right e ∈ discovered root s <;>
      simp only [h1, h2, not_true_eq_false, not_false_eq_true, and_true, and_false, true_and,
        false_and, ite_true, ite_false, Option.isSome_some, Option.isSome_none,
        Bool.false_eq_true, decide_true, decide_false] at he ⊢
    all_goals
      refine Prod.ext ?_ ?_
      · apply List.ext_getElem (by simp)
        intro k hk1 hk2
        simp only [List.getElem_mapIdx, List.getElem_ofFn, mem_discovered_snoc, Fin.ext_iff,
          Nat.cast_inj]
        split_ifs <;> simp_all
      · simp [treeCode]

theorem init_discList (root : Fin n) :
    (List.range n).map (fun i : ℕ => decide ((i : ℤ) = (root : ℕ))) =
      discList (m := m) root [] := by
  apply List.ext_getElem (by simp [discList])
  intro k h1 h2
  simp [discList, discovered, Fin.ext_iff]

theorem iterate_stepSpec (root : Fin n) (k : ℕ) :
    (stepSpec (edgeList left right))^[k] (discList (m := m) root [], []) =
      (discList root ((grow left right root)^[k] []),
        (treeCode ((grow left right root)^[k] [])).reverse) := by
  induction k with
  | zero => simp [treeCode]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, stepSpec_grow, Function.iterate_succ_apply']

/-- **The search program computes the spanning tree.** -/
theorem treeFn_tree (root : Fin n) :
    treeFn.apply (edgeList left right, ((n : ℤ), ((root : ℕ) : ℤ))) =
      treeCode (tree left right root) := by
  rw [treeFn_apply]
  simp only [Int.toNat_natCast]
  rw [init_discList (m := m), iterate_stepSpec]
  simp [tree]

end MWIS.FunCoordinates

end
