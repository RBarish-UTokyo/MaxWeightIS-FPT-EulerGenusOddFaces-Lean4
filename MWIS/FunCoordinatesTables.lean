module

public import MWIS.FunCoordinatesMatrix

/-!
# The coordinate tables in `Fun`

`coordFn` reads the endpoint pairs of the edges, the stub codes of the face columns, the
vertex count, the face count and the root. It returns the free rank and, for every edge
`e`, the free coordinates `freeMap (Pi.single e 1)`, the parity row
`parityRow (Pi.single e 1)` and the residue label of `Pi.single e 1`: its parity value in
`{0, 1}` and its free coordinates reduced into `[0, modulus rank)`.
-/

@[expose] public section

namespace MWIS.FunCoordinates

open MWIS.Fun MWIS.FunLP MWIS.TreeCotree

/-! ## Programs -/

/-- The argument: edges, column codes, vertex count, face count, root. -/
abbrev CoordArg : Ty :=
  .prod (.list (.prod .int .int)) (.prod (.list (.list .int)) (.prod .int (.prod .int .int)))

/-- The table row of one edge: free coordinates, parity row, residue parity, residue
coordinates. -/
abbrev RowTy : Ty := .prod (.list .int) (.prod .int (.prod .int (.list .int)))

/-- The output: the free rank and the rows of all edges. -/
abbrev CoordOut : Ty := .prod .int (.list RowTy)

/-- `(P, (l, r)) ↦ (P[l] + P[r]) / 2`. -/
def halfItem : Fn (.prod (.list .int) (.prod .int .int)) .int :=
  .arith .div (.arith .add (call getIntFn (.pair (.fst v0) (.fst (.snd v0))))
    (call getIntFn (.pair (.fst v0) (.snd (.snd v0))))) (.int 2)

/-- `((P, u), (k, (l, r))) ↦ [k = u] - (P[l] + P[r])`. -/
def residItem : Fn (.prod (.prod (.list .int) .int) (.prod .int (.prod .int .int))) .int :=
  .arith .sub (.ite (.cmp .eq (.fst (.snd v0)) (.snd (.fst v0))) (.int 1) (.int 0))
    (.arith .add (call getIntFn (.pair (.fst (.fst v0)) (.fst (.snd (.snd v0)))))
      (call getIntFn (.pair (.fst (.fst v0)) (.snd (.snd (.snd v0))))))

/-- One step of the coordinate-edge filter. -/
def ceStep : Expr [.prod .int .bool, .list .int, .prod .int (.list .bool)] (.list .int) :=
  .ite (.snd v0) (.ite (.cmp .eq (.fst v0) (.fst v2)) v1 (.cons (.fst v0) v1)) v1

/-- `(j, F)`: the positions flagged in `F`, other than `j`. -/
def coordEdgesFn : Fn (.prod .int (.list .bool)) (.list .int) :=
  call (crevFn .int) (.foldl (call (indexedFn .bool) (.snd v0)) .nil ceStep)

/-- The length of a list. -/
def lengthFn (a : Ty) : Fn (.list a) .int := .foldl v0 (.int 0) (.arith .add v1 (.int 1))

/-- `((res, (lead, H)), c) ↦ res[c] - lead * H[c]`. -/
def freeItem : Fn (.prod (.prod (.list .int) (.prod .int (.list .int))) .int) .int :=
  .arith .sub (call getIntFn (.pair (.fst (.fst v0)) (.snd v0)))
    (.arith .mul (.fst (.snd (.fst v0))) (call getIntFn (.pair (.snd (.snd (.fst v0))) (.snd v0))))

/-- `(M, x) ↦ x mod M`. -/
def modItem : Fn (.prod .int .int) .int := .arith .mod (.snd v0) (.fst v0)

/-- The data shared by the rows: `((T, edges), ((n, root), ((H, j), (CE, M))))`. -/
abbrev EdgeParam : Ty :=
  .prod (.prod (.list (.prod .int .int)) (.list (.prod .int .int)))
    (.prod (.prod .int .int) (.prod (.prod (.list .int) .int) (.prod (.list .int) .int)))

/-- The table row of edge `k`. The variable `v0` is `(param, (k, (l, r)))`. -/
def edgeItem : Fn (.prod EdgeParam (.prod .int (.prod .int .int))) RowTy :=
  .letE (call potFn (.pair (.fst (.fst (.fst v0))) (.pair (.snd (.fst (.fst v0)))
      (.pair (.fst (.fst (.snd (.fst v0)))) (.pair (.snd (.fst (.snd (.fst v0))))
        (.pair (.fst (.snd v0)) (.int 0)))))))
    (.letE (call (mapIdxFn residItem) (.pair (.pair v0 (.fst (.snd v1))) (.snd (.fst (.fst v1)))))
      (.letE (.ite (.cmp .lt (.snd (.fst (.snd (.snd (.fst v2))))) (.int 0)) (.int 0)
          (call getIntFn (.pair v0 (.snd (.fst (.snd (.snd (.fst v2))))))))
        (.letE (.arith .mul (call getIntFn (.pair (.fst (.fst (.snd (.snd (.fst v3)))))
            (.snd (.fst (.snd (.snd (.fst v3))))))) v0)
          (.letE (call (cmapFn freeItem) (.pair (.pair v2 (.pair v0 (.fst (.fst (.snd (.snd (.fst v4)))))))
              (.fst (.snd (.snd (.snd (.fst v4)))))))
            (.pair v0 (.pair v2 (.pair (.arith .mod v2 (.int 2))
              (call (cmapFn modItem) (.pair (.snd (.snd (.snd (.snd (.fst v5))))) v0)))))))))

/-- The coordinate tables. -/
def coordFn : Fn CoordArg CoordOut :=
  .letE (call treeFn (.pair (.fst v0) (.pair (.fst (.snd (.snd v0))) (.snd (.snd (.snd (.snd v0)))))))
    (.letE (call freeFn (.pair v0 (.pair (.fst v1) (.pair (.fst (.snd v1))
        (.fst (.snd (.snd (.snd v1))))))))
      (.letE (call (cmapFn halfItem) (.pair (call potFn (.pair v1 (.pair (.fst v2)
          (.pair (.fst (.snd (.snd v2))) (.pair (.snd (.snd (.snd (.snd v2))))
            (.pair (.int (-1)) (.int 1))))))) (.fst v2)))
        (.letE (call nonzeroInFn (.pair v1 v0))
          (.letE (call coordEdgesFn (.pair v0 v2))
            (.letE (call (lengthFn .int) v0)
              (.pair v0 (call (mapIdxFn edgeItem)
                (.pair (.pair (.pair v5 (.fst v6))
                    (.pair (.pair (.fst (.snd (.snd v6))) (.snd (.snd (.snd (.snd v6)))))
                      (.pair (.pair v3 v2)
                        (.pair v1 (.ite (.cmp .eq v0 (.int 0)) (.int 2) (.arith .mul (.int 4) v0))))))
                  (.fst v6)))))))))

/-! ## List specifications -/

/-- Half the incidence of a vertex list at an edge. -/
def halfS (P : List ℤ) (lr : ℤ × ℤ) : ℤ := (getI P 0 lr.1 + getI P 0 lr.2) / 2

/-- The residual of the unit vector at `u` from its tree potential `P`. -/
def residS (P : List ℤ) (u : ℤ) (edges : List (ℤ × ℤ)) : List ℤ :=
  edges.mapIdx fun k lr => unitAt u k - (getI P 0 lr.1 + getI P 0 lr.2)

/-- The flagged positions other than `j`. -/
def coordEdgesS (j : ℤ) (F : List Bool) : List ℤ :=
  ((indexed F).filter fun kb => kb.2 && !decide (kb.1 = j)).map Prod.fst

/-- The table row of edge `k`. -/
def edgeS (T edges : List (ℤ × ℤ)) (n root : ℤ) (H : List ℤ) (j : ℤ) (CE : List ℤ) (M k : ℤ) :
    List ℤ × ℤ × ℤ × List ℤ :=
  let res := residS (potFn.apply (T, (edges, (n, (root, (k, 0)))))) k edges
  let par := if j < 0 then 0 else getI res 0 j
  let lead := getI H 0 j * par
  let fr := CE.map fun c => getI res 0 c - lead * getI H 0 c
  (fr, (par, (par % 2, fr.map (· % M))))

/-- The coordinate tables on lists. -/
def coordS (x : CoordArg.denote) : ℤ × List (List ℤ × ℤ × ℤ × List ℤ) :=
  let edges := x.1
  let n := x.2.2.1
  let root := x.2.2.2.2
  let T := treeFn.apply (edges, (n, root))
  let F := freeFn.apply (T, (edges, (x.2.1, x.2.2.2.1)))
  let H := edges.map (halfS (potFn.apply (T, (edges, (n, (root, (-1, 1)))))))
  let j := nonzeroInS F H
  let CE := coordEdgesS j F
  let R : ℤ := CE.length
  (R, edges.mapIdx fun k _ =>
    edgeS T edges n root H j CE (if R = 0 then 2 else 4 * R) k)

/-! ## Denotations -/

@[simp] theorem halfItem_apply (x : (Ty.prod (.list .int) (.prod .int .int)).denote) :
    halfItem.apply x = halfS x.1 x.2 := by
  rw [Fn.apply]
  simp only [halfItem, halfS, Expr.denote, Var.get, denote_call, getIntFn_apply', IntOp.eval]

@[simp] theorem residItem_apply
    (x : (Ty.prod (.prod (.list .int) .int) (.prod .int (.prod .int .int))).denote) :
    residItem.apply x = unitAt x.1.2 x.2.1 - (getI x.1.1 0 x.2.2.1 + getI x.1.1 0 x.2.2.2) := by
  rw [Fn.apply]
  by_cases h : x.2.1 = x.1.2 <;>
    simp [residItem, unitAt, Expr.denote, Var.get, denote_call, getIntFn_apply', IntOp.eval,
      CmpOp.eval, h]

theorem foldl_cons_filter {α β : Type*} (p : α → Bool) (g : α → β) (l : List α) (acc : List β) :
    l.foldl (fun acc x => if p x then g x :: acc else acc) acc = ((l.filter p).map g).reverse ++ acc := by
  induction l generalizing acc with
  | nil => simp
  | cons x l ih =>
    rw [List.foldl_cons, ih]
    by_cases h : p x <;> simp [h, List.filter_cons]

@[simp] theorem coordEdgesFn_apply (x : (Ty.prod .int (.list .bool)).denote) :
    coordEdgesFn.apply x = coordEdgesS x.1 x.2 := by
  rw [Fn.apply]
  simp only [coordEdgesFn, Expr.denote, Var.get, denote_call, indexedFn_apply, crevFn_apply]
  have hs : (fun (acc : List ℤ) (y : ℤ × Bool) => ceStep.denote (y, acc, (x, ()))) =
      fun acc y => if (fun kb : ℤ × Bool => kb.2 && !decide (kb.1 = x.1)) y then y.1 :: acc
        else acc := by
    funext acc y
    obtain ⟨k, b⟩ := y
    by_cases h : k = x.1 <;> cases b <;>
      simp [ceStep, Expr.denote, Var.get, CmpOp.eval, h]
  rw [hs, foldl_cons_filter]
  simp [coordEdgesS]

@[simp] theorem lengthFn_apply (a : Ty) (l : (Ty.list a).denote) :
    (lengthFn a).apply l = l.length := by
  rw [Fn.apply]
  simp only [lengthFn, Expr.denote, Var.get, IntOp.eval]
  have : ∀ (l : List a.denote) (k : ℤ), l.foldl (fun acc _ => acc + 1) k = k + l.length := by
    intro l
    induction l with
    | nil => simp
    | cons y l ih => intro k; rw [List.foldl_cons, ih]; simp; ring
  rw [this]
  simp

@[simp] theorem freeItem_apply
    (x : (Ty.prod (.prod (.list .int) (.prod .int (.list .int))) .int).denote) :
    freeItem.apply x = getI x.1.1 0 x.2 - x.1.2.1 * getI x.1.2.2 0 x.2 := by
  rw [Fn.apply]
  simp only [freeItem, Expr.denote, Var.get, denote_call, getIntFn_apply', IntOp.eval]

@[simp] theorem modItem_apply (x : (Ty.prod .int .int).denote) : modItem.apply x = x.2 % x.1 := by
  rw [Fn.apply]
  simp only [modItem, Expr.denote, Var.get, IntOp.eval]

@[simp] theorem edgeItem_apply (x : (Ty.prod EdgeParam (.prod .int (.prod .int .int))).denote) :
    edgeItem.apply x = edgeS x.1.1.1 x.1.1.2 x.1.2.1.1 x.1.2.1.2 x.1.2.2.1.1 x.1.2.2.1.2
      x.1.2.2.2.1 x.1.2.2.2.2 x.2.1 := by
  rw [Fn.apply]
  simp only [edgeItem, edgeS, residS, Expr.denote, Var.get, denote_call, getIntFn_apply',
    mapIdxFn_apply', residItem_apply, cmapFn_apply', freeItem_apply, modItem_apply, IntOp.eval,
    CmpOp.eval]
  by_cases h : x.1.2.2.1.2 < 0 <;> simp [h]

theorem coordFn_apply (x : CoordArg.denote) : coordFn.apply x = coordS x := by
  rw [Fn.apply]
  simp only [coordFn, coordS, Expr.denote, Var.get, denote_call, cmapFn_apply', halfItem_apply,
    nonzeroInFn_apply, coordEdgesFn_apply, lengthFn_apply, mapIdxFn_apply', edgeItem_apply,
    CmpOp.eval, IntOp.eval]
  by_cases h : ((coordEdgesS (nonzeroInS
      (freeFn.apply (treeFn.apply (x.1, x.2.2.1, x.2.2.2.2), x.1, x.2.1, x.2.2.2.1))
      (x.1.map (halfS (potFn.apply (treeFn.apply (x.1, x.2.2.1, x.2.2.2.2), x.1, x.2.2.1,
        x.2.2.2.2, -1, 1)))))
      (freeFn.apply (treeFn.apply (x.1, x.2.2.1, x.2.2.2.2), x.1, x.2.1, x.2.2.2.1))).length : ℤ) = 0 <;>
    simp [h]

/-! ## Agreement with the quotient coordinates -/

variable {f m n : ℕ} (left right : Fin m → Fin n) (C : Fin m → Walks.Column (Fin f)) (root : Fin n)

/-- The table row of edge `e`: free coordinates, parity row and residue label of `1_e`. -/
def coordRow (e : Fin m) : List ℤ × ℤ × ℤ × List ℤ :=
  (List.ofFn fun i => freeMap left right C root (Pi.single e 1) i,
    (parityRow left right C root (Pi.single e 1),
      (((residueLabel left right C root (Pi.single e 1)).1.val : ℕ) : ℤ),
        List.ofFn fun i => ((((residueLabel left right C root (Pi.single e 1)).2 i).val : ℕ) : ℤ)))

theorem unitAt_single (e : Fin m) :
    (fun d : Fin m => unitAt ((e : ℕ) : ℤ) ((d : ℕ) : ℤ)) = Pi.single e 1 := by
  funext d
  by_cases h : d = e
  · subst h; simp [unitAt]
  · have : ¬ (((d : ℕ) : ℤ) = ((e : ℕ) : ℤ)) := fun h' => h (Fin.ext (by exact_mod_cast h'))
    simp [unitAt, this, h]

theorem unitAt_neg (d : Fin m) : unitAt (-1) ((d : ℕ) : ℤ) = 0 := by
  unfold unitAt
  have : ¬ (((d : ℕ) : ℤ) = -1) := by omega
  simp [this]

theorem potFn_parity :
    potFn.apply (treeCode (tree left right root),
      (edgeList left right, ((n : ℤ), (((root : ℕ) : ℤ), (-1, 1))))) =
      vertexList (parityPotential left right root) := by
  rw [potFn_potential]
  unfold parityPotential
  rw [show (fun d : Fin m => unitAt (-1) ((d : ℕ) : ℤ)) = 0 from funext unitAt_neg]

theorem potFn_single (e : Fin m) :
    potFn.apply (treeCode (tree left right root),
      (edgeList left right, ((n : ℤ), (((root : ℕ) : ℤ), (((e : ℕ) : ℤ), 0))))) =
      vertexList (treePotential left right root (Pi.single e 1)) := by
  rw [potFn_potential, unitAt_single]
  rfl

theorem halfList_eq :
    (edgeList left right).map (halfS (vertexList (parityPotential left right root))) =
      List.ofFn fun e => half left right root e := by
  simp only [edgeList, List.map_ofFn]
  congr 1
  funext e
  simp [halfS, vertexList, getI_ofFn, half, IncidenceSplit.incidence]

theorem residS_eq (e : Fin m) :
    residS (vertexList (treePotential left right root (Pi.single e 1))) ((e : ℕ) : ℤ)
        (edgeList left right) =
      List.ofFn fun e' => residual left right root (Pi.single e 1) e' := by
  simp only [residS, edgeList, mapIdx_ofFn]
  congr 1
  funext e'
  rw [residual_apply]
  have h := congrFun (unitAt_single e) e'
  simp [vertexList, getI_ofFn, IncidenceSplit.incidence, h]

theorem pivot_eq :
    nonzeroInS (freeList left right C root) (List.ofFn fun e => half left right root e) =
      optInt ((pivotEdge left right C root).map Fin.val) := by
  unfold nonzeroInS pivotEdge
  rw [indexed_ofFn, findIdx?_ofFn]
  congr 3
  funext e
  simp [nonzeroP, freeList, getI_ofFn]

theorem coordEdges_eq :
    coordEdgesS (optInt ((pivotEdge left right C root).map Fin.val)) (freeList left right C root) =
      (coordEdges left right C root).map fun e : Fin m => ((e : ℕ) : ℤ) := by
  unfold coordEdgesS freeList coordEdges
  rw [indexed_ofFn, List.ofFn_eq_map, List.filter_map, List.map_map]
  congr 1
  apply List.filter_congr
  intro e _
  simp only [Function.comp_apply]
  cases hp : pivotEdge left right C root with
  | none =>
    have : ¬ (((e : ℕ) : ℤ) = -1) := by omega
    simp [optInt, this]
  | some j =>
    by_cases h : j = e
    · subst h; simp [optInt]
    · have : ¬ (((e : ℕ) : ℤ) = ((j : ℕ) : ℤ)) :=
        fun h' => h (Fin.ext (by exact_mod_cast h'.symm))
      simp [optInt, this, h]

theorem modulus_int :
    (if ((rank left right C root : ℕ) : ℤ) = 0 then 2 else 4 * ((rank left right C root : ℕ) : ℤ)) =
      ((GroupSize.modulus (rank left right C root) : ℕ) : ℤ) := by
  unfold GroupSize.modulus
  by_cases h : rank left right C root = 0 <;> simp [h]

theorem parity_eq (e : Fin m) :
    (if optInt ((pivotEdge left right C root).map Fin.val) < 0 then 0 else
      getI (List.ofFn fun e' => residual left right root (Pi.single e 1) e') 0
        (optInt ((pivotEdge left right C root).map Fin.val))) =
      parityRow left right C root (Pi.single e 1) := by
  cases hp : pivotEdge left right C root with
  | none => simp [optInt, parityRow, hp]
  | some j =>
    have : ¬ (((j : ℕ) : ℤ) < 0) := by omega
    simp [optInt, parityRow, hp, this, getI_ofFn]

theorem lead_eq' (e : Fin m) :
    getI (List.ofFn fun e => half left right root e) 0
        (optInt ((pivotEdge left right C root).map Fin.val)) *
      parityRow left right C root (Pi.single e 1) = lead left right C root (Pi.single e 1) := by
  cases hp : pivotEdge left right C root with
  | none => simp [optInt, parityRow, lead, hp]
  | some j => simp [optInt, parityRow, lead, hp, getI_ofFn]

theorem freeRow_eq (e : Fin m) :
    ((coordEdges left right C root).map fun e : Fin m => ((e : ℕ) : ℤ)).map
        (fun c => getI (List.ofFn fun e' => residual left right root (Pi.single e 1) e') 0 c -
          lead left right C root (Pi.single e 1) *
            getI (List.ofFn fun e => half left right root e) 0 c) =
      List.ofFn fun i => freeMap left right C root (Pi.single e 1) i := by
  apply List.ext_getElem (by simp [rank])
  intro k h1 h2
  simp [freeMap, coordEdge, getI_ofFn]
  rfl

theorem edgeS_eq (e : Fin m) :
    edgeS (treeCode (tree left right root)) (edgeList left right) (n : ℤ) ((root : ℕ) : ℤ)
        (List.ofFn fun e => half left right root e)
        (optInt ((pivotEdge left right C root).map Fin.val))
        ((coordEdges left right C root).map fun e : Fin m => ((e : ℕ) : ℤ))
        (if ((rank left right C root : ℕ) : ℤ) = 0 then 2 else 4 * ((rank left right C root : ℕ) : ℤ))
        ((e : ℕ) : ℤ) = coordRow left right C root e := by
  unfold edgeS coordRow
  rw [potFn_single left right root e]
  simp only [ residS_eq, parity_eq, lead_eq', freeRow_eq, modulus_int,
    Prod.mk.injEq, true_and, List.map_ofFn]
  constructor
  · show _ = (((((parityRow left right C root (Pi.single e 1) : ℤ) : ZMod 2)).val : ℕ) : ℤ)
    rw [ZMod.val_intCast]
    norm_num
  · congr 1
    funext i
    show _ = (((((freeMap left right C root (Pi.single e 1) i : ℤ) :
      ZMod (GroupSize.modulus (rank left right C root)))).val : ℕ) : ℤ)
    rw [ZMod.val_intCast]
    rfl

/-- **The coordinate program computes the rank and the coordinate tables.** -/
theorem coordFn_tables :
    coordFn.apply (edgeList left right, (colList C, ((n : ℤ), ((f : ℤ), ((root : ℕ) : ℤ))))) =
      ((rank left right C root : ℤ), List.ofFn (coordRow left right C root)) := by
  rw [coordFn_apply]
  unfold coordS
  dsimp only
  rw [treeFn_tree left right root, freeFn_free left right C root, potFn_parity left right root,
    halfList_eq, pivot_eq, coordEdges_eq, List.length_map]
  have hR : (((coordEdges left right C root).length : ℕ) : ℤ) = ((rank left right C root : ℕ) : ℤ) :=
    rfl
  rw [hR]
  simp only [Prod.mk.injEq, true_and]
  conv_lhs => rw [edgeList, mapIdx_ofFn]
  congr 1
  funext e
  exact edgeS_eq left right C root e

end MWIS.FunCoordinates

end
