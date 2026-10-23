module

public import MWIS.FunNetworkFn

/-!
# The `Fun` network program

`networkFn` computes the encoded dense network program from the encoded network
input. With `encodedProgram_eq` it computes `DenseProgram.toFun` of the network
program `FPTHard.program C D c rowsEquiv colsEquiv` (`networkFn_correct`).
`offsetFn` and `bitsFn` compute the threshold-search offset `2 · total c` and the
search width `searchBits c`; `decodeFn` computes the decoded slack
`decode m (total c - value)`.

Prepared 2026-10-23.
-/

@[expose] public section

namespace MWIS.FunNetwork

open MWIS.Fun MWIS.FunLP FPTHard

/-! ## Columns -/

/-- `((v, μ, a), g) ↦ (v, a, g, addE μ g lab(a))`. -/
def colF3 : Fn (.prod (.prod .int (.prod .int tArc)) tL) tCol :=
  .pair (.fst (.fst v0))
    (.pair (.snd (.snd (.fst v0)))
      (.pair (.snd v0)
        (call addFn (.pair (.fst (.snd (.fst v0)))
          (.pair (.snd v0) (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.fst v0)))))))))))))

/-- `((v, μ, groups), a) ↦ groups.map (colF3 (v, μ, a))`. -/
def colF2 : Fn (.prod (.prod .int (.prod .int (.list tL))) tArc) (.list tCol) :=
  call (mapWith colF3)
    (.pair (.pair (.fst (.fst v0)) (.pair (.fst (.snd (.fst v0))) (.snd v0))) (.snd (.snd (.fst v0))))

/-- `((μ, arcs, groups), v) ↦ arcs.flatMap (colF2 (v, μ, groups))`. -/
def colF1 : Fn (.prod (.prod .int (.prod (.list tArc) (.list tL))) .int) (.list tCol) :=
  call (flatMapWith colF2)
    (.pair (.pair (.snd v0) (.pair (.fst (.fst v0)) (.snd (.snd (.fst v0))))) (.fst (.snd (.fst v0))))

/-- `(μ, states, arcs, groups) ↦ colsE μ states arcs groups`. -/
def colsFn : Fn (.prod .int (.prod tL (.prod (.list tArc) (.list tL)))) (.list tCol) :=
  call (flatMapWith colF1)
    (.pair (.pair (.fst v0) (.pair (.fst (.snd (.snd v0))) (.snd (.snd (.snd v0))))) (.fst (.snd v0)))

@[simp] theorem colsFn_apply (x : ℤ × List ℤ × List ArcRec × List (List ℤ)) :
    colsFn.apply x = colsE x.1 x.2.1 x.2.2.1 x.2.2.2 := by
  rw [Fn.apply]; unfold colsFn
  simp only [denote_call, Expr.denote, Var.get, flatMapWith_apply]
  unfold colsE
  apply List.flatMap_congr; intro v _
  rw [Fn.apply]; unfold colF1
  simp only [denote_call, Expr.denote, Var.get, flatMapWith_apply]
  apply List.flatMap_congr; intro a _
  rw [Fn.apply]; unfold colF2
  simp only [denote_call, Expr.denote, Var.get, mapWith_apply]
  apply List.map_congr_left; intro g _
  rw [Fn.apply]; unfold colF3
  simp only [denote_call, Expr.denote, Var.get, addFn_apply]

/-! ## Nodes -/

/-- `(_, g) ↦ (-1, -1, g)`. -/
def hubFn : Fn (.prod .unit tL) tNode := .pair (.int (-1)) (.pair (.int (-1)) (.snd v0))

/-- `((v, u), g) ↦ (v, u, g)`. -/
def nodeF3 : Fn (.prod (.prod .int .int) tL) tNode :=
  .pair (.fst (.fst v0)) (.pair (.snd (.fst v0)) (.snd v0))

/-- `((v, groups), u) ↦ if u = v then [] else groups.map (v, u, ·)`. -/
def nodeF2 : Fn (.prod (.prod .int (.list tL)) .int) (.list tNode) :=
  .ite (.cmp .eq (.snd v0) (.fst (.fst v0))) .nil
    (call (mapWith nodeF3) (.pair (.pair (.fst (.fst v0)) (.snd v0)) (.snd (.fst v0))))

/-- `((states, groups), v) ↦ states.flatMap (nodeF2 (v, groups))`. -/
def nodeF1 : Fn (.prod (.prod tL (.list tL)) .int) (.list tNode) :=
  call (flatMapWith nodeF2) (.pair (.pair (.snd v0) (.snd (.fst v0))) (.fst (.fst v0)))

/-- `(states, groups) ↦ nodesE states groups`. -/
def nodesFn : Fn (.prod tL (.list tL)) (.list tNode) :=
  call (appendFn tNode) (.pair (call (mapWith hubFn) (.pair .unit (.snd v0)))
    (call (flatMapWith nodeF1) (.pair v0 (.fst v0))))

@[simp] theorem nodesFn_apply (x : List ℤ × List (List ℤ)) :
    nodesFn.apply x = nodesE x.1 x.2 := by
  rw [Fn.apply]; unfold nodesFn
  simp only [denote_call, Expr.denote, Var.get, appendFn_apply, mapWith_apply, flatMapWith_apply]
  unfold nodesE
  congr 1
  apply List.flatMap_congr; intro v _
  rw [Fn.apply]; unfold nodeF1
  simp only [denote_call, Expr.denote, Var.get, flatMapWith_apply]
  apply List.flatMap_congr; intro u _
  rw [Fn.apply]; unfold nodeF2
  simp only [denote_call, Expr.denote, Var.get, mapWith_apply, CmpOp.eval, decide_eq_true_eq]
  by_cases h : u = v
  · simp [h]
  · simp only [h, ↓reduceIte]
    rfl

/-! ## Rows -/

/-- The dummy node record. -/
def dummyFn {Γ : List Ty} : Expr Γ tNode := .pair (.int (-2)) (.pair (.int (-2)) .nil)

/-- `(_, i) ↦ (0, 0, i, dummy)`. -/
def idxRowFn : Fn (.prod .unit .int) tRow := .pair (.int 0) (.pair (.int 0) (.pair (.snd v0) dummyFn))

/-- `(_, u) ↦ (1, 0, u)`. -/
def eqNodeFn : Fn (.prod .unit tNode) tEq := .pair (.int 1) (.pair (.int 0) (.snd v0))

/-- `(_, d) ↦ (2, d, dummy)`. -/
def eqCoordFn : Fn (.prod .unit .int) tEq := .pair (.int 2) (.pair (.snd v0) dummyFn)

/-- `(nodes, r) ↦ eqE nodes r`. -/
def eqFn : Fn (.prod (.list tNode) .int) (.list tEq) :=
  call (appendFn tEq) (.pair (call (mapWith eqNodeFn) (.pair .unit (.fst v0)))
    (call (mapWith eqCoordFn) (.pair .unit (call range (.snd v0)))))

/-- `(_, ρ) ↦ signedRows ρ`. -/
def signedFn : Fn (.prod .unit tEq) (.list tRow) :=
  .cons (.pair (.fst (.snd v0)) (.pair (.int 1) (.snd (.snd v0))))
    (.cons (.pair (.fst (.snd v0)) (.pair (.int (-1)) (.snd (.snd v0)))) .nil)

/-- `(N, nodes, r) ↦ rowsE N nodes r`. -/
def rowsFn : Fn (.prod .int (.prod (.list tNode) .int)) (.list tRow) :=
  call (appendFn tRow) (.pair (call (mapWith idxRowFn) (.pair .unit (call range (.fst v0))))
    (call (flatMapWith signedFn) (.pair .unit (call eqFn (.snd v0)))))

@[simp] theorem rowsFn_apply (x : ℤ × List NodeE × ℤ) : rowsFn.apply x = rowsE x.1 x.2.1 x.2.2 := by
  rw [Fn.apply]; unfold rowsFn
  simp only [denote_call, Expr.denote, Var.get, appendFn_apply, mapWith_apply, flatMapWith_apply,
    range_apply]
  unfold rowsE
  congr 1
  rw [Fn.apply]; unfold eqFn
  simp only [denote_call, Expr.denote, Var.get, appendFn_apply, mapWith_apply, range_apply]
  rfl

/-! ## Entries -/

/-- `(a, b) ↦ decide (a = b)` for node records. -/
def nodeEqFn : Fn (.prod tNode tNode) .bool :=
  .ite (.cmp .eq (.fst (.fst v0)) (.fst (.snd v0)))
    (.ite (.cmp .eq (.fst (.snd (.fst v0))) (.fst (.snd (.snd v0))))
      (call eqList (.pair (.snd (.snd (.fst v0))) (.snd (.snd (.snd v0))))) (.bool false))
    (.bool false)

@[simp] theorem nodeEqFn_apply (x : NodeE × NodeE) : nodeEqFn.apply x = decide (x.1 = x.2) := by
  rcases x with ⟨⟨a, b, g⟩, ⟨a', b', g'⟩⟩
  rw [Fn.apply]; unfold nodeEqFn
  simp only [denote_call, Expr.denote, Var.get, CmpOp.eval, eqList_apply, decide_eq_true_eq]
  by_cases h1 : a = a' <;> by_cases h2 : b = b' <;> simp [h1, h2]

/-- `(v, u, g) ↦ stateE v u g`. -/
def stateFn : Fn (.prod .int (.prod .int tL)) tNode :=
  .ite (.cmp .eq (.fst (.snd v0)) (.fst v0))
    (.pair (.int (-1)) (.pair (.int (-1)) (.snd (.snd v0))))
    (.pair (.fst v0) (.pair (.fst (.snd v0)) (.snd (.snd v0))))

@[simp] theorem stateFn_apply (x : ℤ × ℤ × List ℤ) : stateFn.apply x = stateE x.1 x.2.1 x.2.2 := by
  rcases x with ⟨v, u, g⟩
  rw [Fn.apply]; unfold stateFn
  simp only [Expr.denote, Var.get, CmpOp.eval, decide_eq_true_eq, stateE]
  by_cases h : u = v <;> simp [h]

/-- `(w, d) ↦ nthE w d`. -/
def nthFn : Fn (.prod tL .int) .int :=
  .snd (.foldl (.fst v0) (.pair (.int 0) (.int 0))
    (.pair (.arith .add (.fst v1) (.int 1)) (.ite (.cmp .eq (.fst v1) (.snd v2)) v0 (.snd v1))))

@[simp] theorem nthFn_apply (x : List ℤ × ℤ) : nthFn.apply x = nthE x.1 x.2 := by
  rw [Fn.apply]; unfold nthFn nthE
  simp only [Expr.denote, Var.get, IntOp.eval, CmpOp.eval]
  rw [List.foldl_ext _ (fun (s : ℤ × ℤ) a => (s.1 + 1, if s.1 = x.2 then a else s.2))]
  intro s a _
  by_cases h : s.1 = x.2 <;> simp [h]

/-- Indicator of a Boolean expression. -/
def b2i {Γ : List Ty} (e : Expr Γ .bool) : Expr Γ .int := .ite e (.int 1) (.int 0)

/-- `(row, jc) ↦ entryE row jc`. -/
def entryFn : Fn (.prod tRow tColI) .int :=
  .ite (.cmp .eq (.fst (.fst v0)) (.int 0))
    (.ite (.cmp .eq (.fst (.snd (.snd (.fst v0)))) (.fst (.snd v0))) (.int (-1)) (.int 0))
    (.ite (.cmp .eq (.fst (.fst v0)) (.int 1))
      (.arith .mul (.fst (.snd (.fst v0)))
        (.arith .sub
          (b2i (call nodeEqFn (.pair
            (call stateFn (.pair (.fst (.snd (.snd v0)))
              (.pair (.fst (.snd (.snd (.snd (.fst (.snd (.snd (.snd v0))))))))
                (.snd (.snd (.snd (.snd (.snd v0))))))))
            (.snd (.snd (.snd (.fst v0)))))))
          (b2i (call nodeEqFn (.pair
            (call stateFn (.pair (.fst (.snd (.snd v0)))
              (.pair (.fst (.snd (.snd (.fst (.snd (.snd (.snd v0)))))))
                (.fst (.snd (.snd (.snd (.snd v0))))))))
            (.snd (.snd (.snd (.fst v0)))))))))
      (.arith .mul (.fst (.snd (.fst v0)))
        (call nthFn (.pair
          (.fst (.snd (.snd (.snd (.snd (.snd (.fst (.snd (.snd (.snd v0))))))))))
          (.fst (.snd (.snd (.fst v0))))))))

@[simp] theorem entryFn_apply (x : RowE × ColI) : entryFn.apply x = entryE x.1 x.2 := by
  rcases x with ⟨⟨t, sg, d, nd⟩, ⟨j, ⟨v, ⟨⟨e, b, src, tgt, lab, w, ob⟩, ⟨g, gT⟩⟩⟩⟩⟩
  rw [Fn.apply]; unfold entryFn b2i
  simp only [denote_call, Expr.denote, Var.get, IntOp.eval, CmpOp.eval,
    nodeEqFn_apply, stateFn_apply, nthFn_apply, entryE]
  by_cases h0 : t = 0
  · subst h0
    by_cases h1 : d = j <;> simp [h1]
  · by_cases h1 : t = 1
    · subst h1
      by_cases hA : stateE v tgt gT = nd <;> by_cases hB : stateE v src g = nd <;> simp [hA, hB]
    · simp [h0, h1]

/-- `((η0, z0), row) ↦ rhsE η0 z0 row`. -/
def rhsFn : Fn (.prod (.prod tL tL) tRow) .int :=
  .ite (.cmp .eq (.fst (.snd v0)) (.int 1))
    (.arith .mul (.fst (.snd (.snd v0)))
      (.arith .sub
        (b2i (call nodeEqFn (.pair (.snd (.snd (.snd (.snd v0))))
          (.pair (.int (-1)) (.pair (.int (-1)) (.fst (.fst v0)))))))
        (b2i (call nodeEqFn (.pair (.snd (.snd (.snd (.snd v0))))
          (.pair (.int (-1)) (.pair (.int (-1)) (.snd (.fst v0)))))))))
    (.int 0)

@[simp] theorem rhsFn_apply (x : (List ℤ × List ℤ) × RowE) : rhsFn.apply x = rhsE x.1.1 x.1.2 x.2 := by
  rw [Fn.apply]; unfold rhsFn b2i
  rcases x with ⟨⟨η0, z0⟩, ⟨t, sg, d, nd⟩⟩
  simp only [denote_call, Expr.denote, Var.get, IntOp.eval, CmpOp.eval, nodeEqFn_apply, rhsE]
  by_cases h1 : t = 1
  · subst h1
    by_cases hA : nd = (-1, -1, η0) <;> by_cases hB : nd = (-1, -1, z0) <;> simp [hA, hB]
  · simp [h1]

/-- `(_, jc) ↦ objE jc`. -/
def objFn : Fn (.prod .unit tColI) .int :=
  .snd (.snd (.snd (.snd (.snd (.snd (.fst (.snd (.snd (.snd v0)))))))))

@[simp] theorem objFn_apply (x : Unit × ColI) : objFn.apply x = objE x.2 := rfl

/-- `(colsI, row) ↦ colsI.map (entryE row)`. -/
def rowMatFn : Fn (.prod (.list tColI) tRow) tL :=
  call (mapWith entryFn) (.pair (.snd v0) (.fst v0))

@[simp] theorem rowMatFn_apply (x : List ColI × RowE) :
    rowMatFn.apply x = x.1.map (entryE x.2) := by
  rw [Fn.apply]; unfold rowMatFn
  simp only [denote_call, Expr.denote, Var.get, mapWith_apply, entryFn_apply]

/-! ## The network program -/

/-- The network program on the input `(f, r, μ, edges)`. -/
def networkFn : Fn tIn tOut :=
  .letE (call statesFn (.fst v0)) <|
  .letE (call groupFn (.pair (.fst (.snd v1)) (.fst (.snd (.snd v1))))) <|
  .letE (call powFn (.arith .add (call (lengthFn tE) (.snd (.snd (.snd v2)))) (.int 1))) <|
  .letE (call arcsFn (.pair v0 (.snd (.snd (.snd v3))))) <|
  .letE (call colsFn (.pair (.fst (.snd (.snd v4))) (.pair v3 (.pair v0 v2)))) <|
  .letE (call (indexFromFn tCol) v0) <|
  .letE (call nodesFn (.pair v5 v4)) <|
  .letE (call rowsFn (.pair (call (lengthFn tCol) v2) (.pair v0 (.fst (.snd v7))))) <|
  .letE (call replFn (.fst (.snd v8))) <|
  .pair (call (mapWith rowMatFn) (.pair v3 v1))
    (.pair (call (mapWith rhsFn) (.pair (.pair (.cons (.int 1) v0) (.cons (.int 0) v0)) v1))
      (call (mapWith objFn) (.pair .unit v3)))

theorem networkFn_apply (x : ℤ × ℤ × ℤ × List EdgeIn) :
    networkFn.apply x = encodedProgram x.1 x.2.1 x.2.2.1 x.2.2.2 := by
  rw [Fn.apply]; unfold networkFn
  simp only [denote_call, Expr.denote, Var.get, IntOp.eval, statesFn_apply, groupFn_apply,
    powFn_apply, lengthFn_apply, arcsFn_apply, colsFn_apply, indexFromFn_apply, nodesFn_apply,
    rowsFn_apply, replFn_apply, mapWith_apply, rowMatFn_apply, rhsFn_apply, objFn_apply]
  unfold encodedProgram
  have hP : (2 : ℤ) ^ ((x.2.2.2.length : ℤ) + 1).toNat = 2 ^ (x.2.2.2.length + 1) := by
    congr 1
  rw [hP]

/-- **The `Fun` network program computes the dense network program.** -/
theorem networkFn_correct {f m : ℕ} (C : Fin m → Walks.Column (Fin f)) (D : CoordinateData m)
    (c : Fin m → ℕ) :
    networkFn.apply (networkInput C D c) =
      DenseProgram.toFun (program C D c (rowsEquiv C D.rank) (colsEquiv C D.rank)) := by
  rw [networkFn_apply]
  exact encodedProgram_eq C D c

end MWIS.FunNetwork

end
