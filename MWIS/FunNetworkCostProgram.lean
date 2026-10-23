module

public import MWIS.FunNetworkCostLib
public import MWIS.FunNetworkProgram

/-!
# Side conditions of the network program functions

For every closed function of `MWIS.FunNetworkProgram`, the side condition
`OkAt L B` of the syntactic cost bound holds under explicit bounds on the lengths
of the lists and the sizes of the integers involved.

Prepared 2026-10-23.
-/

@[expose] public section

namespace MWIS.FunNetwork

open MWIS.Fun MWIS.FunLP

/-! ## Columns -/

theorem colF3_ok (L B A : ℕ) (x : (ℤ × ℤ × ArcRec) × List ℤ)
    (hg : ∀ z ∈ x.2, z.natAbs ≤ A) (hlab : ∀ z ∈ x.1.2.2.2.2.2.2.1, z.natAbs ≤ A)
    (hA : 2 * A ≤ B) (hμ : bits x.1.2.1 ≤ B) (hB : 2 ≤ B) (hl : x.2.length ≤ L) :
    OkAt L B colF3 x := by
  simp only [OkAt, colF3, Ok, ok_call, Expr.denote, Var.get, true_and]
  exact addFn_ok L B A _ hg hlab hA hμ hB hl

theorem colF2_length (x : (ℤ × ℤ × List (List ℤ)) × ArcRec) :
    (colF2.apply x).length = x.1.2.2.length := by
  rw [Fn.apply]; unfold colF2
  simp only [denote_call, Expr.denote, Var.get, mapWith_apply, List.length_map]

theorem colF1_length (x : (ℤ × List ArcRec × List (List ℤ)) × ℤ) :
    (colF1.apply x).length = x.1.2.1.length * x.1.2.2.length := by
  rw [Fn.apply]; unfold colF1
  simp only [denote_call, Expr.denote, Var.get, flatMapWith_apply]
  exact length_flatMap_const _ _ _ (fun a _ => colF2_length _)

theorem colF2_ok (L B A : ℕ) (x : (ℤ × ℤ × List (List ℤ)) × ArcRec)
    (hg : ∀ g ∈ x.1.2.2, g.length ≤ L ∧ ∀ z ∈ g, z.natAbs ≤ A)
    (hlab : ∀ z ∈ x.2.2.2.2.2.1, z.natAbs ≤ A)
    (hA : 2 * A ≤ B) (hμ : bits x.1.2.1 ≤ B) (hB : 2 ≤ B) (hl : x.1.2.2.length ≤ L) :
    OkAt L B colF2 x := by
  simp only [OkAt, colF2, Ok, ok_call, Expr.denote, Var.get, true_and]
  exact mapWith_ok L B _ _ hl (fun g hg' => colF3_ok L B A _ (hg g hg').2 hlab hA hμ hB (hg g hg').1)

theorem colF1_ok (L B A : ℕ) (x : (ℤ × List ArcRec × List (List ℤ)) × ℤ)
    (hg : ∀ g ∈ x.1.2.2, g.length ≤ L ∧ ∀ z ∈ g, z.natAbs ≤ A)
    (hlab : ∀ a ∈ x.1.2.1, ∀ z ∈ a.2.2.2.2.1, z.natAbs ≤ A)
    (hA : 2 * A ≤ B) (hμ : bits x.1.1 ≤ B) (hB : 2 ≤ B) (hl : x.1.2.2.length ≤ L)
    (hl1 : x.1.2.1.length ≤ L) (hl2 : x.1.2.1.length * x.1.2.2.length ≤ L) :
    OkAt L B colF1 x := by
  simp only [OkAt, colF1, Ok, ok_call, Expr.denote, Var.get, true_and]
  apply flatMapWith_ok
  · exact hl1
  · intro a ha
    exact ⟨colF2_ok L B A _ hg (hlab a ha) hA hμ hB hl, by rw [colF2_length]; exact hl⟩
  · dsimp only
    rw [length_flatMap_const _ _ x.1.2.2.length (fun a _ => colF2_length ((x.2, x.1.1, x.1.2.2), a))]
    exact hl2

theorem colsFn_ok (L B A : ℕ) (x : ℤ × List ℤ × List ArcRec × List (List ℤ))
    (hg : ∀ g ∈ x.2.2.2, g.length ≤ L ∧ ∀ z ∈ g, z.natAbs ≤ A)
    (hlab : ∀ a ∈ x.2.2.1, ∀ z ∈ a.2.2.2.2.1, z.natAbs ≤ A)
    (hA : 2 * A ≤ B) (hμ : bits x.1 ≤ B) (hB : 2 ≤ B) (hl : x.2.2.2.length ≤ L)
    (hl1 : x.2.2.1.length ≤ L) (hl2 : x.2.2.1.length * x.2.2.2.length ≤ L)
    (hl0 : x.2.1.length ≤ L) (hl3 : x.2.1.length * (x.2.2.1.length * x.2.2.2.length) ≤ L) :
    OkAt L B colsFn x := by
  simp only [OkAt, colsFn, Ok, ok_call, Expr.denote, Var.get, true_and]
  apply flatMapWith_ok
  · exact hl0
  · intro v _
    exact ⟨colF1_ok L B A _ hg hlab hA hμ hB hl hl1 hl2, by rw [colF1_length]; exact hl2⟩
  · dsimp only
    rw [length_flatMap_const _ _ (x.2.2.1.length * x.2.2.2.length)
      (fun a _ => colF1_length ((x.1, x.2.2.1, x.2.2.2), a))]
    exact hl3

/-! ## Nodes -/

theorem hubFn_ok (L B : ℕ) (x : Unit × List ℤ) : OkAt L B hubFn x := by
  simp [OkAt, hubFn, Ok]

theorem nodeF3_ok (L B : ℕ) (x : (ℤ × ℤ) × List ℤ) : OkAt L B nodeF3 x := by
  simp [OkAt, nodeF3, Ok]

theorem nodeF2_length (x : (ℤ × List (List ℤ)) × ℤ) :
    (nodeF2.apply x).length ≤ x.1.2.length := by
  rw [Fn.apply]; unfold nodeF2
  simp only [denote_call, Expr.denote, Var.get, mapWith_apply, CmpOp.eval]
  split <;> simp

theorem nodeF2_ok (L B : ℕ) (x : (ℤ × List (List ℤ)) × ℤ) (hv : bits x.1.1 ≤ B)
    (hu : bits x.2 ≤ B) (hl : x.1.2.length ≤ L) : OkAt L B nodeF2 x := by
  simp only [OkAt, nodeF2, Ok, ok_call, Expr.denote, Var.get, true_and, implies_true, true_implies, false_implies, Bool.false_eq_true, Bool.true_eq_false, and_true,]
  exact ⟨⟨hu, hv⟩, fun _ => mapWith_ok L B _ _ hl (fun _ _ => nodeF3_ok L B _)⟩

theorem nodeF1_length (x : (List ℤ × List (List ℤ)) × ℤ) :
    (nodeF1.apply x).length ≤ x.1.1.length * x.1.2.length := by
  rw [Fn.apply]; unfold nodeF1
  simp only [denote_call, Expr.denote, Var.get, flatMapWith_apply]
  exact length_flatMap_le _ _ _ (fun a _ => nodeF2_length _)

theorem nodeF1_ok (L B : ℕ) (x : (List ℤ × List (List ℤ)) × ℤ) (hv : bits x.2 ≤ B)
    (hs : ∀ u ∈ x.1.1, bits u ≤ B) (hl : x.1.2.length ≤ L) (hl0 : x.1.1.length ≤ L)
    (hl1 : x.1.1.length * x.1.2.length ≤ L) : OkAt L B nodeF1 x := by
  simp only [OkAt, nodeF1, Ok, ok_call, Expr.denote, Var.get, true_and]
  apply flatMapWith_ok
  · exact hl0
  · intro u hu
    exact ⟨nodeF2_ok L B _ hv (hs u hu) hl, (nodeF2_length _).trans hl⟩
  · dsimp only
    exact (length_flatMap_le _ _ x.1.2.length
      (fun a _ => nodeF2_length ((x.2, x.1.2), a))).trans hl1

theorem nodesFn_ok (L B : ℕ) (x : List ℤ × List (List ℤ)) (hs : ∀ u ∈ x.1, bits u ≤ B)
    (hl : x.2.length ≤ L) (hl0 : x.1.length ≤ L) (hl1 : x.1.length * x.2.length ≤ L)
    (hl2 : x.1.length * (x.1.length * x.2.length) ≤ L) : OkAt L B nodesFn x := by
  simp only [OkAt, nodesFn, Ok, ok_call, Expr.denote, Var.get, true_and, denote_call]
  refine ⟨⟨mapWith_ok L B _ _ hl (fun _ _ => hubFn_ok L B _), ?_⟩, ?_⟩
  · apply flatMapWith_ok
    · exact hl0
    · intro v hv
      exact ⟨nodeF1_ok L B _ (hs v hv) hs hl hl0 hl1, (nodeF1_length _).trans hl1⟩
    · dsimp only
      exact (length_flatMap_le _ _ (x.1.length * x.2.length)
        (fun a _ => nodeF1_length (x, a))).trans hl2
  · apply appendFn_ok
    simp only [mapWith_apply, List.length_map]; exact hl

/-! ## Rows -/

theorem eqFn_ok (L B : ℕ) (x : List NodeE × ℤ) (hl : x.1.length ≤ L) (hr : x.2.toNat ≤ L)
    (hrB : bits x.2 ≤ B) (hB : 1 ≤ B) : OkAt L B eqFn x := by
  simp only [OkAt, eqFn, Ok, ok_call, Expr.denote, Var.get, true_and, denote_call]
  refine ⟨⟨mapWith_ok L B _ _ hl (fun _ _ => by simp [OkAt, eqNodeFn, Ok]), range_ok L B _ hr hrB hB,
    mapWith_ok L B _ _ (by simp only [range_apply, List.length_map, List.length_range]; exact hr) (fun _ _ => by simp [OkAt, eqCoordFn, dummyFn, Ok])⟩, ?_⟩
  apply appendFn_ok
  simp only [mapWith_apply, List.length_map]; exact hl

theorem eqFn_length (x : List NodeE × ℤ) : (eqFn.apply x).length = x.1.length + x.2.toNat := by
  rw [Fn.apply]; unfold eqFn
  simp [denote_call, Expr.denote, Var.get, appendFn_apply, mapWith_apply, range_apply]

theorem rowsFn_ok (L B : ℕ) (x : ℤ × List NodeE × ℤ) (hN : x.1.toNat ≤ L) (hNB : bits x.1 ≤ B)
    (hl : x.2.1.length ≤ L) (hr : x.2.2.toNat ≤ L) (hrB : bits x.2.2 ≤ B) (hB : 1 ≤ B)
    (hl2 : 2 * (x.2.1.length + x.2.2.toNat) ≤ L) (h2L : 2 ≤ L) : OkAt L B rowsFn x := by
  simp only [OkAt, rowsFn, Ok, ok_call, Expr.denote, Var.get, true_and, denote_call]
  refine ⟨⟨⟨range_ok L B _ hN hNB hB, mapWith_ok L B _ _
    (by simp only [range_apply, List.length_map, List.length_range]; exact hN)
    (fun _ _ => by simp [OkAt, idxRowFn, dummyFn, Ok])⟩, eqFn_ok L B _ hl hr hrB hB, ?_⟩, ?_⟩
  · apply flatMapWith_ok
    · dsimp only; rw [eqFn_length]; omega
    · intro a _
      exact ⟨by simp [OkAt, signedFn, Ok], (show (signedFn.apply _).length = 2 from rfl).le.trans h2L⟩
    · dsimp only; rw [length_flatMap_const _ _ 2 (fun _ _ => rfl), eqFn_length]; omega
  · apply appendFn_ok
    simp only [mapWith_apply, List.length_map, range_apply, List.length_range]; exact hN

/-! ## Entries -/

/-- A list of length at most `L` with entries of absolute value at most `A`. -/
def SmallList (L A : ℕ) (g : List ℤ) : Prop := g.length ≤ L ∧ ∀ z ∈ g, z.natAbs ≤ A

/-- A node record with small entries. -/
def NodeSmall (L : ℕ) (n : NodeE) : Prop :=
  n.1.natAbs ≤ L ∧ n.2.1.natAbs ≤ L ∧ SmallList L L n.2.2

/-- A row record with small entries. -/
def RowSmall (L : ℕ) (ρ : RowE) : Prop :=
  ρ.1.natAbs ≤ L ∧ ρ.2.1.natAbs ≤ 1 ∧ ρ.2.2.1.natAbs ≤ L ∧ NodeSmall L ρ.2.2.2

/-- A numbered column record with small entries and free coordinates of binary
length at most `K`. -/
def ColSmall (L K : ℕ) (jc : ColI) : Prop :=
  jc.1.natAbs ≤ L ∧ jc.2.1.natAbs ≤ L ∧ jc.2.2.1.2.2.1.natAbs ≤ L ∧
    jc.2.2.1.2.2.2.1.natAbs ≤ L ∧ SmallList L L jc.2.2.2.1 ∧ SmallList L L jc.2.2.2.2 ∧
    jc.2.2.1.2.2.2.2.2.1.length ≤ L ∧ ∀ z ∈ jc.2.2.1.2.2.2.2.2.1, bits z ≤ K

theorem nodeEqFn_ok (L B : ℕ) (x : NodeE × NodeE) (h1 : NodeSmall L x.1) (h2 : NodeSmall L x.2)
    (hLB : L ≤ B) : OkAt L B nodeEqFn x := by
  rcases x with ⟨⟨a, b, g⟩, ⟨a', b', g'⟩⟩
  obtain ⟨ha, hb, hgl, hg⟩ := h1
  obtain ⟨ha', hb', hgl', hg'⟩ := h2
  simp only at ha hb hgl hg ha' hb' hgl' hg'
  simp only [OkAt, nodeEqFn, Ok, ok_call, Expr.denote, Var.get, true_and, implies_true, true_implies, false_implies, Bool.false_eq_true, Bool.true_eq_false, and_true,]
  exact ⟨⟨bits_le_of_natAbs (by omega), bits_le_of_natAbs (by omega)⟩,
    fun _ => ⟨⟨bits_le_of_natAbs (by omega), bits_le_of_natAbs (by omega)⟩,
      fun _ => eqList_ok L B _ hgl (fun z hz => bits_le_of_natAbs ((hg z hz).trans hLB))
        (fun z hz => bits_le_of_natAbs ((hg' z hz).trans hLB))⟩⟩

theorem stateFn_ok (L B : ℕ) (x : ℤ × ℤ × List ℤ) (hv : bits x.1 ≤ B) (hu : bits x.2.1 ≤ B) :
    OkAt L B stateFn x := by
  simp only [OkAt, stateFn, Ok, Expr.denote, Var.get, true_and, implies_true, true_implies, false_implies, Bool.false_eq_true, Bool.true_eq_false, and_true,]
  exact ⟨hu, hv⟩

theorem stateE_small (L : ℕ) (v u : ℤ) (g : List ℤ) (hL : 1 ≤ L) (hv : v.natAbs ≤ L)
    (hu : u.natAbs ≤ L) (hg : SmallList L L g) : NodeSmall L (stateE v u g) := by
  unfold stateE
  split
  · exact ⟨by simp; omega, by simp; omega, hg⟩
  · exact ⟨hv, hu, hg⟩

theorem fold_fst_succ (G : ℤ × ℤ → ℤ → ℤ) :
    ∀ (l : List ℤ) (k v : ℤ), (l.foldl (fun s a => (s.1 + 1, G s a)) (k, v)).1 = k + l.length
  | [], k, v => by simp
  | a :: l, k, v => by
    rw [List.foldl_cons, fold_fst_succ G l]; simp only [List.length_cons]; push_cast; ring

theorem nthFn_ok (L B : ℕ) (x : List ℤ × ℤ) (hl : x.1.length ≤ L) (hLB : L + 1 ≤ B)
    (hd : bits x.2 ≤ B) : OkAt L B nthFn x := by
  simp only [OkAt, nthFn, Ok, Expr.denote, Var.get, IntOp.eval, true_and, bits_one,
    ite_self, and_true]
  refine ⟨hl, FoldOK.of_prefix _ _ _ _ (fun i hi => ?_)⟩
  rw [fold_fst_succ]
  have hb : bits ((0 : ℤ) + ((List.take i x.1).length : ℕ)) ≤ B := by
    apply bits_le_of_natAbs
    simp only [List.length_take, zero_add]
    omega
  exact ⟨⟨hb, by omega⟩, ⟨hb, hd⟩, fun _ => trivial, fun _ => trivial⟩

theorem nthE_bits (w : List ℤ) (d : ℤ) (K : ℕ) (h : ∀ z ∈ w, bits z ≤ K) : bits (nthE w d) ≤ K := by
  unfold nthE
  rw [nthE_foldl]
  split_ifs with hc
  · have hn : (d - 0).toNat < w.length := by omega
    rw [List.getD_eq_getElem _ _ hn]
    exact h _ (List.getElem_mem hn)
  · simp

theorem bits_ind_sub (p q : Prop) [Decidable p] [Decidable q] :
    bits ((if p then (1 : ℤ) else 0) - (if q then 1 else 0)) ≤ 1 := by
  split_ifs <;> decide

theorem bits_ind (p : Prop) [Decidable p] : bits (if p then (1 : ℤ) else 0) ≤ 1 := by
  split_ifs <;> decide

theorem entryFn_ok (L B K : ℕ) (x : RowE × ColI) (hr : RowSmall L x.1) (hc : ColSmall L K x.2)
    (hLB : 2 * L + 2 ≤ B) (hK : K ≤ B) (hL : 1 ≤ L) : OkAt L B entryFn x := by
  rcases x with ⟨⟨t, sg, d, nd⟩, ⟨j, ⟨v, ⟨⟨e, b, src, tgt, lab, w, ob⟩, ⟨g, gT⟩⟩⟩⟩⟩
  obtain ⟨ht, hsg, hd, hnd⟩ := hr
  obtain ⟨hj, hv, hsrc, htgt, hg, hgT, hwl, hw⟩ := hc
  simp only at ht hsg hd hnd hj hv hsrc htgt hg hgT hwl hw
  have bt : bits t ≤ B := bits_le_of_natAbs (by omega)
  have bsg : bits sg ≤ B := bits_le_of_natAbs (by omega)
  have bd : bits d ≤ B := bits_le_of_natAbs (by omega)
  have bj : bits j ≤ B := bits_le_of_natAbs (by omega)
  have bv : bits v ≤ B := bits_le_of_natAbs (by omega)
  have bsrc : bits src ≤ B := bits_le_of_natAbs (by omega)
  have btgt : bits tgt ≤ B := bits_le_of_natAbs (by omega)
  have hL' : L ≤ B := by omega
  have hn1 := nodeEqFn_ok L B (stateE v tgt gT, nd) (stateE_small L v tgt gT hL hv htgt hgT) hnd hL'
  have hn2 := nodeEqFn_ok L B (stateE v src g, nd) (stateE_small L v src g hL hv hsrc hg) hnd hL'
  have hs1 := stateFn_ok L B (v, tgt, gT) bv btgt
  have hs2 := stateFn_ok L B (v, src, g) bv bsrc
  have hnth := nthFn_ok L B (w, d) hwl (by omega) bd
  have hnb := nthE_bits w d B (fun z hz => (hw z hz).trans hK)
  simp only [OkAt, entryFn, b2i, Ok, ok_call, Expr.denote, Var.get, IntOp.eval, denote_call,
    nodeEqFn_apply, stateFn_apply, nthFn_apply, true_and, bits_zero, bits_one, implies_true, true_implies, false_implies, Bool.false_eq_true, Bool.true_eq_false, and_true,]
  refine ⟨⟨bt, by omega⟩, fun _ => ⟨bd, bj⟩, fun _ => ⟨⟨bt, by omega⟩,
    fun _ => ⟨⟨⟨hs1, hn1⟩, ⟨hs2, hn2⟩, ?_, ?_⟩, bsg, ?_⟩, fun _ => ⟨hnth, bsg, hnb⟩⟩⟩
  · exact (bits_ind _).trans (by omega)
  · exact (bits_ind _).trans (by omega)
  · exact (bits_ind_sub _ _).trans (by omega)

theorem rhsFn_ok (L B : ℕ) (x : (List ℤ × List ℤ) × RowE) (hr : RowSmall L x.2)
    (hη : SmallList L L x.1.1) (hz : SmallList L L x.1.2)
    (hLB : 2 * L + 2 ≤ B) (hL : 1 ≤ L) : OkAt L B rhsFn x := by
  rcases x with ⟨⟨η0, z0⟩, ⟨t, sg, d, nd⟩⟩
  obtain ⟨ht, hsg, hd, hnd⟩ := hr
  simp only at ht hsg hd hnd hη hz
  have bt : bits t ≤ B := bits_le_of_natAbs (by omega)
  have bsg : bits sg ≤ B := bits_le_of_natAbs (by omega)
  have hL' : L ≤ B := by omega
  have hn1 := nodeEqFn_ok L B (nd, (-1, -1, η0)) hnd ⟨by simp; omega, by simp; omega, hη⟩ hL'
  have hn2 := nodeEqFn_ok L B (nd, (-1, -1, z0)) hnd ⟨by simp; omega, by simp; omega, hz⟩ hL'
  simp only [OkAt, rhsFn, b2i, Ok, ok_call, Expr.denote, Var.get, IntOp.eval, denote_call,
    nodeEqFn_apply, true_and, bits_one, implies_true, true_implies, false_implies, Bool.false_eq_true, Bool.true_eq_false, and_true,]
  refine ⟨⟨bt, by omega⟩, fun _ => ⟨⟨hn1, hn2, ?_, ?_⟩, bsg, ?_⟩⟩
  · exact (bits_ind _).trans (by omega)
  · exact (bits_ind _).trans (by omega)
  · exact (bits_ind_sub _ _).trans (by omega)

theorem objFn_ok (L B : ℕ) (x : Unit × ColI) : OkAt L B objFn x := by
  simp [OkAt, objFn, Ok]

theorem rowMatFn_ok (L B K : ℕ) (x : List ColI × RowE) (hl : x.1.length ≤ L)
    (hr : RowSmall L x.2) (hc : ∀ jc ∈ x.1, ColSmall L K jc)
    (hLB : 2 * L + 2 ≤ B) (hK : K ≤ B) (hL : 1 ≤ L) : OkAt L B rowMatFn x := by
  simp only [OkAt, rowMatFn, Ok, ok_call, Expr.denote, Var.get, true_and]
  exact mapWith_ok L B _ _ hl (fun jc hjc => entryFn_ok L B K _ hr (hc jc hjc) hLB hK hL)

end MWIS.FunNetwork

end
