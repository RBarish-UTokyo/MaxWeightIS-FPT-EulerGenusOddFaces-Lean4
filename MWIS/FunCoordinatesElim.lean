module

public import MWIS.FunCoordinatesPotential
public import MWIS.TreeCotreeElimination

/-!
# Unit-pivot elimination in `Fun`

The elimination state is encoded by the flags of the remaining rows, the flags of the active
columns and the full matrix as a list of rows. `elimStepFn` performs exactly one step of
`TreeCotree.ElimState.step` on this encoding, so `f` iterations compute the encoding of
`ElimState.run`; in particular the final active flags are the free edges.
-/

@[expose] public section

namespace MWIS.FunCoordinates

open MWIS.Fun MWIS.FunLP MWIS.TreeCotree

/-! ## Programs -/

/-- The encoded elimination state: row flags, column flags, matrix rows. -/
abbrev ElimTy : Ty := .prod (.list .bool) (.prod (.list .bool) (.list (.list .int)))

/-- Pair every element with its position. -/
def pairItem (a : Ty) : Fn (.prod .unit (.prod .int a)) (.prod .int a) := .snd v0

/-- The list of `(position, element)` pairs. -/
def indexedFn (a : Ty) : Fn (.list a) (.list (.prod .int a)) :=
  call (mapIdxFn (pairItem a)) (.pair .unit v0)

/-- `(act, (c, x))`: column `c` is active and `x = ±1`. -/
def unitPred : Fn (.prod (.list .bool) (.prod .int .int)) .bool :=
  .ite (call getBoolFn (.pair (.fst v0) (.fst (.snd v0))))
    (.ite (.cmp .eq (.snd (.snd v0)) (.int 1)) (.bool true) (.cmp .eq (.snd (.snd v0)) (.int (-1))))
    (.bool false)

/-- `(act, (c, x))`: column `c` is active and `x ≠ 0`. -/
def nonzeroPred : Fn (.prod (.list .bool) (.prod .int .int)) .bool :=
  .ite (call getBoolFn (.pair (.fst v0) (.fst (.snd v0))))
    (.ite (.cmp .eq (.snd (.snd v0)) (.int 0)) (.bool false) (.bool true))
    (.bool false)

/-- The first active unit position of a row, or `-1`. -/
def unitInFn : Fn (.prod (.list .bool) (.list .int)) .int :=
  call (findIdxFn unitPred) (.pair (.fst v0) (call (indexedFn .int) (.snd v0)))

/-- The first active nonzero position of a row, or `-1`. -/
def nonzeroInFn : Fn (.prod (.list .bool) (.list .int)) .int :=
  call (findIdxFn nonzeroPred) (.pair (.fst v0) (call (indexedFn .int) (.snd v0)))

/-- `((act, rows), (r, row))`: row `r` remains and has an active unit entry. -/
def rowUnitPred : Fn (.prod (.prod (.list .bool) (.list .bool)) (.prod .int (.list .int))) .bool :=
  .ite (call getBoolFn (.pair (.snd (.fst v0)) (.fst (.snd v0))))
    (.ite (.cmp .lt (call unitInFn (.pair (.fst (.fst v0)) (.snd (.snd v0)))) (.int 0))
      (.bool false) (.bool true))
    (.bool false)

/-- `((act, rows), (r, row))`: row `r` remains and has an active nonzero entry. -/
def rowNonzeroPred : Fn (.prod (.prod (.list .bool) (.list .bool)) (.prod .int (.list .int))) .bool :=
  .ite (call getBoolFn (.pair (.snd (.fst v0)) (.fst (.snd v0))))
    (.ite (.cmp .lt (call nonzeroInFn (.pair (.fst (.fst v0)) (.snd (.snd v0)))) (.int 0))
      (.bool false) (.bool true))
    (.bool false)

/-- `(i, (k, b)) ↦ if k = i then false else b`. -/
def clearItem : Fn (.prod .int (.prod .int .bool)) .bool :=
  .ite (.cmp .eq (.fst (.snd v0)) (.fst v0)) (.bool false) (.snd (.snd v0))

/-- Clear the flag at a position. -/
def clearFn : Fn (.prod .int (.list .bool)) (.list .bool) := mapIdxFn clearItem

/-- `((rowR, t), (k, x)) ↦ x - t * rowR[k]`. -/
def updItem : Fn (.prod (.prod (.list .int) .int) (.prod .int .int)) .int :=
  .arith .sub (.snd (.snd v0))
    (.arith .mul (.snd (.fst v0)) (call getIntFn (.pair (.fst (.fst v0)) (.fst (.snd v0)))))

/-- `((rowR, c, s), row) ↦ row - (row[c] * s) * rowR`. -/
def updRow : Fn (.prod (.prod (.list .int) (.prod .int .int)) (.list .int)) (.list .int) :=
  call (mapIdxFn updItem)
    (.pair (.pair (.fst (.fst v0))
        (.arith .mul (call getIntFn (.pair (.snd v0) (.fst (.snd (.fst v0))))) (.snd (.snd (.fst v0)))))
      (.snd v0))

/-- Eliminate column `c` with the unit entry of row `r`. -/
def pivotFn : Fn (.prod ElimTy (.prod .int .int)) ElimTy :=
  .letE (call (getListFn .int) (.pair (.snd (.snd (.fst v0))) (.fst (.snd v0))))
    (.pair (call clearFn (.pair (.fst (.snd v1)) (.fst (.fst v1))))
      (.pair (call clearFn (.pair (.snd (.snd v1)) (.fst (.snd (.fst v1)))))
        (call (cmapFn updRow)
          (.pair (.pair v0 (.pair (.snd (.snd v1)) (call getIntFn (.pair v0 (.snd (.snd v1))))))
            (.snd (.snd (.fst v1)))))))

/-- `(r, (k, row)) ↦ if k = r then row / 2 else row`. -/
def halveItem : Fn (.prod .int (.prod .int (.list .int))) (.list .int) :=
  .ite (.cmp .eq (.fst (.snd v0)) (.fst v0))
    (call (cmapFn (.arith .div (.snd v0) (.int 2))) (.pair .unit (.snd (.snd v0))))
    (.snd (.snd v0))

/-- Halve row `r`. -/
def halveFn : Fn (.prod ElimTy .int) ElimTy :=
  .pair (.fst (.fst v0))
    (.pair (.fst (.snd (.fst v0))) (call (mapIdxFn halveItem) (.pair (.snd v0) (.snd (.snd (.fst v0))))))

/-- One elimination step. -/
def elimStepFn : Fn ElimTy ElimTy :=
  .letE (call (findIdxFn rowUnitPred) (.pair (.pair (.fst (.snd v0)) (.fst v0))
      (call (indexedFn (.list .int)) (.snd (.snd v0)))))
    (.ite (.cmp .lt v0 (.int 0))
      (.letE (call (findIdxFn rowNonzeroPred) (.pair (.pair (.fst (.snd v1)) (.fst v1))
          (call (indexedFn (.list .int)) (.snd (.snd v1)))))
        (.ite (.cmp .lt v0 (.int 0)) v2
          (.letE (call halveFn (.pair v2 v0))
            (.letE (call unitInFn (.pair (.fst (.snd v0)) (call (getListFn .int) (.pair (.snd (.snd v0)) v1))))
              (.ite (.cmp .lt v0 (.int 0)) v1 (call pivotFn (.pair v1 (.pair v2 v0))))))))
      (call pivotFn (.pair v1 (.pair v0
        (call unitInFn (.pair (.fst (.snd v1)) (call (getListFn .int) (.pair (.snd (.snd v1)) v0))))))))

/-! ## List specifications -/

/-- Pair the elements with their positions. -/
def indexed {α : Type*} (l : List α) : List (ℤ × α) := l.mapIdx fun k x => ((k : ℤ), x)

/-- Active unit entry. -/
def unitP (act : List Bool) (kx : ℤ × ℤ) : Bool :=
  decide (getI act false kx.1 = true ∧ (kx.2 = 1 ∨ kx.2 = -1))

/-- Active nonzero entry. -/
def nonzeroP (act : List Bool) (kx : ℤ × ℤ) : Bool :=
  decide (getI act false kx.1 = true ∧ kx.2 ≠ 0)

/-- The first active unit position of a row. -/
def unitInS (act : List Bool) (row : List ℤ) : ℤ := optInt ((indexed row).findIdx? (unitP act))

/-- The first active nonzero position of a row. -/
def nonzeroInS (act : List Bool) (row : List ℤ) : ℤ :=
  optInt ((indexed row).findIdx? (nonzeroP act))

/-- A remaining row with an active unit entry. -/
def rowUnitP (act rows : List Bool) (r : ℤ × List ℤ) : Bool :=
  decide (getI rows false r.1 = true ∧ ¬ unitInS act r.2 < 0)

/-- A remaining row with an active nonzero entry. -/
def rowNonzeroP (act rows : List Bool) (r : ℤ × List ℤ) : Bool :=
  decide (getI rows false r.1 = true ∧ ¬ nonzeroInS act r.2 < 0)

/-- Clear the flag at a position. -/
def clearS (i : ℤ) (l : List Bool) : List Bool := l.mapIdx fun k b => if (k : ℤ) = i then false else b

/-- The row update of a pivot. -/
def updRowS (rowR : List ℤ) (c s : ℤ) (row : List ℤ) : List ℤ :=
  row.mapIdx fun k x => x - getI row 0 c * s * getI rowR 0 k

/-- The pivot on encoded states. -/
def pivotS (st : List Bool × List Bool × List (List ℤ)) (r c : ℤ) :
    List Bool × List Bool × List (List ℤ) :=
  let rowR := getI st.2.2 [] r
  (clearS r st.1, clearS c st.2.1, st.2.2.map (updRowS rowR c (getI rowR 0 c)))

/-- Halving on encoded states. -/
def halveS (st : List Bool × List Bool × List (List ℤ)) (r : ℤ) :
    List Bool × List Bool × List (List ℤ) :=
  (st.1, st.2.1, st.2.2.mapIdx fun k row => if (k : ℤ) = r then row.map (· / 2) else row)

/-- One step on encoded states. -/
def stepS (st : List Bool × List Bool × List (List ℤ)) : List Bool × List Bool × List (List ℤ) :=
  let r1 := optInt ((indexed st.2.2).findIdx? (rowUnitP st.2.1 st.1))
  if r1 < 0 then
    let r2 := optInt ((indexed st.2.2).findIdx? (rowNonzeroP st.2.1 st.1))
    if r2 < 0 then st else
      let H := halveS st r2
      let c := unitInS H.2.1 (getI H.2.2 [] r2)
      if c < 0 then H else pivotS H r2 c
  else pivotS st r1 (unitInS st.2.1 (getI st.2.2 [] r1))

/-! ## Denotations -/

@[simp] theorem indexedFn_apply (a : Ty) (l : (Ty.list a).denote) :
    (indexedFn a).apply l = indexed l := by
  rw [Fn.apply]
  simp only [indexedFn, Expr.denote, Var.get, denote_call, mapIdxFn_apply', indexed]
  congr 1

@[simp] theorem unitPred_apply (x : (Ty.prod (.list .bool) (.prod .int .int)).denote) :
    unitPred.apply x = unitP x.1 x.2 := by
  rw [Fn.apply]
  simp only [unitPred, unitP, Expr.denote, Var.get, denote_call, getBoolFn_apply', CmpOp.eval]
  by_cases h1 : getI x.1 false x.2.1 = true <;> by_cases h2 : x.2.2 = 1 <;>
    by_cases h3 : x.2.2 = -1 <;> simp_all

@[simp] theorem nonzeroPred_apply (x : (Ty.prod (.list .bool) (.prod .int .int)).denote) :
    nonzeroPred.apply x = nonzeroP x.1 x.2 := by
  rw [Fn.apply]
  simp only [nonzeroPred, nonzeroP, Expr.denote, Var.get, denote_call, getBoolFn_apply', CmpOp.eval]
  by_cases h1 : getI x.1 false x.2.1 = true <;> by_cases h2 : x.2.2 = 0 <;> simp_all

@[simp] theorem unitInFn_apply (x : (Ty.prod (.list .bool) (.list .int)).denote) :
    unitInFn.apply x = unitInS x.1 x.2 := by
  rw [Fn.apply]
  simp only [unitInFn, Expr.denote, Var.get, denote_call, findIdxFn_apply', indexedFn_apply,
    unitPred_apply, unitInS]

@[simp] theorem nonzeroInFn_apply (x : (Ty.prod (.list .bool) (.list .int)).denote) :
    nonzeroInFn.apply x = nonzeroInS x.1 x.2 := by
  rw [Fn.apply]
  simp only [nonzeroInFn, Expr.denote, Var.get, denote_call, findIdxFn_apply', indexedFn_apply,
    nonzeroPred_apply, nonzeroInS]

@[simp] theorem rowUnitPred_apply
    (x : (Ty.prod (.prod (.list .bool) (.list .bool)) (.prod .int (.list .int))).denote) :
    rowUnitPred.apply x = rowUnitP x.1.1 x.1.2 x.2 := by
  rw [Fn.apply]
  simp only [rowUnitPred, rowUnitP, Expr.denote, Var.get, denote_call, getBoolFn_apply',
    unitInFn_apply, CmpOp.eval]
  by_cases h1 : getI x.1.2 false x.2.1 = true <;> by_cases h2 : unitInS x.1.1 x.2.2 < 0 <;> simp_all

@[simp] theorem rowNonzeroPred_apply
    (x : (Ty.prod (.prod (.list .bool) (.list .bool)) (.prod .int (.list .int))).denote) :
    rowNonzeroPred.apply x = rowNonzeroP x.1.1 x.1.2 x.2 := by
  rw [Fn.apply]
  simp only [rowNonzeroPred, rowNonzeroP, Expr.denote, Var.get, denote_call, getBoolFn_apply',
    nonzeroInFn_apply, CmpOp.eval]
  by_cases h1 : getI x.1.2 false x.2.1 = true <;> by_cases h2 : nonzeroInS x.1.1 x.2.2 < 0 <;>
    simp_all

@[simp] theorem clearFn_apply (x : (Ty.prod .int (.list .bool)).denote) :
    clearFn.apply x = clearS x.1 x.2 := by
  rw [clearFn, mapIdxFn_apply', clearS]
  congr 1
  funext k b
  rw [Fn.apply]
  by_cases h : (k : ℤ) = x.1 <;> simp [clearItem, Expr.denote, Var.get, CmpOp.eval, h]

@[simp] theorem updRow_apply (x : (Ty.prod (.prod (.list .int) (.prod .int .int)) (.list .int)).denote) :
    updRow.apply x = updRowS x.1.1 x.1.2.1 x.1.2.2 x.2 := by
  rw [Fn.apply]
  simp only [updRow, updRowS, Expr.denote, Var.get, denote_call, getIntFn_apply', IntOp.eval,
    mapIdxFn_apply']
  congr 1
  funext k y
  rw [Fn.apply]
  simp [updItem, Expr.denote, Var.get, denote_call, getIntFn_apply', IntOp.eval, mul_assoc]

@[simp] theorem pivotFn_apply (x : (Ty.prod ElimTy (.prod .int .int)).denote) :
    pivotFn.apply x = pivotS x.1 x.2.1 x.2.2 := by
  rw [Fn.apply]
  simp only [pivotFn, pivotS, Expr.denote, Var.get, denote_call, getListFn_apply',
    getIntFn_apply', clearFn_apply, cmapFn_apply', updRow_apply]

@[simp] theorem halveFn_apply (x : (Ty.prod ElimTy .int).denote) :
    halveFn.apply x = halveS x.1 x.2 := by
  rw [Fn.apply]
  simp only [halveFn, halveS, Expr.denote, Var.get, denote_call, mapIdxFn_apply']
  congr 2
  apply congrArg (fun g => List.mapIdx g _)
  funext k row
  rw [Fn.apply]
  by_cases hk : (k : ℤ) = x.2
  · simp only [halveItem, Expr.denote, Var.get, denote_call, cmapFn_apply', CmpOp.eval, hk,
      decide_true, ite_true]
    apply List.map_congr_left
    intro y _
    rfl
  · simp [halveItem, Expr.denote, Var.get, CmpOp.eval, hk]

@[simp] theorem elimStepFn_apply (st : ElimTy.denote) : elimStepFn.apply st = stepS st := by
  rw [Fn.apply]
  simp only [elimStepFn, stepS, Expr.denote, Var.get, denote_call, findIdxFn_apply',
    indexedFn_apply, getListFn_apply', CmpOp.eval, rowUnitPred_apply, rowNonzeroPred_apply,
    pivotFn_apply, halveFn_apply, unitInFn_apply]
  simp only [decide_eq_true_eq]

/-! ## Agreement with `ElimState.step` -/

theorem optInt_neg_iff (o : Option ℕ) : optInt o < 0 ↔ o = none := by
  cases o <;> simp [optInt]

theorem indexed_ofFn {α : Type*} {k : ℕ} (g : Fin k → α) :
    indexed (List.ofFn g) = List.ofFn fun i : Fin k => (((i : ℕ) : ℤ), g i) := by
  apply List.ext_getElem (by simp [indexed])
  intro j h1 h2
  simp [indexed]

theorem mapIdx_ofFn {α β : Type*} {k : ℕ} (g : Fin k → α) (h : ℕ → α → β) :
    (List.ofFn g).mapIdx h = List.ofFn fun i : Fin k => h i (g i) := by
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp

theorem getI_ofFn_nat {α : Type*} {k : ℕ} (g : Fin k → α) (d : α) (j : ℕ) (hj : j < k) :
    getI (List.ofFn g) d (j : ℤ) = g ⟨j, hj⟩ := getI_ofFn g d ⟨j, hj⟩

theorem clearS_ofFn {k : ℕ} (g : Fin k → Bool) (i : Fin k) :
    clearS (i : ℤ) (List.ofFn g) = List.ofFn fun j => if j = i then false else g j := by
  unfold clearS
  rw [mapIdx_ofFn]
  congr 1
  funext j
  simp [Fin.ext_iff]

variable {f m : ℕ}

/-- The encoding of an elimination state (the pivot list is not encoded). -/
def encS (S : ElimState f m) : List Bool × List Bool × List (List ℤ) :=
  (List.ofFn fun r => decide (r ∈ S.rows), List.ofFn fun c => decide (c ∈ S.act),
    List.ofFn fun r => List.ofFn (S.M r))

theorem unitInS_enc (S : ElimState f m) (r : Fin f) :
    unitInS (encS S).2.1 (List.ofFn (S.M r)) = optInt ((S.unitIn r).map Fin.val) := by
  unfold unitInS ElimState.unitIn encS
  rw [indexed_ofFn, findIdx?_ofFn]
  congr 3
  funext c
  simp [unitP, getI_ofFn]

theorem nonzeroInS_enc (S : ElimState f m) (r : Fin f) :
    nonzeroInS (encS S).2.1 (List.ofFn (S.M r)) =
      optInt (((List.finRange m).find? fun c => decide (c ∈ S.act ∧ S.M r c ≠ 0)).map Fin.val) := by
  unfold nonzeroInS encS
  rw [indexed_ofFn, findIdx?_ofFn]
  congr 3
  funext c
  simp [nonzeroP, getI_ofFn]

theorem rowUnit_enc (S : ElimState f m) :
    (indexed (encS S).2.2).findIdx? (rowUnitP (encS S).2.1 (encS S).1) =
      ((List.finRange f).find? fun r =>
        (if r ∈ S.rows then (S.unitIn r).map (r, ·) else none).isSome).map Fin.val := by
  have h : (encS S).2.2 = List.ofFn fun r => List.ofFn (S.M r) := rfl
  rw [h, indexed_ofFn, findIdx?_ofFn]
  congr 3
  funext r
  unfold rowUnitP
  simp only [unitInS_enc, optInt_neg_iff]
  simp only [encS, getI_ofFn]
  by_cases hr : r ∈ S.rows <;> cases hu : S.unitIn r <;> simp [hr, hu]

theorem rowNonzero_enc (S : ElimState f m) :
    (indexed (encS S).2.2).findIdx? (rowNonzeroP (encS S).2.1 (encS S).1) =
      S.nonzeroRow.map Fin.val := by
  have h : (encS S).2.2 = List.ofFn fun r => List.ofFn (S.M r) := rfl
  rw [h, indexed_ofFn, findIdx?_ofFn, ElimState.nonzeroRow]
  congr 3
  funext r
  unfold rowNonzeroP
  simp only [nonzeroInS_enc, optInt_neg_iff]
  simp only [encS, getI_ofFn]
  cases hu : (List.finRange m).find? (fun c => decide (c ∈ S.act ∧ S.M r c ≠ 0)) with
  | none =>
    have := List.find?_eq_none.mp hu
    simp only [Option.map_none, not_true_eq_false, and_false, decide_false, Bool.false_eq_true]
    symm
    simp only [decide_eq_false_iff_not, not_and, not_exists, not_not]
    intro _ c hc
    have := this c (List.mem_finRange c)
    simp only [decide_eq_true_eq, not_and, not_not] at this
    exact this hc
  | some c =>
    have := List.find?_some hu
    simp only [decide_eq_true_eq] at this
    simp only [Option.map_some, reduceCtorEq, not_false_eq_true, and_true]
    by_cases hr : r ∈ S.rows
    · simp only [hr, decide_true, true_and]
      exact (decide_eq_true ⟨c, this.1, this.2⟩).symm
    · simp [hr]

theorem pivotS_enc (S : ElimState f m) (r : Fin f) (c : Fin m) :
    pivotS (encS S) (r : ℤ) (c : ℤ) = encS (S.pivotAt r c) := by
  unfold pivotS encS ElimState.pivotAt
  simp only [getI_ofFn, clearS_ofFn, List.map_ofFn, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · congr 1; funext j; by_cases h : j = r <;> simp [h]
  · congr 1; funext j; by_cases h : j = c <;> simp [h]
  · congr 1
    funext r'
    simp only [Function.comp_apply, updRowS, getI_ofFn, mapIdx_ofFn]

theorem halveS_enc (S : ElimState f m) (r : Fin f) :
    halveS (encS S) (r : ℤ) = encS (S.halve r) := by
  unfold halveS encS ElimState.halve
  simp only [mapIdx_ofFn, Prod.mk.injEq, true_and]
  congr 1
  funext r'
  by_cases h : r' = r
  · subst h; simp [List.map_ofFn, Function.comp_def]
  · have : ¬ (((r' : ℕ) : ℤ) = ((r : ℕ) : ℤ)) := by
      intro h'; exact h (Fin.ext (by exact_mod_cast h'))
    simp [this, h]

/-- **One encoded step is one elimination step.** -/
theorem stepS_enc (S : ElimState f m) : stepS (encS S) = encS S.step := by
  unfold stepS
  rw [rowUnit_enc]
  have hfs := findSome?_eq_bind_find
    (fun r => if r ∈ S.rows then (S.unitIn r).map (r, ·) else none) (List.finRange f)
  unfold ElimState.step
  rw [ElimState.unitAt, hfs]
  cases h1 : (List.finRange f).find? (fun r =>
      (if r ∈ S.rows then (S.unitIn r).map (r, ·) else none).isSome) with
  | some r =>
    have hp := List.find?_some h1
    have hr : r ∈ S.rows := by by_contra hr; simp [hr] at hp
    simp only [hr, ite_true, Option.isSome_map] at hp
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hp
    simp only [Option.map_some, optInt, Option.bind_some, hr, ite_true, hc, Option.map_some]
    have hpos : ¬ ((r : ℕ) : ℤ) < 0 := by omega
    simp only [hpos, ite_false]
    have : getI (encS S).2.2 [] ((r : ℕ) : ℤ) = List.ofFn (S.M r) := getI_ofFn _ _ r
    rw [this, unitInS_enc, hc]
    exact pivotS_enc S r c
  | none =>
    simp only [Option.map_none, optInt, Option.bind_none]
    simp only [show (-1 : ℤ) < 0 by norm_num, ite_true]
    rw [rowNonzero_enc]
    cases h2 : S.nonzeroRow with
    | none => simp [optInt]
    | some r =>
      have hpos : ¬ ((r : ℕ) : ℤ) < 0 := by omega
      have : getI (encS (S.halve r)).2.2 [] ((r : ℕ) : ℤ) = List.ofFn ((S.halve r).M r) :=
        getI_ofFn _ _ r
      simp only [Option.map_some, optInt, hpos, ite_false, halveS_enc, this, unitInS_enc]
      cases h3 : (S.halve r).unitIn r with
      | none => simp [optInt]
      | some c =>
        have hpos' : ¬ ((c : ℕ) : ℤ) < 0 := by omega
        simp only [Option.map_some, optInt, hpos', ite_false]
        exact pivotS_enc _ r c

theorem iterate_stepS_enc (S : ElimState f m) (k : ℕ) :
    stepS^[k] (encS S) = encS (ElimState.step^[k] S) := by
  induction k generalizing S with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, stepS_enc, ih]

/-- **The encoded elimination computes the encoding of `ElimState.run`.** -/
theorem run_enc (S : ElimState f m) : stepS^[f] (encS S) = encS S.run :=
  iterate_stepS_enc S f

end MWIS.FunCoordinates

end
