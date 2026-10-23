module

public import MWIS.FunNetworkEncode

/-!
# The encoded dense network program

`encodedProgram f r μ edges` computes, from integer data only, the coefficient
rows, the right-hand sides and the objective of the dense finite-group network
program. `encodedProgram_eq` proves that on the encoded data of `(C, D, c)` it is
exactly `DenseProgram.toFun (FPTHard.program C D c rowsEquiv colsEquiv)`.

Prepared 2026-10-23.
-/

@[expose] public section

namespace MWIS.FunNetwork

open Walks ResidueJensen AlgorithmNetworkEncoding AlgorithmThresholdLP FPTHard

/-! ## Encoded rows -/

/-- Row records: tag (0 nonnegativity, 1 node balance, 2 free coordinate), sign,
index (column number or coordinate), and node code. -/
abbrev RowE := ℤ × ℤ × ℤ × NodeE

/-- The node code used where no node is involved. -/
def dummyNode : NodeE := (-2, -2, [])

/-- The sign of an equality-row copy. -/
def signE (s : Bool) : ℤ := if s then 1 else -1

/-- Encoded equality rows: tag, index and node code. -/
def eqE (nodes : List NodeE) (r : ℤ) : List (ℤ × ℤ × NodeE) :=
  nodes.map (fun u => (1, 0, u)) ++ (zrange r).map (fun d => (2, d, dummyNode))

/-- Both signs of an encoded equality row. -/
def signedRows (ρ : ℤ × ℤ × NodeE) : List RowE :=
  [(ρ.1, 1, ρ.2.1, ρ.2.2), (ρ.1, -1, ρ.2.1, ρ.2.2)]

/-- All encoded rows, for `N` columns. -/
def rowsE (N : ℤ) (nodes : List NodeE) (r : ℤ) : List RowE :=
  (zrange N).map (fun i => (0, 0, i, dummyNode)) ++ (eqE nodes r).flatMap signedRows

variable {f m : ℕ} (C : Fin m → Column (Fin f))

/-- The code of an equality row. -/
def eqCode {r : ℕ} : EqualityRow (Row := Fin f) (G := Residue r) r → ℤ × ℤ × NodeE
  | .inl u => (1, 0, nodeCode u)
  | .inr d => (2, ((d : ℕ) : ℤ), dummyNode)

/-- The code of an inequality row. -/
noncomputable def rowCode (r : ℕ) : InequalityRow C (G := Residue r) r → RowE
  | .inl a => (0, 0, ((colsEquiv C r a : ℕ) : ℤ), dummyNode)
  | .inr (x, s) => ((eqCode x).1, signE s, (eqCode x).2.1, (eqCode x).2.2)

theorem ofFn_getElem_map {α β : Type*} (l : List α) (G : α → β) :
    List.ofFn (fun i : Fin l.length => G l[i]) = l.map G := by
  apply List.ext_getElem <;> simp

theorem eqRowList_code (r : ℕ) :
    (eqRowList (f := f) r).map eqCode = eqE (nodesE (statesE f) (groupE r (GroupSize.modulus r))) r := by
  rw [← nodeList_code, eqRowList, eqE, List.map_append, List.map_map, List.map_map, List.map_map,
    ← finRange_map_val, List.map_map]
  rfl

theorem rowList_code (r : ℕ) :
    (rowList C r).map (rowCode C r) =
      rowsE (colList C r).length (nodesE (statesE f) (groupE r (GroupSize.modulus r))) r := by
  rw [rowList, rowsE, List.map_append, ← eqRowList_code]
  congr 1
  · rw [List.map_map, ← ofFn_getElem_map, ← finRange_map_val, List.map_map]
    have : (fun i : Fin (colList C r).length => ((rowCode C r ∘ Sum.inl) (colList C r)[i])) =
        (fun i : Fin (colList C r).length => ((0 : ℤ), (0 : ℤ), ((i : ℕ) : ℤ), dummyNode)) := by
      funext i
      simp only [Function.comp_apply, rowCode, colsEquiv_getElem]
    rw [this, List.ofFn_eq_map]
    rfl
  · simp only [SProd.sprod, List.product, List.map_flatMap, List.flatMap_map, List.map_map]
    apply List.flatMap_congr
    intro x _
    simp [rowCode, signedRows, signE, Function.comp_def]

/-! ## Encoded entries -/

/-- Numbered column records. -/
abbrev ColI := ℤ × ColRec

/-- The coefficient of an encoded row at a numbered column record. -/
def entryE (row : RowE) (jc : ColI) : ℤ :=
  if row.1 = 0 then (if row.2.2.1 = jc.1 then -1 else 0)
  else if row.1 = 1 then
    row.2.1 * ((if stateE jc.2.1 jc.2.2.1.2.2.2.1 jc.2.2.2.2 = row.2.2.2 then 1 else 0) -
      (if stateE jc.2.1 jc.2.2.1.2.2.1 jc.2.2.2.1 = row.2.2.2 then 1 else 0))
  else row.2.1 * nthE jc.2.2.1.2.2.2.2.2.1 row.2.2.1

/-- The right-hand side of an encoded row, given the codes of the target and
zero residues. -/
def rhsE (η0 z0 : List ℤ) (row : RowE) : ℤ :=
  if row.1 = 1 then
    row.2.1 * ((if row.2.2.2 = (-1, -1, η0) then 1 else 0) -
      (if row.2.2.2 = (-1, -1, z0) then 1 else 0))
  else 0

/-- The objective coefficient of a numbered column record. -/
def objE (jc : ColI) : ℤ := jc.2.2.1.2.2.2.2.2.2

theorem rowSign_eq (s : Bool) : rowSign s = signE s := rfl

/-- Conditions on an injective code decide the same branch, for any decidability
instances. -/
theorem ite_congr_inj {α β : Type*} (g : α → β) (hg : Function.Injective g) (x y : α)
    (a b : ℤ) (d1 : Decidable (x = y)) (d2 : Decidable (g x = g y)) :
    @ite ℤ (x = y) d1 a b = @ite ℤ (g x = g y) d2 a b := by
  by_cases h : x = y
  · rw [if_pos h, if_pos (congrArg g h)]
  · rw [if_neg h, if_neg (fun e => h (hg e))]

theorem entry_code (D : CoordinateData m) (c : Fin m → ℕ)
    (row : InequalityRow C (G := Residue D.rank) D.rank) (j : Fin (colList C D.rank).length) :
    matrix C D.free D.residue row (colList C D.rank)[j] =
      entryE (rowCode C D.rank row) (((j : ℕ) : ℤ), colRec C D c (colList C D.rank)[j]) := by
  rcases row with a | ⟨u | d, s⟩
  · simp only [matrix, rowCode, entryE, ↓reduceIte]
    have hiff : a = (colList C D.rank)[j] ↔ ((colsEquiv C D.rank a : ℕ) : ℤ) = ((j : ℕ) : ℤ) := by
      constructor
      · rintro rfl; rw [colsEquiv_getElem]
      · intro h
        have h' : colsEquiv C D.rank a = j := Fin.ext (by exact_mod_cast h)
        rw [← h', ← colsEquiv_symm_apply, Equiv.symm_apply_apply]
    by_cases h : a = (colList C D.rank)[j]
    · simp only [h, ↓reduceIte]
      rw [colsEquiv_getElem]
      simp
    · have h' : ¬ ((colsEquiv C D.rank a : ℕ) : ℤ) = ((j : ℕ) : ℤ) := fun e => h (hiff.mpr e)
      simp only [h, h', ↓reduceIte]
  · simp only [matrix, equalityCoefficient, incidenceCoefficient, rowCode, eqCode, entryE,
      rowSign_eq]
    simp only [show (1 : ℤ) ≠ 0 by decide, ↓reduceIte]
    congr 1
    set x := (colList C D.rank)[j]
    have ht : nodeCode (GroupNetwork.hubTarget (target C) (FiniteExtension.arcLabel C D.residue) x) =
        stateE (colRec C D c x).1 (colRec C D c x).2.1.2.2.2.1 (colRec C D c x).2.2.2 := by
      simp only [GroupNetwork.hubTarget, nodeCode_state, colRec, arcRec]
    have hs : nodeCode (GroupNetwork.hubSource (source C) x) =
        stateE (colRec C D c x).1 (colRec C D c x).2.1.2.2.1 (colRec C D c x).2.2.1 := by
      simp only [GroupNetwork.hubSource, nodeCode_state, colRec, arcRec]
    have hinj := nodeCode_injective (f := f) D.rank
    rw [← ht, ← hs]
    congr 1 <;> exact ite_congr_inj nodeCode hinj _ _ _ _ _ _
  · simp only [matrix, equalityCoefficient, rowCode, eqCode, entryE, rowSign_eq]
    simp only [show (2 : ℤ) ≠ 0 by decide, show (2 : ℤ) ≠ 1 by decide, ↓reduceIte]
    congr 1
    simp only [colRec, arcRec, originalEdge]
    exact (nthE_ofFn (fun d' => D.free (Pi.single _ 1) d') d).symm

theorem residueCode_target (r : ℕ) :
    residueCode (AlgorithmComputedNetwork.target r) = 1 :: List.replicate r 0 := by
  rw [residueCode]
  simp only [AlgorithmComputedNetwork.target, Pi.zero_apply, ZMod.val_zero, Nat.cast_zero,
    List.ofFn_const]
  rfl

theorem residueCode_zero (r : ℕ) :
    residueCode (0 : Residue r) = 0 :: List.replicate r 0 := by
  simp [residueCode, List.ofFn_const]

theorem rhs_code (r : ℕ) (row : InequalityRow C (G := Residue r) r) :
    bound C (AlgorithmComputedNetwork.target r) row =
      rhsE (1 :: List.replicate r 0) (0 :: List.replicate r 0) (rowCode C r row) := by
  rcases row with a | ⟨u | d, s⟩
  · simp [bound, rowCode, rhsE]
  · simp only [bound, equalityBound, GroupNetwork.demand, rowCode, eqCode, rhsE, rowSign_eq,
      ↓reduceIte]
    congr 1
    have hinj := nodeCode_injective (f := f) r
    rw [← residueCode_target, ← residueCode_zero]
    have h1 : ((-1 : ℤ), (-1 : ℤ), residueCode (AlgorithmComputedNetwork.target r)) =
        nodeCode (f := f) (Sum.inl (AlgorithmComputedNetwork.target r)) := rfl
    have h0 : ((-1 : ℤ), (-1 : ℤ), residueCode (0 : Residue r)) =
        nodeCode (f := f) (Sum.inl (0 : Residue r)) := rfl
    rw [h1, h0]
    congr 1 <;> exact ite_congr_inj nodeCode hinj _ _ _ _ _ _
  · simp [bound, equalityBound, rowCode, eqCode, rhsE]

theorem objective_code (D : CoordinateData m) (c : Fin m → ℕ) (j : ℤ)
    (x : FiniteExtension.ExtensionArc C (Residue D.rank)) :
    objectiveNumerator C (fun e => 2 * (perturbed c e : ℤ)) x = objE (j, colRec C D c x) := by
  simp [objectiveNumerator, originalEdge, objE, colRec, arcRec, perturbed]

/-! ## The encoded dense program -/

/-- The dense network program computed from integer data only. -/
def encodedProgram (f r μ : ℤ) (edges : List EdgeIn) : List (List ℤ) × List ℤ × List ℤ :=
  let states := statesE f
  let groups := groupE r μ
  let cols := colsE μ states (arcsE (2 ^ (edges.length + 1)) edges) groups
  let colsI := indexFrom 0 cols
  let rows := rowsE cols.length (nodesE states groups) r
  (rows.map (fun ρ => colsI.map (entryE ρ)),
    rows.map (rhsE (1 :: List.replicate r.toNat 0) (0 :: List.replicate r.toNat 0)),
    colsI.map objE)

/-- The encoded input of the network program. -/
def networkInput (D : CoordinateData m) (c : Fin m → ℕ) : ℤ × ℤ × ℤ × List EdgeIn :=
  (f, D.rank, GroupSize.modulus D.rank, edgeInput C D c)

/-- **Identification of the encoded program.** On the encoded data of `(C, D, c)`
the integer computation returns exactly the dense network program for the explicit
numbering of rows and columns. -/
theorem encodedProgram_eq (D : CoordinateData m) (c : Fin m → ℕ) :
    encodedProgram f D.rank (GroupSize.modulus D.rank) (edgeInput C D c) =
      DenseProgram.toFun (program C D c (rowsEquiv C D.rank) (colsEquiv C D.rank)) := by
  have hlen : (edgeInput C D c).length = m := by simp [edgeInput]
  have hcols := colList_code C D c
  have hrows := rowList_code C D.rank
  have hI : indexFrom 0 ((colList C D.rank).map (colRec C D c)) =
      List.ofFn (fun j : Fin (colList C D.rank).length =>
        (((j : ℕ) : ℤ), colRec C D c (colList C D.rank)[j])) := by
    rw [← ofFn_getElem_map, indexFrom_ofFn]
    simp
  simp only [encodedProgram, hlen, Int.toNat_natCast]
  rw [← hcols, List.length_map, ← hrows, hI]
  simp only [DenseProgram.toFun, program, toDense, rowsEquiv_symm_apply, colsEquiv_symm_apply]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> dsimp only
  · simp only [List.map_map]
    rw [← ofFn_getElem_map]
    congr 1
    funext i
    simp only [Function.comp_apply, List.map_ofFn]
    congr 1
    funext j
    exact (entry_code C D c _ j).symm
  · simp only [List.map_map]
    rw [← ofFn_getElem_map]
    congr 1
    funext i
    exact (rhs_code C D.rank _).symm
  · rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext j
    exact (objective_code C D c _ _).symm

end MWIS.FunNetwork

end
