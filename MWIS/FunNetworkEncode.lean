module

public import MWIS.FunNetworkEnum
public import MWIS.FunNetworkLib

/-!
# Integer encodings of the finite-group network program

The dense network program is described on integer codes: signed-cover states and
stubs become integers, residues become integer lists, and columns and rows become
nested integer records. `encodedProgram` computes the dense program, as lists of
integers, from encoded per-edge input records only. `encodedProgram_eq` proves
that it is the `Fun` encoding `DenseProgram.toFun` of the network program
`FPTHard.program C D c` for the explicit numbering of `MWIS.FunNetworkEnum`.

Prepared 2026-10-23.
-/

@[expose] public section

namespace MWIS.FunNetwork

open Walks ResidueJensen AlgorithmNetworkEncoding AlgorithmThresholdLP FPTHard

/-! ## The `Fun` encoding of a dense program -/

/-- Dense programs as integer lists: the coefficient rows, the right-hand
sides, and the objective. -/
def DenseProgram.toFun {M N : ℕ} (P : DenseProgram M N) : List (List ℤ) × List ℤ × List ℤ :=
  (List.ofFn fun i => List.ofFn (P.coefficient i), List.ofFn P.rhs, List.ofFn P.objective)

/-! ## Integer ranges and indexed lists -/

/-- `[0, 1, …, n - 1]` as integers. -/
def zrange (n : ℤ) : List ℤ := (List.range n.toNat).map (fun i : ℕ => (i : ℤ))

theorem finRange_map_val (n : ℕ) :
    (List.finRange n).map (fun i : Fin n => ((i : ℕ) : ℤ)) = zrange n := by
  apply List.ext_getElem
  · simp [zrange]
  · intro i h1 h2
    simp [zrange]

/-- Number a list from `k`. -/
def indexFrom {α : Type*} (k : ℤ) : List α → List (ℤ × α)
  | [] => []
  | a :: l => (k, a) :: indexFrom (k + 1) l

theorem indexFrom_ofFn {α : Type*} : ∀ (n : ℕ) (g : Fin n → α) (k : ℤ),
    indexFrom k (List.ofFn g) = List.ofFn (fun i => (k + (i : ℕ), g i))
  | 0, _, _ => rfl
  | n + 1, g, k => by
    rw [List.ofFn_succ, indexFrom, indexFrom_ofFn n, List.ofFn_succ]
    congr 1
    · simp
    · congr 1; funext i; simp only [Fin.val_succ]; push_cast; ring_nf

/-- Number a list from `k`, together with the powers `p·2^i`. -/
def indexPow {α : Type*} (k p : ℤ) : List α → List (ℤ × ℤ × α)
  | [] => []
  | a :: l => (k, p, a) :: indexPow (k + 1) (2 * p) l

theorem indexPow_ofFn {α : Type*} : ∀ (n : ℕ) (g : Fin n → α) (k p : ℤ),
    indexPow k p (List.ofFn g) = List.ofFn (fun i => (k + (i : ℕ), p * 2 ^ (i : ℕ), g i))
  | 0, _, _, _ => rfl
  | n + 1, g, k, p => by
    rw [List.ofFn_succ, indexPow, indexPow_ofFn n, List.ofFn_succ]
    congr 1
    · simp
    · congr 1; funext i; simp only [Fin.val_succ, pow_succ]; push_cast; ring_nf

/-- Lookup of position `d` in an integer list, with default zero. -/
def nthE (w : List ℤ) (d : ℤ) : ℤ :=
  (w.foldl (fun (s : ℤ × ℤ) a => (s.1 + 1, if s.1 = d then a else s.2)) (0, 0)).2

theorem nthE_foldl : ∀ (w : List ℤ) (k v d : ℤ),
    (w.foldl (fun (s : ℤ × ℤ) a => (s.1 + 1, if s.1 = d then a else s.2)) (k, v)).2 =
      if k ≤ d ∧ d < k + w.length then w.getD (d - k).toNat 0 else v
  | [], k, v, d => by simp
  | a :: w, k, v, d => by
    rw [List.foldl_cons, nthE_foldl w]
    simp only [List.length_cons]
    by_cases hkd : k = d
    · subst hkd
      rw [if_neg (by omega), if_pos rfl, if_pos (by push_cast; omega)]
      simp
    · by_cases h1 : k + 1 ≤ d ∧ d < k + 1 + w.length
      · rw [if_pos h1, if_pos (by push_cast; omega)]
        have ht : (d - k).toNat = (d - (k + 1)).toNat + 1 := by omega
        rw [ht, List.getD_cons_succ]
      · rw [if_neg h1, if_neg hkd, if_neg (by push_cast; omega)]

theorem nthE_ofFn {n : ℕ} (h : Fin n → ℤ) (d : Fin n) : nthE (List.ofFn h) d = h d := by
  unfold nthE
  rw [nthE_foldl]
  have : (0 : ℤ) ≤ (d : ℕ) ∧ ((d : ℕ) : ℤ) < 0 + (List.ofFn h).length := by
    simp only [List.length_ofFn]; omega
  rw [if_pos this]
  simp

/-! ## Codes of states, stubs, columns and residues -/

variable {f m : ℕ}

/-- The code `2k + 1` of `(k, -)` and `2k + 2` of `(k, +)`. -/
def stubCode (s : Stub (Fin f)) : ℤ := 2 * (s.1 : ℕ) + 1 + if s.2 then 1 else 0

/-- The hub has code zero. -/
def stateCode : State (Fin f) → ℤ
  | none => 0
  | some s => stubCode s

theorem stateCode_injective : Function.Injective (stateCode (f := f)) := by
  intro x y h
  rcases x with _ | ⟨k, b⟩ <;> rcases y with _ | ⟨k', b'⟩
  · rfl
  · cases b' <;> simp [stateCode, stubCode] at h <;> omega
  · cases b <;> simp [stateCode, stubCode] at h <;> omega
  · simp only [stateCode, stubCode] at h
    have hk : (k : ℕ) = k' := by cases b <;> cases b' <;> simp at h <;> omega
    have hb : b = b' := by cases b <;> cases b' <;> simp_all <;> omega
    rw [Fin.ext hk, hb]

/-- The signed stubs of a column, as codes. -/
def columnCode : Column (Fin f) → List ℤ
  | .zero => []
  | .one s => [stubCode s]
  | .two s t => [stubCode s, stubCode t]

/-- The code of the opposite stub. -/
def oppE (c : ℤ) : ℤ := if c % 2 = 1 then c + 1 else c - 1

theorem stubCode_opposite (s : Stub (Fin f)) : stubCode (opposite s) = oppE (stubCode s) := by
  rcases s with ⟨k, b⟩
  cases b <;> simp [stubCode, opposite, oppE] <;> omega

/-- The source code of the arc with direction `b` of a column with stub codes `col`. -/
def srcE (col : List ℤ) (b : Bool) : ℤ :=
  match col with
  | [] => 0
  | [s] => if b then oppE s else 0
  | s :: t :: _ => if b then oppE t else oppE s

/-- The target code of the arc with direction `b` of a column with stub codes `col`. -/
def tgtE (col : List ℤ) (b : Bool) : ℤ :=
  match col with
  | [] => 0
  | [s] => if b then 0 else s
  | s :: t :: _ => if b then s else t

theorem stateCode_source (C : Fin m → Column (Fin f)) (a : Arc C) :
    stateCode (source C a) = srcE (columnCode (C a.val.1)) a.val.2 := by
  unfold source
  cases h : C a.val.1 <;> simp only [columnCode, srcE] <;> (try split_ifs) <;>
    simp [stateCode, stubCode_opposite]

theorem stateCode_target (C : Fin m → Column (Fin f)) (a : Arc C) :
    stateCode (target C a) = tgtE (columnCode (C a.val.1)) a.val.2 := by
  unfold target
  cases h : C a.val.1 <;> simp only [columnCode, tgtE] <;> (try split_ifs) <;> simp [stateCode]

/-- Residue codes: the parity value followed by the free residue values. -/
def residueCode {r : ℕ} (g : Residue r) : List ℤ :=
  ((g.1.val : ℕ) : ℤ) :: List.ofFn (fun i => (((g.2 i).val : ℕ) : ℤ))

theorem residueCode_injective (r : ℕ) : Function.Injective (residueCode (r := r)) := by
  intro g h hgh
  simp only [residueCode, List.cons.injEq, Nat.cast_inj] at hgh
  obtain ⟨h1, h2⟩ := hgh
  have h2' := List.ofFn_injective h2
  refine Prod.ext (ZMod.val_injective _ h1) (funext fun i => ?_)
  have := congrFun h2' i
  simp only [Nat.cast_inj] at this
  exact ZMod.val_injective _ this

/-- Addition of residue codes: parity modulo two, free values modulo `μ`. -/
def addE (μ : ℤ) : List ℤ → List ℤ → List ℤ
  | a :: g, b :: h => ((a + b) % 2) :: List.zipWith (fun x y => (x + y) % μ) g h
  | _, _ => []

theorem zipWith_ofFn {α β γ : Type*} (F : α → β → γ) : ∀ {n : ℕ} (a : Fin n → α) (b : Fin n → β),
    List.zipWith F (List.ofFn a) (List.ofFn b) = List.ofFn (fun i => F (a i) (b i))
  | 0, _, _ => rfl
  | n + 1, a, b => by
    rw [List.ofFn_succ, List.ofFn_succ, List.zipWith_cons_cons, zipWith_ofFn, List.ofFn_succ]

theorem residueCode_add {r : ℕ} (g h : Residue r) :
    residueCode (g + h) = addE (GroupSize.modulus r) (residueCode g) (residueCode h) := by
  simp only [residueCode, addE, Prod.fst_add, Prod.snd_add, Pi.add_apply, zipWith_ofFn,
    ZMod.val_add, Int.natCast_mod, Nat.cast_add, Nat.cast_ofNat]

/-! ## Encoded enumerations -/

/-- Encoded states. -/
def statesE (f : ℤ) : List ℤ := 0 :: (zrange f).flatMap (fun k => [2 * k + 1, 2 * k + 2])

theorem stateList_code (f : ℕ) : (stateList f).map stateCode = statesE f := by
  simp only [stateList, statesE, List.map_cons, List.map_map, stateCode]
  congr 1
  rw [← finRange_map_val, List.flatMap_map]
  simp only [SProd.sprod, List.product, List.map_flatMap, List.map_map]
  apply List.flatMap_congr
  intro k _
  simp only [Function.comp_def, stateCode, stubCode, List.map_cons, List.map_nil]
  simp only [Bool.false_eq_true, ↓reduceIte, List.cons.injEq, and_true]
  constructor <;> ring

/-- Encoded vectors of residue values. -/
def vecsE (μ : ℤ) : ℕ → List (List ℤ)
  | 0 => [[]]
  | k + 1 => (zrange μ).flatMap (fun x => (vecsE μ k).map (x :: ·))

theorem zmodList_flatMap {β : Type*} (μ : ℕ) [NeZero μ] (F : ℤ → List β) :
    (zmodList μ).flatMap (fun x => F ((x.val : ℕ) : ℤ)) = (zrange μ).flatMap F := by
  unfold zmodList zrange
  rw [List.flatMap_map, List.flatMap_map]
  simp only [Int.toNat_natCast]
  apply List.flatMap_congr
  intro i hi
  rw [ZMod.val_natCast_of_lt (List.mem_range.mp hi)]

theorem vecList_code (μ : ℕ) [NeZero μ] : ∀ k,
    (vecList μ k).map (fun v => List.ofFn (fun i => (((v i).val : ℕ) : ℤ))) = vecsE μ k
  | 0 => rfl
  | k + 1 => by
    rw [vecList, vecsE, List.map_flatMap, ← zmodList_flatMap, ← vecList_code μ k]
    apply List.flatMap_congr
    intro x _
    simp [List.map_map, Function.comp_def, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]

/-- Encoded residues. -/
def groupE (r μ : ℤ) : List (List ℤ) :=
  (zrange 2).flatMap (fun p => (vecsE μ r.toNat).map (p :: ·))

theorem residueList_code (r : ℕ) :
    (residueList r).map residueCode = groupE r (GroupSize.modulus r) := by
  simp only [residueList, groupE, SProd.sprod, List.product, List.map_flatMap, List.map_map,
    Int.toNat_natCast]
  rw [show (fun a : ZMod 2 => List.map (residueCode ∘ Prod.mk a)
      (vecList (GroupSize.modulus r) r)) = (fun a : ZMod 2 =>
        (fun p : ℤ => (vecsE (GroupSize.modulus r) r).map (p :: ·)) ((a.val : ℕ) : ℤ)) from ?_]
  · exact zmodList_flatMap 2 (fun p : ℤ => (vecsE (GroupSize.modulus r) r).map (p :: ·))
  · funext a
    rw [← vecList_code (GroupSize.modulus r) r]
    simp only [List.map_map]
    apply List.map_congr_left
    intro v _
    rfl

/-! ## Encoded arcs -/

/-- Per-edge input records: stub codes of the column, the free coordinates of the
edge's unit vector, the residue code of its label, and its natural cost. -/
abbrev EdgeIn := List ℤ × List ℤ × List ℤ × ℤ

/-- The input records of all edges. -/
def edgeInput (C : Fin m → Column (Fin f)) (D : CoordinateData m) (c : Fin m → ℕ) :
    List EdgeIn :=
  List.ofFn fun e => (columnCode (C e), List.ofFn (fun d => D.free (Pi.single e 1) d),
    residueCode (D.residue (Pi.single e 1)), (c e : ℤ))

/-- Arc records: edge, direction, source code, target code, residue code of the
label, free coordinates of the edge, and the objective numerator. -/
abbrev ArcRec := ℤ × Bool × ℤ × ℤ × List ℤ × List ℤ × ℤ

/-- The directions of the arcs of a column with stub codes `col`. -/
def dirsE (col : List ℤ) : List Bool := if col = [] then [false] else [false, true]

/-- The arc records of one numbered edge, with `p = 2^e` and `P = 2^(m+1)`. -/
def edgeArcs (P : ℤ) (x : ℤ × ℤ × EdgeIn) : List ArcRec :=
  (dirsE x.2.2.1).map fun b =>
    (x.1, b, srcE x.2.2.1 b, tgtE x.2.2.1 b, x.2.2.2.2.1, x.2.2.2.1,
      2 * (P * x.2.2.2.2.2 + x.2.1))

/-- All encoded arc records. -/
def arcsE (P : ℤ) (edges : List EdgeIn) : List ArcRec :=
  (indexPow 0 1 edges).flatMap (edgeArcs P)

/-- The record of an actual arc. -/
def arcRec (C : Fin m → Column (Fin f)) (D : CoordinateData m) (c : Fin m → ℕ)
    (a : Arc C) : ArcRec :=
  ((a.val.1 : ℕ), a.val.2, stateCode (source C a), stateCode (target C a),
    residueCode (D.residue (Pi.single a.val.1 1)),
    List.ofFn (fun d => D.free (Pi.single a.val.1 1) d),
    2 * ((2 : ℤ) ^ (m + 1) * (c a.val.1 : ℤ) + 2 ^ (a.val.1 : ℕ)))

theorem arcList_code (C : Fin m → Column (Fin f)) (D : CoordinateData m) (c : Fin m → ℕ) :
    (arcList C).map (arcRec C D c) = arcsE (2 ^ (m + 1)) (edgeInput C D c) := by
  unfold arcsE edgeInput arcList
  rw [indexPow_ofFn, List.ofFn_eq_map, List.flatMap_map, List.map_flatMap]
  apply List.flatMap_congr
  intro e _
  simp only [edgeArcs, zero_add, one_mul]
  unfold arcsOf dirsE
  by_cases hz : C e = .zero
  · rw [dif_pos hz, if_pos (by rw [hz]; rfl)]
    simp only [List.map_cons, List.map_nil, arcRec, stateCode_source, stateCode_target]
  · rw [dif_neg hz, if_neg (by cases h : C e <;> simp_all [columnCode])]
    simp only [List.map_cons, List.map_nil, arcRec, stateCode_source, stateCode_target]

/-! ## Encoded columns -/

/-- Column records: base state code, arc record, starting residue code and
target residue code. -/
abbrev ColRec := ℤ × ArcRec × List ℤ × List ℤ

/-- All encoded columns. -/
def colsE (μ : ℤ) (states : List ℤ) (arcs : List ArcRec) (groups : List (List ℤ)) :
    List ColRec :=
  states.flatMap fun v => arcs.flatMap fun a => groups.map fun g => (v, a, g, addE μ g a.2.2.2.2.1)

/-- The record of an actual network column. -/
def colRec (C : Fin m → Column (Fin f)) (D : CoordinateData m) (c : Fin m → ℕ)
    (x : FiniteExtension.ExtensionArc C (Residue D.rank)) : ColRec :=
  (stateCode x.1, arcRec C D c x.2.1, residueCode x.2.2,
    residueCode (x.2.2 + FiniteExtension.arcLabel C D.residue x.2.1))

theorem colList_code (C : Fin m → Column (Fin f)) (D : CoordinateData m) (c : Fin m → ℕ) :
    (colList C D.rank).map (colRec C D c) =
      colsE (GroupSize.modulus D.rank) (statesE f) (arcsE (2 ^ (m + 1)) (edgeInput C D c))
        (groupE D.rank (GroupSize.modulus D.rank)) := by
  rw [← stateList_code, ← arcList_code, ← residueList_code]
  simp only [colList, colsE, SProd.sprod, List.product, List.map_flatMap, List.flatMap_map,
    List.map_map]
  apply List.flatMap_congr; intro v _
  apply List.flatMap_congr; intro a _
  apply List.map_congr_left; intro g _
  simp only [colRec, arcRec, residueCode_add, FiniteExtension.arcLabel, Function.comp_def]
  rfl

/-! ## Encoded nodes -/

/-- Node records: base and state codes and residue code; hubs use `(-1, -1)`. -/
abbrev NodeE := ℤ × ℤ × List ℤ

/-- The code of a network node. -/
def nodeCode {r : ℕ} : GroupNetwork.Node (State (Fin f)) (Residue r) → NodeE
  | .inl g => (-1, -1, residueCode g)
  | .inr ⟨v, u, g⟩ => (stateCode v, stateCode u.val, residueCode g)

theorem nodeCode_injective (r : ℕ) :
    Function.Injective (nodeCode (f := f) (r := r)) := by
  intro x y h
  rcases x with g | ⟨v, u, g⟩ <;> rcases y with g' | ⟨v', u', g'⟩
  · simp only [nodeCode, Prod.mk.injEq, true_and] at h
    rw [residueCode_injective r h]
  · simp only [nodeCode, Prod.mk.injEq] at h
    have : (0 : ℤ) ≤ stateCode v' := by
      rcases v' with _ | ⟨k, b⟩ <;> simp [stateCode, stubCode] <;> split_ifs <;> omega
    omega
  · simp only [nodeCode, Prod.mk.injEq] at h
    have : (0 : ℤ) ≤ stateCode v := by
      rcases v with _ | ⟨k, b⟩ <;> simp [stateCode, stubCode] <;> split_ifs <;> omega
    omega
  · simp only [nodeCode, Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    have hv := stateCode_injective h1
    subst hv
    have hu := Subtype.ext (stateCode_injective h2)
    subst hu
    rw [residueCode_injective r h3]

/-- The encoded state of a copy: the hub if the state is the base. -/
def stateE (v u : ℤ) (g : List ℤ) : NodeE := if u = v then (-1, -1, g) else (v, u, g)

theorem nodeCode_state {r : ℕ} (v u : State (Fin f)) (g : Residue r) :
    nodeCode (GroupNetwork.state v u g) = stateE (stateCode v) (stateCode u) (residueCode g) := by
  unfold GroupNetwork.state stateE
  by_cases h : u = v
  · simp [h, nodeCode]
  · have h' : stateCode u ≠ stateCode v := fun e => h (stateCode_injective e)
    simp [h, h', nodeCode]

/-- All encoded nodes. -/
def nodesE (states : List ℤ) (groups : List (List ℤ)) : List NodeE :=
  groups.map (fun g => (-1, -1, g)) ++
    states.flatMap fun v => states.flatMap fun u =>
      if u = v then [] else groups.map fun g => (v, u, g)

theorem otherStates_flatMap {β : Type*} (v : State (Fin f)) (G : State (Fin f) → List β) :
    (otherStates v).flatMap (fun u => G u.val) =
      (stateList f).flatMap (fun u => if u = v then [] else G u) := by
  unfold otherStates
  generalize stateList f = l
  induction l with
  | nil => rfl
  | cons u l ih =>
    by_cases h : u = v
    · simp [h, ih]
    · simp [h, ih]

theorem nodeList_code (r : ℕ) :
    (nodeList (f := f) r).map nodeCode =
      nodesE (statesE f) (groupE r (GroupSize.modulus r)) := by
  rw [← stateList_code, ← residueList_code]
  simp only [nodeList, nodesE, List.map_append, List.map_map, List.map_flatMap, List.flatMap_map]
  congr 1
  apply List.flatMap_congr; intro v _
  try simp only [Function.comp_def, nodeCode]
  have hG := otherStates_flatMap v
    (fun u' => (residueList r).map fun g => (stateCode v, stateCode u', residueCode g))
  try simp only at hG
  rw [hG]
  apply List.flatMap_congr; intro u _
  by_cases h : u = v
  · simp [h]
  · have h' : stateCode u ≠ stateCode v := fun e => h (stateCode_injective e)
    simp [h, h', List.map_map, Function.comp_def]

end MWIS.FunNetwork

end
