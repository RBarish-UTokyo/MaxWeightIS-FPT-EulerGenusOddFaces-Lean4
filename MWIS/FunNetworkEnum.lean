module

public import MWIS.FPTHardNetwork
public import Mathlib.Data.List.NodupEquivFin

/-!
# An explicit list enumeration of the finite-group network

Duplicate-free lists of all signed-cover states, signed-cover arcs, residues,
network columns (extension arcs), network nodes and inequality rows, in a fixed
product order. They define the numberings `colsEquiv` and `rowsEquiv` of the
dense network program used by the `Fun` network program.

Prepared 2026-10-23.
-/

@[expose] public section

namespace MWIS.FunNetwork

open Walks ResidueJensen AlgorithmNetworkEncoding

/-! ## Residues -/

/-- The residues `0, 1, …, μ - 1` of `ZMod μ`. -/
def zmodList (μ : ℕ) : List (ZMod μ) := (List.range μ).map (fun i : ℕ => (Nat.cast i : ZMod μ))

theorem zmodList_nodup (μ : ℕ) [NeZero μ] : (zmodList μ).Nodup := by
  unfold zmodList
  apply List.Nodup.map_on _ (List.nodup_range)
  intro a ha b hb hab
  have ha' := List.mem_range.mp ha
  have hb' := List.mem_range.mp hb
  have := congrArg ZMod.val hab
  rwa [ZMod.val_natCast_of_lt ha', ZMod.val_natCast_of_lt hb'] at this

theorem mem_zmodList (μ : ℕ) [NeZero μ] (x : ZMod μ) : x ∈ zmodList μ :=
  List.mem_map.mpr ⟨x.val, List.mem_range.mpr (ZMod.val_lt x), ZMod.natCast_zmod_val x⟩

/-- All vectors `Fin k → ZMod μ`, first coordinate outermost. -/
def vecList (μ : ℕ) : (k : ℕ) → List (Fin k → ZMod μ)
  | 0 => [Fin.elim0]
  | k + 1 => (zmodList μ).flatMap (fun x => (vecList μ k).map (Fin.cons x))

theorem vecList_nodup (μ : ℕ) [NeZero μ] : ∀ k, (vecList μ k).Nodup
  | 0 => by simp [vecList]
  | k + 1 => by
    rw [vecList, List.nodup_flatMap]
    refine ⟨fun x _ => (vecList_nodup μ k).map (fun a b h => by simpa using congrArg Fin.tail h), ?_⟩
    refine (zmodList_nodup μ).imp fun {x y} hxy => ?_
    rw [Function.onFun, List.disjoint_left]
    intro v hv hv'
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hv
    obtain ⟨b, _, hb⟩ := List.mem_map.mp hv'
    have := congrFun hb 0
    simp only [Fin.cons_zero] at this
    exact hxy this.symm

theorem mem_vecList (μ : ℕ) [NeZero μ] : ∀ k (v : Fin k → ZMod μ), v ∈ vecList μ k
  | 0, v => by
    simp only [vecList, List.mem_singleton]
    funext i; exact i.elim0
  | k + 1, v => by
    rw [vecList, List.mem_flatMap]
    refine ⟨v 0, mem_zmodList μ _, List.mem_map.mpr ⟨Fin.tail v, mem_vecList μ k _, ?_⟩⟩
    exact Fin.cons_self_tail v

/-- All residues, parity coordinate outermost. -/
def residueList (r : ℕ) : List (Residue r) :=
  zmodList 2 ×ˢ vecList (GroupSize.modulus r) r

theorem residueList_nodup (r : ℕ) : (residueList r).Nodup :=
  (zmodList_nodup 2).product (vecList_nodup _ r)

theorem mem_residueList (r : ℕ) (g : Residue r) : g ∈ residueList r :=
  List.mem_product.mpr ⟨mem_zmodList 2 _, mem_vecList _ r _⟩

/-! ## Signed-cover states and arcs -/

/-- The hub followed by `(k, false), (k, true)` for every row `k`. -/
def stateList (f : ℕ) : List (State (Fin f)) :=
  none :: (List.finRange f ×ˢ [false, true]).map some

theorem stateList_nodup (f : ℕ) : (stateList f).Nodup := by
  rw [stateList, List.nodup_cons]
  refine ⟨by simp, ?_⟩
  exact ((List.nodup_finRange f).product (by simp)).map (Option.some_injective _)

theorem mem_stateList (f : ℕ) (s : State (Fin f)) : s ∈ stateList f := by
  rcases s with _ | ⟨k, b⟩
  · simp [stateList]
  · simp only [stateList, List.mem_cons, reduceCtorEq, false_or, List.mem_map, Option.some.injEq]
    exact ⟨(k, b), List.mem_product.mpr ⟨List.mem_finRange k, by cases b <;> simp⟩, rfl⟩

variable {f m : ℕ} (C : Fin m → Column (Fin f))

local instance nodeDecidableEq (r : ℕ) :
    DecidableEq (GroupNetwork.Node (State (Fin f)) (Residue r)) :=
  @instDecidableEqSum _ (Σ v : State (Fin f), {u : State (Fin f) // u ≠ v} × Residue r)
    inferInstance inferInstance

/-- The arcs of one edge: the forward arc, and the backward arc for a nonzero column. -/
def arcsOf (e : Fin m) : List (Arc C) :=
  if h : C e = .zero then [⟨(e, false), Or.inr rfl⟩]
  else [⟨(e, false), Or.inr rfl⟩, ⟨(e, true), Or.inl h⟩]

/-- All signed-cover arcs, by edge. -/
def arcList : List (Arc C) := (List.finRange m).flatMap (arcsOf C)

theorem mem_arcsOf (a : Arc C) : a ∈ arcsOf C a.val.1 := by
  rcases a with ⟨⟨e, b⟩, hb⟩
  unfold arcsOf
  split_ifs with h
  · have : b = false := by
      rcases hb with hb | hb
      · exact absurd h hb
      · simpa using hb
    subst this; simp
  · cases b <;> simp

theorem arcsOf_edge (e : Fin m) (a : Arc C) (ha : a ∈ arcsOf C e) : a.val.1 = e := by
  unfold arcsOf at ha
  split_ifs at ha <;> simp at ha <;> rcases ha with rfl | rfl <;> rfl

theorem arcList_nodup : (arcList C).Nodup := by
  rw [arcList, List.nodup_flatMap]
  refine ⟨fun e _ => ?_, ?_⟩
  · unfold arcsOf
    split_ifs <;> simp [Subtype.ext_iff]
  · refine (List.nodup_finRange m).imp fun {e e'} hne => ?_
    rw [Function.onFun, List.disjoint_left]
    intro a ha ha'
    exact hne ((arcsOf_edge C e a ha).symm.trans (arcsOf_edge C e' a ha'))

theorem mem_arcList (a : Arc C) : a ∈ arcList C :=
  List.mem_flatMap.mpr ⟨a.val.1, List.mem_finRange _, mem_arcsOf C a⟩

/-! ## Network columns -/

/-- All network columns (extension arcs): base state, signed-cover arc, starting residue. -/
def colList (r : ℕ) : List (FiniteExtension.ExtensionArc C (Residue r)) :=
  stateList f ×ˢ (arcList C ×ˢ residueList r)

theorem colList_nodup (r : ℕ) : (colList C r).Nodup :=
  (stateList_nodup f).product ((arcList_nodup C).product (residueList_nodup r))

theorem mem_colList (r : ℕ) (x : FiniteExtension.ExtensionArc C (Residue r)) :
    x ∈ colList C r :=
  List.mem_product.mpr ⟨mem_stateList f _,
    List.mem_product.mpr ⟨mem_arcList C _, mem_residueList r _⟩⟩

/-- The numbering of the network columns by their list position. -/
def colsEquiv (r : ℕ) : FiniteExtension.ExtensionArc C (Residue r) ≃ Fin (colList C r).length :=
  (List.Nodup.getEquivOfForallMemList _ (colList_nodup C r) (mem_colList C r)).symm

theorem colsEquiv_symm_apply (r : ℕ) (j : Fin (colList C r).length) :
    (colsEquiv C r).symm j = (colList C r)[j] := rfl

/-! ## Network nodes -/

/-- The states different from `v`, in list order. -/
def otherStates (v : State (Fin f)) : List {u : State (Fin f) // u ≠ v} :=
  (stateList f).filterMap fun u => if h : u = v then none else some ⟨u, h⟩

theorem mem_otherStates (v : State (Fin f)) (u : {u : State (Fin f) // u ≠ v}) :
    u ∈ otherStates v := by
  rw [otherStates, List.mem_filterMap]
  exact ⟨u.val, mem_stateList f _, by simp [u.property]⟩

theorem otherStates_nodup (v : State (Fin f)) : (otherStates (f := f) v).Nodup := by
  apply List.Nodup.filterMap _ (stateList_nodup f)
  intro a a' b hb hb'
  simp only [Option.mem_def] at hb hb'
  split_ifs at hb hb' <;> simp only [reduceCtorEq, Option.some.injEq] at hb hb'
  have e1 := congrArg Subtype.val hb
  have e2 := congrArg Subtype.val hb'
  exact e1.trans e2.symm

/-- All network nodes: the common hubs first, then the private states by base. -/
def nodeList (r : ℕ) : List (GroupNetwork.Node (State (Fin f)) (Residue r)) :=
  (residueList r).map Sum.inl ++
    (stateList f).flatMap fun v => (otherStates v).flatMap fun u =>
      (residueList r).map fun g => Sum.inr ⟨v, u, g⟩

theorem nodeList_nodup (r : ℕ) : (nodeList (f := f) r).Nodup := by
  rw [nodeList, List.nodup_append]
  refine ⟨(residueList_nodup r).map Sum.inl_injective, ?_, ?_⟩
  · rw [List.nodup_flatMap]
    refine ⟨fun v _ => ?_, ?_⟩
    · rw [List.nodup_flatMap]
      refine ⟨fun u _ => (residueList_nodup r).map (fun g g' h => by simpa using h), ?_⟩
      refine (otherStates_nodup v).imp fun {u u'} hne => ?_
      rw [Function.onFun, List.disjoint_left]
      intro x hx hx'
      obtain ⟨g, _, rfl⟩ := List.mem_map.mp hx
      obtain ⟨g', _, h⟩ := List.mem_map.mp hx'
      simp only [Sum.inr.injEq, Sigma.mk.injEq, heq_eq_eq, true_and, Prod.mk.injEq] at h
      exact hne h.1.symm
    · refine (stateList_nodup f).imp fun {v v'} hne => ?_
      rw [Function.onFun, List.disjoint_left]
      intro x hx hx'
      obtain ⟨u, _, hu⟩ := List.mem_flatMap.mp hx
      obtain ⟨g, _, rfl⟩ := List.mem_map.mp hu
      obtain ⟨u', _, hu'⟩ := List.mem_flatMap.mp hx'
      obtain ⟨g', _, h⟩ := List.mem_map.mp hu'
      simp only [Sum.inr.injEq, Sigma.mk.injEq] at h
      exact hne h.1.symm
  · intro a ha b hb hab
    subst hab
    obtain ⟨g, _, rfl⟩ := List.mem_map.mp ha
    obtain ⟨v, _, hv⟩ := List.mem_flatMap.mp hb
    obtain ⟨u, _, hu⟩ := List.mem_flatMap.mp hv
    obtain ⟨g', _, h⟩ := List.mem_map.mp hu
    exact Sum.inr_ne_inl h

theorem mem_nodeList (r : ℕ) (x : GroupNetwork.Node (State (Fin f)) (Residue r)) :
    x ∈ nodeList r := by
  rw [nodeList, List.mem_append]
  rcases x with g | ⟨v, u, g⟩
  · exact Or.inl (List.mem_map.mpr ⟨g, mem_residueList r g, rfl⟩)
  · refine Or.inr (List.mem_flatMap.mpr ⟨v, mem_stateList f v,
      List.mem_flatMap.mpr ⟨u, mem_otherStates v u, List.mem_map.mpr ⟨g, mem_residueList r g, rfl⟩⟩⟩)

/-! ## Inequality rows -/

/-- All equality rows: node balances, then free coordinates. -/
def eqRowList (r : ℕ) : List (EqualityRow (Row := Fin f) (G := Residue r) r) :=
  (nodeList r).map (fun u => (Sum.inl u : EqualityRow (Row := Fin f) (G := Residue r) r)) ++
    (List.finRange r).map (fun d => (Sum.inr d : EqualityRow (Row := Fin f) (G := Residue r) r))

theorem eqRowList_nodup (r : ℕ) : (eqRowList (f := f) r).Nodup := by
  rw [eqRowList, List.nodup_append]
  refine ⟨(nodeList_nodup r).map Sum.inl_injective,
    (List.nodup_finRange r).map Sum.inr_injective, ?_⟩
  intro a ha b hb hab
  subst hab
  obtain ⟨u, _, rfl⟩ := List.mem_map.mp ha
  obtain ⟨d, _, h⟩ := List.mem_map.mp hb
  exact Sum.inr_ne_inl h

theorem mem_eqRowList (r : ℕ) (x : EqualityRow (Row := Fin f) (G := Residue r) r) :
    x ∈ eqRowList r := by
  rw [eqRowList, List.mem_append]
  rcases x with u | d
  · exact Or.inl (List.mem_map.mpr ⟨u, mem_nodeList r u, rfl⟩)
  · exact Or.inr (List.mem_map.mpr ⟨d, List.mem_finRange d, rfl⟩)

/-- All inequality rows: nonnegativity in column order, then both signs of
every equality row. -/
def rowList (r : ℕ) : List (InequalityRow C (G := Residue r) r) :=
  (colList C r).map (fun a => (Sum.inl a : InequalityRow C (G := Residue r) r)) ++
    (eqRowList r ×ˢ [true, false]).map (fun x => (Sum.inr x : InequalityRow C (G := Residue r) r))

theorem rowList_nodup (r : ℕ) : (rowList C r).Nodup := by
  rw [rowList, List.nodup_append]
  refine ⟨(colList_nodup C r).map Sum.inl_injective,
    ((eqRowList_nodup r).product (by simp)).map Sum.inr_injective, ?_⟩
  intro a ha b hb hab
  subst hab
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha
  obtain ⟨y, _, h⟩ := List.mem_map.mp hb
  exact Sum.inr_ne_inl h

theorem mem_rowList (r : ℕ) (x : InequalityRow C (G := Residue r) r) : x ∈ rowList C r := by
  rw [rowList, List.mem_append]
  rcases x with a | ⟨u, s⟩
  · exact Or.inl (List.mem_map.mpr ⟨a, mem_colList C r a, rfl⟩)
  · exact Or.inr (List.mem_map.mpr ⟨(u, s),
      List.mem_product.mpr ⟨mem_eqRowList r u, by cases s <;> simp⟩, rfl⟩)

/-- The numbering of the inequality rows by their list position. -/
noncomputable def rowsEquiv (r : ℕ) : InequalityRow C (G := Residue r) r ≃ Fin (rowList C r).length :=
  haveI := Classical.decEq (InequalityRow C (G := Residue r) r)
  (List.Nodup.getEquivOfForallMemList _ (rowList_nodup C r) (mem_rowList C r)).symm

theorem rowsEquiv_symm_apply (r : ℕ) (i : Fin (rowList C r).length) :
    (rowsEquiv C r).symm i = (rowList C r)[i] := rfl

/-- The column number of the `j`-th listed column is `j`. -/
theorem colsEquiv_getElem (r : ℕ) (j : Fin (colList C r).length) :
    colsEquiv C r (colList C r)[j] = j := by
  rw [← colsEquiv_symm_apply]; exact Equiv.apply_symm_apply _ _

end MWIS.FunNetwork

end
