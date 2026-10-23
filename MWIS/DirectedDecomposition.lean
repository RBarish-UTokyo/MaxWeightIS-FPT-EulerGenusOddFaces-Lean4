module

public import MWIS.GroupNetwork
public import Mathlib.Data.List.Count
public import Mathlib.Data.Finset.Basic
public import Mathlib.Tactic.Push

/-!
# Integral directed circulation decomposition

Every nonnegative integral circulation in a finite directed multigraph is a
finite family of closed walks, with all arc multiplicities preserved.

Date: 2026-10-23.
-/

@[expose] public section
namespace MWIS.DirectedDecomposition

variable {U E : Type*}

/-- The unit potential of a base vertex. -/
def potential [DecidableEq U] (u r : U) : ℤ := if u = r then 1 else 0

/-- A directed incidence column, including loops. -/
def column [DecidableEq U] (source target : E → U) (e : E) (r : U) : ℤ :=
  potential (target e) r - potential (source e) r

/-- A finite directed walk, with adjacency enforced by its endpoint types. -/
inductive Walk (source target : E → U) : U → U → Type _
  | nil (u : U) : Walk source target u u
  | cons (e : E) {v : U} (tail : Walk source target (target e) v) :
      Walk source target (source e) v

/-- Ordered original arc occurrences along a walk. -/
def Walk.edges {source target : E → U} {u v : U} : Walk source target u v → List E
  | .nil _ => []
  | .cons e tail => e :: tail.edges

/-- A closed walk together with a choice of anchor. -/
abbrev ClosedWalk (source target : E → U) := Σ u, Walk source target u u

/-- Incidence columns telescope along a directed walk. -/
theorem Walk.telescope [DecidableEq U] {source target : E → U} {u v : U}
    (w : Walk source target u v) (r : U) :
    (w.edges.map (fun e => column source target e r)).sum =
      potential v r - potential u r := by
  induction w with
  | nil u => simp [Walk.edges]
  | cons e tail ih =>
    simp only [Walk.edges, List.map_cons, List.sum_cons]
    rw [ih]
    simp only [column]
    omega

/-- Any open partial walk can continue using an unconsumed outgoing arc. -/
theorem exists_outgoing [DecidableEq U] (source target : E → U)
    (l : List E) (u v : U) (hne : u ≠ v)
    (hsum : ∀ r, (l.map (fun e => column source target e r)).sum =
      potential u r - potential v r) :
    ∃ e ∈ l, source e = v := by
  by_contra! hn
  have hz : 0 ≤ (l.map (fun e => column source target e v)).sum := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    have he' := hn e he
    simp only [column, potential, ite_eq_right he', sub_zero]
    split <;> omega
  have hh := hsum v
  simp [potential, hne] at hh
  omega

/-- Complete a walk and leave a balanced multiset of unused arc occurrences. -/
theorem complete_walk [DecidableEq U] [DecidableEq E]
    (source target : E → U) (l : List E) (u v : U)
    (hsum : ∀ r, (l.map (fun e => column source target e r)).sum =
      potential u r - potential v r) :
    ∃ w : Walk source target v u, ∃ rest : List E,
      l.Perm (w.edges ++ rest) ∧
      ∀ r, (rest.map (fun e => column source target e r)).sum = 0 := by
  by_cases huv : u = v
  · subst v
    exact ⟨.nil u, l, by simp [Walk.edges], fun r => by simpa using hsum r⟩
  · obtain ⟨e, he, hv⟩ := exists_outgoing source target l u v huv hsum
    subst v
    have hp := List.perm_cons_erase he
    have hrem : ∀ r, ((l.erase e).map (fun e => column source target e r)).sum =
        potential u r - potential (target e) r := by
      intro r
      have hh := (hp.map (fun e => column source target e r)).sum_eq
      simp only [List.map_cons, List.sum_cons] at hh
      have hs := hsum r
      change (l.map (fun e => column source target e r)).sum =
        (potential (target e) r - potential (source e) r) +
          ((l.erase e).map (fun e => column source target e r)).sum at hh
      omega
    obtain ⟨w, rest, hw, hz⟩ := complete_walk source target (l.erase e) u (target e) hrem
    refine ⟨.cons e w, rest, ?_, hz⟩
    simpa [Walk.edges] using hp.trans (List.Perm.cons e hw)
termination_by l.length
decreasing_by
  have hlen := List.length_erase_of_mem he
  have hpos : 0 < l.length := List.length_pos_of_mem he
  omega

/-- A balanced list of occurrences decomposes into closed directed walks. -/
theorem decompose_list [DecidableEq U] [DecidableEq E]
    (source target : E → U) (l : List E)
    (hzero : ∀ r, (l.map (fun e => column source target e r)).sum = 0) :
    ∃ ws : List (ClosedWalk source target), l.Perm (ws.flatMap (fun w => w.2.edges)) := by
  cases l with
  | nil => exact ⟨[], by simp⟩
  | cons e l =>
    have hrem : ∀ r, (l.map (fun e => column source target e r)).sum =
        potential (source e) r - potential (target e) r := by
      intro r
      have hz := hzero r
      simp only [List.map_cons, List.sum_cons] at hz
      change (potential (target e) r - potential (source e) r) +
        (l.map (fun e => column source target e r)).sum = 0 at hz
      omega
    obtain ⟨w, rest, hp, hz⟩ := complete_walk source target l (source e) (target e) hrem
    obtain ⟨ws, hws⟩ := decompose_list source target rest hz
    refine ⟨⟨source e, .cons e w⟩ :: ws, ?_⟩
    have hfirst := List.Perm.cons e hp
    have hsecond := List.Perm.append_left (e :: w.edges) hws
    simpa [List.flatMap_cons, Walk.edges] using hfirst.trans hsecond
termination_by l.length
decreasing_by
  have hlen := hp.length_eq
  simp_all only [List.length_cons, List.length_append]
  omega

/-- Each occurrence contributes once to its arc's multiplicity. -/
theorem sum_count [Fintype E] [DecidableEq E] {A : Type*} [AddCommMonoid A]
    (l : List E) (f : E → A) :
    (∑ e, l.count e • f e) = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.count_cons, List.map_cons, List.sum_cons]
    simp only [beq_iff_eq, ite_smul, add_smul, one_smul, zero_smul]
    rw [Finset.sum_add_distrib, ih]
    simp [add_comm]

/-- A concrete finite list containing all arc copies of a natural flow. -/
noncomputable def copies [Fintype E] (y : E → ℕ) : List E :=
  Finset.univ.toList.flatMap (fun e => List.replicate (y e) e)

@[simp] theorem count_copies [Fintype E] [DecidableEq E] (y : E → ℕ) (e : E) :
    (copies y).count e = y e := by
  simp only [copies, List.count_flatMap, Function.comp_def, List.count_replicate, beq_iff_eq]
  rw [← List.sum_toFinset _ (Finset.nodup_toList _)]
  simp

/-- Every integral directed circulation has a closed-walk decomposition with
exactly the prescribed multiplicity of every original arc. -/
theorem decompose_flow [Fintype E] [DecidableEq E] [DecidableEq U]
    (source target : E → U) (y : E → ℕ)
    (hy : ∀ r, GroupNetwork.boundary source target (fun e => (y e : ℤ)) r = 0) :
    ∃ ws : List (ClosedWalk source target),
      ∀ e, (ws.flatMap (fun w => w.2.edges)).count e = y e := by
  have hz : ∀ r, ((copies y).map (fun e => column source target e r)).sum = 0 := by
    intro r
    rw [← sum_count]
    simp only [count_copies, nsmul_eq_mul, column, potential, mul_sub, mul_ite,
      mul_one, mul_zero, Finset.sum_sub_distrib]
    exact hy r
  obtain ⟨ws, hp⟩ := decompose_list source target (copies y) hz
  refine ⟨ws, fun e => ?_⟩
  have he := hp.count_eq e
  rw [count_copies] at he
  exact he.symm

end MWIS.DirectedDecomposition
end
