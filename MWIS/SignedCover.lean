module

public import MWIS.Decomposition
public import MWIS.GroupNetwork
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Integral circulation lifting for the signed cover

Every nonnegative integral signed-stub flow lifts to an ordinary nonnegative
integral circulation in the explicit signed-state graph. The converse follows
from its potential identity. Zero, one, and two-port columns are all permitted;
the two-port case is the signed dual cover.
Prepared 2026-10-23.
-/

@[expose] public section

namespace MWIS.SignedCover

open scoped BigOperators
open MWIS.Walks

variable {Row Edge : Type*} [DecidableEq Row]

/-- The ordered actual arcs of a directed signed-state walk. -/
def arcList {C : Edge → Column Row} {u v : State Row} :
    Walk C u v → List (Arc C)
  | .nil _ => []
  | .cons a tail => a :: arcList tail

omit [DecidableEq Row] in
theorem arcList_labels {C : Edge → Column Row} {u v : State Row}
    (w : Walk C u v) : (arcList w).map (fun a => a.val.1) = w.labels := by
  induction w with
  | nil => rfl
  | cons a tail ih => simp [arcList, Walk.labels, ih]

/-- Endpoint balance of the arc list, with every traversal counted. -/
theorem arcList_balance {C : Edge → Column Row} {u v : State Row}
    (w : Walk C u v) (r : State Row) :
    ((arcList w).map (fun a => if target C a = r then (1 : ℤ) else 0)).sum -
      ((arcList w).map (fun a => if source C a = r then (1 : ℤ) else 0)).sum =
      (if v = r then 1 else 0) - (if u = r then 1 else 0) := by
  induction w with
  | nil => simp [arcList]
  | cons a tail ih =>
    simp only [arcList, List.map_cons, List.sum_cons]
    omega

/-- Projection from actual arc multiplicities to original edge multiplicities. -/
def projection [Fintype Edge] [DecidableEq Edge] (C : Edge → Column Row)
    (f : Arc C → ℕ) (e : Edge) : ℕ :=
  ∑ a, if a.val.1 = e then f a else 0

private theorem sum_fiber_count {A D : Type*} [Fintype A] [DecidableEq A]
    [DecidableEq D] (label : A → D) (l : List A) (d : D) :
    (∑ a, if label a = d then l.count a else 0) = (l.map label).count d := by
  induction l with
  | nil => simp
  | cons b l ih =>
    simp only [List.count_cons, List.map_cons]
    have hadd (a : A) :
        (if label a = d then l.count a + (if b == a then 1 else 0) else 0) =
        (if label a = d then l.count a else 0) +
        (if label a = d then (if b == a then 1 else 0) else 0) := by split_ifs <;> omega
    simp_rw [hadd]
    rw [Finset.sum_add_distrib, ih]
    simp only [beq_iff_eq]
    have hs : (∑ a, if label a = d then (if b = a then 1 else 0) else 0) =
        (if label b = d then 1 else 0) := by
      trans ∑ a, if a = b then (if label b = d then 1 else 0) else 0
      · apply Finset.sum_congr rfl
        intro a _
        by_cases hab : a = b
        · subst a; simp
        · simp [hab, Ne.symm hab]
      · simp
    rw [hs]

/-- The arc-count function has the same projected edge counts as its label list. -/
theorem projection_counts [Fintype Edge] [DecidableEq Edge]
    (C : Edge → Column Row) (l : List (Arc C)) (e : Edge) :
    projection C (Walks.projection l) e = (l.map (fun a => a.val.1)).count e := by
  simpa only [projection, Walks.projection] using
    sum_fiber_count (fun a : Arc C => a.val.1) l e

/-- A finite collection of closed signed-state walks defines an ordinary
integral circulation in the cover. -/
theorem closed_walks_balance [Fintype Edge] [DecidableEq Edge]
    (C : Edge → Column Row) (ws : List (ClosedWalk C)) (r : State Row) :
    GroupNetwork.boundary (source C) (target C)
      (fun a => (Walks.projection (ws.flatMap (fun w => arcList w.2)) a : ℤ)) r = 0 := by
  let l := ws.flatMap (fun w => arcList w.2)
  have hin := sum_mul_projection l (fun a => if target C a = r then (1 : ℤ) else 0)
  have hout := sum_mul_projection l (fun a => if source C a = r then (1 : ℤ) else 0)
  simp only [ite_mul, one_mul, zero_mul] at hin hout
  change (∑ a, if target C a = r then (Walks.projection l a : ℤ) else 0) -
    (∑ a, if source C a = r then (Walks.projection l a : ℤ) else 0) = 0
  have hh := congrArg₂ (fun x y : ℤ => x - y) hin hout
  rw [hh]
  dsimp [l]
  clear hin hout hh l
  induction ws with
  | nil => simp
  | cons w ws ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append]
    have h := arcList_balance w.2 r
    omega

/-- Every nonnegative integral signed flow has an actual ordinary-circulation
lift. Decomposition into closed walks is proved and supplies the witness. -/
theorem integral_lift [Fintype Row] [Fintype Edge] [DecidableEq Edge]
    (C : Edge → Column Row) (y : Edge → ℕ)
    (hy : ∀ r, (∑ e, columnVector (C e) r * (y e : ℤ)) = 0) :
    ∃ f : Arc C → ℕ,
      (∀ r, GroupNetwork.boundary (source C) (target C) (fun a => (f a : ℤ)) r = 0) ∧
      ∀ e, projection C f e = y e := by
  obtain ⟨ws, hp, _⟩ := Decomposition.decompose_flow C y hy
  refine ⟨Walks.projection (ws.flatMap (fun w => arcList w.2)), ?_, ?_⟩
  · exact closed_walks_balance C ws
  · intro e
    rw [projection_counts]
    have hm : (ws.flatMap (fun w => arcList w.2)).map (fun a => a.val.1) =
        ws.flatMap (fun w => w.2.labels) := by
      simp [List.map_flatMap, arcList_labels]
    rw [hm]
    exact hp e

/-- Linear objectives commute with summing cover arcs over their edge labels. -/
theorem weighted_projection [Fintype Edge] [DecidableEq Edge]
    (C : Edge → Column Row) (f : Arc C → ℕ) (c : Edge → ℤ) :
    (∑ e, c e * (projection C f e : ℤ)) =
      ∑ a, c a.val.1 * (f a : ℤ) := by
  simp only [projection, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero,
    Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp

/-- Additive group labels, including torsion labels, commute with projection. -/
theorem label_projection [Fintype Edge] [DecidableEq Edge]
    {G : Type*} [AddCommMonoid G] (C : Edge → Column Row)
    (f : Arc C → ℕ) (label : Edge → G) :
    (∑ e, projection C f e • label e) =
      ∑ a, f a • label a.val.1 := by
  simp only [projection, Finset.sum_smul, ite_smul, zero_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp

/-- Every ordinary nonnegative integral cover circulation projects to a signed
flow satisfying the original row equations. -/
theorem integral_projection_sound [Fintype Row] [Fintype Edge] [DecidableEq Edge]
    (C : Edge → Column Row) (f : Arc C → ℕ)
    (hf : ∀ u, GroupNetwork.boundary (source C) (target C)
      (fun a => (f a : ℤ)) u = 0) (r : Row) :
    (∑ e, columnVector (C e) r * (projection C f e : ℤ)) = 0 := by
  have ht := GroupNetwork.telescope (source C) (target C) (fun a => (f a : ℤ))
    (fun u => potential u r)
  simp only [hf, zero_zsmul, Finset.sum_const_zero] at ht
  simp_rw [← arc_potential C _ r] at ht
  simp only [zsmul_eq_mul] at ht
  rw [weighted_projection]
  simpa only [mul_comm, Int.cast_id] using ht

/-- Exact integral projection equality for the signed cover, including columns
with missing ports. The extra hub represents the missing endpoint. -/
theorem signed_flow_iff_cover_circulation [Fintype Row] [Fintype Edge]
    [DecidableEq Edge] (C : Edge → Column Row) (y : Edge → ℕ) :
    (∀ r, (∑ e, columnVector (C e) r * (y e : ℤ)) = 0) ↔
      ∃ f : Arc C → ℕ,
        (∀ r, GroupNetwork.boundary (source C) (target C)
          (fun a => (f a : ℤ)) r = 0) ∧ ∀ e, projection C f e = y e := by
  constructor
  · exact integral_lift C y
  · rintro ⟨f, hf, hp⟩ r
    have h := integral_projection_sound C f hf r
    simpa only [hp] using h

end MWIS.SignedCover

end
