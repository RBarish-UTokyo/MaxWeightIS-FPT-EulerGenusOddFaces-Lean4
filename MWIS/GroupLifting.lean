module

public import MWIS.DirectedDecomposition
public import Mathlib.Tactic.Ring

/-!
# Integral lifting into the finite-group hub network

Closed directed walks lift to paths between common group hubs. Concatenating
these paths lifts an arbitrary nonnegative integral circulation with the
required label. The walk decomposition is proved in DirectedDecomposition.

Date: 2026-10-23.
-/

@[expose] public section
namespace MWIS.GroupLifting

open GroupNetwork DirectedDecomposition

variable {U E G : Type*} [AddCommGroup G]

/-- Total additive label of an ordered list of original arcs. -/
def labelSum (label : E → G) (l : List E) : G := (l.map label).sum

/-- Lift the arc occurrences of a walk in the copy with the chosen base,
starting at the specified group coordinate. -/
def liftEdges {source target : E → U} (label : E → G) {u t : U}
    (w : Walk source target u t) (v : U) (a : G) : List (Arc U E G) :=
  match w with
  | .nil _ => []
  | .cons e tail => (v, e, a) :: liftEdges label tail v (a + label e)

/-- Lifting changes no original arc occurrence. -/
theorem liftEdges_projection {source target : E → U} (label : E → G)
    {u t : U} (w : Walk source target u t) (v : U) (a : G) :
    (liftEdges label w v a).map (fun x => x.2.1) = w.edges := by
  induction w generalizing a with
  | nil u => rfl
  | cons e tail ih => simp [liftEdges, Walk.edges, ih]

/-- The lifted walk's incidence sum telescopes between its actual group states. -/
theorem liftEdges_boundary [DecidableEq U] [DecidableEq G]
    {source target : E → U} (label : E → G) {u t : U}
    (w : Walk source target u t) (v : U) (a : G) (r : Node U G) :
    ((liftEdges label w v a).map
      (fun x => column (hubSource source) (hubTarget target label) x r)).sum =
      potential (state v t (a + labelSum label w.edges)) r - potential (state v u a) r := by
  induction w generalizing a with
  | nil u => simp [liftEdges, Walk.edges, labelSum]
  | cons e tail ih =>
    simp only [liftEdges, List.map_cons, List.sum_cons, Walk.edges]
    rw [ih]
    have heq : a + labelSum label (e :: tail.edges) =
        (a + label e) + labelSum label tail.edges := by
      simp [labelSum, add_assoc]
    rw [heq]
    change (potential (state v (target e) (a + label e)) r -
        potential (state v (source e) a) r) + _ = _
    omega

/-- Consecutively lift a family of closed walks through their successive hubs. -/
def liftFamily {source target : E → U} (label : E → G)
    (ws : List (ClosedWalk source target)) (a : G) : List (Arc U E G) :=
  match ws with
  | [] => []
  | w :: rest => liftEdges label w.2 w.1 a ++
      liftFamily label rest (a + labelSum label w.2.edges)

/-- Concatenated lifts preserve the complete multiset of original arcs. -/
theorem liftFamily_projection {source target : E → U} (label : E → G)
    (ws : List (ClosedWalk source target)) (a : G) :
    (liftFamily label ws a).map (fun x => x.2.1) = ws.flatMap (fun w => w.2.edges) := by
  induction ws generalizing a with
  | nil => rfl
  | cons w rest ih => simp [liftFamily, liftEdges_projection, ih]

/-- The family lift has only its two endpoint hub imbalances. -/
theorem liftFamily_boundary [DecidableEq U] [DecidableEq G]
    {source target : E → U} (label : E → G)
    (ws : List (ClosedWalk source target)) (a : G) (r : Node U G) :
    ((liftFamily label ws a).map
      (fun x => column (hubSource source) (hubTarget target label) x r)).sum =
      potential (.inl (a + labelSum label (ws.flatMap (fun w => w.2.edges)))) r -
        potential (.inl a) r := by
  induction ws generalizing a with
  | nil => simp [liftFamily, labelSum]
  | cons w rest ih =>
    simp only [liftFamily, List.map_append, List.sum_append, liftEdges_boundary, ih,
      List.flatMap_cons]
    simp only [state, dite_true]
    have heq : a + labelSum label (w.2.edges ++ rest.flatMap (fun w => w.2.edges)) =
        (a + labelSum label w.2.edges) + labelSum label (rest.flatMap (fun w => w.2.edges)) := by
      simp [labelSum, add_assoc]
    rw [heq]
    omega

omit [AddCommGroup G] in
/-- Projecting integer occurrence counts equals counting projected occurrences. -/
theorem projection_counts [Fintype U] [Fintype G] [DecidableEq U]
    [DecidableEq E] [DecidableEq G] (l : List (Arc U E G)) (e : E) :
    projection (fun x => (l.count x : ℤ)) e =
      ((l.map (fun x => x.2.1)).count e : ℤ) := by
  induction l with
  | nil => simp [projection]
  | cons x l ih =>
    simp only [projection, List.count_cons, List.map_cons, Nat.cast_add,
      Finset.sum_add_distrib] at *
    rw [ih]
    congr 1
    rcases x with ⟨v, e', a⟩
    by_cases he : e' = e
    · subst e'
      simp only [beq_self_eq_true, ↓reduceIte, Nat.cast_one, beq_iff_eq,
        Prod.mk.injEq, true_and]
      simp_rw [ite_and]
      simp
    · simp [Prod.mk.injEq, he]

/-- The boundary of occurrence counts is the sum of the occurrence columns. -/
theorem boundary_counts {V A : Type*} [Fintype A] [DecidableEq A] [DecidableEq V]
    (source target : A → V) (l : List A) (r : V) :
    boundary source target (fun e => (l.count e : ℤ)) r =
      (l.map (fun e => column source target e r)).sum := by
  rw [← sum_count]
  simp [boundary, column, potential, mul_sub, mul_ite, Finset.sum_sub_distrib]

/-- Every natural directed circulation of prescribed total group label admits
an integral nonnegative lift to the explicit shared-hub network. -/
theorem integral_lift [Fintype U] [Fintype E] [Fintype G]
    [DecidableEq U] [DecidableEq E] [DecidableEq G]
    (source target : E → U) (label : E → G) (η : G) (y : E → ℕ)
    (hy : ∀ r, boundary source target (fun e => (y e : ℤ)) r = 0)
    (hlabel : (∑ e, y e • label e) = η) :
    ∃ z : Arc U E G → ℤ, (∀ x, 0 ≤ z x) ∧
      Balanced source target label η z ∧
      ∀ e, projection z e = (y e : ℤ) := by
  obtain ⟨ws, hws⟩ := decompose_flow source target y hy
  let l := liftFamily label ws 0
  refine ⟨fun x => (l.count x : ℤ), fun _ => Int.natCast_nonneg _, ?_, ?_⟩
  · intro r
    rw [boundary_counts]
    dsimp [l]
    rw [liftFamily_boundary]
    have hsum : labelSum label (ws.flatMap (fun w => w.2.edges)) = η := by
      rw [labelSum, ← sum_count]
      simp only [hws]
      exact hlabel
    rw [hsum, zero_add]
    simp [potential, demand, eq_comm]
  · intro e
    rw [projection_counts]
    dsimp [l]
    rw [liftFamily_projection, hws]

/-- Exact integral projection theorem for the explicitly constructed finite
hub network. No existence or decomposition assumptions are left over. -/
theorem integral_projection_exact [Fintype U] [Fintype E] [Fintype G]
    [DecidableEq U] [DecidableEq E] [DecidableEq G]
    (source target : E → U) (label : E → G) (η : G) (y : E → ℤ) :
    ((∀ e, 0 ≤ y e) ∧ (∀ u, boundary source target y u = 0) ∧
      (∑ e, y e • label e) = η) ↔
    ∃ z : Arc U E G → ℤ, (∀ x, 0 ≤ z x) ∧
      Balanced source target label η z ∧ projection z = y := by
  constructor
  · rintro ⟨hn, hb, hl⟩
    have hcast : ∀ e, ((y e).toNat : ℤ) = y e := fun e => Int.toNat_of_nonneg (hn e)
    obtain ⟨z, hz, hbal, hp⟩ := integral_lift source target label η
      (fun e => (y e).toNat) (by simpa only [hcast] using hb)
      (by simpa only [← natCast_zsmul, hcast] using hl)
    exact ⟨z, hz, hbal, funext (fun e => (hp e).trans (hcast e))⟩
  · rintro ⟨z, hn, hz, rfl⟩
    exact integral_projection_sound source target label η z hn hz


end MWIS.GroupLifting
end
