module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Abel

/-!
# Finite-group hub networks

The hub construction has one group-expanded copy for every base vertex.
Its integral balance equations imply both circulation of the projection and
its prescribed total group label. All vertices and arcs are defined explicitly.

Date: 2026-10-23.
-/

@[expose] public section

namespace MWIS.GroupNetwork

variable {U E G : Type*}

/-- Incoming flow minus outgoing flow, counting a loop in both terms. -/
def boundary {R : Type*} [AddCommGroup R] [Fintype E] [DecidableEq U]
    (source target : E → U) (z : E → R) (u : U) : R :=
  (∑ e, if target e = u then z e else 0) -
    ∑ e, if source e = u then z e else 0

/-- Summation by parts for the directed incidence map and any abelian-group
potential. This identity also applies to finite groups with torsion. -/
theorem telescope [Fintype U] [Fintype E] [DecidableEq U]
    [AddCommGroup G] (source target : E → U) (z : E → ℤ) (p : U → G) :
    (∑ e, z e • (p (target e) - p (source e))) =
      ∑ u, boundary source target z u • p u := by
  simp only [boundary, smul_sub, Finset.sum_sub_distrib, sub_smul,
    Finset.sum_smul]
  congr 1
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _
    simp only [ite_smul, zero_smul]
    simp
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _
    simp only [ite_smul, zero_smul]
    simp

/-- A common group hub, or a nonbase state private to one expanded copy. -/
abbrev Node (U G : Type*) := G ⊕ (Σ v : U, {u : U // u ≠ v} × G)

/-- An arc records its copy's base, its original arc, and its starting label. -/
abbrev Arc (U E G : Type*) := U × E × G

/-- The state over the base is identified with its common hub. -/
def state [DecidableEq U] (v u : U) (a : G) : Node U G :=
  if h : u = v then .inl a else .inr ⟨v, ⟨⟨u, h⟩, a⟩⟩

/-- Source of an arc in the hub network. -/
def hubSource [DecidableEq U] (source : E → U) (x : Arc U E G) : Node U G :=
  state x.1 (source x.2.1) x.2.2

/-- Target of an arc in the hub network. -/
def hubTarget [DecidableEq U] [Add G] (target : E → U) (label : E → G)
    (x : Arc U E G) : Node U G :=
  state x.1 (target x.2.1) (x.2.2 + label x.2.1)

/-- The group coordinate is well defined even at an identified hub. -/
def groupPotential : Node U G → G
  | .inl a => a
  | .inr x => x.2.2

@[simp] theorem groupPotential_state [DecidableEq U] (v u : U) (a : G) :
    groupPotential (state v u a) = a := by
  by_cases h : u = v <;> simp [state, groupPotential, h]

/-- Every lifted arc changes the group coordinate by its original label. -/
theorem arc_group_potential [DecidableEq U] [AddCommGroup G]
    (source target : E → U) (label : E → G) (x : Arc U E G) :
    groupPotential (hubTarget target label x) -
      groupPotential (hubSource source x) = label x.2.1 := by
  simp [hubSource, hubTarget]

/-- Projection sums over all copies and all starting group states. -/
def projection [Fintype U] [Fintype G] (z : Arc U E G → ℤ) (e : E) : ℤ :=
  ∑ v, ∑ a, z (v, e, a)

/-- One unit is sent from the zero hub to the prescribed group hub.
For a zero prescribed label the balance is identically zero. -/
def demand [DecidableEq U] [DecidableEq G] [Zero G] (η : G) (x : Node U G) : ℤ :=
  (if x = .inl η then 1 else 0) - (if x = .inl 0 then 1 else 0)

/-- The integral flow equations of the explicit hub network. -/
def Balanced [Fintype U] [Fintype E] [Fintype G]
    [DecidableEq U] [DecidableEq G] [AddCommGroup G]
    (source target : E → U) (label : E → G) (η : G)
    (z : Arc U E G → ℤ) : Prop :=
  ∀ x, boundary (hubSource source) (hubTarget target label) z x = demand η x

/-- Reindexing the total group label through the projection. -/
theorem projection_label {A : Type*} [Fintype U] [Fintype E] [Fintype G]
    [AddCommGroup A] (label : E → A) (z : Arc U E G → ℤ) :
    (∑ e, projection z e • label e) = ∑ x, z x • label x.2.1 := by
  simp only [projection, Finset.sum_smul, Fintype.sum_prod_type]
  rw [Finset.sum_comm]

/-- Every integral hub flow has the requested total group label. -/
theorem balanced_label [Fintype U] [Fintype E] [Fintype G]
    [DecidableEq U] [DecidableEq G] [AddCommGroup G]
    (source target : E → U) (label : E → G) (η : G)
    (z : Arc U E G → ℤ) (hz : Balanced source target label η z) :
    (∑ e, projection z e • label e) = η := by
  change ∀ x, boundary (hubSource source) (hubTarget target label) z x = demand η x at hz
  rw [projection_label]
  calc
    (∑ x, z x • label x.2.1) =
        ∑ x, z x • (groupPotential (hubTarget target label x) -
          groupPotential (hubSource source x)) := by
      simp only [arc_group_potential]
    _ = ∑ x, boundary (hubSource source) (hubTarget target label) z x •
        groupPotential x := telescope _ _ _ _
    _ = η := by
      simp only [hz, demand, sub_smul, ite_smul, one_smul, zero_smul,
        Finset.sum_sub_distrib]
      simp [groupPotential]

/-- Base incidence potentials vanish at every common hub. The correction by
the copy's base makes the potential independent of the hub representative. -/
def basePotential [DecidableEq U] (r : U) : Node U G → ℤ
  | .inl _ => 0
  | .inr x => (if x.2.1.1 = r then 1 else 0) - (if x.1 = r then 1 else 0)

@[simp] theorem basePotential_state [DecidableEq U] (r v u : U) (a : G) :
    basePotential r (state v u a) =
      (if u = r then 1 else 0) - (if v = r then 1 else 0) := by
  by_cases h : u = v
  · subst u; simp [state, basePotential]
  · simp [state, basePotential, h]

/-- The corrected base potential changes by the original incidence column. -/
theorem arc_base_potential [DecidableEq U] [Add G]
    (source target : E → U) (label : E → G) (r : U) (x : Arc U E G) :
    basePotential r (hubTarget target label x) -
      basePotential r (hubSource source x) =
      (if target x.2.1 = r then 1 else 0) -
        (if source x.2.1 = r then 1 else 0) := by
  simp only [hubSource, hubTarget, basePotential_state]
  omega

/-- The base projection of every balanced hub flow is a circulation.
This follows from incidence potentials, so no walk decomposition is assumed. -/
theorem balanced_projection [Fintype U] [Fintype E] [Fintype G]
    [DecidableEq U] [DecidableEq G] [AddCommGroup G]
    (source target : E → U) (label : E → G) (η : G)
    (z : Arc U E G → ℤ) (hz : Balanced source target label η z) (r : U) :
    boundary source target (projection z) r = 0 := by
  change ∀ x, boundary (hubSource source) (hubTarget target label) z x = demand η x at hz
  calc
    boundary source target (projection z) r =
        ∑ e, projection z e • ((if target e = r then (1 : ℤ) else 0) -
          (if source e = r then 1 else 0)) := by
      simp [boundary, mul_sub, Finset.sum_sub_distrib, mul_ite]
    _ = ∑ x, z x • ((if target x.2.1 = r then (1 : ℤ) else 0) -
          (if source x.2.1 = r then 1 else 0)) := projection_label _ _
    _ = ∑ x, z x • (basePotential r (hubTarget target label x) -
          basePotential r (hubSource source x)) := by
      simp only [arc_base_potential]
    _ = ∑ x, boundary (hubSource source) (hubTarget target label) z x •
          basePotential r x := telescope _ _ _ _
    _ = 0 := by
      simp only [hz, demand, sub_smul, ite_smul, one_smul, zero_smul,
        Finset.sum_sub_distrib]
      simp [basePotential]

/-- Nonnegative flows have nonnegative projections. -/
theorem projection_nonneg [Fintype U] [Fintype G]
    (z : Arc U E G → ℤ) (hz : ∀ x, 0 ≤ z x) (e : E) :
    0 ≤ projection z e := by
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => hz _))

/-- The integral soundness direction of the finite-group extension, for the
actual finite network with shared group hubs. -/
theorem integral_projection_sound [Fintype U] [Fintype E] [Fintype G]
    [DecidableEq U] [DecidableEq G] [AddCommGroup G]
    (source target : E → U) (label : E → G) (η : G)
    (z : Arc U E G → ℤ) (hn : ∀ x, 0 ≤ z x)
    (hz : Balanced source target label η z) :
    (∀ e, 0 ≤ projection z e) ∧
      (∀ u, boundary source target (projection z) u = 0) ∧
      (∑ e, projection z e • label e) = η :=
  ⟨projection_nonneg z hn, balanced_projection source target label η z hz,
    balanced_label source target label η z hz⟩

/-- The number of arcs is exactly the group size times the numbers of original
vertices and arcs. -/
theorem arc_card [Fintype U] [Fintype E] [Fintype G] :
    Fintype.card (Arc U E G) = Fintype.card U * Fintype.card E * Fintype.card G := by
  simp [Arc, Nat.mul_assoc]

end MWIS.GroupNetwork

end
