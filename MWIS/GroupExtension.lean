module

public import MWIS.GroupLifting
public import MWIS.UnitFlowIntegrality

/-!
# Exact finite-group circulation extension

The explicitly constructed finite hub-network polyhedron projects exactly to
the convex hull of nonnegative integral circulations with a prescribed total
group label. Both integral lifting and real polyhedral integrality are proved.

Date: 2026-10-23.
-/

@[expose] public section
namespace MWIS.GroupExtension

open GroupNetwork UnitFlowIntegrality
variable {U E G : Type*}

/-- The real linear map summing lifted arcs over copies and group states. -/
noncomputable def projectionLinear [Fintype U] [Fintype G] :
    (Arc U E G → ℝ) →ₗ[ℝ] (E → ℝ) where
  toFun z e := ∑ v, ∑ a, z (v, e, a)
  map_add' x y := by ext e; simp [Finset.sum_add_distrib]
  map_smul' a x := by ext e; simp [Finset.mul_sum]

/-- The actual real nonnegative flow polyhedron of the common-hub network. -/
def realHubFlows [Fintype U] [Fintype E] [Fintype G]
    [DecidableEq U] [DecidableEq G] [AddCommGroup G]
    (source target : E → U) (label : E → G) (η : G) : Set (Arc U E G → ℝ) :=
  {z | (∀ x, 0 ≤ z x) ∧ ∀ x,
    boundary (hubSource source) (hubTarget target label) z x = (demand η x : ℝ)}

/-- Original nonnegative integral circulations with the prescribed group label. -/
def residueFlows [Fintype E] [DecidableEq U] [AddCommGroup G]
    (source target : E → U) (label : E → G) (η : G) : Set (E → ℤ) :=
  {y | (∀ e, 0 ≤ y e) ∧ (∀ u, boundary source target y u = 0) ∧
    (∑ e, y e • label e) = η}

/-- Projection commutes with the integer-to-real coordinate embedding. -/
theorem projection_cast [Fintype U] [Fintype G] (z : Arc U E G → ℤ) :
    projectionLinear (castVector z) = castVector (projection z) := by
  ext e
  simp [projectionLinear, castVector, projection]

/-- The hub balances are the usual one-source, one-sink unit-flow balances. -/
theorem realHubFlows_eq_unit [Fintype U] [Fintype E] [Fintype G]
    [DecidableEq U] [DecidableEq G] [AddCommGroup G]
    (source target : E → U) (label : E → G) (η : G) :
    realHubFlows source target label η =
      realUnitFlows (hubSource source) (hubTarget target label) (.inl 0) (.inl η) := by
  simp [realHubFlows, realUnitFlows, unitDemand, demand, eq_comm]

/-- Exact projection of integer points, followed by the coordinate embedding. -/
theorem projection_integer_image [Fintype U] [Fintype E] [Fintype G]
    [DecidableEq U] [DecidableEq E] [DecidableEq G] [AddCommGroup G]
    (source target : E → U) (label : E → G) (η : G) :
    projectionLinear '' (castVector ''
      integerUnitFlows (hubSource source) (hubTarget target label) (.inl 0) (.inl η)) =
      castVector '' residueFlows source target label η := by
  apply Set.Subset.antisymm
  · rintro _ ⟨_, ⟨z, ⟨hn, hz⟩, rfl⟩, rfl⟩
    have hbal : Balanced source target label η z := by
      intro x
      simpa [unitDemand, demand, eq_comm] using hz x
    exact ⟨projection z, integral_projection_sound source target label η z hn hbal,
      (projection_cast z).symm⟩
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨z, hn, hz, hp⟩ := (GroupLifting.integral_projection_exact
      source target label η y).mp hy
    refine ⟨castVector z, ⟨z, ⟨hn, ?_⟩, rfl⟩, ?_⟩
    · intro x
      simpa [unitDemand, demand, eq_comm] using hz x
    · rw [projection_cast, hp]

/-- The finite common-hub network is an exact extended formulation of the
convex hull of group-constrained nonnegative integral circulations. -/
theorem projection_real_hull [Fintype U] [Fintype E] [Fintype G]
    [DecidableEq U] [DecidableEq E] [DecidableEq G] [AddCommGroup G]
    (source target : E → U) (label : E → G) (η : G) :
    projectionLinear '' realHubFlows source target label η =
      convexHull ℝ (castVector '' residueFlows source target label η) := by
  rw [realHubFlows_eq_unit, realUnitFlows_eq_convexHull,
    LinearMap.image_convexHull, projection_integer_image]

end MWIS.GroupExtension
end
