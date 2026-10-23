module

public import MWIS.GroupNetwork
public import MWIS.NetworkBirkhoff
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Option
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Analysis.Convex.Hull

/-!
# Bounded-circulation reduction for unit flows

An unbounded nonnegative unit flow becomes a bounded circulation by adding
one return arc and splitting every ordinary arc into equally weighted copies.
The integral projection recovers the original unit-flow equations.

Date: 2026-10-23.
-/

@[expose] public section
namespace MWIS.UnitFlowIntegrality

open GroupNetwork
variable {U E : Type*}

/-- A return arc together with a fixed number of copies of every ordinary arc. -/
abbrev SplitArc (E : Type*) (m : ℕ) := Option (E × Fin m)

/-- The return arc starts at the original sink. -/
def splitSource (source : E → U) (t : U) {m : ℕ} : SplitArc E m → U
  | none => t
  | some x => source x.1

/-- The return arc ends at the original source. -/
def splitTarget (target : E → U) (s : U) {m : ℕ} : SplitArc E m → U
  | none => s
  | some x => target x.1

/-- Sum all ordinary copies and discard the return arc. -/
def project {R : Type*} [AddCommMonoid R] {m : ℕ}
    (z : SplitArc E m → R) (e : E) : R := ∑ i, z (some (e, i))

/-- A unit demand at the sink, with the opposite demand at the source. -/
def unitDemand [DecidableEq U] (s t u : U) : ℤ :=
  (if t = u then 1 else 0) - (if s = u then 1 else 0)

/-- Boundary under the split-arc projection, with the return arc accounted for
separately. The identity holds over any abelian group. -/
theorem boundary_project {R : Type*} [AddCommGroup R]
    [Fintype E] [DecidableEq U] (source target : E → U) (s t u : U)
    {m : ℕ} (z : SplitArc E m → R) :
    boundary source target (project z) u =
      boundary (splitSource source t) (splitTarget target s) z u -
      ((if s = u then z none else 0) - (if t = u then z none else 0)) := by
  simp only [boundary, Fintype.sum_option, Fintype.sum_prod_type]
  change ((∑ e, if target e = u then ∑ i, z (some (e, i)) else 0) -
    ∑ e, if source e = u then ∑ i, z (some (e, i)) else 0) =
    (((if s = u then z none else 0) +
      ∑ e, ∑ i, if target e = u then z (some (e, i)) else 0) -
      ((if t = u then z none else 0) +
      ∑ e, ∑ i, if source e = u then z (some (e, i)) else 0)) -
      ((if s = u then z none else 0) - (if t = u then z none else 0))
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]
  abel

/-- Equal copies of a real flow, closed by a return arc of weight one. -/
noncomputable def splitFlow (m : ℕ) (x : E → ℝ) : SplitArc E m → ℝ
  | none => 1
  | some a => x a.1 / (m : ℝ)

/-- Summing the equal copies recovers the original real flow. -/
theorem project_splitFlow {m : ℕ} (hm : 0 < m) (x : E → ℝ) :
    project (splitFlow m x) = x := by
  funext e
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hm)
  simp only [project, splitFlow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- Boundedness is achieved by choosing the number of copies above every
original arc value. -/
theorem splitFlow_bounds {m : ℕ} (hm : 0 < m) (x : E → ℝ)
    (hn : ∀ e, 0 ≤ x e) (hupper : ∀ e, x e ≤ (m : ℝ)) :
    ∀ a, 0 ≤ splitFlow m x a ∧ splitFlow m x a ≤ 1 := by
  intro a
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  cases a with
  | none => simp [splitFlow]
  | some a =>
    simp only [splitFlow]
    exact ⟨div_nonneg (hn _) (le_of_lt hm'), (div_le_one hm').mpr (hupper _)⟩

/-- The added return arc closes the split unit flow into a circulation. -/
theorem splitFlow_boundary [Fintype E] [DecidableEq U]
    (source target : E → U) (s t : U) {m : ℕ} (hm : 0 < m) (x : E → ℝ)
    (hb : ∀ u, boundary source target x u = (unitDemand s t u : ℝ)) :
    ∀ u, boundary (splitSource source t) (splitTarget target s) (splitFlow m x) u = 0 := by
  intro u
  have h := boundary_project source target s t u (splitFlow m x)
  rw [project_splitFlow hm, hb] at h
  simp only [splitFlow, unitDemand, Int.cast_sub, Int.cast_ite, Int.cast_one, Int.cast_zero] at h
  linarith

/-- Integral circulations using the return arc exactly once project to integral
unit flows with the original source and sink. -/
theorem project_integral_unit [Fintype E] [DecidableEq U]
    (source target : E → U) (s t : U) {m : ℕ} (z : SplitArc E m → ℤ)
    (hn : ∀ a, 0 ≤ z a) (hone : z none = 1)
    (hb : ∀ u, boundary (splitSource source t) (splitTarget target s) z u = 0) :
    (∀ e, 0 ≤ project z e) ∧
      (∀ u, boundary source target (project z) u = unitDemand s t u) := by
  constructor
  · intro e
    exact Finset.sum_nonneg (fun _ _ => hn _)
  · intro u
    rw [boundary_project, hb, hone]
    simp only [unitDemand]
    abel

/-- Real linear projection from split arcs to original arcs. -/
noncomputable def projectLinear (m : ℕ) : (SplitArc E m → ℝ) →ₗ[ℝ] (E → ℝ) where
  toFun := project
  map_add' x y := by ext e; simp [project, Finset.sum_add_distrib]
  map_smul' a x := by ext e; simp [project, Finset.mul_sum]

/-- Integral unit flows, without any upper capacities. -/
def integerUnitFlows [Fintype E] [DecidableEq U]
    (source target : E → U) (s t : U) : Set (E → ℤ) :=
  {y | (∀ e, 0 ≤ y e) ∧ ∀ u, boundary source target y u = unitDemand s t u}

/-- The coordinatewise embedding of integer vectors into real vectors. -/
def castVector {A : Type*} (y : A → ℤ) : A → ℝ := fun e => (y e : ℝ)

/-- Projection commutes with the integer-to-real coordinate embedding. -/
theorem project_cast {m : ℕ} (z : SplitArc E m → ℤ) :
    projectLinear m (castVector z) = castVector (project z) := by
  ext e
  simp [projectLinear, project, castVector]

/-- A bounded-circulation convex-hull representation transfers through the
explicit split-arc construction to an unbounded integral-unit-flow hull. -/
theorem unit_mem_convexHull_of_split [Fintype E] [DecidableEq U]
    (source target : E → U) (s t : U) {m : ℕ} (hm : 0 < m) (x : E → ℝ)
    (hc : splitFlow m x ∈ convexHull ℝ (castVector ''
      {z : SplitArc E m → ℤ | (∀ a, z a = 0 ∨ z a = 1) ∧
        (∀ u, boundary (splitSource source t) (splitTarget target s) z u = 0) ∧
        (∀ a, splitFlow m x a = 1 → z a = 1)})) :
    x ∈ convexHull ℝ (castVector '' integerUnitFlows source target s t) := by
  have hp := Set.mem_image_of_mem (projectLinear m) hc
  rw [(projectLinear m).image_convexHull] at hp
  have hpx : projectLinear m (splitFlow m x) = x := project_splitFlow hm x
  rw [hpx] at hp
  apply (convexHull_mono ?_) hp
  rintro _ ⟨z, ⟨y, ⟨hy, hb, hfixed⟩, rfl⟩, rfl⟩
  have hnonneg : ∀ a, 0 ≤ y a := by
    intro a
    rcases hy a with h | h <;> simp [h]
  have hone : y none = 1 := hfixed none rfl
  exact ⟨project y, project_integral_unit source target s t y hnonneg hone hb,
    (project_cast y).symm⟩

/-- Every finite family of nonnegative real arc values admits one positive
integer bound suitable for the equal-copy construction. -/
theorem exists_copy_bound [Fintype E] (x : E → ℝ) (hn : ∀ e, 0 ≤ x e) :
    ∃ m : ℕ, 0 < m ∧ ∀ e, x e ≤ (m : ℝ) := by
  obtain ⟨m, hm⟩ := exists_nat_gt (∑ e, x e)
  refine ⟨m + 1, Nat.succ_pos _, ?_⟩
  intro e
  have hle : x e ≤ ∑ a, x a := Finset.single_le_sum (fun a _ => hn a) (Finset.mem_univ e)
  have hs : (m : ℝ) ≤ (m + 1 : ℕ) := by norm_num
  exact hle.trans ((le_of_lt hm).trans hs)


/-- Every nonnegative real unit flow belongs to the convex hull of integral
nonnegative unit flows. The bounded-circulation decomposition is discharged
by the Birkhoff theorem and the explicit equal-copy construction. -/
theorem unit_mem_convexHull [Fintype E] [DecidableEq E] [DecidableEq U]
    (source target : E → U) (s t : U) (x : E → ℝ)
    (hn : ∀ e, 0 ≤ x e)
    (hb : ∀ u, boundary source target x u = (unitDemand s t u : ℝ)) :
    x ∈ convexHull ℝ (castVector '' integerUnitFlows source target s t) := by
  obtain ⟨m, hm, hupper⟩ := exists_copy_bound x hn
  have hbounds := splitFlow_bounds hm x hn hupper
  have hc := NetworkBirkhoff.bounded_circulation_mem_convexHull
    (splitSource source t) (splitTarget target s) (splitFlow m x)
    (fun a => (hbounds a).1) (fun a => (hbounds a).2)
    (splitFlow_boundary source target s t hm x hb)
  exact unit_mem_convexHull_of_split source target s t hm x hc


/-- The directed incidence map as a real linear map. -/
noncomputable def boundaryLinear [Fintype E] [DecidableEq U]
    (source target : E → U) : (E → ℝ) →ₗ[ℝ] (U → ℝ) where
  toFun := boundary source target
  map_add' x y := by
    ext u
    simp only [boundary, Pi.add_apply]
    have h (v : E → U) (e : E) :
        (if v e = u then x e + y e else 0) =
          (if v e = u then x e else 0) + (if v e = u then y e else 0) := by
      split <;> simp_all
    simp_rw [h]
    simp only [Finset.sum_add_distrib]
    abel
  map_smul' a x := by
    ext u
    simp only [boundary, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    have h (v : E → U) (e : E) :
        (if v e = u then a * x e else 0) = a * (if v e = u then x e else 0) := by
      split <;> simp_all
    simp_rw [h, ← Finset.mul_sum]
    ring

/-- The actual real nonnegative unit-flow polyhedron. -/
def realUnitFlows [Fintype E] [DecidableEq U]
    (source target : E → U) (s t : U) : Set (E → ℝ) :=
  {x | (∀ e, 0 ≤ x e) ∧ ∀ u, boundary source target x u = (unitDemand s t u : ℝ)}

/-- Nonnegativity and fixed real incidence balances define a convex set. -/
theorem convex_realUnitFlows [Fintype E] [DecidableEq U]
    (source target : E → U) (s t : U) : Convex ℝ (realUnitFlows source target s t) := by
  intro x hx y hy a b ha hb hab
  constructor
  · intro e
    exact add_nonneg (mul_nonneg ha (hx.1 e)) (mul_nonneg hb (hy.1 e))
  · intro u
    have h := congrFun ((boundaryLinear source target).map_add (a • x) (b • y)) u
    simp only [map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
    change boundary source target (a • x + b • y) u =
      a * boundary source target x u + b * boundary source target y u at h
    rw [h, hx.2 u, hy.2 u, ← add_mul, hab, one_mul]

/-- Casting an integral flow commutes with its directed incidence map. -/
theorem boundary_cast [Fintype E] [DecidableEq U]
    (source target : E → U) (y : E → ℤ) (u : U) :
    boundary source target (castVector y) u = ((boundary source target y u : ℤ) : ℝ) := by
  simp [boundary, castVector, Int.cast_sum]

/-- The unit-flow polyhedron is exactly the convex hull of its integral points. -/
theorem realUnitFlows_eq_convexHull [Fintype E] [DecidableEq E] [DecidableEq U]
    (source target : E → U) (s t : U) :
    realUnitFlows source target s t =
      convexHull ℝ (castVector '' integerUnitFlows source target s t) := by
  apply Set.Subset.antisymm
  · intro x hx
    exact unit_mem_convexHull source target s t x hx.1 hx.2
  · apply convexHull_min _ (convex_realUnitFlows source target s t)
    rintro _ ⟨y, hy, rfl⟩
    constructor
    · intro e
      change 0 ≤ (y e : ℝ)
      exact_mod_cast hy.1 e
    · intro u
      rw [boundary_cast, hy.2 u]


end MWIS.UnitFlowIntegrality
end
