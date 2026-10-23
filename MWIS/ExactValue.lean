module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Choose

/-!
# Exact value of the residue relaxation

This module proves the convex-hull argument for the exact value. The integer class
coordinates retain the fixed torsion coordinate through the choice of the
residue-feasible set. The coarse Jensen inequality, the description of that
set, and the network projection equality are explicit hypotheses here.
The module does not assert a construction or complexity bound for the network.
-/

@[expose] public section

namespace MWIS.ExactValue

/-- Coarse Jensen at the zero free coordinate, within one fixed torsion class. -/
def CoarseJensenAtZero {D : Type*} (F : (D → ℤ) → ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] (weights : ι → ℝ) (z : ι → D → ℤ),
    (∀ i, 0 ≤ weights i) → (∑ i, weights i) = 1 →
    (∀ d, ∑ i, weights i * (z i d : ℝ) = 0) →
    F 0 ≤ ∑ i, weights i * F (z i)

/-- Vanishing of the free-coordinate map on a convex combination implies
vanishing of the averaged integral class coordinates. -/
theorem free_average_zero {ι D E : Type*} [Fintype ι]
    [AddCommGroup E] [Module ℝ E]
    (W : E →ₗ[ℝ] (D → ℝ)) (μ : ℝ) (hμ : μ ≠ 0)
    (weights : ι → ℝ) (y : ι → E) (z : ι → D → ℤ)
    (hfree : ∀ i, W (y i) = fun d => μ * (z i d : ℝ))
    (hbalance : W (∑ i, weights i • y i) = 0) :
    ∀ d, ∑ i, weights i * (z i d : ℝ) = 0 := by
  intro d
  have h : μ * (∑ i, weights i * (z i d : ℝ)) = 0 := by
    calc
      μ * (∑ i, weights i * (z i d : ℝ)) =
          ∑ i, weights i * (μ * (z i d : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = W (∑ i, weights i • y i) d := by
        simp [map_sum, map_smul, hfree, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      _ = 0 := by rw [hbalance]; rfl
  exact (mul_eq_zero.mp h).resolve_left hμ

/-- Every zero-free-coordinate point of the residue convex hull has cost at
least the exact class value. The point need not be integral. -/
theorem convex_hull_cost_lower_bound {D E : Type*}
    [AddCommGroup E] [Module ℝ E]
    (S : Set E) (cost : E →ₗ[ℝ] ℝ) (W : E →ₗ[ℝ] (D → ℝ))
    (μ : ℝ) (hμ : 0 < μ) (F : (D → ℤ) → ℝ)
    (hJensen : CoarseJensenAtZero F)
    (hresidue : ∀ y ∈ S, ∃ z : D → ℤ,
      W y = (fun d => μ * (z d : ℝ)) ∧ F z ≤ cost y)
    (y : E) (hy : y ∈ convexHull ℝ S) (hbalance : W y = 0) :
    F 0 ≤ cost y := by
  classical
  obtain ⟨ι, inst, weights, points, hweights, hsum, hpoints, hcomb⟩ :=
    mem_convexHull_iff_exists_fintype.mp hy
  let _ := inst
  choose z hzW hzCost using fun i => hresidue (points i) (hpoints i)
  have hzero : ∀ d, ∑ i, weights i * (z i d : ℝ) = 0 :=
    free_average_zero W μ (ne_of_gt hμ) weights points z hzW (by rw [hcomb, hbalance])
  calc
    F 0 ≤ ∑ i, weights i * F (z i) := hJensen ι weights z hweights hsum hzero
    _ ≤ ∑ i, weights i * cost (points i) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hzCost i) (hweights i))
    _ = cost y := by rw [← hcomb]; simp [map_sum, map_smul, smul_eq_mul]

/-- An exact-class minimizer attains the minimum on the zero-free-coordinate
slice of the residue convex hull. -/
theorem exact_minimum_on_slice {D E : Type*}
    [AddCommGroup E] [Module ℝ E]
    (S : Set E) (cost : E →ₗ[ℝ] ℝ) (W : E →ₗ[ℝ] (D → ℝ))
    (μ : ℝ) (hμ : 0 < μ) (F : (D → ℤ) → ℝ)
    (hJensen : CoarseJensenAtZero F)
    (hresidue : ∀ y ∈ S, ∃ z : D → ℤ,
      W y = (fun d => μ * (z d : ℝ)) ∧ F z ≤ cost y)
    (hattain : ∃ y ∈ S, W y = 0 ∧ cost y = F 0) :
    IsLeast (cost '' {y | y ∈ convexHull ℝ S ∧ W y = 0}) (F 0) := by
  constructor
  · obtain ⟨y, hy, hW, hc⟩ := hattain
    exact ⟨y, ⟨subset_convexHull ℝ S hy, hW⟩, hc⟩
  · rintro v ⟨y, ⟨hy, hW⟩, rfl⟩
    exact convex_hull_cost_lower_bound S cost W μ hμ F hJensen hresidue y hy hW

/-- Any extension projecting exactly to the residue convex hull has the same
attained optimum after the free-coordinate equations are imposed. No
integrality of the optimizing extension variable is required. -/
theorem exact_value_of_extension {D E X : Type*}
    [AddCommGroup E] [Module ℝ E]
    (S : Set E) (Z : Set X) (ρ : X → E)
    (cost : E →ₗ[ℝ] ℝ) (W : E →ₗ[ℝ] (D → ℝ))
    (μ : ℝ) (hμ : 0 < μ) (F : (D → ℤ) → ℝ)
    (hJensen : CoarseJensenAtZero F)
    (hresidue : ∀ y ∈ S, ∃ z : D → ℤ,
      W y = (fun d => μ * (z d : ℝ)) ∧ F z ≤ cost y)
    (hprojection : ρ '' Z = convexHull ℝ S)
    (hattain : ∃ y ∈ S, W y = 0 ∧ cost y = F 0) :
    IsLeast ((fun x => cost (ρ x)) '' {x | x ∈ Z ∧ W (ρ x) = 0}) (F 0) := by
  constructor
  · obtain ⟨y, hy, hW, hc⟩ := hattain
    have hy' : y ∈ ρ '' Z := hprojection.symm ▸ subset_convexHull ℝ S hy
    obtain ⟨x, hx, rfl⟩ := hy'
    exact ⟨x, ⟨hx, hW⟩, hc⟩
  · rintro v ⟨x, ⟨hx, hW⟩, rfl⟩
    have hy : ρ x ∈ convexHull ℝ S := hprojection ▸ Set.mem_image_of_mem ρ hx
    exact convex_hull_cost_lower_bound S cost W μ hμ F hJensen hresidue (ρ x) hy hW

end MWIS.ExactValue

end
