module

public import MWIS.CoarseJensen
public import MWIS.ExactValue

/-!
# Coarse Jensen applied to the exact-value relaxation

The coarse Jensen hypothesis in the convex optimization bridge is derived
from midpoint convexity, including rank zero. The remaining residue,
projection and attainment hypotheses are explicit.
-/

@[expose] public section

namespace MWIS.CoreBridge

theorem coarse_jensen_at_zero (r k : ℕ) (hk : 2 * r ≤ k)
    (f : (Fin r → ℤ) → ℝ) (hf : CoarseJensen.MidpointConvex f) :
    ExactValue.CoarseJensenAtZero (fun z => f (k • z)) := by
  intro ι _ weights z hnonneg hsum hzero
  by_cases hr : r = 0
  · subst r
    have hz (i : ι) : z i = 0 := by
      funext a
      exact Fin.elim0 a
    simp only [hz, smul_zero, ← Finset.sum_mul, hsum, one_mul]
    exact le_rfl
  · have h := CoarseJensen.coarse_jensen (by omega : 1 ≤ r) f hf k hk
      z weights hnonneg hsum 0 (fun a => by simpa using (hzero a).symm)
    simpa only [smul_zero] using h

/-- Exactness of a residue-hull extension after imposing zero free coordinates,
with the coarse Jensen inequality proved from midpoint convexity. -/
theorem exact_value_of_midpoint_extension {E X : Type*}
    [AddCommGroup E] [Module ℝ E]
    (r k : ℕ) (hk : 2 * r ≤ k)
    (f : (Fin r → ℤ) → ℝ) (hf : CoarseJensen.MidpointConvex f)
    (S : Set E) (Z : Set X) (ρ : X → E)
    (cost : E →ₗ[ℝ] ℝ) (W : E →ₗ[ℝ] (Fin r → ℝ))
    (μ : ℝ) (hμ : 0 < μ)
    (hresidue : ∀ y ∈ S, ∃ z : Fin r → ℤ,
      W y = (fun d => μ * (z d : ℝ)) ∧ f (k • z) ≤ cost y)
    (hprojection : ρ '' Z = convexHull ℝ S)
    (hattain : ∃ y ∈ S, W y = 0 ∧ cost y = f 0) :
    IsLeast ((fun x => cost (ρ x)) '' {x | x ∈ Z ∧ W (ρ x) = 0}) (f 0) := by
  simpa only [smul_zero] using ExactValue.exact_value_of_extension
    S Z ρ cost W μ hμ (fun z => f (k • z))
    (coarse_jensen_at_zero r k hk f hf) hresidue hprojection
    (by simpa only [smul_zero] using hattain)

end MWIS.CoreBridge

end
