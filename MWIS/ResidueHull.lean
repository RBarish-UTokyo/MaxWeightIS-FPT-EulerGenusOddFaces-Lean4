module

public import MWIS.ResidueJensen
public import MWIS.RealCoordinates
public import MWIS.KernelMidpoint

/-!
# Exact minimum on the finite-residue convex hull

The residue description is derived from an integral class-group decomposition.
The real free-coordinate map is the explicit extension of its integer
coefficients. Midpoint convexity and attained class minima imply exactness
of the zero-coordinate slice of the resulting convex hull.

Prepared 2026-10-23.
-/

@[expose] public section

namespace MWIS.ResidueHull

open ResidueJensen RealCoordinates

variable {E K H : Type*} [Fintype E] [DecidableEq E]
    [AddCommGroup K] [AddCommGroup H]

/-- Real edge vectors obtained from nonnegative integral cycles having the
distinguished finite residue. -/
def points {r : ℕ} (B : (E → ℤ) →+ K) (Q : B.ker →+ H)
    (e : H ≃+ (Fin r → ℤ) × ZMod 2) (κ : H) : Set (E → ℝ) :=
  {u | ∃ y : B.ker, KernelMidpoint.Nonnegative y ∧
    residueMap e (Q y) = residueMap e κ ∧ castVector y.val = u}

/-- The residue convex hull has the exact distinguished-class minimum after
the free-coordinate equations are imposed. The residue and Jensen conditions
are consequences of the stated class decomposition and midpoint inequality. -/
theorem exact_minimum {r : ℕ} (B : (E → ℤ) →+ K) (Q : B.ker →+ H)
    (e : H ≃+ (Fin r → ℤ) × ZMod 2) (κ : H) (hκ : e κ = (0, 1))
    (W : (E → ℤ) →+ (Fin r → ℤ))
    (hW : ∀ y : B.ker, W y.val = (e (Q y)).1)
    (c : E → ℚ) (F : H → ℝ)
    (hattain : ∀ h, ∃ y : B.ker, KernelMidpoint.Nonnegative y ∧ Q y = h ∧
      ClassMinimum.realCost c y.val = F h)
    (hlower : ∀ h (y : B.ker), KernelMidpoint.Nonnegative y → Q y = h →
      F h ≤ ClassMinimum.realCost c y.val)
    (hmid : ∀ h₀ z d, 2 * F (h₀ + 2 • z) ≤
      F (h₀ + 2 • (z - d)) + F (h₀ + 2 • (z + d))) :
    IsLeast ((cost c) '' {u | u ∈ convexHull ℝ (points B Q e κ) ∧ extension W u = 0})
      (F κ) := by
  let f : (Fin r → ℤ) → ℝ := fun z => F (κ + GroupSize.modulus r • freeLift e z)
  have hf0 : f 0 = F κ := by simp [f]
  rw [← hf0]
  apply ExactValue.exact_minimum_on_slice (points B Q e κ) (cost c) (extension W)
    (GroupSize.modulus r : ℝ) (by exact_mod_cast GroupSize.modulus_pos r) f
    (class_coarse_jensen e κ F hmid)
  · rintro u ⟨y, hy, hres, rfl⟩
    obtain ⟨z, hz⟩ := (residue_fiber e κ hκ (Q y)).mp hres
    refine ⟨z, ?_, ?_⟩
    · rw [extension_cast, hW, hz]
      ext d
      simp [castVector, hκ, freeLift, nsmul_eq_mul]
    · rw [cost_cast]
      exact hlower _ y hy hz
  · obtain ⟨y, hy, hQy, hcost⟩ := hattain κ
    refine ⟨castVector y.val, ⟨y, hy, by rw [hQy], rfl⟩, ?_, ?_⟩
    · rw [extension_cast, hW, hQy, hκ]
      ext d
      simp [castVector]
    · rw [cost_cast, hcost, hf0]

end MWIS.ResidueHull

end
