module

public import MWIS.ClassMinimum
public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Midpoint convexity for labels defined on the cycle lattice

The label homomorphism is defined on the integer kernel of the boundary map.
No ambient extension of homology coordinates is required. Rational nonnegative
edge costs attain their minima, and conformal splitting gives midpoint
convexity of the resulting class-value function.

Prepared 2026-10-23.
-/

@[expose] public section

namespace MWIS.KernelMidpoint

/-- A cycle is nonnegative when each of its integral coordinates is nonnegative. -/
def Nonnegative {E K : Type*} [AddCommGroup K]
    {B : (E → ℤ) →+ K} (y : B.ker) : Prop := ∀ e, 0 ≤ y.val e

/-- The two complementary conformal moves between nonnegative cycles remain
nonnegative. -/
theorem nonnegative_intermediates {E K : Type*} [AddCommGroup K]
    (B : (E → ℤ) →+ K) (ym yp a : B.ker)
    (hm : Nonnegative ym) (hp : Nonnegative yp)
    (ha : MWIS.Midpoint.Conformal a.val (yp.val - ym.val)) :
    Nonnegative (ym + a) ∧ Nonnegative (yp - a) := by
  have h := MWIS.Midpoint.feasible_intermediates B ym.val yp.val a.val
    ⟨ym.property, hm⟩ ⟨yp.property, hp⟩ a.property ha
  exact ⟨h.1.2, h.2.2⟩

/-- Conformal half-splitting implies midpoint convexity of class minima when
labels are homomorphisms on the integer cycle lattice itself. -/
theorem midpoint_from_conformal_splitting {E K H : Type*}
    [AddCommGroup K] [AddCommGroup H]
    (B : (E → ℤ) →+ K) (Q : B.ker →+ H)
    (cost : (E → ℤ) →+ ℝ) (F : H → ℝ)
    (hattain : ∀ h, ∃ y : B.ker, Nonnegative y ∧ Q y = h ∧ cost y.val = F h)
    (hlower : ∀ h (y : B.ker), Nonnegative y → Q y = h → F h ≤ cost y.val)
    (hsplit : ∀ (v : B.ker) d, Q v = 4 • d →
      ∃ a : B.ker, Q a = 2 • d ∧ MWIS.Midpoint.Conformal a.val v.val)
    (h₀ z d : H) :
    2 * F (h₀ + 2 • z) ≤
      F (h₀ + 2 • (z - d)) + F (h₀ + 2 • (z + d)) := by
  obtain ⟨ym, hm, hQm, hcm⟩ := hattain (h₀ + 2 • (z - d))
  obtain ⟨yp, hp, hQp, hcp⟩ := hattain (h₀ + 2 • (z + d))
  have hQ : Q (yp - ym) = 4 • d := by
    rw [map_sub, hQp, hQm]
    abel
  obtain ⟨a, hQa, hconf⟩ := hsplit (yp - ym) d hQ
  obtain ⟨hfirst, hsecond⟩ := nonnegative_intermediates B ym yp a hm hp hconf
  have hQfirst : Q (ym + a) = h₀ + 2 • z := by
    rw [map_add, hQm, hQa]
    abel
  have hQsecond : Q (yp - a) = h₀ + 2 • z := by
    rw [map_sub, hQp, hQa]
    abel
  have hfirstCost := hlower _ _ hfirst hQfirst
  have hsecondCost := hlower _ _ hsecond hQsecond
  change F (h₀ + 2 • z) ≤ cost (ym.val + a.val) at hfirstCost
  change F (h₀ + 2 • z) ≤ cost (yp.val - a.val) at hsecondCost
  rw [map_add, hcm] at hfirstCost
  rw [map_sub, hcp] at hsecondCost
  linarith

/-- Rational nonnegative costs give a class-value function with attained minima
on every class that has a nonnegative representative. -/
theorem exists_class_values {E K H : Type*} [Fintype E]
    [AddCommGroup K] [AddCommGroup H]
    (B : (E → ℤ) →+ K) (Q : B.ker →+ H)
    (c : E → ℚ) (hc : ∀ e, 0 ≤ c e)
    (hne : ∀ h, ∃ y : B.ker, Nonnegative y ∧ Q y = h) :
    ∃ F : H → ℝ,
      (∀ h, ∃ y : B.ker, Nonnegative y ∧ Q y = h ∧
        MWIS.ClassMinimum.realCost c y.val = F h) ∧
      (∀ h (y : B.ker), Nonnegative y → Q y = h →
        F h ≤ MWIS.ClassMinimum.realCost c y.val) := by
  let P (h : H) (y : E → ℤ) :=
    ∃ hy : B y = 0, (∀ e, 0 ≤ y e) ∧ Q ⟨y, hy⟩ = h
  have hPne : ∀ h, ∃ y, P h y := by
    intro h
    obtain ⟨y, hy, hQ⟩ := hne h
    exact ⟨y.val, y.property, hy, hQ⟩
  obtain ⟨F, hattain, hlower⟩ := MWIS.ClassMinimum.exists_class_values c hc P hPne
    (fun _ _ hy => hy.choose_spec.1)
  refine ⟨F, ?_, ?_⟩
  · intro h
    obtain ⟨y, ⟨hy, hnonneg, hQ⟩, hcost⟩ := hattain h
    exact ⟨⟨y, hy⟩, hnonneg, hQ, hcost⟩
  · intro h y hy hQ
    exact hlower h y.val ⟨y.property, hy, hQ⟩

/-- Class minima exist and satisfy midpoint convexity once every class has a
nonnegative representative and conformal half-splitting holds in the cycle lattice. -/
theorem exists_midpoint_class_values {E K H : Type*} [Fintype E]
    [AddCommGroup K] [AddCommGroup H]
    (B : (E → ℤ) →+ K) (Q : B.ker →+ H)
    (c : E → ℚ) (hc : ∀ e, 0 ≤ c e)
    (hne : ∀ h, ∃ y : B.ker, Nonnegative y ∧ Q y = h)
    (hsplit : ∀ (v : B.ker) d, Q v = 4 • d →
      ∃ a : B.ker, Q a = 2 • d ∧ MWIS.Midpoint.Conformal a.val v.val) :
    ∃ F : H → ℝ,
      (∀ h, ∃ y : B.ker, Nonnegative y ∧ Q y = h ∧
        MWIS.ClassMinimum.realCost c y.val = F h) ∧
      (∀ h (y : B.ker), Nonnegative y → Q y = h →
        F h ≤ MWIS.ClassMinimum.realCost c y.val) ∧
      (∀ h₀ z d, 2 * F (h₀ + 2 • z) ≤
        F (h₀ + 2 • (z - d)) + F (h₀ + 2 • (z + d))) := by
  obtain ⟨F, hattain, hlower⟩ := exists_class_values B Q c hc hne
  exact ⟨F, hattain, hlower,
    midpoint_from_conformal_splitting B Q (MWIS.ClassMinimum.realCost c) F
      hattain hlower hsplit⟩

end MWIS.KernelMidpoint

end
