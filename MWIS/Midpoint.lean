module

public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith

/-!
# Midpoint convexity from conformal splitting

The algebraic passage from exact conformal splitting to midpoint convexity of
the minimum cost function. The splitting property and attainment of the class
minima are explicit hypotheses; their surface construction is not asserted.
-/

@[expose] public section

namespace MWIS.Midpoint

/-- Nonnegative integer vectors satisfying the cycle equations. -/
def Feasible {E K : Type*} [AddCommGroup K]
    (B : (E → ℤ) →+ K) (y : E → ℤ) : Prop :=
  B y = 0 ∧ ∀ e, 0 ≤ y e

/-- A conformal summand lies between zero and the original vector in every
coordinate, with either sign allowed for the original vector. -/
def Conformal {E : Type*} (a d : E → ℤ) : Prop :=
  ∀ e, min 0 (d e) ≤ a e ∧ a e ≤ max 0 (d e)

theorem feasible_intermediates {E K : Type*} [AddCommGroup K]
    (B : (E → ℤ) →+ K) (ym yp a : E → ℤ)
    (hm : Feasible B ym) (hp : Feasible B yp)
    (ha : B a = 0) (hconf : Conformal a (yp - ym)) :
    Feasible B (ym + a) ∧ Feasible B (yp - a) := by
  refine ⟨⟨by rw [map_add, hm.1, ha, add_zero], ?_⟩,
    ⟨by rw [map_sub, hp.1, ha, sub_zero], ?_⟩⟩
  · intro e
    have hb := hconf e
    have hm' := hm.2 e
    have hp' := hp.2 e
    simp only [Pi.sub_apply] at hb
    change 0 ≤ ym e + a e
    by_cases hd : 0 ≤ yp e - ym e
    · rw [min_eq_left hd] at hb
      omega
    · rw [min_eq_right (by omega)] at hb
      omega
  · intro e
    have hb := hconf e
    have hm' := hm.2 e
    have hp' := hp.2 e
    simp only [Pi.sub_apply] at hb
    change 0 ≤ yp e - a e
    by_cases hd : 0 ≤ yp e - ym e
    · rw [max_eq_right hd] at hb
      omega
    · rw [max_eq_left (by omega)] at hb
      omega

/-- Exact conformal splitting of every cycle with class `4 • d` gives midpoint
convexity on each coset of twice the class group. `Q` is an ambient label map
whose restriction to cycles represents their classes. -/
theorem midpoint_from_conformal_splitting {E K H : Type*}
    [AddCommGroup K] [AddCommGroup H]
    (B : (E → ℤ) →+ K) (Q : (E → ℤ) →+ H)
    (cost : (E → ℤ) →+ ℝ) (F : H → ℝ)
    (hattain : ∀ h, ∃ y, Feasible B y ∧ Q y = h ∧ cost y = F h)
    (hlower : ∀ h y, Feasible B y → Q y = h → F h ≤ cost y)
    (hsplit : ∀ v d, B v = 0 → Q v = 4 • d →
      ∃ a, B a = 0 ∧ Q a = 2 • d ∧ Conformal a v)
    (h₀ z d : H) :
    2 * F (h₀ + 2 • z) ≤
      F (h₀ + 2 • (z - d)) + F (h₀ + 2 • (z + d)) := by
  obtain ⟨ym, hm, hQm, hcm⟩ := hattain (h₀ + 2 • (z - d))
  obtain ⟨yp, hp, hQp, hcp⟩ := hattain (h₀ + 2 • (z + d))
  have hB : B (yp - ym) = 0 := by rw [map_sub, hp.1, hm.1, sub_self]
  have hQ : Q (yp - ym) = 4 • d := by
    rw [map_sub, hQp, hQm]
    abel
  obtain ⟨a, hBa, hQa, hconf⟩ := hsplit (yp - ym) d hB hQ
  obtain ⟨hfirst, hsecond⟩ := feasible_intermediates B ym yp a hm hp hBa hconf
  have hQfirst : Q (ym + a) = h₀ + 2 • z := by
    rw [map_add, hQm, hQa]
    abel
  have hQsecond : Q (yp - a) = h₀ + 2 • z := by
    rw [map_sub, hQp, hQa]
    abel
  have hfirstCost := hlower _ _ hfirst hQfirst
  have hsecondCost := hlower _ _ hsecond hQsecond
  rw [map_add, hcm] at hfirstCost
  rw [map_sub, hcp] at hsecondCost
  linarith

end MWIS.Midpoint

end
