module

public import MWIS.CycleQuotient
public import MWIS.Slack
public import MWIS.CoreBridge

/-!
# Independent-set optimum and the actual integral class minimum

The distinguished class of the integral incidence quotient consists exactly
of the integer slack vectors. Its attained minimum therefore determines a
maximum-weight independent set. The same value function satisfies the midpoint
inequality proved by coordinate rounding.

Prepared 2026-10-23.
-/

@[expose] public section

namespace MWIS.CoreOptimum

open CycleQuotient

variable {V E K : Type*} [AddCommGroup K]

/-- The slack of an integer vertex vector, regarded as an integral cycle. -/
def slackCycle (left right : E → V) (B : (E → ℤ) →+ K)
    (hBA : ∀ z, B (IncidenceSplit.incidence left right z) = 0)
    (hB1 : B (fun _ => 1) = 0) (x : V → ℤ) : B.ker :=
  ⟨(fun _ => 1) - IncidenceSplit.incidence left right x, by
    change B ((fun _ => 1) - IncidenceSplit.incidence left right x) = 0
    rw [map_sub, hB1, hBA, sub_self]⟩

theorem slackCycle_apply (left right : E → V) (B : (E → ℤ) →+ K)
    (hBA : ∀ z, B (IncidenceSplit.incidence left right z) = 0)
    (hB1 : B (fun _ => 1) = 0) (x : V → ℤ) (e : E) :
    (slackCycle left right B hBA hB1 x).val e = Slack.slack left right x e := by
  simp [slackCycle, IncidenceSplit.incidence, Slack.slack]
  omega

theorem slackCycle_class (left right : E → V) (B : (E → ℤ) →+ K)
    (hBA : ∀ z, B (IncidenceSplit.incidence left right z) = 0)
    (hB1 : B (fun _ => 1) = 0) (x : V → ℤ) :
    classMap left right B hBA (slackCycle left right B hBA hB1 x) =
      characteristicClass left right B hBA hB1 := by
  apply (classMap_eq_iff left right B hBA _ _).mpr
  refine ⟨-x, ?_⟩
  rw [map_neg]
  change -IncidenceSplit.incidence left right x =
    ((fun _ => 1) - IncidenceSplit.incidence left right x) - (fun _ => 1)
  abel

/-- Equality with the distinguished quotient class is precisely the integral
slack condition, with no boundedness hypothesis on the slack or vertex vector. -/
theorem characteristic_fiber (left right : E → V) (B : (E → ℤ) →+ K)
    (hBA : ∀ z, B (IncidenceSplit.incidence left right z) = 0)
    (hB1 : B (fun _ => 1) = 0) (y : B.ker) :
    classMap left right B hBA y = characteristicClass left right B hBA hB1 ↔
      ∃ x, slackCycle left right B hBA hB1 x = y := by
  constructor
  · intro hy
    obtain ⟨z, hz⟩ := (classMap_eq_iff left right B hBA y ⟨fun _ => 1, hB1⟩).mp hy
    refine ⟨-z, Subtype.ext ?_⟩
    change (fun _ => 1) - IncidenceSplit.incidence left right (-z) = y.val
    rw [map_neg, hz]
    abel
  · rintro ⟨x, rfl⟩
    exact slackCycle_class left right B hBA hB1 x

theorem slackCycle_nonnegative (left right : E → V) (B : (E → ℤ) →+ K)
    (hBA : ∀ z, B (IncidenceSplit.incidence left right z) = 0)
    (hB1 : B (fun _ => 1) = 0) (x : V → ℤ) :
    KernelMidpoint.Nonnegative (slackCycle left right B hBA hB1 x) ↔
      Slack.Feasible left right x := by
  simp only [KernelMidpoint.Nonnegative, slackCycle_apply]
  exact (Slack.feasible_iff_slack_nonnegative left right x).symm

theorem slackCycle_cost [Fintype E]
    (left right : E → V) (B : (E → ℤ) →+ K)
    (hBA : ∀ z, B (IncidenceSplit.incidence left right z) = 0)
    (hB1 : B (fun _ => 1) = 0) (c : E → ℚ) (x : V → ℤ) :
    ClassMinimum.realCost c (slackCycle left right B hBA hB1 x).val =
      (Slack.slackCost left right c x : ℝ) := by
  simp only [ClassMinimum.realCost, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    ClassMinimum.rationalCost, slackCycle_apply, Slack.slackCost]

/-- The distinguished class minimum is the total edge cost minus the maximum
independent-set weight. This statement uses the actual quotient, and all minima,
representatives and midpoint inequalities are constructed. -/
theorem exists_midpoint_optimum [Fintype V] [Fintype E] [DecidableEq V]
    (left right : E → V) (B : (E → ℤ) →+ K)
    (hBA : ∀ z, B (IncidenceSplit.incidence left right z) = 0)
    (hB1 : B (fun _ => 1) = 0) (c : E → ℚ) (hc : ∀ e, 0 ≤ c e) :
    ∃ (F : Homology left right B hBA → ℝ) (I : Finset V),
      Slack.Independent left right I ∧
      (∀ J : Finset V, Slack.Independent left right J →
        Slack.setWeight left right c J ≤ Slack.setWeight left right c I) ∧
      (Slack.setWeight left right c I : ℝ) = (Slack.totalCost c : ℝ) -
        F (characteristicClass left right B hBA hB1) ∧
      (∀ h, ∃ y : B.ker, KernelMidpoint.Nonnegative y ∧
        classMap left right B hBA y = h ∧ ClassMinimum.realCost c y = F h) ∧
      (∀ h (y : B.ker), KernelMidpoint.Nonnegative y →
        classMap left right B hBA y = h → F h ≤ ClassMinimum.realCost c y) ∧
      (∀ h₀ z d, 2 * F (h₀ + 2 • z) ≤
        F (h₀ + 2 • (z - d)) + F (h₀ + 2 • (z + d))) := by
  obtain ⟨F, hattain, hlower, hmid⟩ := exists_midpoint_minima left right B hBA c hc
  obtain ⟨I, hI, hfeas, _, hmax, hmin, hvalue⟩ :=
    Slack.integer_slack_optimum left right c hc
  have hF : F (characteristicClass left right B hBA hB1) =
      (Slack.slackCost left right c (Slack.indicator I) : ℝ) := by
    apply le_antisymm
    · have h := hlower _ (slackCycle left right B hBA hB1 (Slack.indicator I))
        ((slackCycle_nonnegative left right B hBA hB1 _).mpr hfeas)
        (slackCycle_class left right B hBA hB1 _)
      simpa only [slackCycle_cost] using h
    · obtain ⟨y, hy, hclass, hcost⟩ := hattain (characteristicClass left right B hBA hB1)
      obtain ⟨x, rfl⟩ := (characteristic_fiber left right B hBA hB1 y).mp hclass
      have h := hmin x ((slackCycle_nonnegative left right B hBA hB1 x).mp hy)
      rw [slackCycle_cost] at hcost
      rw [← hcost]
      exact_mod_cast h
  refine ⟨F, I, hI, hmax, ?_, hattain, hlower, hmid⟩
  rw [hF]
  exact_mod_cast hvalue

end MWIS.CoreOptimum

end
