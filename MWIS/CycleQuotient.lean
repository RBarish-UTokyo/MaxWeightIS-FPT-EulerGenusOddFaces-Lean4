module

public import MWIS.IncidenceSplit
public import MWIS.ClassMinimum
public import MWIS.KernelMidpoint
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Integral cycle classes modulo unsigned incidence

The homology group here is an actual quotient of the integral cycle subgroup.
Its representative and kernel properties follow from the quotient construction.
Every class has a nonnegative representative by adding an incidence vector with
constant positive coordinates.

Prepared 2026-10-23.
-/

@[expose] public section

namespace MWIS.CycleQuotient

variable {V E K : Type*} [AddCommGroup K]

/-- Unsigned incidence regarded as a homomorphism into the integral cycles. -/
def boundary (left right : E → V) (B : (E → ℤ) →+ K)
    (hBA : ∀ z, B (IncidenceSplit.incidence left right z) = 0) :
    (V → ℤ) →+ B.ker where
  toFun z := ⟨IncidenceSplit.incidence left right z, hBA z⟩
  map_zero' := by apply Subtype.ext; exact map_zero _
  map_add' x y := by apply Subtype.ext; exact map_add _ x y

/-- Integral cycles modulo the image of unsigned vertex incidence. -/
abbrev Homology (left right : E → V) (B : (E → ℤ) →+ K)
    (hBA : ∀ z, B (IncidenceSplit.incidence left right z) = 0) :=
  B.ker ⧸ (boundary left right B hBA).range

/-- The canonical class map from integral cycles to their incidence quotient. -/
def classMap (left right : E → V) (B : (E → ℤ) →+ K)
    (hBA : ∀ z, B (IncidenceSplit.incidence left right z) = 0) :
    B.ker →+ Homology left right B hBA :=
  QuotientAddGroup.mk' (boundary left right B hBA).range

theorem classMap_surjective (left right : E → V) (B : (E → ℤ) →+ K)
    (hBA : ∀ z, B (IncidenceSplit.incidence left right z) = 0) :
    Function.Surjective (classMap left right B hBA) :=
  QuotientAddGroup.mk'_surjective _

theorem classMap_eq_zero_iff (left right : E → V) (B : (E → ℤ) →+ K)
    (hBA : ∀ z, B (IncidenceSplit.incidence left right z) = 0) (x : B.ker) :
    classMap left right B hBA x = 0 ↔
      ∃ z, IncidenceSplit.incidence left right z = (x : E → ℤ) := by
  change QuotientAddGroup.mk' _ x = 0 ↔ _
  rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, congrArg Subtype.val hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, Subtype.ext hz⟩

theorem classMap_boundary (left right : E → V) (B : (E → ℤ) →+ K)
    (hBA : ∀ z, B (IncidenceSplit.incidence left right z) = 0) (z : V → ℤ) :
    classMap left right B hBA (boundary left right B hBA z) = 0 := by
  apply (classMap_eq_zero_iff left right B hBA _).mpr
  exact ⟨z, rfl⟩

/-- Two cycles represent the same class exactly when their difference is an
unsigned incidence vector. -/
theorem classMap_eq_iff (left right : E → V) (B : (E → ℤ) →+ K)
    (hBA : ∀ z, B (IncidenceSplit.incidence left right z) = 0) (x y : B.ker) :
    classMap left right B hBA x = classMap left right B hBA y ↔
      ∃ z, IncidenceSplit.incidence left right z = (x : E → ℤ) - y := by
  rw [← sub_eq_zero, ← map_sub]
  exact classMap_eq_zero_iff left right B hBA (x - y)

/-- The distinguished class of the all-ones edge vector. -/
def characteristicClass (left right : E → V) (B : (E → ℤ) →+ K)
    (hBA : ∀ z, B (IncidenceSplit.incidence left right z) = 0)
    (hB1 : B (fun _ => 1) = 0) : Homology left right B hBA :=
  classMap left right B hBA ⟨fun _ => 1, hB1⟩

/-- Twice the distinguished class vanishes, because the constant-two vector
is the incidence of the constant-one vertex vector. -/
theorem twice_characteristicClass (left right : E → V) (B : (E → ℤ) →+ K)
    (hBA : ∀ z, B (IncidenceSplit.incidence left right z) = 0)
    (hB1 : B (fun _ => 1) = 0) :
    2 • characteristicClass left right B hBA hB1 = 0 := by
  unfold characteristicClass
  rw [← map_nsmul]
  apply (classMap_eq_zero_iff left right B hBA _).mpr
  exact ⟨fun _ => 1, by ext e; simp [IncidenceSplit.incidence]⟩

/-- Every integral cycle class admits a nonnegative integral representative.
No connectedness, surface hypothesis, or nonempty edge set is required. -/
theorem nonnegative_representative [Fintype E]
    (left right : E → V) (B : (E → ℤ) →+ K)
    (hBA : ∀ z, B (IncidenceSplit.incidence left right z) = 0)
    (h : Homology left right B hBA) :
    ∃ y : B.ker, (∀ e, 0 ≤ (y : E → ℤ) e) ∧ classMap left right B hBA y = h := by
  obtain ⟨y, hy⟩ := classMap_surjective left right B hBA h
  let t : ℕ := ∑ e, ((y : E → ℤ) e).natAbs
  let z : B.ker := y + boundary left right B hBA (fun _ => (t : ℤ))
  refine ⟨z, ?_, ?_⟩
  · intro e
    have hb : ((y : E → ℤ) e).natAbs ≤ t :=
      Finset.single_le_sum (f := fun e => ((y : E → ℤ) e).natAbs)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ e)
    have hb' : (((y : E → ℤ) e).natAbs : ℤ) ≤ t := by exact_mod_cast hb
    have ha := Int.le_natAbs (a := -(y : E → ℤ) e)
    simp only [Int.natAbs_neg] at ha
    change 0 ≤ (y : E → ℤ) e + ((t : ℤ) + (t : ℤ))
    omega
  · dsimp only [z]
    rw [map_add, classMap_boundary, add_zero, hy]

/-- The minimum nonnegative rational edge cost exists in every actual quotient
class. The value function and its lower bounds are both constructed. -/
theorem exists_class_minima [Fintype E]
    (left right : E → V) (B : (E → ℤ) →+ K)
    (hBA : ∀ z, B (IncidenceSplit.incidence left right z) = 0)
    (c : E → ℚ) (hc : ∀ e, 0 ≤ c e) :
    ∃ F : Homology left right B hBA → ℝ,
      (∀ h, ∃ y : B.ker, (∀ e, 0 ≤ (y : E → ℤ) e) ∧
        classMap left right B hBA y = h ∧ ClassMinimum.realCost c y = F h) ∧
      (∀ h (y : B.ker), (∀ e, 0 ≤ (y : E → ℤ) e) →
        classMap left right B hBA y = h → F h ≤ ClassMinimum.realCost c y) := by
  let P (h : Homology left right B hBA) (y : E → ℤ) : Prop :=
    ∃ hy : B y = 0, (∀ e, 0 ≤ y e) ∧ classMap left right B hBA ⟨y, hy⟩ = h
  have hne (h : Homology left right B hBA) : ∃ y, P h y := by
    obtain ⟨y, hy, hclass⟩ := nonnegative_representative left right B hBA h
    exact ⟨y, y.property, hy, hclass⟩
  obtain ⟨F, hattain, hlower⟩ := ClassMinimum.exists_class_values c hc P hne
    (fun _ _ hy => hy.choose_spec.1)
  refine ⟨F, ?_, ?_⟩
  · intro h
    obtain ⟨y, ⟨hy, hpos, hclass⟩, hcost⟩ := hattain h
    exact ⟨⟨y, hy⟩, hpos, hclass, hcost⟩
  · intro h y hpos hclass
    exact hlower h y ⟨y.property, hpos, hclass⟩

/-- The actual incidence quotient has attained rational class minima and the
midpoint inequality. All splitting, kernel, and attainment properties are
proved from the quotient and the two endpoints of each edge. -/
theorem exists_midpoint_minima [Fintype E]
    (left right : E → V) (B : (E → ℤ) →+ K)
    (hBA : ∀ z, B (IncidenceSplit.incidence left right z) = 0)
    (c : E → ℚ) (hc : ∀ e, 0 ≤ c e) :
    ∃ F : Homology left right B hBA → ℝ,
      (∀ h, ∃ y : B.ker, KernelMidpoint.Nonnegative y ∧
        classMap left right B hBA y = h ∧ ClassMinimum.realCost c y = F h) ∧
      (∀ h (y : B.ker), KernelMidpoint.Nonnegative y →
        classMap left right B hBA y = h → F h ≤ ClassMinimum.realCost c y) ∧
      (∀ h₀ z d, 2 * F (h₀ + 2 • z) ≤
        F (h₀ + 2 • (z - d)) + F (h₀ + 2 • (z + d))) := by
  apply KernelMidpoint.exists_midpoint_class_values B (classMap left right B hBA) c hc
    (nonnegative_representative left right B hBA)
  apply IncidenceSplit.split_cycle_class left right B hBA
    (classMap left right B hBA)
  · exact classMap_boundary left right B hBA
  · exact classMap_surjective left right B hBA
  · intro x hx
    obtain ⟨z, hz⟩ := (classMap_eq_zero_iff left right B hBA x).mp hx
    exact ⟨z, Subtype.ext hz⟩

end MWIS.CycleQuotient

end
