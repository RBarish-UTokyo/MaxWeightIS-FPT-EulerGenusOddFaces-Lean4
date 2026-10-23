module

public import MWIS.Midpoint
public import Mathlib.LinearAlgebra.Matrix.Integer
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring

/-!
# Attainment of rational cost minima in integral cycle classes

A finite rational cost vector has a common positive denominator. Consequently,
its nonnegative values on integer vectors have a least value on any nonempty
feasible set. A positive vector in the joint kernel supplies nonnegative
representatives of every represented cycle class.

Prepared 2026-10-23.
-/

@[expose] public section

namespace MWIS.ClassMinimum

open scoped BigOperators

/-- Rational linear cost of an integer vector. -/
def rationalCost {E : Type*} [Fintype E] (c : E → ℚ) (y : E → ℤ) : ℚ :=
  ∑ e, c e * (y e : ℚ)

/-- The rational objective viewed as an additive real-valued map. -/
def realCost {E : Type*} [Fintype E] (c : E → ℚ) : (E → ℤ) →+ ℝ where
  toFun y := (rationalCost c y : ℝ)
  map_zero' := by
    simp only [rationalCost, Pi.zero_apply, Int.cast_zero, mul_zero,
      Finset.sum_const_zero, Rat.cast_zero]
  map_add' x y := by
    letI : CharZero ℝ := IsStrictOrderedRing.toCharZero
    simp only [rationalCost, Pi.add_apply, Int.cast_add, mul_add,
      Finset.sum_add_distrib, Rat.cast_add]

/-- All coefficients of a finite rational objective have a common positive
integer denominator. -/
theorem common_denominator {E : Type*} [Fintype E] (c : E → ℚ) :
    ∃ D : ℕ, 0 < D ∧ ∃ a : E → ℤ, ∀ e, (a e : ℚ) = D * c e := by
  let A : Matrix Unit E ℚ := fun _ e => c e
  refine ⟨A.den, Nat.pos_of_ne_zero (Matrix.den_ne_zero A),
    fun e => A.num () e, ?_⟩
  intro e
  have h := Matrix.num_div_den A () e
  have hD : (A.den : ℚ) ≠ 0 := by exact_mod_cast Matrix.den_ne_zero A
  have he : (A.num () e : ℚ) = c e * A.den := (div_eq_iff hD).mp h
  simpa [mul_comm] using he

/-- Nonnegative rational costs, evaluated on nonnegative integral vectors,
become natural numbers after multiplication by one fixed denominator. -/
theorem scaled_cost_natural {E : Type*} [Fintype E] (c : E → ℚ)
    (hc : ∀ e, 0 ≤ c e) :
    ∃ D : ℕ, 0 < D ∧ ∀ y : E → ℤ, (∀ e, 0 ≤ y e) →
      ∃ n : ℕ, (n : ℚ) = D * rationalCost c y := by
  obtain ⟨D, hD, a, ha⟩ := common_denominator c
  refine ⟨D, hD, ?_⟩
  intro y hy
  let k : ℤ := ∑ e, a e * y e
  have hk : (k : ℚ) = D * rationalCost c y := by
    simp only [k, Int.cast_sum, Int.cast_mul, rationalCost, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    rw [ha]
    ring
  have hnonneg : 0 ≤ k := by
    have hcost : 0 ≤ rationalCost c y := by
      apply Finset.sum_nonneg
      intro e _
      exact mul_nonneg (hc e) (by exact_mod_cast hy e)
    have : (0 : ℚ) ≤ k := by rw [hk]; positivity
    exact_mod_cast this
  refine ⟨k.toNat, ?_⟩
  calc
    (k.toNat : ℚ) = (k : ℚ) := by exact_mod_cast Int.toNat_of_nonneg hnonneg
    _ = _ := hk

/-- Every nonempty family of nonnegative integer vectors has an attained
minimum for any fixed nonnegative rational linear objective. -/
theorem exists_minimum {E : Type*} [Fintype E]
    (c : E → ℚ) (hc : ∀ e, 0 ≤ c e) (P : (E → ℤ) → Prop)
    (hne : ∃ y, P y) (hP : ∀ y, P y → ∀ e, 0 ≤ y e) :
    ∃ y, P y ∧ ∀ z, P z → rationalCost c y ≤ rationalCost c z := by
  classical
  obtain ⟨D, hD, hscale⟩ := scaled_cost_natural c hc
  have hex : ∃ n : ℕ, ∃ y, P y ∧ (n : ℚ) = D * rationalCost c y := by
    obtain ⟨y, hy⟩ := hne
    obtain ⟨n, hn⟩ := hscale y (hP y hy)
    exact ⟨n, y, hy, hn⟩
  obtain ⟨y, hy, heq⟩ := Nat.find_spec hex
  refine ⟨y, hy, ?_⟩
  intro z hz
  obtain ⟨n, hn⟩ := hscale z (hP z hz)
  have hmin : Nat.find hex ≤ n := Nat.find_min' hex ⟨z, hz, hn⟩
  have hmin' : (Nat.find hex : ℚ) ≤ n := by exact_mod_cast hmin
  rw [heq, hn] at hmin'
  exact (mul_le_mul_iff_right₀ (show (0 : ℚ) < D by exact_mod_cast hD)).mp hmin'

/-- A positive joint-kernel vector turns any cycle representative into a
nonnegative representative of the same class. -/
theorem nonnegative_representative {E K H : Type*} [Fintype E]
    [AddCommGroup K] [AddCommGroup H]
    (B : (E → ℤ) →+ K) (Q : (E → ℤ) →+ H)
    (s : E → ℤ) (hBs : B s = 0) (hQs : Q s = 0) (hs : ∀ e, 1 ≤ s e)
    (y : E → ℤ) (hy : B y = 0) :
    ∃ z, MWIS.Midpoint.Feasible B z ∧ Q z = Q y := by
  let t : ℕ := ∑ e, (y e).natAbs
  have hbound (e : E) : -(y e) ≤ (t : ℤ) := by
    have hle : (y e).natAbs ≤ t :=
      Finset.single_le_sum (f := fun e => (y e).natAbs)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ e)
    have hle' : ((y e).natAbs : ℤ) ≤ t := by exact_mod_cast hle
    have habs : -(y e) ≤ ((y e).natAbs : ℤ) := by
      simpa using (Int.le_natAbs (a := -y e))
    exact habs.trans hle'
  refine ⟨y + t • s, ⟨?_, ?_⟩, ?_⟩
  · rw [map_add, map_nsmul, hy, hBs, nsmul_zero, add_zero]
  · intro e
    change 0 ≤ y e + (t • s) e
    simp only [Pi.smul_apply, nsmul_eq_mul]
    have hmul : (t : ℤ) ≤ (t : ℤ) * s e := by
      simpa using mul_le_mul_of_nonneg_left (hs e) (Int.natCast_nonneg t)
    linarith [hbound e]
  · rw [map_add, map_nsmul, hQs, nsmul_zero, add_zero]

/-- Every label represented by an integral cycle is represented by a feasible
cycle when twice the all-ones vector lies in the joint kernel. -/
theorem nonnegative_representative_of_twice_ones {E K H : Type*} [Fintype E]
    [AddCommGroup K] [AddCommGroup H]
    (B : (E → ℤ) →+ K) (Q : (E → ℤ) →+ H)
    (hB : B (fun _ => 2) = 0) (hQ : Q (fun _ => 2) = 0)
    (h : H) (hrep : ∃ y, B y = 0 ∧ Q y = h) :
    ∃ y, MWIS.Midpoint.Feasible B y ∧ Q y = h := by
  obtain ⟨y, hBy, hQy⟩ := hrep
  obtain ⟨z, hz, heq⟩ := nonnegative_representative B Q (fun _ => 2) hB hQ
    (fun _ => by norm_num) y hBy
  exact ⟨z, hz, heq.trans hQy⟩

/-- The class objective attains a minimum whenever the class has an integral
representative and a positive joint-kernel shift is available. -/
theorem exists_class_minimum {E K H : Type*} [Fintype E]
    [AddCommGroup K] [AddCommGroup H]
    (B : (E → ℤ) →+ K) (Q : (E → ℤ) →+ H)
    (c : E → ℚ) (hc : ∀ e, 0 ≤ c e)
    (s : E → ℤ) (hBs : B s = 0) (hQs : Q s = 0) (hs : ∀ e, 1 ≤ s e)
    (h : H) (hrep : ∃ y, B y = 0 ∧ Q y = h) :
    ∃ y, MWIS.Midpoint.Feasible B y ∧ Q y = h ∧
      ∀ z, MWIS.Midpoint.Feasible B z → Q z = h → realCost c y ≤ realCost c z := by
  obtain ⟨y, hBy, hQy⟩ := hrep
  obtain ⟨z, hz, hQz⟩ := nonnegative_representative B Q s hBs hQs hs y hBy
  obtain ⟨v, hv, hmin⟩ := exists_minimum c hc
    (fun x => MWIS.Midpoint.Feasible B x ∧ Q x = h)
    ⟨z, hz, hQz.trans hQy⟩ (fun _ hx => hx.1.2)
  refine ⟨v, hv.1, hv.2, ?_⟩
  intro x hx hQx
  change (rationalCost c v : ℝ) ≤ (rationalCost c x : ℝ)
  exact_mod_cast hmin x ⟨hx, hQx⟩

/-- Attained class values for any family of nonnegative integer feasible sets.
The class predicate may use labels defined only on cycles or a quotient group;
no extension of the label map to the ambient lattice is required. -/
theorem exists_class_values {E H : Type*} [Fintype E]
    (c : E → ℚ) (hc : ∀ e, 0 ≤ c e)
    (P : H → (E → ℤ) → Prop)
    (hne : ∀ h, ∃ y, P h y)
    (hP : ∀ h y, P h y → ∀ e, 0 ≤ y e) :
    ∃ F : H → ℝ,
      (∀ h, ∃ y, P h y ∧ realCost c y = F h) ∧
      (∀ h y, P h y → F h ≤ realCost c y) := by
  classical
  have hex (h : H) := exists_minimum c hc (P h) (hne h) (hP h)
  choose y hy hmin using hex
  refine ⟨fun h => realCost c (y h), ?_, ?_⟩
  · intro h
    exact ⟨y h, hy h, rfl⟩
  · intro h z hz
    change (rationalCost c (y h) : ℝ) ≤ (rationalCost c z : ℝ)
    exact_mod_cast hmin h z hz

end MWIS.ClassMinimum

end
