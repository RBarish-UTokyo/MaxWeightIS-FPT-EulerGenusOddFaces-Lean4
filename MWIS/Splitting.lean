module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Data.Int.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Exact splitting by parity rounding

This module proves the finite algebraic step in the exact splitting lemma.
The topological construction of the boundary matrix is a separate obligation.
The columns of that matrix describe relative two-cycle boundaries. Its rows
have absolute sum at most two, reflecting the two sides of each circle.
-/

@[expose] public section

namespace MWIS.Splitting

/-- The integer boundary vector associated with column coefficients `z`. -/
def boundary {S R : Type*} [Fintype R] (T : S → R → ℤ) (z : R → ℤ) : S → ℤ :=
  fun i => ∑ j, T i j * z j

/-- The cokernel has torsion exponent at most two: whenever a positive
multiple of a class lies in the image, its double already lies in the image.
This formulation avoids choosing representatives of the quotient group. -/
def TwoTorsionCokernel {S H : Type*} [AddCommGroup H] (Q : (S → ℤ) →+ H) : Prop :=
  ∀ (h : H) (n : ℕ), 0 < n → (∃ x, Q x = n • h) → ∃ x, Q x = 2 • h

/-- Rounding an integer to the congruent representative in `{-1, 0}`. -/
def parityRepresentative (z : ℤ) : ℤ := -(z % 2)

/-- The rounded coefficient is either negative one or zero. -/
theorem parityRepresentative_values (z : ℤ) :
    parityRepresentative z = -1 ∨ parityRepresentative z = 0 := by
  have h₀ := Int.emod_nonneg z (by norm_num : (2 : ℤ) ≠ 0)
  have h₁ := Int.emod_lt_of_pos z (by norm_num : (0 : ℤ) < 2)
  unfold parityRepresentative
  omega

/-- Rounding changes an integer by an even integer. -/
theorem parityRepresentative_decomposition (z : ℤ) :
    z = parityRepresentative z + 2 * ((z - parityRepresentative z) / 2) := by
  unfold parityRepresentative
  omega

/-- A matrix whose rows have absolute sum at most two maps coefficients in
`{-1,0}` to vectors with every coordinate between negative two and two. -/
theorem boundary_abs_le_two {S R : Type*} [Fintype R]
    (T : S → R → ℤ) (z : R → ℤ)
    (hrow : ∀ i, ∑ j, |T i j| ≤ 2)
    (hz : ∀ j, z j = -1 ∨ z j = 0) :
    ∀ i, |boundary T z i| ≤ 2 := by
  intro i
  calc
    |boundary T z i| ≤ ∑ j, |T i j * z j| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |T i j| := by
      apply Finset.sum_le_sum
      intro j _
      rcases hz j with h | h <;> simp [h]
    _ ≤ 2 := hrow i

/-- The finite algebraic exact splitting theorem.

`Q` sends integer circle coefficients to their homology class; `T` describes
all integral relations among those classes. The row bound, kernel equality,
and cokernel torsion property are explicit geometric inputs. A total class
`4 • b` then has a subfamily and complementary subfamily of class `2 • b`.
No choice of a free part or loss of torsion information occurs. -/
theorem exact_split {S R H : Type*} [Fintype R] [AddCommGroup H]
    (T : S → R → ℤ) (Q : (S → ℤ) →+ H)
    (hrow : ∀ i, ∑ j, |T i j| ≤ 2)
    (hker : ∀ v, Q v = 0 ↔ ∃ z, boundary T z = v)
    (hcoker : TwoTorsionCokernel Q)
    (b : H) (htotal : Q (fun _ => 1) = 4 • b) :
    ∃ a : S → ℤ, (∀ i, a i = 0 ∨ a i = 1) ∧
      Q a = 2 • b ∧ Q ((fun _ => 1) - a) = 2 • b := by
  obtain ⟨x, hx⟩ := hcoker b 4 (by norm_num) ⟨fun _ => 1, htotal⟩
  have hrelation : Q ((fun _ => 1) - 2 • x) = 0 := by
    rw [map_sub, map_nsmul, htotal, hx]
    abel
  obtain ⟨z, hz⟩ := (hker _).mp hrelation
  let z' : R → ℤ := fun j => parityRepresentative (z j)
  let t : R → ℤ := fun j => (z j - z' j) / 2
  have hdecomp : ∀ j, z j = z' j + 2 * t j := by
    intro j
    exact parityRepresentative_decomposition (z j)
  have hbound : ∀ i, |boundary T z' i| ≤ 2 :=
    boundary_abs_le_two T z' hrow (fun j => parityRepresentative_values (z j))
  have hcoord : ∀ i, boundary T z i = boundary T z' i + 2 * boundary T t i := by
    intro i
    simp only [boundary]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [hdecomp j]
    ring
  have hzero : Q (boundary T t) = 0 := (hker _).mpr ⟨t, rfl⟩
  let a : S → ℤ := x + boundary T t
  have ha : ∀ i, a i = 0 ∨ a i = 1 := by
    intro i
    have hzi : boundary T z i = 1 - 2 * x i := by
      simpa only [Pi.sub_apply, Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat] using congrFun hz i
    have hci := hcoord i
    have hbi := abs_le.mp (hbound i)
    change x i + boundary T t i = 0 ∨ x i + boundary T t i = 1
    omega
  have hclass : Q a = 2 • b := by
    change Q (x + boundary T t) = 2 • b
    rw [map_add, hzero, add_zero, hx]
  refine ⟨a, ha, hclass, ?_⟩
  rw [map_sub, htotal, hclass]
  abel

/-- The same theorem expressed as a partition of a finite family of circles.
The two displayed coefficient functions are the indicators of a subfamily
and its complement. -/
theorem exact_subfamily_split {S R H : Type*} [Fintype S] [Fintype R] [DecidableEq S]
    [AddCommGroup H] (T : S → R → ℤ) (Q : (S → ℤ) →+ H)
    (hrow : ∀ i, ∑ j, |T i j| ≤ 2)
    (hker : ∀ v, Q v = 0 ↔ ∃ z, boundary T z = v)
    (hcoker : TwoTorsionCokernel Q)
    (b : H) (htotal : Q (fun _ => 1) = 4 • b) :
    ∃ I : Finset S,
      Q (fun i => if i ∈ I then 1 else 0) = 2 • b ∧
      Q (fun i => if i ∉ I then 1 else 0) = 2 • b := by
  classical
  obtain ⟨a, ha, hleft, hright⟩ := exact_split T Q hrow hker hcoker b htotal
  let I : Finset S := Finset.univ.filter (fun i => a i = 1)
  have hI : (fun i => if i ∈ I then (1 : ℤ) else 0) = a := by
    funext i
    rcases ha i with h | h <;> simp [I, h]
  have hIc : (fun i => if i ∉ I then (1 : ℤ) else 0) = (fun _ => 1) - a := by
    funext i
    rcases ha i with h | h <;> simp [I, h]
  refine ⟨I, ?_, ?_⟩
  · rw [hI]
    exact hleft
  · rw [hIc]
    exact hright

end MWIS.Splitting

end
