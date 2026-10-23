module

public import MWIS.AlgorithmBounds
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Exact integer encoding of rational weights

Prepared 2026-10-23.

Multiplication by the product of positive denominators preserves every set
objective comparison. The product and the resulting integer vector have
explicit binary-length bounds, including when some weights are negative.
-/

@[expose] public section

namespace MWIS.AlgorithmRational

open scoped BigOperators

variable {V : Type*} [Fintype V]

/-- Total bits for signs, numerator magnitudes and positive denominators. -/
def rationalBits (w : V → ℚ) : ℕ :=
  ∑ v, (1 + (w v).num.natAbs.size + (w v).den.size)

/-- Total bits for signs and integer magnitudes. -/
def integerBits (w : V → ℤ) : ℕ := ∑ v, (1 + (w v).natAbs.size)

/-- A positive common denominator, computed by a finite product. -/
def denominatorProduct (w : V → ℚ) : ℕ := ∏ v, (w v).den

/-- Exact integerized weights, with division performed only on a known divisor. -/
def integerize (w : V → ℚ) (v : V) : ℤ :=
  (w v).num * (denominatorProduct w / (w v).den : ℕ)

theorem denominatorProduct_pos (w : V → ℚ) : 0 < denominatorProduct w :=
  Finset.prod_pos fun v _ => (w v).den_pos

theorem denominator_dvd_product (w : V → ℚ) (v : V) :
    (w v).den ∣ denominatorProduct w := by
  classical
  exact Finset.dvd_prod_of_mem (fun u => (w u).den) (Finset.mem_univ v)

/-- The integerized vector is exactly a common positive multiple. -/
theorem integerize_eq (w : V → ℚ) (v : V) :
    (integerize w v : ℚ) = (denominatorProduct w : ℚ) * w v := by
  have hmul : (denominatorProduct w / (w v).den) * (w v).den = denominatorProduct w :=
    Nat.div_mul_cancel (denominator_dvd_product w v)
  have hcast : (denominatorProduct w : ℚ) =
      (denominatorProduct w / (w v).den : ℕ) * (w v).den := by exact_mod_cast hmul.symm
  have hnum : ((w v).num : ℚ) = w v * (w v).den := by
    exact (div_eq_iff (by exact_mod_cast (w v).den_ne_zero)).mp (Rat.num_div_den (w v))
  simp only [integerize, Int.cast_mul, Int.cast_natCast]
  rw [hnum, hcast]
  ring

/-- Clearing denominators preserves all comparisons of finite-set objectives. -/
theorem objective_le_iff (w : V → ℚ) (I J : Finset V) :
    (∑ v ∈ I, integerize w v) ≤ (∑ v ∈ J, integerize w v) ↔
      (∑ v ∈ I, w v) ≤ (∑ v ∈ J, w v) := by
  have hpos : (0 : ℚ) < denominatorProduct w := by exact_mod_cast denominatorProduct_pos w
  have hI : ((∑ v ∈ I, integerize w v : ℤ) : ℚ) =
      (denominatorProduct w : ℚ) * ∑ v ∈ I, w v := by
    simp only [Int.cast_sum, integerize_eq, Finset.mul_sum]
  have hJ : ((∑ v ∈ J, integerize w v : ℤ) : ℚ) =
      (denominatorProduct w : ℚ) * ∑ v ∈ J, w v := by
    simp only [Int.cast_sum, integerize_eq, Finset.mul_sum]
  rw [← Int.cast_le (R := ℚ), hI, hJ, mul_le_mul_iff_right₀ hpos]

private theorem product_size_le {ι : Type*} (s : Finset ι) (f : ι → ℕ) :
    (∏ i ∈ s, f i).size ≤ 1 + ∑ i ∈ s, (f i).size := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have h := AlgorithmBounds.product_address_bits (f a) (∏ i ∈ s, f i)
    omega

/-- A common denominator has at most one plus the sum of denominator bit lengths. -/
theorem denominatorProduct_size (w : V → ℚ) :
    (denominatorProduct w).size ≤ 1 + ∑ v, (w v).den.size :=
  product_size_le Finset.univ (fun v => (w v).den)

/-- The vertex count is already bounded by the signed rational input length. -/
theorem card_le_rationalBits (w : V → ℚ) : Fintype.card V ≤ rationalBits w := by
  calc
    Fintype.card V = ∑ _v : V, (1 : ℕ) := by simp
    _ ≤ rationalBits w := Finset.sum_le_sum fun v _ => by omega

/-- Every scaled weight has at most one plus the total rational input length. -/
theorem integerize_size (w : V → ℚ) (v : V) :
    (integerize w v).natAbs.size ≤ 1 + rationalBits w := by
  classical
  have hd := denominatorProduct_size w
  have hdiv := Nat.size_le_size (Nat.div_le_self (denominatorProduct w) (w v).den)
  have hmul := AlgorithmBounds.product_address_bits (w v).num.natAbs
    (denominatorProduct w / (w v).den)
  have hv : (w v).num.natAbs.size ≤ ∑ u : V, (w u).num.natAbs.size :=
    Finset.single_le_sum (f := fun u : V => (w u).num.natAbs.size)
      (fun u _ => Nat.zero_le _) (Finset.mem_univ v)
  have hbits : rationalBits w = Fintype.card V +
      (∑ u : V, (w u).num.natAbs.size) + ∑ u : V, (w u).den.size := by
    simp [rationalBits, Finset.sum_add_distrib]
  simp only [integerize, Int.natAbs_mul, Int.natAbs_natCast]
  omega

/-- Clearing all denominators increases total weight encoding length quadratically. -/
theorem integerize_total_bits (w : V → ℚ) :
    integerBits (integerize w) ≤ rationalBits w * (rationalBits w + 2) := by
  have hs : integerBits (integerize w) ≤ Fintype.card V * (rationalBits w + 2) := by
    calc
      integerBits (integerize w) ≤ ∑ _v : V, (rationalBits w + 2) :=
        Finset.sum_le_sum fun v _ => by have h := integerize_size w v; omega
      _ = _ := by simp
  exact hs.trans (Nat.mul_le_mul_right _ (card_le_rationalBits w))

/-- One explicit integer vector preserves every feasible-set maximum, with a
quadratic encoding bound. No approximation of the rational weights is used. -/
theorem integerize_preserves_maximum (w : V → ℚ) (feasible : Finset V → Prop)
    (I : Finset V) :
    ((∀ J, feasible J → (∑ v ∈ J, integerize w v) ≤ ∑ v ∈ I, integerize w v) ↔
      (∀ J, feasible J → (∑ v ∈ J, w v) ≤ ∑ v ∈ I, w v)) ∧
      integerBits (integerize w) ≤ rationalBits w * (rationalBits w + 2) := by
  refine ⟨?_, integerize_total_bits w⟩
  exact forall_congr' fun J => imp_congr_right fun _ => objective_le_iff w J I

end MWIS.AlgorithmRational
