module

public import MWIS.IntegerFeasibilityEquiv
public import MWIS.AlgorithmEllipsoidComplete

/-!
# Executable integer encoding of the perturbed feasibility system

Clearing the explicit positive perturbation denominator and reversing signs
turns the boxed real lower-bound system into the exact integer upper-bound
system consumed by the rational ellipsoid program.

Prepared 2026-10-23.
-/

@[expose] public section
namespace MWIS.IntegerFeasibilityEncoding

open Matrix
open scoped BigOperators
open IntegerFeasibility IntegerFeasibility.SmaleNinth
open AlgorithmEllipsoidComplete

/-- The positive integer denominator of the feasibility perturbation. -/
def denominator (n U : ℕ) : ℕ := 2 * (n + 1) * (n + 1).factorial * U ^ (n + 1)

/-- The integer box radius, before inclusion into the reals. -/
def box (n U : ℕ) : ℕ := n.factorial * U ^ n + 1

/-- The original rows followed by positive and negative coordinate rows. -/
def augmentedMatrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    Matrix (Fin (m + n + n)) (Fin n) ℤ := fun i j =>
  if h : (i : ℕ) < m then A ⟨(i : ℕ), h⟩ j
  else if (i : ℕ) < m + n then (if (j : ℕ) = (i : ℕ) - m then 1 else 0)
  else (if (j : ℕ) = (i : ℕ) - m - n then -1 else 0)

/-- The integer matrix actually supplied to the upper-bound separator. -/
def matrix {m n : ℕ} (U : ℕ) (A : Matrix (Fin m) (Fin n) ℤ) :
    Matrix (Fin (m + n + n)) (Fin n) ℤ :=
  fun i j => -(denominator n U : ℤ) * augmentedMatrix A i j

/-- The integer right-hand side actually supplied to the separator. -/
def bound {m : ℕ} (n U : ℕ) (b : Fin m → ℤ) : Fin (m + n + n) → ℤ := fun i =>
  if h : (i : ℕ) < m then -(denominator n U : ℤ) * b ⟨(i : ℕ), h⟩ + 1
  else (denominator n U : ℤ) * (box n U : ℤ)

/-- Every allowed input bound gives a strictly positive common denominator. -/
theorem denominator_pos (n U : ℕ) (hU : 1 ≤ U) : 0 < denominator n U := by
  unfold denominator
  have hUp : 0 < U := by omega
  have hf := Nat.factorial_pos (n + 1)
  positivity

/-- The integer radius agrees with the real feasibility box. -/
theorem box_cast (n U : ℕ) : (box n U : ℝ) = khachiyanBox n U := by
  simp [box, khachiyanBox]

/-- The explicit perturbation is exactly the reciprocal integer denominator. -/
theorem eps_eq_inv (n U : ℕ) : khachiyanEps n U = (denominator n U : ℝ)⁻¹ := by
  simp [khachiyanEps, denominator, one_div]

/-- The augmented integer rows cast to the real perturbed-system rows. -/
theorem augmentedMatrix_cast {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (i j) :
    (augmentedMatrix A i j : ℝ) = khachiyanSystemA A i j := by
  unfold augmentedMatrix khachiyanSystemA
  split <;> rename_i h
  · rfl
  · split <;> split <;> norm_num

/-- The executable matrix is the negated denominator-scaled real matrix. -/
theorem matrix_cast {m n : ℕ} (U : ℕ) (A : Matrix (Fin m) (Fin n) ℤ) (i j) :
    (matrix U A i j : ℝ) = -(denominator n U : ℝ) * khachiyanSystemA A i j := by
  simp only [matrix, Int.cast_mul, Int.cast_neg, Int.cast_natCast, augmentedMatrix_cast]

/-- The executable right-hand side is the same negated denominator scaling. -/
theorem bound_cast {m : ℕ} (n U : ℕ) (hU : 1 ≤ U) (b : Fin m → ℤ) (i) :
    (bound n U b i : ℝ) = -(denominator n U : ℝ) * khachiyanSystemb n U b i := by
  have hd : (denominator n U : ℝ) ≠ 0 := by
    exact_mod_cast (denominator_pos n U hU).ne'
  unfold bound khachiyanSystemb
  split <;> rename_i h
  · simp only [Int.cast_add, Int.cast_mul, Int.cast_neg, Int.cast_natCast, Int.cast_one]
    rw [eps_eq_inv]
    field_simp
    ring
  · simp only [Int.cast_mul, Int.cast_natCast, box_cast]
    ring

/-- The actual integer system has precisely the intended perturbed and boxed
real solution set. -/
theorem realFeasible_eq {m n : ℕ} (U : ℕ) (hU : 1 ≤ U)
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) :
    realFeasible (matrix U A) (bound n U b) =
      IntegerFeasibility.LinearOptimization.polyhedron
        (khachiyanSystemA A) (khachiyanSystemb n U b) := by
  ext x
  change (∀ i, (∑ j, (matrix U A i j : ℝ) * x j) ≤ (bound n U b i : ℝ)) ↔
    (∀ i, khachiyanSystemb n U b i ≤ (khachiyanSystemA A).mulVec x i)
  apply forall_congr'
  intro i
  have hd : (0 : ℝ) < denominator n U := by exact_mod_cast denominator_pos n U hU
  simp_rw [matrix_cast, bound_cast n U hU b, mul_assoc, ← Finset.mul_sum]
  change -(denominator n U : ℝ) * (khachiyanSystemA A).mulVec x i ≤
    -(denominator n U : ℝ) * khachiyanSystemb n U b i ↔ _
  constructor
  · intro h
    by_contra hn
    have hp := mul_pos hd (sub_pos.mpr (lt_of_not_ge hn))
    nlinarith
  · intro h
    exact mul_le_mul_of_nonpos_left h (neg_nonpos.mpr hd.le)

/-- Feasibility of the original integer lower-bound system is equivalent to
feasibility of the concrete integer system passed to the rounded solver. -/
theorem feasibility_equiv {m n : ℕ} (U : ℕ) (hU : 1 ≤ U) (hn : 1 ≤ n)
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (hA : ∀ i j, |A i j| ≤ (U : ℤ)) (hb : ∀ i, |b i| ≤ (U : ℤ)) :
    (IntegerFeasibility.LinearOptimization.polyhedron
      (A.map (Int.cast : ℤ → ℝ)) (fun i => (b i : ℝ))).Nonempty ↔
        (realFeasible (matrix U A) (bound n U b)).Nonempty := by
  rw [realFeasible_eq U hU A b]
  exact khachiyan_feasibility_equiv U hU hn A b hA hb

end MWIS.IntegerFeasibilityEncoding
end
