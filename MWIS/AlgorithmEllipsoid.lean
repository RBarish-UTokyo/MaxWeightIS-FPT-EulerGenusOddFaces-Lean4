module

public import MWIS.AlgorithmSeparation
public import MWIS.AlgorithmSqrt
public import MWIS.AlgorithmMatrixRounding

/-!
# A finite rational ellipsoid computation

Prepared 2026-10-23.

States store integer numerators on one fixed dyadic grid. The update computes
its centre using a rational square-root enclosure and stores a rounded centre
and a padded, rounded shape matrix. The finite loop uses the exact integer-row
separator. Every returned point is feasible. A depleted iteration budget is an
explicit inconclusive result; completeness requires the geometric precision
and volume estimates, rather than being built into this program's interface.
-/

@[expose] public section

namespace MWIS.AlgorithmEllipsoid

open scoped BigOperators
open AlgorithmRounding

/-- Finite storage for a dyadic centre and shape matrix. -/
structure State (n : ℕ) where
  centerNumerator : Fin n → ℤ
  shapeNumerator : Matrix (Fin n) (Fin n) ℤ

/-- The rational centre decoded from the fixed grid. -/
def center {n : ℕ} (k : ℕ) (s : State n) : Fin n → ℚ :=
  fun i => dyadic k (s.centerNumerator i)

/-- The rational shape matrix decoded from the fixed grid. -/
def shape {n : ℕ} (k : ℕ) (s : State n) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => dyadic k (s.shapeNumerator i j)

/-- Matrix-vector multiplication in exact rational arithmetic. -/
def direction {n : ℕ} (D : Matrix (Fin n) (Fin n) ℚ)
    (a : Fin n → ℤ) : Fin n → ℚ := fun i => ∑ j, D i j * (a j : ℚ)

/-- The squared shape norm of the integer cutting normal. -/
def normalSquare {n : ℕ} (D : Matrix (Fin n) (Fin n) ℚ)
    (a : Fin n → ℤ) : ℚ := ∑ i, (a i : ℚ) * direction D a i

/-- The exact rational shape update. Only the centre formula needs a square root. -/
def rawShape {n : ℕ} (D : Matrix (Fin n) (Fin n) ℚ)
    (a : Fin n → ℤ) : Matrix (Fin n) (Fin n) ℚ :=
  let v := direction D a
  let q := normalSquare D a
  fun i j => ((n : ℚ) ^ 2 / ((n : ℚ) ^ 2 - 1)) *
    (D i j - (2 / ((n : ℚ) + 1)) * q⁻¹ * (v i * v j))

/-- Rational approximation of the exact central-cut centre using the safe upper
square-root endpoint. The normal points into the retained halfspace. -/
def approximateCenter {n : ℕ} (k : ℕ) (z : Fin n → ℚ)
    (D : Matrix (Fin n) (Fin n) ℚ) (a : Fin n → ℤ) : Fin n → ℚ :=
  fun i => z i + direction D a i /
    (((n : ℚ) + 1) * AlgorithmSqrt.upper k (normalSquare D a))

/-- An enlarged rational shape before entrywise rounding. -/
def enlargedShape {n : ℕ} (ε : ℚ) (D : Matrix (Fin n) (Fin n) ℚ)
    (a : Fin n → ℤ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => (1 + ε) ^ 2 * rawShape D a i j

/-- A concrete finite-precision update, including both stored rounding operations. -/
def update {n : ℕ} (k : ℕ) (ε : ℚ) (s : State n)
    (a : Fin n → ℤ) : State n where
  centerNumerator i := roundNumerator k
    (approximateCenter k (center k s) (shape k s) a i)
  shapeNumerator i j := AlgorithmMatrixRounding.paddedNumerator k
    (enlargedShape ε (shape k s) a) i j

/-- Decoding the updated centre yields precisely the prescribed scalar rounding. -/
theorem update_center {n : ℕ} (k : ℕ) (ε : ℚ) (s : State n)
    (a : Fin n → ℤ) (i : Fin n) :
    center k (update k ε s a) i =
      roundDown k (approximateCenter k (center k s) (shape k s) a i) := rfl

/-- Decoding the updated shape yields the controlled matrix-rounding construction. -/
theorem update_shape {n : ℕ} (k : ℕ) (ε : ℚ) (s : State n)
    (a : Fin n → ℤ) :
    shape k (update k ε s a) =
      AlgorithmMatrixRounding.padded k (enlargedShape ε (shape k s) a) := by
  ext i j
  exact (AlgorithmMatrixRounding.padded_eq_dyadic k _ i j).symm

/-- The raw shape formula preserves symmetry without any inverse computation. -/
theorem rawShape_symmetric {n : ℕ} (D : Matrix (Fin n) (Fin n) ℚ)
    (hD : ∀ i j, D i j = D j i) (a : Fin n → ℤ) :
    ∀ i j, rawShape D a i j = rawShape D a j i := by
  intro i j
  simp only [rawShape, hD i j, mul_comm (direction D a i) (direction D a j)]

/-- Exact symmetry survives enlargement, rounding, and diagonal padding. -/
theorem update_symmetric {n : ℕ} (k : ℕ) (ε : ℚ) (s : State n)
    (hs : ∀ i j, shape k s i j = shape k s j i) (a : Fin n → ℤ) :
    ∀ i j, shape k (update k ε s a) i j = shape k (update k ε s a) j i := by
  rw [update_shape]
  apply AlgorithmMatrixRounding.padded_symmetric
  intro i j
  simp only [enlargedShape, rawShape_symmetric _ hs a i j]

/-- The updated centre differs from its rational approximation by less than a grid unit. -/
theorem update_center_error {n : ℕ} (k : ℕ) (ε : ℚ) (s : State n)
    (a : Fin n → ℤ) (i : Fin n) :
    |center k (update k ε s a) i -
      approximateCenter k (center k s) (shape k s) a i| < 1 / 2 ^ k :=
  abs_roundDown_error k _

/-- Stored integer payload length; sign bits are counted explicitly. -/
def payloadBits {n : ℕ} (s : State n) : ℕ :=
  (∑ i, (1 + (s.centerNumerator i).natAbs.size)) +
    ∑ i, ∑ j, (1 + (s.shapeNumerator i j).natAbs.size)

/-- Bounds on the unrounded numerical quantities yield a polynomial bound on
all integers actually stored by the update. -/
theorem update_payloadBits {n : ℕ} (k Bc Bs : ℕ) (ε : ℚ) (s : State n)
    (a : Fin n → ℤ)
    (hc : ∀ i, |approximateCenter k (center k s) (shape k s) a i| ≤ 2 ^ Bc)
    (hD : ∀ i j, |enlargedShape ε (shape k s) a i j| ≤ 2 ^ Bs) :
    payloadBits (update k ε s a) ≤
      n * (k + Bc + 3) + n ^ 2 * (k + Bs + n.size + 4) := by
  unfold payloadBits
  apply add_le_add
  · calc
      _ ≤ ∑ _i : Fin n, (k + Bc + 3) := by
        apply Finset.sum_le_sum
        intro i _
        have h := roundNumerator_size k Bc _ (hc i)
        change 1 + (roundNumerator k _).natAbs.size ≤ _
        omega
      _ = _ := by simp
  · calc
      _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, (k + Bs + n.size + 4) := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        have h := AlgorithmMatrixRounding.paddedNumerator_size k Bs _ hD i j
        simp only [Fintype.card_fin] at h
        change 1 + (AlgorithmMatrixRounding.paddedNumerator k _ i j).natAbs.size ≤ _
        omega
      _ = _ := by simp [pow_two, mul_assoc]

/-- A zero-centred Euclidean ball with radius `2^B` has an exact dyadic state. -/
def initial (n k B : ℕ) : State n where
  centerNumerator _ := 0
  shapeNumerator i j := if i = j then (2 ^ (k + 2 * B) : ℕ) else 0

/-- Initial centres decode exactly to zero. -/
theorem initial_center (n k B : ℕ) : center k (initial n k B) = 0 := by
  funext i
  simp [center, initial, dyadic]

/-- Initial shapes decode exactly to the diagonal matrix for the stated ball. -/
theorem initial_shape (n k B : ℕ) (i j : Fin n) :
    shape k (initial n k B) i j = if i = j then (2 : ℚ) ^ (2 * B) else 0 := by
  by_cases hij : i = j
  · simp [shape, initial, hij, dyadic, pow_add]
  · simp [shape, initial, hij, dyadic]

/-- The execution distinguishes an exhausted budget from a verified inconsistent
zero row and a feasible returned centre. -/
inductive Outcome (n : ℕ) where
  | feasible (state : State n)
  | zeroRow
  | exhausted

/-- Run at most `fuel` updates and at most `fuel+1` exact separation queries. -/
def run {m n : ℕ} (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ)
    (k : ℕ) (ε : ℚ) : ℕ → State n → Outcome n
  | fuel, s =>
    match AlgorithmSeparation.separate A b (center k s) with
    | none => .feasible s
    | some i =>
      if A i = 0 then .zeroRow else
        match fuel with
        | 0 => .exhausted
        | t + 1 => run A b k ε t (update k ε s (fun j => -A i j))

/-- Every state actually returned by the computation has a feasible centre. -/
theorem run_feasible {m n : ℕ} (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ)
    (k : ℕ) (ε : ℚ) (fuel : ℕ) (s t : State n)
    (h : run A b k ε fuel s = .feasible t) :
    AlgorithmSeparation.Feasible A b (center k t) := by
  induction fuel generalizing s with
  | zero =>
      unfold run at h
      split at h
      · rename_i hs
        cases h
        exact (AlgorithmSeparation.separate_none_iff A b _).mp hs
      · split at h <;> contradiction
  | succ fuel ih =>
      unfold run at h
      split at h
      · rename_i hs
        cases h
        exact (AlgorithmSeparation.separate_none_iff A b _).mp hs
      · split at h
        · contradiction
        · exact ih _ h

/-- A reported zero-row contradiction rules out every rational feasible point. -/
theorem run_zeroRow {m n : ℕ} (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ)
    (k : ℕ) (ε : ℚ) (fuel : ℕ) (s : State n)
    (h : run A b k ε fuel s = .zeroRow) :
    ¬ ∃ x, AlgorithmSeparation.Feasible A b x := by
  induction fuel generalizing s with
  | zero =>
      unfold run at h
      split at h
      · contradiction
      · rename_i i hi
        split at h
        · rename_i hz
          exact AlgorithmSeparation.separate_zero_row_infeasible A b _ i hi hz
        · contradiction
  | succ fuel ih =>
      unfold run at h
      split at h
      · contradiction
      · rename_i i hi
        split at h
        · rename_i hz
          exact AlgorithmSeparation.separate_zero_row_infeasible A b _ i hi hz
        · exact ih _ h

end MWIS.AlgorithmEllipsoid
