module

public import MWIS.IntegerFeasibilityGeneral
public import MWIS.AlgorithmNetworkEncoding
public import MWIS.AlgorithmThresholdSearch

/-!
# Concrete integer LP threshold decisions and exact value search

Each threshold query computes its own coefficient magnitude bound and calls
the proved finite-precision feasibility program. Integer objective values are
recovered by the executable high-bit search, without a solver oracle.

Prepared 2026-10-23.
-/

@[expose] public section
namespace MWIS.AlgorithmThresholdLP

open scoped BigOperators
open AlgorithmNetworkEncoding

/-- A dense integer row evaluated at a real vector. -/
def dot {n : ℕ} (a : Fin n → ℤ) (x : Fin n → ℝ) : ℝ := ∑ j, (a j : ℝ) * x j

/-- Real upper-bound feasibility for a stored dense program. -/
def RealFeasible {m n : ℕ} (P : DenseProgram m n) (x : Fin n → ℝ) : Prop :=
  ∀ i, dot (P.coefficient i) x ≤ (P.rhs i : ℝ)

/-- An explicitly computed bound on all signed integer entries. -/
def magnitude {m n : ℕ} (P : DenseProgram m n) : ℕ :=
  1 + (∑ i, ∑ j, (P.coefficient i j).natAbs) +
    (∑ i, (P.rhs i).natAbs) + ∑ j, (P.objective j).natAbs

theorem magnitude_pos {m n : ℕ} (P : DenseProgram m n) : 1 ≤ magnitude P := by
  unfold magnitude
  omega

theorem coefficient_abs_le {m n : ℕ} (P : DenseProgram m n) (i : Fin m) (j : Fin n) :
    |P.coefficient i j| ≤ (magnitude P : ℤ) := by
  have h1 : (P.coefficient i j).natAbs ≤ ∑ k, (P.coefficient i k).natAbs :=
    Finset.single_le_sum (f := fun k => (P.coefficient i k).natAbs)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have h2 : (∑ k, (P.coefficient i k).natAbs) ≤ ∑ a, ∑ k, (P.coefficient a k).natAbs :=
    Finset.single_le_sum (f := fun a => ∑ k, (P.coefficient a k).natAbs)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  rw [← Int.natCast_natAbs]
  exact_mod_cast (show (P.coefficient i j).natAbs ≤ magnitude P by unfold magnitude; omega)

theorem rhs_abs_le {m n : ℕ} (P : DenseProgram m n) (i : Fin m) :
    |P.rhs i| ≤ (magnitude P : ℤ) := by
  have h : (P.rhs i).natAbs ≤ ∑ k, (P.rhs k).natAbs :=
    Finset.single_le_sum (f := fun k => (P.rhs k).natAbs)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  rw [← Int.natCast_natAbs]
  exact_mod_cast (show (P.rhs i).natAbs ≤ magnitude P by unfold magnitude; omega)

/-- No numerical bounds are supplied to the caller: they are computed from
all matrix and bound entries before running the integer feasibility program. -/
def feasible {m n : ℕ} (P : DenseProgram m n) : Bool :=
  IntegerFeasibilityGeneral.feasible (magnitude P) (magnitude P).size
    (fun i j => -P.coefficient i j) (fun i => -P.rhs i)

/-- Correctness of the concrete upper-inequality feasibility decision. -/
theorem feasible_iff {m n : ℕ} (P : DenseProgram m n) :
    feasible P = true ↔ ∃ x, RealFeasible P x := by
  have hpow : (magnitude P : ℝ) ≤ 2 ^ (magnitude P).size := by
    exact_mod_cast (Nat.lt_size_self (magnitude P)).le
  have h := IntegerFeasibilityGeneral.feasible_iff (magnitude P) (magnitude P).size
    (magnitude_pos P) hpow (fun i j => -P.coefficient i j) (fun i => -P.rhs i)
    (fun i j => by simpa using coefficient_abs_le P i j)
    (fun i => by simpa using rhs_abs_le P i)
  change feasible P = true ↔ ∃ x : Fin n → ℝ,
    ∀ i, ((-P.rhs i : ℤ) : ℝ) ≤ ∑ j, ((-P.coefficient i j : ℤ) : ℝ) * x j at h
  simpa only [Int.cast_neg, neg_mul, Finset.sum_neg_distrib, neg_le_neg_iff,
    RealFeasible, dot] using h

/-- Decide an upper bound on the integer objective numerator. -/
def below {m n : ℕ} (P : DenseProgram m n) (threshold : ℤ) : Bool :=
  feasible (P.withThreshold threshold)

theorem below_iff {m n : ℕ} (P : DenseProgram m n) (threshold : ℤ) :
    below P threshold = true ↔
      ∃ x, RealFeasible P x ∧ dot P.objective x ≤ (threshold : ℝ) := by
  rw [below, feasible_iff]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, (fun i => hx i.succ), hx 0⟩
  · rintro ⟨x, hx, ht⟩
    refine ⟨x, fun i => ?_⟩
    exact Fin.cases ht (fun j => hx j) i

/-- Attainment converts threshold feasibility into a comparison with the minimum. -/
theorem below_iff_minimum {m n : ℕ} (P : DenseProgram m n) (minimum : ℝ)
    (hmin : IsLeast (dot P.objective '' {x | RealFeasible P x}) minimum) (threshold : ℤ) :
    below P threshold = true ↔ minimum ≤ (threshold : ℝ) := by
  rw [below_iff]
  constructor
  · rintro ⟨x, hx, ht⟩
    exact (hmin.2 ⟨x, hx, rfl⟩).trans ht
  · intro ht
    obtain ⟨x, hx, he⟩ := hmin.1
    exact ⟨x, hx, he ▸ ht⟩

/-- Test whether an independent-set value can reach a given integer threshold.
`offset` is the sum of vertex weights, twice the dual total cost. -/
def atLeast {m n : ℕ} (P : DenseProgram m n) (offset : ℤ) (threshold : ℕ) : Bool :=
  below P (offset - 2 * (threshold : ℤ))

/-- The cost denominator two exactly matches the integer maximization lattice. -/
theorem atLeast_iff {m n : ℕ} (P : DenseProgram m n) (offset : ℤ) (opt : ℕ)
    (minimum : ℝ) (hmin : IsLeast (dot P.objective '' {x | RealFeasible P x}) minimum)
    (hvalue : minimum = (offset : ℝ) - 2 * (opt : ℝ)) (threshold : ℕ) :
    atLeast P offset threshold = true ↔ threshold ≤ opt := by
  rw [atLeast, below_iff_minimum P minimum hmin, hvalue]
  push_cast
  constructor
  · intro h
    have ht : (threshold : ℝ) ≤ (opt : ℝ) := by linarith
    exact_mod_cast ht
  · intro h
    have ht : (threshold : ℝ) ≤ (opt : ℝ) := by exact_mod_cast h
    linarith

/-- The concrete exact optimizer: every search query executes the proved
integer linear-feasibility program. -/
def optimize {m n : ℕ} (P : DenseProgram m n) (offset : ℤ) (bits : ℕ) : ℕ :=
  AlgorithmThresholdSearch.solve (atLeast P offset) bits

/-- Exact output of the executable dense-program optimizer. -/
theorem optimize_correct {m n : ℕ} (P : DenseProgram m n) (offset : ℤ) (bits opt : ℕ)
    (minimum : ℝ) (hmin : IsLeast (dot P.objective '' {x | RealFeasible P x}) minimum)
    (hvalue : minimum = (offset : ℝ) - 2 * (opt : ℝ)) (hopt : opt < 2 ^ bits) :
    optimize P offset bits = opt := by
  exact AlgorithmThresholdSearch.solve_correct _ bits opt hopt
    (fun t _ => atLeast_iff P offset opt minimum hmin hvalue t)

end MWIS.AlgorithmThresholdLP
end
