module

public import MWIS.AlgorithmThresholdLP

/-!
# Exact optimization of the finite-group network program

The concrete dense integer feasibility solver is connected to the actual
real hub-flow polyhedron and its objective, including the common cost
denominator two.

Prepared 2026-10-23.
-/

@[expose] public section
namespace MWIS.AlgorithmNetworkOptimize

open scoped BigOperators
open Walks FiniteExtension AlgorithmNetworkEncoding AlgorithmThresholdLP

variable {Row Edge G : Type*} [Fintype Row] [Fintype Edge] [Fintype G]
    [DecidableEq Row] [DecidableEq Edge] [DecidableEq G] [AddCommGroup G]
variable (C : Edge → Column Row)

/-- Real feasibility of the dense encoding agrees with the original hub LP. -/
theorem toDense_realFeasible_iff {r m n : ℕ} (W : (Edge → ℤ) →+ (Fin r → ℤ))
    (ell : (Edge → ℤ) →+ G) (η : G) (numerator : Edge → ℤ)
    (rows : InequalityRow C (G := G) r ≃ Fin m)
    (cols : ExtensionArc C G ≃ Fin n) (x : Fin n → ℝ) :
    RealFeasible (toDense C W ell η numerator rows cols) x ↔
      (fun a => x (cols a)) ∈ polyhedron C ell η ∧
        RealCoordinates.extension W (rho C (fun a => x (cols a))) = 0 := by
  rw [← AlgorithmNetworkEncoding.feasible_iff]
  constructor
  · intro h i
    have hi := h (rows i)
    simp only [dot, toDense, Equiv.symm_apply_apply] at hi
    have hs := cols.sum_comp
      (fun j => (matrix C W ell i (cols.symm j) : ℝ) * x j)
    simp only [Equiv.symm_apply_apply] at hs
    rw [← hs] at hi
    exact hi
  · intro h i
    have hi := h (rows.symm i)
    have hs := cols.sum_comp
      (fun j => (matrix C W ell (rows.symm i) (cols.symm j) : ℝ) * x j)
    simp only [Equiv.symm_apply_apply] at hs
    rw [hs] at hi
    exact hi

/-- Dense integer objective equals twice the original rational-cost objective. -/
theorem toDense_objective_twice {r m n : ℕ} (W : (Edge → ℤ) →+ (Fin r → ℤ))
    (ell : (Edge → ℤ) →+ G) (η : G) (numerator : Edge → ℤ) (c : Edge → ℚ)
    (hc : ∀ e, c e = (numerator e : ℚ) / 2)
    (rows : InequalityRow C (G := G) r ≃ Fin m)
    (cols : ExtensionArc C G ≃ Fin n) (x : Fin n → ℝ) :
    dot (toDense C W ell η numerator rows cols).objective x =
      2 * RealCoordinates.cost c (rho C (fun a => x (cols a))) := by
  rw [← objective_twice C numerator hc]
  symm
  simpa only [Equiv.symm_apply_apply, dot, toDense] using
    cols.sum_comp (fun j => (objectiveNumerator C numerator (cols.symm j) : ℝ) * x j)

/-- An attained minimum on the actual network is the attained minimum of
its explicit dense integer encoding, after multiplication by two. -/
theorem toDense_minimum {r m n : ℕ} (W : (Edge → ℤ) →+ (Fin r → ℤ))
    (ell : (Edge → ℤ) →+ G) (η : G) (numerator : Edge → ℤ) (c : Edge → ℚ)
    (hc : ∀ e, c e = (numerator e : ℚ) / 2)
    (rows : InequalityRow C (G := G) r ≃ Fin m)
    (cols : ExtensionArc C G ≃ Fin n) (v : ℝ)
    (hmin : IsLeast ((fun z => RealCoordinates.cost c (rho C z)) ''
      {z | z ∈ polyhedron C ell η ∧ RealCoordinates.extension W (rho C z) = 0}) v) :
    IsLeast (dot (toDense C W ell η numerator rows cols).objective ''
      {x | RealFeasible (toDense C W ell η numerator rows cols) x}) (2 * v) := by
  constructor
  · obtain ⟨z, hz, he⟩ := hmin.1
    change z ∈ polyhedron C ell η ∧ RealCoordinates.extension W (rho C z) = 0 at hz
    change RealCoordinates.cost c (rho C z) = v at he
    let x : Fin n → ℝ := fun j => z (cols.symm j)
    have hx : (fun a => x (cols a)) = z := by funext a; simp [x]
    refine ⟨x, (toDense_realFeasible_iff C W ell η numerator rows cols x).mpr ?_, ?_⟩
    · simpa only [hx] using hz
    · rw [toDense_objective_twice C W ell η numerator c hc rows cols x, hx, he]
  · rintro y ⟨x, hx, rfl⟩
    have hz := (toDense_realFeasible_iff C W ell η numerator rows cols x).mp hx
    have h := hmin.2 ⟨_, hz, rfl⟩
    rw [toDense_objective_twice C W ell η numerator c hc rows cols x]
    linarith

/-- The concrete integer-feasibility search returns the exact independent-set
value associated with the network minimum. -/
theorem optimize_network_correct {r m n : ℕ} (W : (Edge → ℤ) →+ (Fin r → ℤ))
    (ell : (Edge → ℤ) →+ G) (η : G) (numerator : Edge → ℤ) (c : Edge → ℚ)
    (hc : ∀ e, c e = (numerator e : ℚ) / 2)
    (rows : InequalityRow C (G := G) r ≃ Fin m)
    (cols : ExtensionArc C G ≃ Fin n) (v : ℝ)
    (hmin : IsLeast ((fun z => RealCoordinates.cost c (rho C z)) ''
      {z | z ∈ polyhedron C ell η ∧ RealCoordinates.extension W (rho C z) = 0}) v)
    (offset : ℤ) (hoffset : (offset : ℝ) = 2 * (Slack.totalCost c : ℝ))
    (opt bits : ℕ) (hvalue : (Slack.totalCost c : ℝ) - v = (opt : ℝ))
    (hopt : opt < 2 ^ bits) :
    optimize (toDense C W ell η numerator rows cols) offset bits = opt := by
  apply optimize_correct _ offset bits opt (2 * v)
    (toDense_minimum C W ell η numerator c hc rows cols v hmin) _ hopt
  linarith

end MWIS.AlgorithmNetworkOptimize
end
