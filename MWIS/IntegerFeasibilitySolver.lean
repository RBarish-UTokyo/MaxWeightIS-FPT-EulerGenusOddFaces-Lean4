module

public import MWIS.IntegerFeasibilityEncoding
public import MWIS.IntegerFeasibilityBounds
public import MWIS.AlgorithmPrecision

/-!
# A concrete rounded solver for integer linear feasibility

The program uses explicit integer preprocessing, dyadic precision, and a
polynomial iteration budget. Its Boolean result is equivalent to real
feasibility. No geometric update or completeness premise is supplied by
the caller.

Prepared 2026-10-23.
-/

@[expose] public section
namespace MWIS.IntegerFeasibilitySolver

open Matrix
open scoped BigOperators
open IntegerFeasibility IntegerFeasibility.SmaleNinth IntegerFeasibility.LinearOptimization
open AlgorithmEllipsoid AlgorithmEllipsoidComplete AlgorithmTrajectory
open AlgorithmPrecision

/-- Run the finite integer-payload solver on the explicitly encoded system. -/
def solve {m n : ℕ} (U B : ℕ) (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) :
    Outcome n :=
  let T := feasibilityIterations n B
  let k := precision n T
  run (IntegerFeasibilityEncoding.matrix U A) (IntegerFeasibilityEncoding.bound n U b)
    k (inflation n) T (initial n k (outerExponent n B))

/-- The executable Boolean feasibility decision. -/
def feasible {m n : ℕ} (U B : ℕ) (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) : Bool :=
  match solve U B A b with
  | .feasible _ => true
  | .zeroRow => false
  | .exhausted => false

/-- Every original feasible system yields a successful actual finite execution. -/
theorem solve_complete {m n : ℕ} (hn : 2 ≤ n) (U B : ℕ) (hU : 1 ≤ U)
    (hUB : (U : ℝ) ≤ 2 ^ B) (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (hA : ∀ i j, |A i j| ≤ (U : ℤ)) (hb : ∀ i, |b i| ≤ (U : ℤ))
    (hne : (polyhedron (A.map (Int.cast : ℤ → ℝ)) (fun i => (b i : ℝ))).Nonempty) :
    ∃ result, solve U B A b = .feasible result := by
  let T := feasibilityIterations n B
  let k := precision n T
  let encA := IntegerFeasibilityEncoding.matrix U A
  let encb := IntegerFeasibilityEncoding.bound n U b
  let state := initial n k (outerExponent n B)
  have hn1 : 1 ≤ n := by omega
  obtain ⟨z, hz⟩ := exists_inner_sphere hn1 hU A b hA hb hne
  have hεmax : (inflation n : ℝ) ≤ 1 / (32 * ((n : ℝ) + 1) ^ 2) := by
    simp [inflation]
  have hp : ∀ t < T, ∀ i,
      AlgorithmSeparation.separate encA encb (center k (trajectory encA encb k (inflation n) state t)) = some i →
      encA i ≠ 0 → Nonempty (EllipsoidUpdateBridge.StepPrecision k (inflation n)
        (trajectory encA encb k (inflation n) state t) (fun j => -encA i j)) := by
    intro t ht i _ ha
    exact ⟨trajectory_stepPrecision hn encA encb (outerExponent n B) T t ht.le
      _ (neg_normal_ne_zero (encA i) ha)⟩
  have hball : EllipsoidGeometry.ellipsoid z
      (VolAux.halfSide n U ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)) ⊆ realFeasible encA encb := by
    rw [IntegerFeasibilityEncoding.realFeasible_eq U hU A b]
    exact hz
  have hboxed : realFeasible encA encb ⊆ stateEllipsoid k state := by
    rw [IntegerFeasibilityEncoding.realFeasible_eq U hU A b, initial_ellipsoid]
    intro x hx
    have hsmall := boxed_subset_sphere hn1 A b hx
    have hR : 0 < outerRadius n U := mul_pos (by exact_mod_cast hn1) (KhachAux.box_pos n U)
    apply (EllipsoidIteration.mem_spherical_ellipsoid_iff 0 x _ (by positivity)).mpr
    have hq := (EllipsoidIteration.mem_spherical_ellipsoid_iff 0 x _ hR).mp hsmall
    exact hq.trans ((sq_le_sq₀ hR.le (by positivity)).mpr (outerRadius_le_dyadic n U B hUB))
  obtain ⟨result, hresult, _⟩ := run_feasible_of_inner_ball hn encA encb k (inflation n)
    (inflation_pos n) hεmax T (radiusExponent n B) state (initial_positive n k _)
    hp z (2 ^ outerExponent n B) (VolAux.halfSide n U) (by positivity)
    (VolAux.halfSide_pos hn1 hU) (initial_ellipsoid n k _)
    hball hboxed (dyadic_radius_ratio_le n U B hUB)
    (by unfold T feasibilityIterations; omega)
  exact ⟨result, hresult⟩

/-- Every successful actual finite execution certifies original real feasibility. -/
theorem solve_sound {m n : ℕ} (hn : 2 ≤ n) (U B : ℕ) (hU : 1 ≤ U)
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (hA : ∀ i j, |A i j| ≤ (U : ℤ)) (hb : ∀ i, |b i| ≤ (U : ℤ))
    (result : State n) (h : solve U B A b = .feasible result) :
    (polyhedron (A.map (Int.cast : ℤ → ℝ)) (fun i => (b i : ℝ))).Nonempty := by
  apply (IntegerFeasibilityEncoding.feasibility_equiv U hU (by omega) A b hA hb).mpr
  have hf := run_feasible _ _ _ _ _ _ result h
  exact ⟨EllipsoidCenterRounding.castVector (center _ result), (feasible_cast_iff _ _ _).mpr hf⟩

/-- Correctness of the fully specified executable Boolean solver. -/
theorem feasible_iff {m n : ℕ} (hn : 2 ≤ n) (U B : ℕ) (hU : 1 ≤ U)
    (hUB : (U : ℝ) ≤ 2 ^ B) (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (hA : ∀ i j, |A i j| ≤ (U : ℤ)) (hb : ∀ i, |b i| ≤ (U : ℤ)) :
    feasible U B A b = true ↔
      (polyhedron (A.map (Int.cast : ℤ → ℝ)) (fun i => (b i : ℝ))).Nonempty := by
  constructor
  · intro h
    unfold feasible at h
    split at h
    · rename_i result heq
      exact solve_sound hn U B hU A b hA hb result heq
    · contradiction
    · contradiction
  · intro h
    obtain ⟨result, heq⟩ := solve_complete hn U B hU hUB A b hA hb h
    simp only [feasible, heq]

end MWIS.IntegerFeasibilitySolver
end
