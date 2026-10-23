module

public import MWIS.FPTHardNetwork
public import MWIS.ExecutableReduction

/-!
# The fixed-parameter hard-component output for an embedded component

For a connected nonbipartite component given by a ribbon, the facial columns are
the computed even-face columns `R.computedColumn (Flag.canonicalOrder m)`, the
natural edge costs are XP's computed integer costs
`IntegerEdgeCosts.integerCost`, and the odd row is `ExecutableReduction.parityRow`.
These are exactly the data used by XP's hard solver
`ExecutableReduction.hardSolve`; only the expanded search is replaced by the
finite-group network LP of `MWIS.FPTHard` for given coordinate data.

`fptHardWith_correct` is the analogue of `ExecutableReduction.hardSolve_correct`:
for connected, nonbipartite, all-half optimal instances with nonnegative weights
and valid coordinate data, the output is independent and maximum.

Prepared 2026-10-23.
-/

@[expose] public section

namespace MWIS.FPTHard

open scoped BigOperators
open EmbeddingFaces Matrix

/-! ## Facial equations from a spanning row family -/

section Span

variable {Row : Type*} [Fintype Row] [DecidableEq Row] {n m : ℕ}
  (left right : Fin m → Fin n)

/-- If the facial rows lie in the left kernel of unsigned incidence, the
facial homomorphism annihilates every incidence vector. -/
theorem columnHom_incidence_of_span (C : Fin m → Walks.Column Row) (S : Set (Fin m → ℚ))
    (hspan : Submodule.span ℚ (Set.range (Reduction.localMatrix C) ∪ S) =
      LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin) :
    ∀ z, columnHom C (IncidenceSplit.incidence left right z) = 0 := by
  intro z
  funext i
  have hx : Reduction.localMatrix C i ∈
      LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin := by
    rw [← hspan]
    exact Submodule.subset_span (Or.inl ⟨i, rfl⟩)
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_transpose] at hx
  have hq : ((columnHom C (IncidenceSplit.incidence left right z) i : ℤ) : ℚ) = 0 := by
    have he : ((columnHom C (IncidenceSplit.incidence left right z) i : ℤ) : ℚ) =
        Reduction.localMatrix C i ⬝ᵥ
          (Incidence.unsigned left right *ᵥ fun v => (z v : ℚ)) := by
      simp [columnHom_apply, IncidenceSplit.incidence, dotProduct, Reduction.localMatrix]
    rw [he, Matrix.dotProduct_mulVec, hx, zero_dotProduct]
  simpa using hq

/-- The facial homomorphism annihilates the all-ones vector. -/
theorem columnHom_one_of_incidence (C : Fin m → Walks.Column Row)
    (hBA : ∀ z, columnHom C (IncidenceSplit.incidence left right z) = 0) :
    columnHom C (fun _ => 1) = 0 := by
  funext i
  have h := congrFun (hBA (fun _ => 1)) i
  simp only [columnHom_apply, IncidenceSplit.incidence, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk, Pi.zero_apply] at h ⊢
  have h2 : (∑ e, Walks.columnVector (C e) i * (1 + 1)) =
      2 * ∑ e, Walks.columnVector (C e) i * 1 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [h2] at h
  omega

end Span

/-! ## Cost scaling -/

section Scaling

variable {n m : ℕ} (left right : Fin m → Fin n)

theorem setWeight_smul (k : ℚ) (cost : Fin m → ℚ) (I : Finset (Fin n)) :
    Slack.setWeight left right (fun e => k * cost e) I =
      k * Slack.setWeight left right cost I := by
  rw [Slack.set_weight_incidence, Slack.set_weight_incidence]
  unfold Slack.edgeObjective
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  ring

end Scaling

/-! ## The embedded component -/

variable {n m : ℕ} {left right : Fin m → Fin n}

/-- The computed even-face columns of a ribbon in canonical flag order. -/
abbrev faceColumns (R : Ribbon left right) :
    Fin m → Walks.Column (R.EvenRowIndex (Flag.canonicalOrder m)) :=
  R.computedColumn (Flag.canonicalOrder m)

/-- XP's computed natural edge costs. -/
def integerCosts (left right : Fin m → Fin n) (weights : Fin n → ℚ) : Fin m → ℕ :=
  IntegerEdgeCosts.integerCost left right (List.finRange m) (List.finRange n) weights

theorem faceColumns_incidence (R : Ribbon left right)
    (hc : Incidence.Connected left right) (hnb : ¬Incidence.Bipartite left right) :
    ∀ z, columnHom (faceColumns R) (IncidenceSplit.incidence left right z) = 0 :=
  columnHom_incidence_of_span left right (faceColumns R) _
    (ComputedEmbeddedMatrices.computed_matrices_spec R hc hnb).2

theorem faceColumns_one (R : Ribbon left right)
    (hc : Incidence.Connected left right) (hnb : ¬Incidence.Bipartite left right) :
    columnHom (faceColumns R) (fun _ => 1) = 0 :=
  columnHom_one_of_incidence left right _ (faceColumns_incidence R hc hnb)

/-- The fixed-parameter hard-component output for given coordinate data. -/
def fptHardWith (D : CoordinateData m) (R : Ribbon left right) (weights : Fin n → ℚ)
    (root : Fin n) : Finset (Fin n) :=
  recoveredSet left right (faceColumns R) D (integerCosts left right weights) root
    (ExecutableReduction.parityRow (left := left) (right := right) root)
    (AlgorithmNetworkEnumeration.rows (faceColumns R) D.rank)
    (AlgorithmNetworkEnumeration.columns (faceColumns R) D.rank)

/-- The natural cost weight is `2D` times the vertex weight. -/
theorem natSetWeight_integerCosts (weights : Fin n → ℚ) (hw : ∀ v, 0 ≤ weights v)
    (ho : Persistence.Optimal (EdgeTransport.Adj left right) weights (fun _ => 1 / 2))
    (J : Finset (Fin n)) :
    (natSetWeight left right (integerCosts left right weights) J : ℚ) =
      (2 * (MaxFlowPreprocessing.denominator weights : ℚ)) * Persistence.weight weights J := by
  have hd : (0 : ℚ) < MaxFlowPreprocessing.denominator weights := by
    exact_mod_cast MaxFlowPreprocessing.denominator_positive weights
  have hcost : (fun e => ((integerCosts left right weights e : ℕ) : ℚ)) =
      fun e => (2 * (MaxFlowPreprocessing.denominator weights : ℚ)) *
        EdgeAllocation.computedCost left right (List.finRange m) (List.finRange n) weights e := by
    funext e
    rw [IntegerEdgeCosts.integerCost_exact left right (List.finRange m) (List.finRange n)
      (fun v => List.mem_finRange v) weights hw ho e]
    unfold integerCosts
    field_simp
  have hweights := (EdgeAllocation.computedCost_correct left right (List.finRange m)
    (fun e => List.mem_finRange e) (List.finRange n) (fun v => List.mem_finRange v)
    weights hw ho).2
  rw [← setWeight_natCast, hcost, setWeight_smul, InducedReduction.weight_eq_sum]
  simp only [Slack.setWeight, hweights]

/-- **Correctness of the fixed-parameter hard-component output.** On every
connected nonbipartite all-half component with nonnegative weights, for valid
coordinate data, the output is independent and of maximum weight. -/
theorem fptHardWith_correct (D : CoordinateData m) (R : Ribbon left right)
    (weights : Fin n → ℚ) (root : Fin n)
    (hc : Incidence.Connected left right) (hnb : ¬Incidence.Bipartite left right)
    (hw : ∀ v, 0 ≤ weights v)
    (ho : Persistence.Optimal (EdgeTransport.Adj left right) weights (fun _ => 1 / 2))
    (hD : ∀ hBA hB1, D.Valid left right (faceColumns R) hBA hB1) :
    Persistence.Independent (EdgeTransport.Adj left right) (fptHardWith D R weights root) ∧
      ∀ J, Persistence.Independent (EdgeTransport.Adj left right) J →
        Persistence.weight weights J ≤
          Persistence.weight weights (fptHardWith D R weights root) := by
  have hBA := faceColumns_incidence R hc hnb
  have hB1 := faceColumns_one R hc hnb
  have hπ : IntegerSlacks.OddRow left right root
      (ExecutableReduction.parityRow (left := left) (right := right) root) :=
    ComputedOddRow.oddRow_correct left right (List.finRange m) (fun e => List.mem_finRange e)
      (List.finRange n) (fun v => List.mem_finRange v) root hc hnb
  obtain ⟨hI, hmax⟩ := recoveredSet_correct left right (faceColumns R) hBA hB1 D (hD hBA hB1)
    (integerCosts left right weights) root hc _ hπ
    (AlgorithmNetworkEnumeration.rows (faceColumns R) D.rank)
    (AlgorithmNetworkEnumeration.columns (faceColumns R) D.rank)
  refine ⟨(OriginalReduction.independent_iff _).mp hI, ?_⟩
  intro J hJ
  have h := hmax J ((OriginalReduction.independent_iff _).mpr hJ)
  have hq : (natSetWeight left right (integerCosts left right weights) J : ℚ) ≤
      natSetWeight left right (integerCosts left right weights)
        (fptHardWith D R weights root) := by exact_mod_cast h
  rw [natSetWeight_integerCosts weights hw ho, natSetWeight_integerCosts weights hw ho] at hq
  have hd : (0 : ℚ) < 2 * (MaxFlowPreprocessing.denominator weights : ℚ) := by
    have := MaxFlowPreprocessing.denominator_positive weights
    positivity
  exact le_of_mul_le_mul_left hq hd

end MWIS.FPTHard

end
