module

public import MWIS.SpecBridge

/-!
# The deterministic solver with a parametric hard-component function

This is the solver `ExecutableMIS.solve` with the solver of connected
nonbipartite all-half components replaced by an arbitrary function `hs`. The
remaining stages are those of `ExecutableMIS.solve`: truncation of negative
weights, the maximum-flow half-integral point, the induced residual ribbon,
its computed components, the bipartite colour classes, the assembly, the
restoration of fixed vertices and the pruning of negative weights. The output
is a maximum-weight independent set whenever `hs` returns maximum sets on
connected nonbipartite all-half instances with nonnegative weights
(`HardCorrect`). With `hs = ExecutableReduction.hardSolve` this is the XP
solver itself (`solve_hardSolve`).
-/

@[expose] public section

namespace MWIS.Generic

open EmbeddingFaces ComputedComponents Persistence

/-- A solver of single components: a ribbon graph, vertex weights and a root. -/
abbrev HardFn : Type :=
  ∀ {n m : ℕ} {left right : Fin m → Fin n}, Ribbon left right → (Fin n → ℚ) → Fin n →
    Finset (Fin n)

/-- The hard function returns a maximum-weight independent set on every connected
nonbipartite instance whose all-half point is optimal, with nonnegative weights. -/
def HardCorrect (hs : HardFn) : Prop :=
  ∀ {n m : ℕ} {left right : Fin m → Fin n} (R : Ribbon left right) (weights : Fin n → ℚ)
    (root : Fin n), Incidence.Connected left right → ¬ Incidence.Bipartite left right →
    (∀ v, 0 ≤ weights v) → Optimal (EdgeTransport.Adj left right) weights (fun _ => 1 / 2) →
    Independent (EdgeTransport.Adj left right) (hs R weights root) ∧
      ∀ J, Independent (EdgeTransport.Adj left right) J →
        weight weights J ≤ weight weights (hs R weights root)

/-- The XP hard solver, as a hard function. -/
def xpHard : HardFn := fun R weights root => ExecutableReduction.hardSolve R weights root

/-- The XP hard solver is correct. -/
theorem xpHard_correct : HardCorrect xpHard :=
  fun R weights root hc hnb hw ho => ExecutableReduction.hardSolve_correct R weights root hc hnb hw ho

variable (hs : HardFn)
variable {n m : ℕ} {left right : Fin m → Fin n}

/-- Parity detection chooses the hard function or the bipartite colour class. -/
def halfSolve (R : Ribbon left right) (weights : Fin n → ℚ) (root : Fin n) : Finset (Fin n) :=
  if (root, true) ∈ (ComputedOddRow.paritySearch left right (List.finRange m) (List.finRange n) root).seen then
    hs R weights root
  else
    BipartiteRecovery.colorClass
      (BipartiteRecovery.coloring left right (List.finRange m) (List.finRange n) root) false

theorem halfSolve_correct {hs : HardFn} (hcor : HardCorrect hs)
    (R : Ribbon left right) (weights : Fin n → ℚ) (root : Fin n)
    (hc : Incidence.Connected left right) (hw : ∀ v, 0 ≤ weights v)
    (ho : Optimal (EdgeTransport.Adj left right) weights (fun _ => 1 / 2)) :
    Independent (EdgeTransport.Adj left right) (halfSolve hs R weights root) ∧
      ∀ J, Independent (EdgeTransport.Adj left right) J →
        weight weights J ≤ weight weights (halfSolve hs R weights root) := by
  unfold halfSolve
  split_ifs with hseen
  · exact hcor R weights root hc
      (ComputedOddRow.nonbipartite_of_seen left right (List.finRange m) (List.finRange n)
        (fun v => List.mem_finRange v) root hseen) hw ho
  · exact BipartiteRecovery.searched_color_maximum left right (List.finRange m)
      (fun e => List.mem_finRange e) (List.finRange n) (fun v => List.mem_finRange v) root hc hseen
      weights ho

/-- The canonical-root solver of a connected component. -/
def connectedSolve (R : Ribbon left right) (weights : Fin n → ℚ) : Finset (Fin n) :=
  if hn : 0 < n then halfSolve hs R weights ⟨0, hn⟩ else ∅

theorem connectedSolve_correct {hs : HardFn} (hcor : HardCorrect hs)
    (R : Ribbon left right) (weights : Fin n → ℚ)
    (hc : Incidence.Connected left right) (hw : ∀ v, 0 ≤ weights v)
    (ho : Optimal (EdgeTransport.Adj left right) weights (fun _ => 1 / 2)) :
    Independent (EdgeTransport.Adj left right) (connectedSolve hs R weights) ∧
      ∀ J, Independent (EdgeTransport.Adj left right) J →
        weight weights J ≤ weight weights (connectedSolve hs R weights) := by
  unfold connectedSolve
  split_ifs with hn
  · exact halfSolve_correct hcor R weights ⟨0, hn⟩ hc hw ho
  · have hz : n = 0 := by omega
    subst n
    constructor
    · intro u; exact Fin.elim0 u
    · intro J _
      have he : J = ∅ := by ext v; exact Fin.elim0 v
      rw [he]

/-- The component solution transported into its representative fiber. -/
def fiberSolve (R : Ribbon left right) (weights : Fin n → ℚ) (root : Fin n) :
    Finset {v : Fin n // representative left right v = root} :=
  if hfix : representative left right root = root then
    GraphRelabeling.mapSet (representativeFiberEquiv left right root hfix)
      (connectedSolve hs (componentRibbon left right root R)
        (fun v => weights (vertexEquiv left right root v).val))
  else ∅

theorem fiberSolve_correct {hs : HardFn} (hcor : HardCorrect hs)
    (R : Ribbon left right) (weights : Fin n → ℚ)
    (hw : ∀ v, 0 ≤ weights v)
    (ho : Optimal (EdgeTransport.Adj left right) weights (fun _ => 1 / 2)) (root : Fin n) :
    Independent (fun u v : {v : Fin n // representative left right v = root} =>
      EdgeTransport.Adj left right u.val v.val) (fiberSolve hs R weights root) ∧
      ∀ J, Independent (fun u v : {v : Fin n // representative left right v = root} =>
          EdgeTransport.Adj left right u.val v.val) J →
        weight (fun v : {v : Fin n // representative left right v = root} => weights v.val) J ≤
          weight (fun v : {v : Fin n // representative left right v = root} => weights v.val)
            (fiberSolve hs R weights root) := by
  unfold fiberSolve
  split_ifs with hfix
  · have hlocal := connectedSolve_correct hcor (componentRibbon left right root R)
      (fun v => weights (vertexEquiv left right root v).val)
      (local_connected left right root) (fun v => hw _) (local_half_optimal left right root weights ho)
    exact GraphRelabeling.maximum_map (representativeFiberEquiv left right root hfix)
      (EdgeTransport.Adj (localLeft left right root) (localRight left right root))
      (fun u v : {v : Fin n // representative left right v = root} =>
        EdgeTransport.Adj left right u.val v.val)
      (representativeFiber_adj left right root hfix)
      (fun v : {v : Fin n // representative left right v = root} => weights v.val)
      _ hlocal.1 hlocal.2
  · have hempty : IsEmpty {v : Fin n // representative left right v = root} := by
      refine ⟨fun v => hfix ?_⟩
      rw [← v.property, representative_idempotent]
    constructor
    · intro u; exact isEmptyElim u
    · intro J _
      have hj : J = ∅ := by ext v; exact isEmptyElim v
      rw [hj]

/-- Solve and assemble the components of an all-half instance. -/
def allHalfSolve (R : Ribbon left right) (weights : Fin n → ℚ) : Finset (Fin n) :=
  ComponentAssembly.assemble (representative left right) (fiberSolve hs R weights)

theorem allHalfSolve_correct {hs : HardFn} (hcor : HardCorrect hs)
    (R : Ribbon left right) (weights : Fin n → ℚ)
    (hw : ∀ v, 0 ≤ weights v)
    (ho : Optimal (EdgeTransport.Adj left right) weights (fun _ => 1 / 2)) :
    Independent (EdgeTransport.Adj left right) (allHalfSolve hs R weights) ∧
      ∀ J, Independent (EdgeTransport.Adj left right) J →
        weight weights J ≤ weight weights (allHalfSolve hs R weights) := by
  have hclosed : ∀ u v, EdgeTransport.Adj left right u v →
      representative left right u = representative left right v := by
    intro u v huv
    apply representative_eq_of_reachable left right
    exact (Incidence.componentOf_eq_iff left right u v).mp
      (ComponentAssembly.component_closed left right u v huv)
  exact ComponentAssembly.assemble_maximum (EdgeTransport.Adj left right)
    (representative left right) hclosed weights (fiberSolve hs R weights)
    (fun root => (fiberSolve_correct hcor R weights hw ho root).1)
    (fun root => (fiberSolve_correct hcor R weights hw ho root).2)

/-- The deterministic weighted independent-set solver with hard function `hs`. -/
def solve (R : Ribbon left right) (weights : Fin n → ℚ) : Finset (Fin n) :=
  let z := OriginalReduction.preprocessingPoint (left := left) (right := right) weights (List.finRange n)
  let keep := fun v => z v = 1 / 2
  let e := ComputedInduced.vertexEquiv keep
  let H := ComputedInduced.ribbon left right keep R
  let w := fun v => NegativeWeights.nonnegative weights (e v).val
  let J := allHalfSolve hs H w
  let lifted := InducedReduction.lift (GraphRelabeling.mapSet e J)
  NegativeWeights.prune weights (replacement z lifted)

/-- With the XP hard solver this is the XP solver. -/
theorem solve_xpHard (R : Ribbon left right) (weights : Fin n → ℚ) :
    solve xpHard R weights = ExecutableMIS.solve R weights := rfl

theorem solve_correct {hs : HardFn} (hcor : HardCorrect hs)
    (R : Ribbon left right) (weights : Fin n → ℚ) :
    Independent (EdgeTransport.Adj left right) (solve hs R weights) ∧
      ∀ J, Independent (EdgeTransport.Adj left right) J →
        weight weights J ≤ weight weights (solve hs R weights) := by
  let z := OriginalReduction.preprocessingPoint (left := left) (right := right) weights (List.finRange n)
  let keep := fun v => z v = 1 / 2
  let e := ComputedInduced.vertexEquiv keep
  let H := ComputedInduced.ribbon left right keep R
  let w := fun v => NegativeWeights.nonnegative weights (e v).val
  let J := allHalfSolve hs H w
  have hz := OriginalReduction.preprocessingPoint_correct (left := left) (right := right)
    weights (List.finRange n) (fun v => List.mem_finRange v)
  have hr := InducedReduction.residual_optimal (EdgeTransport.Adj left right)
    (NegativeWeights.nonnegative weights) z hz.2 hz.1
  have hopt := ComputedInduced.half_optimal left right keep (NegativeWeights.nonnegative weights) hr
  have hJ := allHalfSolve_correct hcor H w
    (fun v => NegativeWeights.nonnegative_nonnegative weights _) hopt
  have hmap := GraphRelabeling.maximum_map e
    (EdgeTransport.Adj (ComputedInduced.localLeft left right keep) (ComputedInduced.localRight left right keep))
    (fun u v : {v : Fin n // keep v} => EdgeTransport.Adj left right u.val v.val)
    (ComputedInduced.local_adj left right keep)
    (fun v : {v : Fin n // keep v} => NegativeWeights.nonnegative weights v.val) J hJ.1 hJ.2
  have h := InducedReduction.residual_maximum (EdgeTransport.Adj left right)
    (NegativeWeights.nonnegative weights) z hz.2 hz.1 (GraphRelabeling.mapSet e J) hmap.1 hmap.2
  exact NegativeWeights.optimum_of_truncated (EdgeTransport.Adj left right) weights _ h.1 h.2.2

/-- **Correctness in statement terms.** For a drawing in a closed-surface map, the
solver on the internal ribbon returns a maximum-weight independent set. -/
theorem solve_isMaximum {hs : HardFn} (hcor : HardCorrect hs)
    (A : Spec.Map) (hA : A.IsClosedSurface) (D : Spec.Drawing) (W : D.In A)
    (weights : Fin D.vertices → ℚ) :
    D.IsMaximum weights (solve hs (Spec.Drawing.ribbon hA W) weights) :=
  D.isMaximum_of weights _ (solve_correct hcor _ weights).1 (solve_correct hcor _ weights).2

end MWIS.Generic

end
