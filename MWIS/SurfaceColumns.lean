module

public import MWIS.SurfaceComplex
public import MWIS.ColumnEncoding
public import MWIS.Decomposition

/-!
# Signed-stub columns from the supplied embedding

The actual even-face incidence matrix has column norm at most two because
every edge has two genuine sides. Converting these columns to signed stubs
gives precisely the zero-, one-, or two-port data used by the signed cover.
No matrix representation or bound is supplied as an additional hypothesis.

Prepared 2026-10-23.
-/

@[expose] public section

namespace MWIS.SurfaceComplex

open scoped BigOperators
open EmbeddingFaces EmbeddedReduction Walks

variable {V E F : Type*} {left right : E → V}
    [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]
    (M : CellularEmbedding left right F)

/-- The signed-stub columns constructed from the actual even facial rows. -/
noncomputable def columns : E → Column (Faces.EvenFaces M.faces) :=
  fun e => ColumnEncoding.columnOfVector (fun f => Faces.integerMatrix M.faces f e)

/-- The representation preserves every integral matrix coefficient exactly. -/
theorem columns_exact (e : E) (f : Faces.EvenFaces M.faces) :
    columnVector (columns M e) f = Faces.integerMatrix M.faces f e :=
  ColumnEncoding.columnOfVector_spec (fun f => Faces.integerMatrix M.faces f e)
    (Faces.column_natAbs_sum_le_two M.faces M.twoSides e) f

/-- The actual face map is exactly the balance equation of the constructed columns. -/
theorem boundary_eq_columns (y : E → ℤ) (f : Faces.EvenFaces M.faces) :
    faceBoundary left right M.faces y f = ∑ e, columnVector (columns M e) f * y e := by
  simp only [columns_exact]
  rfl

/-- Integral nonnegative even-face cycles are precisely signed-stub flows. -/
theorem flow_iff_cycle (y : E → ℕ) :
    (∀ f, (∑ e, columnVector (columns M e) f * (y e : ℤ)) = 0) ↔
      faceBoundary left right M.faces (fun e => (y e : ℤ)) = 0 := by
  constructor
  · intro h
    ext f
    rw [boundary_eq_columns]
    exact h f
  · intro h f
    rw [← boundary_eq_columns]
    exact congrFun h f

/-- Both the concrete column presentation and the parameter bound are derived
from the given connected nonbipartite cellular embedding. -/
theorem exists_bounded_columns [Fintype V] [DecidableEq V]
    (hc : Incidence.Connected left right) (hnb : ¬ Incidence.Bipartite left right) :
    ∃ C : E → Column (Faces.EvenFaces M.faces),
      (∀ e f, columnVector (C e) f = Faces.integerMatrix M.faces f e) ∧
      coordinateCount M ≤ M.eulerGenus + oddFaceCount M :=
  ⟨columns M, columns_exact M, coordinateCount_le_parameter left right M hc hnb⟩

end MWIS.SurfaceComplex
