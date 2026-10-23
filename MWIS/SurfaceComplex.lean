module

public import MWIS.EmbeddedDimensions
public import MWIS.DrawingParameters
public import Mathlib.Algebra.Group.Hom.Basic

/-!
# The integral even-face complex of the supplied embedding

The actual unsigned vertex-incidence map and alternating even-face map form
an integral chain complex. The all-ones edge vector is a cycle. Ordinary
rational rank bounds control the complementary coordinates directly by Euler
genus plus the odd-face count, including drawings obtained by deletion.

Prepared 2026-10-23.
-/

@[expose] public section

namespace MWIS.SurfaceComplex

open scoped BigOperators
open EmbeddingFaces EmbeddedReduction

variable {V E F : Type*} (left right : E → V)

/-- The actual unsigned incidence of integer vertex coefficients. -/
def vertexBoundary : (V → ℤ) →+ (E → ℤ) where
  toFun x e := x (left e) + x (right e)
  map_zero' := by ext e; simp
  map_add' := by intro x y; ext e; simp; ring

variable [Fintype E] [DecidableEq E]

/-- The additive map defined by the alternating rows of actual even faces. -/
def faceBoundary (faces : F → Faces.Face left right) :
    (E → ℤ) →+ (Faces.EvenFaces faces → ℤ) where
  toFun y f := ∑ e, Faces.integerMatrix faces f e * y e
  map_zero' := by ext f; simp
  map_add' := by intro x y; ext f; simp [mul_add, Finset.sum_add_distrib]

/-- An actual even facial walk annihilates every integral unsigned vertex vector. -/
theorem boundary_annihilates (faces : F → Faces.Face left right) (x : V → ℤ) :
    faceBoundary left right faces (vertexBoundary left right x) = 0 := by
  ext f
  have h := Faces.Boundary.row_annihilates (faces f.val).boundary f.property
    (fun v => (x v : ℚ))
  change (∑ e, (faces f.val).boundary.row e * (x (left e) + x (right e))) = 0
  exact_mod_cast h

/-- The all-ones vector is a cycle because every selected facial length is even. -/
theorem ones_cycle (faces : F → Faces.Face left right) :
    faceBoundary left right faces (fun _ => 1) = 0 := by
  ext f
  simpa [faceBoundary, Faces.integerMatrix] using
    Faces.Boundary.row_sum_zero (faces f.val).boundary f.property

/-- Every integral vertex boundary belongs to the kernel of the face map. -/
theorem range_le_kernel (faces : F → Faces.Face left right) :
    AddMonoidHom.range (vertexBoundary left right) ≤
      AddMonoidHom.ker (faceBoundary left right faces) := by
  rintro y ⟨x, rfl⟩
  exact boundary_annihilates left right faces x

omit [Fintype E] [DecidableEq E] in
/-- Twice the all-ones vector is the unsigned boundary of all vertex ones. -/
theorem two_ones_boundary :
    vertexBoundary left right (fun _ => 1) = 2 • (fun _ : E => (1 : ℤ)) := by
  ext e
  simp [vertexBoundary]

/-- Nonnegative shifts by twice the all-ones vector preserve the face equations. -/
theorem shifted_cycle (faces : F → Faces.Face left right) (y : E → ℤ)
    (hy : faceBoundary left right faces y = 0) (t : ℤ) :
    faceBoundary left right faces (y + t • vertexBoundary left right (fun _ => 1)) = 0 := by
  rw [map_add, map_zsmul, boundary_annihilates, hy, zsmul_zero, add_zero]

section Rank

variable [Fintype V] [Fintype F] [DecidableEq V] [DecidableEq F]
    (M : CellularEmbedding left right F)

/-- The even-face quotient coordinate dimension is bounded directly by genus
plus odd faces. No modification of the original face collection is required. -/
theorem coordinateCount_le_parameter (hc : Incidence.Connected left right)
    (hnb : ¬ Incidence.Bipartite left right) :
    coordinateCount M ≤ M.eulerGenus + oddFaceCount M :=
  (coordinateCount_le_exponent M hc hnb).trans
    (Parameters.exponent_le_parameter _ _)

omit [DecidableEq F] in
/-- The rational incidence image and even-face row rank leave exactly the
stated number of supplementary coordinates. -/
theorem coordinateCount_exact (hc : Incidence.Connected left right)
    (hnb : ¬ Incidence.Bipartite left right) :
    coordinateCount M + (Faces.matrix M.faces).rank + Fintype.card V =
      Fintype.card E := coordinateCount_identity M hc hnb

/-- Each capped connected retained component has its own parameter bounded
by the genus and odd-region count of the supplied drawing. -/
theorem retained_coordinateCount_bound (g h : E → Prop)
    [DecidablePred g] [DecidablePred h] (hne : Nonempty {e : E // h e})
    (hsub : ∀ e, h e → g e)
    (hc : Incidence.Connected left right)
    (hcH : Incidence.Connected (Ribbon.activeLeft (left := left) (right := right) h)
      (Ribbon.activeRight h))
    (hnbH : ¬ Incidence.Bipartite
      (Ribbon.activeLeft (left := left) (right := right) h) (Ribbon.activeRight h)) :
    coordinateCount (M.cappedDeletion h hne) ≤ M.eulerGenus + M.sides.oddRegionCount g := by
  classical
  have hp := M.drawing_parameter_mono g h hne hsub hc hcH
  exact (coordinateCount_le_parameter _ _ (M.cappedDeletion h hne) hcH hnbH).trans hp.2

end Rank

end MWIS.SurfaceComplex
