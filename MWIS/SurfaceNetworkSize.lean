module

public import MWIS.SurfaceColumns
public import MWIS.FiniteExtension
public import MWIS.DrawingComponents

/-!
# Sizes of actual surface components and their finite-group extensions

Nonempty facial boundary walks and the exact two-side count bound the actual
face types by the number of edges. The explicit signed-cover network therefore
has a quadratic number of arcs per group element. Component counts are bounded
by original vertex counts through the actual component quotient map.

Prepared 2026-10-23.
-/

@[expose] public section

namespace MWIS.SurfaceNetworkSize

open scoped BigOperators
open EmbeddingFaces

/-- Every face consumes at least one of the two sides of an edge. -/
theorem face_card_le_twice_edges {V E F : Type*} [Fintype E] [Fintype F]
    {left right : E → V} (M : CellularEmbedding left right F) :
    Fintype.card F ≤ 2 * Fintype.card E := by
  calc
    Fintype.card F = ∑ _f : F, (1 : ℕ) := by simp
    _ ≤ ∑ f, (M.faces f).boundary.length :=
      Finset.sum_le_sum (fun f _ => M.face_nonempty f)
    _ = _ := M.sides.total_face_length

/-- The actual even-face row type inherits the same incidence bound. -/
theorem even_face_card_le_twice_edges {V E F : Type*} [Fintype E] [Fintype F]
    {left right : E → V} (M : CellularEmbedding left right F) :
    Fintype.card (Faces.EvenFaces M.faces) ≤ 2 * Fintype.card E := by
  classical
  exact (Fintype.card_subtype_le _).trans (face_card_le_twice_edges M)

/-- The actual extension uses at most `(4m+1)(2m)` arcs per group element. -/
theorem extension_arc_card_le {V E F G : Type*}
    [Fintype E] [Fintype F] [Fintype G] [DecidableEq E] [DecidableEq F]
    {left right : E → V} (M : CellularEmbedding left right F) :
    Fintype.card (FiniteExtension.ExtensionArc (SurfaceComplex.columns M) G) ≤
      (4 * Fintype.card E + 1) * (2 * Fintype.card E) * Fintype.card G := by
  have hf := even_face_card_le_twice_edges M
  have hb := FiniteExtension.extension_arc_card_le (G := G) (SurfaceComplex.columns M)
  refine hb.trans ?_
  apply Nat.mul_le_mul_right
  apply Nat.mul_le_mul_right
  omega

/-- The network bound remains uniform under ambient edge and group bounds. -/
theorem extension_arc_card_le_of_bounds {V E F G : Type*}
    [Fintype E] [Fintype F] [Fintype G] [DecidableEq E] [DecidableEq F]
    {left right : E → V} (M : CellularEmbedding left right F) (m q : ℕ)
    (hE : Fintype.card E ≤ m) (hG : Fintype.card G ≤ q) :
    Fintype.card (FiniteExtension.ExtensionArc (SurfaceComplex.columns M) G) ≤
      (4 * m + 1) * (2 * m) * q := by
  refine (extension_arc_card_le (G := G) M).trans ?_
  apply Nat.mul_le_mul _ hG
  apply Nat.mul_le_mul <;> omega

/-- Restricting to retained ambient edge labels never increases the edge bound. -/
theorem retained_extension_arc_card_le {V E F G : Type*}
    [Fintype E] [Fintype F] [Fintype G] [DecidableEq E] [DecidableEq F]
    (keep : E → Prop) [DecidablePred keep]
    {left right : {e : E // keep e} → V} (M : CellularEmbedding left right F)
    (q : ℕ) (hG : Fintype.card G ≤ q) :
    Fintype.card (FiniteExtension.ExtensionArc (SurfaceComplex.columns M) G) ≤
      (4 * Fintype.card E + 1) * (2 * Fintype.card E) * q :=
  extension_arc_card_le_of_bounds M (Fintype.card E) q (Fintype.card_subtype_le keep) hG

/-- The actual graph-component quotient has at most one class per vertex. -/
theorem component_card_le {V E : Type*} [Fintype V]
    (left right : E → V) :
    Fintype.card (Incidence.Component left right) ≤ Fintype.card V := by
  apply Fintype.card_le_of_surjective (Incidence.componentOf left right)
  intro q
  exact ⟨Quotient.out q, Quotient.out_eq q⟩

/-- Any selected collection of components, including the nonbipartite ones,
is bounded by the same original vertex count. -/
theorem selected_component_card_le {V E : Type*} [Fintype V]
    (left right : E → V) (P : Incidence.Component left right → Prop)
    [DecidablePred P] :
    Fintype.card {q : Incidence.Component left right // P q} ≤ Fintype.card V :=
  (Fintype.card_subtype_le P).trans (component_card_le left right)

/-- Actual retained-drawing components are bounded by the original vertex count,
including isolated retained vertices. -/
theorem drawing_part_card_le {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (left right : E → V)
    (g : E → Prop) [DecidablePred g] (keep : V → Prop) [DecidablePred keep] :
    Fintype.card (DrawingComponents.Part left right g keep) ≤ Fintype.card V := by
  have h := component_card_le
    (InducedComponents.edgeLeft (DrawingComponents.graphLeft left g)
      (DrawingComponents.graphRight right g) keep)
    (InducedComponents.edgeRight (DrawingComponents.graphLeft left g)
      (DrawingComponents.graphRight right g) keep)
  exact h.trans (Fintype.card_subtype_le keep)

/-- Any chosen hard retained components satisfy the original vertex-count bound. -/
theorem selected_drawing_part_card_le {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (left right : E → V)
    (g : E → Prop) [DecidablePred g] (keep : V → Prop) [DecidablePred keep]
    (P : DrawingComponents.Part left right g keep → Prop) [DecidablePred P] :
    Fintype.card {q : DrawingComponents.Part left right g keep // P q} ≤ Fintype.card V :=
  (Fintype.card_subtype_le P).trans (drawing_part_card_le left right g keep)

end MWIS.SurfaceNetworkSize

end
