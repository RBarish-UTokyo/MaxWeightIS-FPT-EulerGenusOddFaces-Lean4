module

public import MWIS.TreeCotree
public import MWIS.FPTHard
public import MWIS.HomologyRank

/-!
# Tree–cotree coordinates for the fixed-parameter hard solver

The computed tree–cotree coordinates are packaged as `FPTHard.CoordinateData` and shown
to be valid for every signed column family, in particular for the computed face columns of
a connected nonbipartite ribbon. Their free rank is at most the number of global rows
`ComputedEmbeddedMatrices.globalRows R`, to which XP's parameter bounds apply, and every
free coefficient is at most `4n` in absolute value.
-/

@[expose] public section

namespace MWIS.TreeCotree

open EmbeddingFaces CycleQuotient

variable {f m n : ℕ} (left right : Fin m → Fin n)

/-- The computed coordinate data of a column family. -/
def coordinateData (C : Fin m → Walks.Column (Fin f)) (root : Fin n) : FPTHard.CoordinateData m where
  rank := rank left right C root
  free := freeMap left right C root
  residue := residueLabel left right C root

/-- The computed coordinates are valid for every column family. -/
theorem coordinateData_valid (C : Fin m → Walks.Column (Fin f)) (root : Fin n)
    (hBA : ∀ z, FPTHard.columnHom C (IncidenceSplit.incidence left right z) = 0)
    (hB1 : FPTHard.columnHom C (fun _ => 1) = 0)
    (hc : Incidence.Connected left right) (hn : ¬ Incidence.Bipartite left right) :
    (coordinateData left right C root).Valid left right C hBA hB1 :=
  exists_coordinates (FPTHard.columnHom C) hBA hB1 (fun _ _ => rfl) hc hn

/-- The tree–cotree coordinates of the computed face columns of a ribbon. -/
def faceCoordinates (R : Ribbon left right) (root : Fin n) : FPTHard.CoordinateData m :=
  coordinateData left right (FPTHard.faceColumns R) root

variable {left right}

theorem faceCoordinates_valid (R : Ribbon left right) (root : Fin n)
    (hc : Incidence.Connected left right) (hn : ¬ Incidence.Bipartite left right) :
    ∀ hBA hB1, (faceCoordinates left right R root).Valid left right (FPTHard.faceColumns R)
      hBA hB1 :=
  fun hBA hB1 => coordinateData_valid left right _ root hBA hB1 hc hn

/-- Every free coefficient is at most `4n` in absolute value. -/
theorem faceCoordinates_free_abs (R : Ribbon left right) (root : Fin n) (e : Fin m)
    (i : Fin (faceCoordinates left right R root).rank) :
    |(faceCoordinates left right R root).free (Pi.single e 1) i| ≤ 4 * n :=
  freeMap_single_abs e i

/-- The free rank is at most the number of XP's global rows. -/
theorem faceCoordinates_rank_le (R : Ribbon left right) (root : Fin n)
    (hc : Incidence.Connected left right) (hn : ¬ Incidence.Bipartite left right) :
    (faceCoordinates left right R root).rank ≤ (ComputedEmbeddedMatrices.globalRows R).length := by
  have hBA := FPTHard.faceColumns_incidence R hc hn
  have hB1 := FPTHard.faceColumns_one R hc hn
  obtain ⟨e, -, -, -⟩ := coordinateData_valid left right (FPTHard.faceColumns R) root hBA hB1 hc hn
  let M : Matrix (R.EvenRowIndex (Flag.canonicalOrder m)) (Fin m) ℚ :=
    fun r e => (R.computedIntegerMatrix (Flag.canonicalOrder m) r e : ℚ)
  have hcompat : ∀ y : Fin m → ℤ, FPTHard.columnHom (FPTHard.faceColumns R) y = 0 →
      M.mulVecLin (fun e => (y e : ℚ)) = 0 := by
    intro y hy
    funext r
    have h := congrFun hy r
    rw [FPTHard.columnHom_apply, Pi.zero_apply] at h
    have h2 : ∀ e, Walks.columnVector (FPTHard.faceColumns R e) r =
        R.computedIntegerMatrix (Flag.canonicalOrder m) r e :=
      fun e => R.computedColumn_spec _ Flag.mem_canonicalOrder e r
    simp only [h2] at h
    change ∑ e, M r e * (y e : ℚ) = 0
    simp only [M]
    exact_mod_cast h
  have hr := HomologyRank.free_rank_le_rational_codimension left right
    (FPTHard.columnHom (FPTHard.faceColumns R)) hBA hc hn M.mulVecLin hcompat e
  have hnull := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  rw [Module.finrank_fin_fun] at hnull
  have hrank : Module.finrank ℚ (LinearMap.range M.mulVecLin) =
      Module.finrank ℚ (RationalElimination.listSpan (ComputedEmbeddedMatrices.localRows R)) := by
    have hset : Set.range M.row = {v | v ∈ ComputedEmbeddedMatrices.localRows R} := by
      ext v
      simp only [Set.mem_range, Set.mem_setOf_eq, ComputedEmbeddedMatrices.localRows,
        List.mem_ofFn, Matrix.row, M]
    change M.rank = Module.finrank ℚ
      (Submodule.span ℚ {v | v ∈ ComputedEmbeddedMatrices.localRows R})
    rw [Matrix.rank_eq_finrank_span_row, hset]
  have hlen := (ComputedEmbeddedMatrices.globalRows_spec R hc hn).2.1
  simp only [Fintype.card_fin] at hr
  have hr' : rank left right (FPTHard.faceColumns R) root + n ≤
      Module.finrank ℚ (LinearMap.ker M.mulVecLin) := hr
  change rank left right (FPTHard.faceColumns R) root ≤ _
  omega

end MWIS.TreeCotree

end
