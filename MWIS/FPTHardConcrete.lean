module

public import MWIS.TreeCotreeFPT
public import MWIS.GenericSolve
public import MWIS.FunCoordinatesNetwork
public import MWIS.FunNetworkEncode

/-!
# The concrete fixed-parameter hard function

`fptHard` runs the finite-group network procedure `FPTHard.fptHardWith` on the tree–cotree
coordinates `TreeCotree.faceCoordinates` of the computed face columns. It is a correct hard
function in the sense of `MWIS.Generic.HardCorrect`. This file also collects the size bounds
of the coordinates and states that the `Fun` program `FunCoordinates.coordFn` computes the
coordinate tables of the face columns from their integer codes, at a cost bounded by an explicit
polynomial in the numbers of edges, vertices and face rows.
-/

@[expose] public section

namespace MWIS.FPTHardConcrete

open MWIS.Generic EmbeddingFaces

/-- The fixed-parameter hard function. -/
def fptHard : HardFn := fun {_ _} {left right} R w root =>
  FPTHard.fptHardWith (TreeCotree.faceCoordinates left right R root) R w root

/-- **The fixed-parameter hard function is correct.** -/
theorem fptHard_correct : HardCorrect fptHard := fun R w root hc hnb hw ho =>
  FPTHard.fptHardWith_correct _ R w root hc hnb hw ho
    (TreeCotree.faceCoordinates_valid R root hc hnb)

variable {n m : ℕ} {left right : Fin m → Fin n}

/-- The size bounds of the tree–cotree coordinates: the rank is at most the number of XP's
global rows and at most the number of edges, every free coefficient of a unit edge vector is
at most `4n` in absolute value and every parity coefficient at most `2n`. -/
theorem coordinates_bounds (R : Ribbon left right) (root : Fin n)
    (hc : Incidence.Connected left right) (hn : ¬ Incidence.Bipartite left right) :
    (TreeCotree.faceCoordinates left right R root).rank ≤
        (ComputedEmbeddedMatrices.globalRows R).length ∧
      (TreeCotree.faceCoordinates left right R root).rank ≤ m ∧
      (∀ e i, |(TreeCotree.faceCoordinates left right R root).free (Pi.single e 1) i| ≤ 4 * n) ∧
      (∀ e, |TreeCotree.parityRow left right (FPTHard.faceColumns R) root (Pi.single e 1)| ≤
        2 * n) :=
  ⟨TreeCotree.faceCoordinates_rank_le R root hc hn, TreeCotree.rank_le,
    fun e i => TreeCotree.faceCoordinates_free_abs R root e i,
    fun e => TreeCotree.parityRow_single_abs e⟩

/-- The column codes of the coordinate program are the column codes of the network
program. -/
theorem columnCodeC_eq {f : ℕ} (col : Walks.Column (Fin f)) :
    FunCoordinates.columnCodeC col = FunNetwork.columnCode col := by
  cases col <;> rfl

/-- **The coordinate program computes the coordinate tables of the face columns.** Its
input is the list of endpoint pairs of the edges, the network column codes of the face
columns, the vertex count, the number of face rows and the root. -/
theorem coordFn_faceColumns (R : Ribbon left right) (root : Fin n) :
    FunCoordinates.coordFn.apply (FunCoordinates.edgeList left right,
      (List.ofFn fun e => FunNetwork.columnCode (FPTHard.faceColumns R e),
        ((n : ℤ), (((R.evenRootIndices (Flag.canonicalOrder m)).length : ℤ),
          ((root : ℕ) : ℤ))))) =
      (((TreeCotree.faceCoordinates left right R root).rank : ℤ),
        List.ofFn (FunCoordinates.coordRow left right (FPTHard.faceColumns R) root)) := by
  have h : (List.ofFn fun e => FunNetwork.columnCode (FPTHard.faceColumns R e)) =
      FunCoordinates.colList (FPTHard.faceColumns R) := by
    simp only [FunCoordinates.colList, columnCodeC_eq]
  rw [h]
  exact FunCoordinates.coordFn_tables left right (FPTHard.faceColumns R) root

/-- **The coordinate program runs in polynomial time on the face columns:** at most
`17000 (m + n + f + 5)^5` steps, where `f` is the number of face rows. -/
theorem coordFn_faceColumns_cost (R : Ribbon left right) (root : Fin n) :
    FunCoordinates.coordFn.costAt (FunCoordinates.edgeList left right,
      (List.ofFn fun e => FunNetwork.columnCode (FPTHard.faceColumns R e),
        ((n : ℤ), (((R.evenRootIndices (Flag.canonicalOrder m)).length : ℤ),
          ((root : ℕ) : ℤ))))) ≤
      17000 * (m + n + (R.evenRootIndices (Flag.canonicalOrder m)).length + 5) ^ 5 := by
  have h : (List.ofFn fun e => FunNetwork.columnCode (FPTHard.faceColumns R e)) =
      FunCoordinates.colList (FPTHard.faceColumns R) := by
    simp only [FunCoordinates.colList, columnCodeC_eq]
  rw [h]
  exact FunCoordinates.coordFn_cost left right (FPTHard.faceColumns R) root

/-- **The coordinate parts of the network input.** On the parser output (endpoint pairs and
network column codes of the face columns, in edge order) the program `netCoordFn` returns
the rank of the tree–cotree coordinates and, per edge, the free coordinates and the residue
code of the unit edge vector, as in `FunNetwork.edgeInput`. -/
theorem netCoordFn_faceColumns (R : Ribbon left right) (root : Fin n) :
    FunCoordinates.netCoordFn.apply
      ((List.finRange m).map (fun e => (((left e : ℕ) : ℤ), ((right e : ℕ) : ℤ))),
        ((List.finRange m).map (fun e => FunNetwork.columnCode (FPTHard.faceColumns R e)),
          ((n : ℤ), (((R.evenRootIndices (Flag.canonicalOrder m)).length : ℤ),
            ((root : ℕ) : ℤ))))) =
      (((TreeCotree.faceCoordinates left right R root).rank : ℤ), List.ofFn fun e =>
        (List.ofFn fun d => (TreeCotree.faceCoordinates left right R root).free (Pi.single e 1) d,
          FunNetwork.residueCode
            ((TreeCotree.faceCoordinates left right R root).residue (Pi.single e 1)))) :=
  FunCoordinates.netCoordFn_coordinates left right (FPTHard.faceColumns R) root

/-- The program `netCoordFn` takes at most `17100 (m + n + f + 5)^5` steps on the parser
output, where `f` is the number of face rows. -/
theorem netCoordFn_faceColumns_cost (R : Ribbon left right) (root : Fin n) :
    FunCoordinates.netCoordFn.costAt
      ((List.finRange m).map (fun e => (((left e : ℕ) : ℤ), ((right e : ℕ) : ℤ))),
        ((List.finRange m).map (fun e => FunNetwork.columnCode (FPTHard.faceColumns R e)),
          ((n : ℤ), (((R.evenRootIndices (Flag.canonicalOrder m)).length : ℤ),
            ((root : ℕ) : ℤ))))) ≤
      17100 * (m + n + (R.evenRootIndices (Flag.canonicalOrder m)).length + 5) ^ 5 :=
  FunCoordinates.netCoordFn_cost left right (FPTHard.faceColumns R) root

end MWIS.FPTHardConcrete

end
