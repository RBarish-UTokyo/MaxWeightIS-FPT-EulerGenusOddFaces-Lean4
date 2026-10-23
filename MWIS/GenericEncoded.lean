module

public import MWIS.GenericSolve
public import MWIS.AllHalfEncoded

/-!
# Encoded assembly of the all-half components, for a parametric hard function

This is `AllHalfEncoded` with the component solver `Generic.connectedSolve hs`.
For each computed root the local output is read back to original vertex words,
the outputs of all roots are collected by a left fold, and the range words that
occur in the collection are exactly `setWords` of `Generic.allHalfSolve hs`.
The hard-function-independent lemmas of `AllHalfEncoded` are reused.
-/

@[expose] public section

namespace MWIS.GenericEncoded

open MWIS.EfficientSearch MWIS.RibbonTable MWIS.RegisterWordFilter
open MWIS.ComputedComponents MWIS.EmbeddingFaces
open MWIS.AllHalfEncoded (localWeights mem_selectFilter selectFilter_length_le)

variable (hs : Generic.HardFn)
variable {n m : ℕ} {left right : Fin m → Fin n}

/-- The local solution of the component of `root`. -/
def localSolve (R : Ribbon left right) (w : Fin n → ℚ) (root : Fin n) :
    Finset (Fin (vertices left right root).length) :=
  Generic.connectedSolve hs (componentRibbon left right root R) (localWeights left right w root)

/-- On a computed component the solver is the branch at the canonical root. -/
theorem localSolve_eq (R : Ribbon left right) (w : Fin n → ℚ) (root : Fin n) :
    localSolve hs R w root =
      Generic.halfSolve hs (componentRibbon left right root R)
        (localWeights left right w root) ⟨0, vertices_length_pos left right root⟩ := by
  rw [localSolve, Generic.connectedSolve,
    dite_eq_left_of_eq_true (eq_true (vertices_length_pos left right root))]

/-- Words of the original vertices selected in the component of `root`. -/
def globalWords (W : ℕ) (R : Ribbon left right) (w : Fin n → ℚ) (root : Fin n) :
    List (Bits W) :=
  selectFilter (rangeWords W (vertices left right root).length)
    ((vertices left right root).map (fun u => word W u.val))
    (GraphReachEncoded.setWords W (localSolve hs R w root))

theorem globalWords_length_le (W : ℕ) (R : Ribbon left right) (w : Fin n → ℚ) (root : Fin n) :
    (globalWords hs W R w root).length ≤ n := by
  refine (selectFilter_length_le _ _ _).trans ?_
  simpa using vertices_length_le left right root

theorem mem_globalWords {W : ℕ} (hn : n < 2 ^ W) (R : Ribbon left right) (w : Fin n → ℚ)
    (root v : Fin n) :
    word W v.val ∈ globalWords hs W R w root ↔
      ∃ i ∈ localSolve hs R w root, (vertexEquiv left right root i).val = v := by
  rw [globalWords, mem_selectFilter hn _ (lt_of_le_of_lt (vertices_length_le left right root) hn)]
  rfl

/-- The fold step: prepend the reversed words of one component. -/
def step (W : ℕ) (R : Ribbon left right) (w : Fin n → ℚ) (acc : List (Bits W)) (root : Fin n) :
    List (Bits W) :=
  (globalWords hs W R w root).reverse ++ acc

/-- The collected words of a list of roots. -/
def collect (W : ℕ) (R : Ribbon left right) (w : Fin n → ℚ) (roots : List (Fin n)) :
    List (Bits W) :=
  roots.foldl (step hs W R w) []

theorem mem_foldl_step (W : ℕ) (R : Ribbon left right) (w : Fin n → ℚ) (roots : List (Fin n))
    (acc : List (Bits W)) (x : Bits W) :
    x ∈ roots.foldl (step hs W R w) acc ↔ x ∈ acc ∨ ∃ r ∈ roots, x ∈ globalWords hs W R w r := by
  induction roots generalizing acc with
  | nil => simp
  | cons r rs ih =>
    rw [List.foldl_cons, ih]
    simp only [step, List.mem_append, List.mem_reverse, List.mem_cons, exists_eq_or_imp]
    tauto

theorem mem_collect (W : ℕ) (R : Ribbon left right) (w : Fin n → ℚ) (roots : List (Fin n))
    (x : Bits W) :
    x ∈ collect hs W R w roots ↔ ∃ r ∈ roots, x ∈ globalWords hs W R w r := by
  rw [collect, mem_foldl_step]
  simp

theorem collect_length_le (W : ℕ) (R : Ribbon left right) (w : Fin n → ℚ)
    (roots : List (Fin n)) : (collect hs W R w roots).length ≤ n * roots.length := by
  have key : ∀ (rs : List (Fin n)) (acc : List (Bits W)),
      (rs.foldl (step hs W R w) acc).length ≤ acc.length + n * rs.length := by
    intro rs
    induction rs with
    | nil => simp
    | cons r rs ih =>
      intro acc
      rw [List.foldl_cons]
      refine (ih _).trans ?_
      simp only [step, List.length_append, List.length_reverse, List.length_cons]
      have := globalWords_length_le hs W R w r
      nlinarith
  simpa [collect] using key roots []

/-- A vertex belongs to the assembled all-half output exactly when its word
is collected from the component of some computed root. -/
theorem mem_allHalfSolve_iff {W : ℕ} (hn : n < 2 ^ W) (R : Ribbon left right) (w : Fin n → ℚ)
    (v : Fin n) :
    v ∈ Generic.allHalfSolve hs R w ↔ word W v.val ∈ collect hs W R w (roots left right) := by
  rw [mem_collect]
  simp only [Generic.allHalfSolve, ComponentAssembly.assemble, Finset.mem_filter,
    Finset.mem_univ, true_and]
  have hfix := representative_idempotent left right v
  simp only [Generic.fiberSolve, dite_eq_left_of_eq_true (eq_true hfix),
    GraphRelabeling.mem_mapSet]
  constructor
  · intro hv
    refine ⟨representative left right v, representative_mem_roots left right v, ?_⟩
    rw [mem_globalWords hs hn]
    refine ⟨_, hv, ?_⟩
    rw [← representativeFiberEquiv_val left right _ hfix, Equiv.apply_symm_apply]
  · rintro ⟨r, hr, hx⟩
    rw [mem_globalWords hs hn] at hx
    obtain ⟨i, hi, hiv⟩ := hx
    have hrep : representative left right v = r := by
      have hc := (vertexEquiv left right r i).property
      rw [hiv, Incidence.componentOf_eq_iff] at hc
      rw [representative_eq_of_reachable left right hc]
      exact (mem_roots left right r).mp hr
    subst hrep
    have he : (representativeFiberEquiv left right _ hfix).symm ⟨v, rfl⟩ = i := by
      rw [Equiv.symm_apply_eq]
      exact Subtype.ext hiv.symm
    rw [he]
    exact hi

/-- The range words that occur in the collection are the words of the
assembled all-half output, in increasing order. -/
theorem filter_collect (W : ℕ) (hn : n < 2 ^ W) (R : Ribbon left right) (w : Fin n → ℚ) :
    (rangeWords W n).filter (fun x => decide (x ∈ collect hs W R w (roots left right))) =
      GraphReachEncoded.setWords W (Generic.allHalfSolve hs R w) := by
  rw [← AllHalfEncoded.rangeWords_eq, GraphReachEncoded.filter_rangeWords, GraphReachEncoded.setWords]
  congr 1
  apply List.filter_congr
  intro v _
  rw [AllHalfEncoded.word_eq]
  exact decide_eq_decide.mpr (mem_allHalfSolve_iff hs hn R w v).symm

end MWIS.GenericEncoded

end
