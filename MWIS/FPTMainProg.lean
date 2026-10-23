module

public import MWIS.FPTRunFun
public import MWIS.FPTHardConcrete
public import MWIS.FunNetworkDecode
public import MWIS.FunLPList
public import MWIS.AlgorithmThresholdLP

/-!
# The numerical stage as one `Fun` program

`prog optF` is the five-input `Fun` program of the numerical stage. It

1. parses the face columns, the endpoint pairs, the vertex count, the natural costs
   and the face count from the input trees (`MWIS.FPTTreeParse`);
2. computes the tree–cotree coordinate tables (`FunCoordinates.coordFn`);
3. assembles the per-edge input records of the network program (`inputF`);
4. computes the dense network program (`FunNetwork.networkFn`), the search offset
   `2 · total` and the search width (`offsetFn`, `bitsFn`);
5. runs a dense-program optimizer `optF`;
6. decodes the slack `total - value` (`slackFn`) and writes it as words of width
   `fptWidth n m` (`formatOutput`).

The optimizer is a parameter: `OptSpec optF` says that on the `Fun` encoding of
every dense program it returns `AlgorithmThresholdLP.optimize`.

`prog_denote` proves that, on every instance of the numerical-stage contract, the
denotation is the output tree of the decoded slack of the coordinates
`faceCoords`. This is the denotation half of `FPTRunFun.ProgFunStage`.
-/

@[expose] public section

namespace MWIS.FPTMainProg

open MWIS.Fun MWIS.FunLP MWIS.FPTTrees MWIS.FPTRegister MWIS.FPTTreeParse
open MWIS.FunNetwork (tE tOut tL)

/-! ## The coordinates -/

/-- The tree–cotree coordinates of the face columns. -/
def faceCoords : CoordFn := fun {_ _} {left right} R root =>
  TreeCotree.faceCoordinates left right R root

theorem faceCoords_valid : CoordsValid faceCoords := fun R root hc hnb =>
  TreeCotree.faceCoordinates_valid R root hc hnb

/-! ## The optimizer contract -/

/-- Argument of the optimizer: the encoded dense program, the offset and the width. -/
abbrev OptArg : Ty := .prod tOut (.prod .int .int)

/-- The optimizer computes `AlgorithmThresholdLP.optimize` on every encoded dense
program. -/
def OptSpec (optF : Fn OptArg .int) : Prop :=
  ∀ {M N : ℕ} (P : AlgorithmNetworkEncoding.DenseProgram M N) (offset : ℤ) (b : ℕ),
    optF.apply (FunNetwork.DenseProgram.toFun P, (offset, (b : ℤ))) =
      (AlgorithmThresholdLP.optimize P offset b : ℤ)

/-! ## The stages -/

/-- The five input trees as one value. -/
abbrev Trees5 : Ty := .prod .tree (.prod .tree (.prod .tree (.prod .tree .tree)))

/-- Parsed input: column codes, endpoint pairs, vertex count, costs, face count. -/
abbrev ParsedTy : Ty :=
  .prod (.list (.list .int)) (.prod (.list (.prod .int .int)) (.prod .int (.prod (.list .int) .int)))

/-- Parsed input with the coordinate tables. -/
abbrev S1 : Ty := .prod ParsedTy FunCoordinates.CoordOut

/-- Vertex count, face count, rank and the network input records. -/
abbrev S2 : Ty := .prod .int (.prod .int (.prod .int (.list tE)))

/-- Vertex count, network input records and optimum value. -/
abbrev S3 : Ty := .prod .int (.prod (.list tE) .int)

/-- Parse the five input trees. -/
def parseF : Fn Trees5 ParsedTy :=
  .pair (call parseColumns (.fst v0))
    (.pair (call parseEdges (.fst (.snd v0)))
      (.pair (call (lengthF .tree) (.items (.fst (.snd (.snd v0)))))
        (.pair (call parseWords (.fst (.snd (.snd (.snd v0)))))
          (call parseCount (.snd (.snd (.snd (.snd v0))))))))

/-- Compute the coordinate tables with root `0`. -/
def coordStageF : Fn ParsedTy S1 :=
  .pair v0 (call FunCoordinates.coordFn
    (.pair (.fst (.snd v0)) (.pair (.fst v0) (.pair (.fst (.snd (.snd v0)))
      (.pair (.snd (.snd (.snd (.snd v0)))) (.int 0))))))

/-- One network input record from a column code, a coordinate row and a cost. -/
def edgeRecF : Fn (.prod (.prod (.list .int) FunCoordinates.RowTy) .int) tE :=
  .pair (.fst (.fst v0)) (.pair (.fst (.snd (.fst v0)))
    (.pair (.cons (.fst (.snd (.snd (.snd (.fst v0))))) (.snd (.snd (.snd (.snd (.fst v0))))))
      (.snd v0)))

/-- The network input records of all edges. -/
def inputF : Fn (.prod (.list (.list .int)) (.prod (.list FunCoordinates.RowTy) (.list .int)))
    (.list tE) :=
  call (mapF edgeRecF) (call (zipFn _ .int)
    (.pair (call (zipFn (.list .int) FunCoordinates.RowTy) (.pair (.fst v0) (.fst (.snd v0))))
      (.snd (.snd v0))))

/-- Assemble the network input. -/
def inputStageF : Fn S1 S2 :=
  .pair (.fst (.snd (.snd (.fst v0))))
    (.pair (.snd (.snd (.snd (.snd (.fst v0)))))
      (.pair (.fst (.snd v0))
        (call inputF (.pair (.fst (.fst v0))
          (.pair (.snd (.snd v0)) (.fst (.snd (.snd (.snd (.fst v0))))))))))

/-- The modulus `GroupSize.modulus r` of the free coordinates, as `4r + 2 · ⌊1 / (r + 1)⌋`. -/
def muE {Γ : List Ty} (r : Expr Γ .int) : Expr Γ .int :=
  .arith .add (.arith .mul (.int 4) r)
    (.arith .mul (.int 2) (.arith .div (.int 1) (.arith .add r (.int 1))))

/-- Build and optimize the network program. -/
def optStageF (optF : Fn OptArg .int) : Fn S2 S3 :=
  .pair (.fst v0) (.pair (.snd (.snd (.snd v0)))
    (call optF (.pair
      (call FunNetwork.networkFn (.pair (.fst (.snd v0)) (.pair (.fst (.snd (.snd v0)))
        (.pair (muE (.fst (.snd (.snd v0)))) (.snd (.snd (.snd v0)))))))
      (.pair (call FunNetwork.offsetFn (.snd (.snd (.snd v0))))
        (call FunNetwork.bitsFn (.snd (.snd (.snd v0))))))))

/-- Decode the slack and write the output tree. -/
def finalF : Fn S3 .tree :=
  call formatOutput (.pair
    (.arith .add (.arith .add (.arith .mul (.int 3) (.fst v0))
      (call (lengthF tE) (.fst (.snd v0)))) (.int 4))
    (call FunNetwork.slackFn (.pair (.snd (.snd v0)) (.fst (.snd v0)))))

/-- The numerical stage on the tuple of its input trees. -/
def mainF (optF : Fn OptArg .int) : Fn Trees5 .tree :=
  finalF.comp ((optStageF optF).comp (inputStageF.comp (coordStageF.comp parseF)))

/-- **The numerical-stage program.** -/
def prog (optF : Fn OptArg .int) : Expr [.tree, .tree, .tree, .tree, .tree] .tree :=
  call (mainF optF) (.pair v0 (.pair v1 (.pair v2 (.pair v3 v4))))

/-! ## Denotations of the stages -/

variable {n m : ℕ} {left right : Fin m → Fin n}

/-- The parsed input of an instance. -/
def parsed (_W _c : ℕ) (R : EmbeddingFaces.Ribbon left right) (w : Fin n → ℚ) :
    ParsedTy.denote :=
  ((List.finRange m).map fun e => FunNetwork.columnCode (FPTHard.faceColumns R e),
    ((List.finRange m).map fun e => (((left e : ℕ) : ℤ), ((right e : ℕ) : ℤ)),
      ((n : ℤ), ((List.finRange m).map fun e => (FPTHard.integerCosts left right w e : ℤ),
        (rowCount R : ℤ)))))

/-- The input trees of an instance, as one value. -/
def trees (W c : ℕ) (R : EmbeddingFaces.Ribbon left right) (w : Fin n → ℚ) : Trees5.denote :=
  (columnsTree R, (edgesTree W left right, (wordsTree (RibbonTable.rangeWords W n),
    (costsTree c (FPTHard.integerCosts left right w),
      bitsTree (GraphReachEncoded.word (fptWidth n m) (2 * rowCount R + 1))))))

theorem rowCount_fits (R : EmbeddingFaces.Ribbon left right) :
    2 * rowCount R + 1 < 2 ^ fptWidth n m := by
  have hr : rowCount R ≤ 4 * m := by
    simpa using R.evenRow_count_le (EmbeddingFaces.Flag.canonicalOrder m)
  have := fptWidth_fits n m
  omega

theorem parseF_apply (W c : ℕ) (R : EmbeddingFaces.Ribbon left right) (w : Fin n → ℚ)
    (hn : n < 2 ^ W) (hcost : ∀ e, FPTHard.integerCosts left right w e < 2 ^ c) :
    parseF.apply (trees W c R w) = parsed W c R w := by
  rw [Fn.apply]
  simp only [parseF, Expr.denote, Var.get, denote_call, trees]
  rw [parseColumns_apply, parseEdges_apply W left right hn, lengthF_apply, costsTree,
    parseWords_apply, parseCount_apply _ _ (rowCount_fits R)]
  simp only [parsed, wordsTree, items_listTree, List.length_map, RibbonTable.rangeWords_length,
    List.map_map, Prod.mk.injEq, true_and, and_true]
  apply List.map_congr_left
  intro e _
  simp only [Function.comp_apply]
  rw [GraphReachEncoded.word_value (hcost e)]

/-- The coordinate data of an instance (root `0`). -/
abbrev coordsOf (R : EmbeddingFaces.Ribbon left right) (hn0 : 0 < n) : FPTHard.CoordinateData m :=
  faceCoords R ⟨0, hn0⟩

theorem coordStageF_apply (W c : ℕ) (R : EmbeddingFaces.Ribbon left right) (w : Fin n → ℚ)
    (hn0 : 0 < n) :
    coordStageF.apply (parsed W c R w) =
      (parsed W c R w, (((coordsOf R hn0).rank : ℤ),
        List.ofFn (FunCoordinates.coordRow left right (FPTHard.faceColumns R) ⟨0, hn0⟩))) := by
  rw [Fn.apply]
  simp only [coordStageF, Expr.denote, Var.get, denote_call, parsed]
  have h := FPTHardConcrete.coordFn_faceColumns R ⟨0, hn0⟩
  simp only [List.ofFn_eq_map] at h
  have he : FunCoordinates.edgeList left right =
      (List.finRange m).map fun e => (((left e : ℕ) : ℤ), ((right e : ℕ) : ℤ)) := by
    simp [FunCoordinates.edgeList, List.ofFn_eq_map]
  rw [he] at h
  simpa [List.ofFn_eq_map, coordsOf, faceCoords, rowCount] using h

theorem edgeRecF_apply (x : (Ty.prod (.prod (.list .int) FunCoordinates.RowTy) .int).denote) :
    edgeRecF.apply x = (x.1.1, (x.1.2.1, (x.1.2.2.2.1 :: x.1.2.2.2.2, x.2))) := rfl

/-- The network input records of an instance. -/
abbrev inputOf (R : EmbeddingFaces.Ribbon left right) (w : Fin n → ℚ) (hn0 : 0 < n) :
    List FunNetwork.EdgeIn :=
  FunNetwork.edgeInput (FPTHard.faceColumns R) (coordsOf R hn0) (FPTHard.integerCosts left right w)

theorem inputF_apply (R : EmbeddingFaces.Ribbon left right) (w : Fin n → ℚ) (hn0 : 0 < n) :
    inputF.apply ((List.finRange m).map fun e => FunNetwork.columnCode (FPTHard.faceColumns R e),
      (List.ofFn (FunCoordinates.coordRow left right (FPTHard.faceColumns R) ⟨0, hn0⟩),
        (List.finRange m).map fun e => (FPTHard.integerCosts left right w e : ℤ))) =
      inputOf R w hn0 := by
  rw [Fn.apply]
  simp only [inputF, Expr.denote, Var.get, denote_call, zipFn_apply, mapF_apply,
    List.ofFn_eq_map, List.zip_map', List.map_map]
  simp only [inputOf, FunNetwork.edgeInput, List.ofFn_eq_map]
  apply List.map_congr_left
  intro e _
  simp only [Function.comp_apply, edgeRecF_apply, FunCoordinates.coordRow,
    FunNetwork.residueCode, List.ofFn_eq_map]
  rfl

theorem inputStageF_apply (W c : ℕ) (R : EmbeddingFaces.Ribbon left right) (w : Fin n → ℚ)
    (hn0 : 0 < n) :
    inputStageF.apply (parsed W c R w, (((coordsOf R hn0).rank : ℤ),
        List.ofFn (FunCoordinates.coordRow left right (FPTHard.faceColumns R) ⟨0, hn0⟩))) =
      ((n : ℤ), ((rowCount R : ℤ), (((coordsOf R hn0).rank : ℤ), inputOf R w hn0))) := by
  rw [Fn.apply]
  simp only [inputStageF, Expr.denote, Var.get, denote_call, parsed]
  rw [inputF_apply]

theorem muE_denote {Γ : List Ty} (r : Expr Γ .int) (env : Env Γ) (k : ℕ)
    (hr : r.denote env = k) : (muE r).denote env = (GroupSize.modulus k : ℤ) := by
  simp only [muE, Expr.denote, IntOp.eval, hr, GroupSize.modulus]
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp
  · have h1 : (1 : ℤ) / ((k : ℤ) + 1) = 0 := Int.ediv_eq_zero_of_lt (by norm_num) (by omega)
    have hk0 : k ≠ 0 := by omega
    simp only [h1, hk0, ↓reduceIte]
    push_cast; ring

/-- The optimum value with the executable enumeration of the rows and columns. -/
abbrev valueOf (R : EmbeddingFaces.Ribbon left right) (w : Fin n → ℚ) (hn0 : 0 < n) : ℕ :=
  FPTHard.lpValue (FPTHard.faceColumns R) (coordsOf R hn0) (FPTHard.integerCosts left right w)
    (AlgorithmNetworkEnumeration.rows (FPTHard.faceColumns R) (coordsOf R hn0).rank)
    (AlgorithmNetworkEnumeration.columns (FPTHard.faceColumns R) (coordsOf R hn0).rank)

theorem optStageF_apply {optF : Fn OptArg .int} (hopt : OptSpec optF)
    (R : EmbeddingFaces.Ribbon left right) (w : Fin n → ℚ) (hn0 : 0 < n)
    (hc : Incidence.Connected left right) (hnb : ¬ Incidence.Bipartite left right) :
    (optStageF optF).apply ((n : ℤ), ((rowCount R : ℤ), (((coordsOf R hn0).rank : ℤ),
        inputOf R w hn0))) =
      ((n : ℤ), (inputOf R w hn0, (valueOf R w hn0 : ℤ))) := by
  rw [Fn.apply]
  simp only [optStageF, Expr.denote, Var.get, denote_call]
  rw [muE_denote _ _ (coordsOf R hn0).rank rfl]
  have hnet := FunNetwork.networkFn_correct (FPTHard.faceColumns R) (coordsOf R hn0)
    (FPTHard.integerCosts left right w)
  simp only [FunNetwork.networkInput] at hnet
  rw [hnet, FunNetwork.offsetFn_correct, FunNetwork.bitsFn_correct, hopt]
  have hBA := FPTHard.faceColumns_incidence R hc hnb
  have hB1 := FPTHard.faceColumns_one R hc hnb
  have hv := FPTHard.lpValue_eq_of_valid left right (FPTHard.faceColumns R) hBA hB1
    (coordsOf R hn0) (faceCoords_valid R ⟨0, hn0⟩ hc hnb hBA hB1)
    (FPTHard.integerCosts left right w)
    (FunNetwork.rowsEquiv (FPTHard.faceColumns R) (coordsOf R hn0).rank)
    (FunNetwork.colsEquiv (FPTHard.faceColumns R) (coordsOf R hn0).rank)
    (AlgorithmNetworkEnumeration.rows (FPTHard.faceColumns R) (coordsOf R hn0).rank)
    (AlgorithmNetworkEnumeration.columns (FPTHard.faceColumns R) (coordsOf R hn0).rank)
  unfold FPTHard.lpValue at hv
  rw [hv]
  rfl

theorem inputOf_length (R : EmbeddingFaces.Ribbon left right) (w : Fin n → ℚ) (hn0 : 0 < n) :
    (inputOf R w hn0).length = m := by
  simp [inputOf, FunNetwork.edgeInput]

/-- The optimum value is at most the total perturbed cost. -/
theorem valueOf_le_total (R : EmbeddingFaces.Ribbon left right) (w : Fin n → ℚ) (hn0 : 0 < n)
    (hc : Incidence.Connected left right) (hnb : ¬ Incidence.Bipartite left right) :
    valueOf R w hn0 ≤ FPTHard.total (FPTHard.integerCosts left right w) := by
  have hBA := FPTHard.faceColumns_incidence R hc hnb
  have hB1 := FPTHard.faceColumns_one R hc hnb
  obtain ⟨I, hI, -, hv⟩ := FPTHard.lpValue_spec left right (FPTHard.faceColumns R) hBA hB1
    (coordsOf R hn0) (faceCoords_valid R ⟨0, hn0⟩ hc hnb hBA hB1)
    (FPTHard.integerCosts left right w)
    (AlgorithmNetworkEnumeration.rows (FPTHard.faceColumns R) (coordsOf R hn0).rank)
    (AlgorithmNetworkEnumeration.columns (FPTHard.faceColumns R) (coordsOf R hn0).rank)
  have hs := FPTHard.natSetWeight_add_slack left right
    (FPTHard.perturbed (FPTHard.integerCosts left right w)) hI
  unfold valueOf FPTHard.total
  rw [hv]
  omega

theorem finalF_apply (R : EmbeddingFaces.Ribbon left right) (w : Fin n → ℚ) (hn0 : 0 < n) :
    finalF.apply ((n : ℤ), (inputOf R w hn0, (valueOf R w hn0 : ℤ))) =
      outputTree n m (slackValue faceCoords R w ⟨0, hn0⟩) := by
  rw [Fn.apply]
  simp only [finalF, Expr.denote, Var.get, denote_call, IntOp.eval, lengthF_apply,
    inputOf_length]
  rw [FunNetwork.slackFn_correct]
  have hw : ((3 : ℤ) * n + m + 4) = (fptWidth n m : ℤ) := by
    simp only [fptWidth]; push_cast; ring
  rw [hw, List.ofFn_eq_map]
  have hs : ∀ e, slackValue faceCoords R w ⟨0, hn0⟩ e ≤ 1 := fun e => by
    unfold slackValue; omega
  rw [← formatOutput_apply n m _ hs]
  rfl

/-- **Denotation of the numerical-stage program.** -/
theorem mainF_apply {optF : Fn OptArg .int} (hopt : OptSpec optF) (W c : ℕ)
    (R : EmbeddingFaces.Ribbon left right) (w : Fin n → ℚ) (hn0 : 0 < n) (hn : n < 2 ^ W)
    (hc : Incidence.Connected left right) (hnb : ¬ Incidence.Bipartite left right)
    (hcost : ∀ e, FPTHard.integerCosts left right w e < 2 ^ c) :
    (mainF optF).apply (trees W c R w) = outputTree n m (slackValue faceCoords R w ⟨0, hn0⟩) := by
  simp only [mainF, Fn.apply_comp]
  rw [parseF_apply W c R w hn hcost, coordStageF_apply W c R w hn0, inputStageF_apply W c R w hn0,
    optStageF_apply hopt R w hn0 hc hnb, finalF_apply R w hn0]

theorem prog_denote {optF : Fn OptArg .int} (hopt : OptSpec optF) (W c : ℕ)
    (R : EmbeddingFaces.Ribbon left right) (w : Fin n → ℚ) (hn0 : 0 < n) (hn : n < 2 ^ W)
    (hc : Incidence.Connected left right) (hnb : ¬ Incidence.Bipartite left right)
    (hcost : ∀ e, FPTHard.integerCosts left right w e < 2 ^ c) :
    (prog optF).denote (FPTRunFun.stageEnv W c R w) =
      outputTree n m (slackValue faceCoords R w ⟨0, hn0⟩) := by
  simp only [prog, denote_call, Expr.denote, Var.get]
  exact mainF_apply hopt W c R w hn0 hn hc hnb hcost

end MWIS.FPTMainProg

end
