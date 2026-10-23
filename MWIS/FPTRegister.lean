module

public import MWIS.FPTTrees
public import MWIS.FPTHard
public import MWIS.GenericComponentSolve
public import MWIS.RegisterHardSolve

/-!
# The register-level fixed-parameter hard-component procedure

The hard procedure receives the stored ribbon table, the vertex range words and
the canonical stored weights of a connected nonbipartite all-half component. It

1. reads the endpoint records and the edge index words off the table, and
   computes XP's integer edge costs (`RegisterEdgeCostProgram`), as the XP hard
   procedure does;
2. calls a procedure `consts` on the vertex range words and the edge index words.
   Its contract `ConstsSpec` says that it returns the words of `1` and `0` of the
   width `fptWidth n m = 3 n + m + 4`;
3. runs XP's face stage (`FaceStageProgram`) at that width. It returns the even-face
   columns `R.computedColumn (Flag.canonicalOrder m)` in XP's column format and the
   word of `2 r + 1`, where `r` is the number of even faces;
4. calls one procedure `funStage` on the columns, the endpoint records, the vertex
   range words, the cost words and the row-count word. Its contract `FunStageSpec`
   says that it returns the decoded binary slack `slackValue` of the perturbed
   network value as words of width `fptWidth n m`;
5. computes XP's odd row at that width (`RegisterOddRow`) and runs XP's integer
   potential recovery and threshold (`RegisterHardRecovery`) on the slack.

All inputs and outputs of `consts` and `funStage` are stated as explicit cell
trees (`MWIS.FPTTrees`). `hard_spec` proves the generic hard contract
`GenericHardSpec` for the hard function `solverOf coords` (the output
`FPTHard.fptHardWith`), for any coordinate construction `coords` producing valid
coordinate data, assuming both stage contracts. `fixedBudget_le` bounds the
budget of the other stages by a fixed polynomial.
-/

@[expose] public section

namespace MWIS.FPTRegister

open MWIS.PointerMemory MWIS.RegisterMachine MWIS.EfficientSearch
open MWIS.EfficientSearch.Pointer MWIS.ExpandedWords MWIS.RibbonTable
open MWIS.RegisterFlagKeys MWIS.RegisterHardInputs
open MWIS.RegisterIncidenceRows (EdgeAt)
open MWIS.GenericComponentSolve (GenericHardSpec)
open MWIS.RegisterComponentSolve (HardBudget)
open MWIS.FPTTrees MWIS.FPTHard
open MWIS.Fun (Tree TreeAt)

variable {p : ℕ}

/-! ## The hard function -/

/-- A coordinate construction: coordinate data for every ribbon and root. -/
abbrev CoordFn : Type :=
  ∀ {n m : ℕ} {left right : Fin m → Fin n}, EmbeddingFaces.Ribbon left right → Fin n →
    CoordinateData m

/-- The coordinate data are valid on every connected nonbipartite ribbon. -/
def CoordsValid (coords : CoordFn) : Prop :=
  ∀ {n m : ℕ} {left right : Fin m → Fin n} (R : EmbeddingFaces.Ribbon left right) (root : Fin n),
    Incidence.Connected left right → ¬ Incidence.Bipartite left right →
    ∀ hBA hB1, (coords R root).Valid left right (faceColumns R) hBA hB1

/-- The fixed-parameter hard function for a coordinate construction. -/
def solverOf (coords : CoordFn) : Generic.HardFn :=
  fun R w root => fptHardWith (coords R root) R w root

theorem solverOf_correct {coords : CoordFn} (hco : CoordsValid coords) :
    Generic.HardCorrect (solverOf coords) :=
  fun R w root hc hnb hw ho =>
    fptHardWith_correct (coords R root) R w root hc hnb hw ho (hco R root hc hnb)

variable {n m : ℕ} {left right : Fin m → Fin n}

/-- The minimum perturbed slack cost: total perturbed cost minus the network value. -/
def slackTotal (coords : CoordFn) (R : EmbeddingFaces.Ribbon left right) (w : Fin n → ℚ)
    (root : Fin n) : ℕ :=
  total (integerCosts left right w) -
    lpValue (faceColumns R) (coords R root) (integerCosts left right w)
      (AlgorithmNetworkEnumeration.rows (faceColumns R) (coords R root).rank)
      (AlgorithmNetworkEnumeration.columns (faceColumns R) (coords R root).rank)

/-- The decoded slack bits of an edge. -/
def slackValue (coords : CoordFn) (R : EmbeddingFaces.Ribbon left right) (w : Fin n → ℚ)
    (root : Fin n) (e : Fin m) : ℕ :=
  slackTotal coords R w root / 2 ^ (e : ℕ) % 2

/-- The hard function is the threshold of the recovered potential of the decoded slack. -/
theorem solverOf_eq (coords : CoordFn) (R : EmbeddingFaces.Ribbon left right) (w : Fin n → ℚ)
    (root : Fin n) :
    solverOf coords R w root =
      HardSolveReference.thresholdFrom left right root
        (ExecutableReduction.parityRow (left := left) (right := right) root)
        (fun e => (slackValue coords R w root e : ℤ)) := rfl

/-- For valid coordinates the decoded slack is the binary slack of an
independent set. -/
theorem slack_spec {coords : CoordFn} (hco : CoordsValid coords) (R : EmbeddingFaces.Ribbon left right)
    (w : Fin n → ℚ) (root : Fin n) (hc : Incidence.Connected left right)
    (hnb : ¬ Incidence.Bipartite left right) :
    ∃ I : Finset (Fin n), Slack.Independent left right I ∧
      ∀ e, slackValue coords R w root e = slackBit left right I e := by
  have hBA := faceColumns_incidence R hc hnb
  have hB1 := faceColumns_one R hc hnb
  obtain ⟨I, hI, -, hv⟩ := lpValue_spec left right (faceColumns R) hBA hB1 (coords R root)
    (hco R root hc hnb hBA hB1) (integerCosts left right w)
    (AlgorithmNetworkEnumeration.rows (faceColumns R) (coords R root).rank)
    (AlgorithmNetworkEnumeration.columns (faceColumns R) (coords R root).rank)
  have hslack := natSetWeight_add_slack left right (perturbed (integerCosts left right w)) hI
  have hdiff : slackTotal coords R w root =
      ∑ e, perturbed (integerCosts left right w) e * slackBit left right I e := by
    unfold slackTotal total
    rw [hv]
    omega
  have hdec := decode_perturbed (integerCosts left right w) _ (slackBit_le left right I)
  refine ⟨I, hI, fun e => ?_⟩
  have h := congrFun hdec e
  unfold decode at h
  rw [← hdiff] at h
  exact_mod_cast h

/-! ## Widths and trees -/

/-- The common width of the constants, the face-stage keys, the slack words, the odd
row and the recovery. -/
def fptWidth (n m : ℕ) : ℕ := 3 * n + m + 4

theorem fptWidth_fits (n m : ℕ) : (3 * n + 1) * (m + 2) + 8 * m + 2 < 2 ^ fptWidth n m := by
  unfold fptWidth
  have a : 3 * n + 1 < 2 ^ (3 * n + 1) := Nat.lt_two_pow_self
  have b : m + 2 < 2 ^ (m + 2) := Nat.lt_two_pow_self
  have c : 8 * (m + 1) ≤ 2 ^ (m + 3) := by
    have : m + 1 ≤ 2 ^ m := Nat.lt_two_pow_self
    rw [pow_add]; omega
  have hab : (3 * n + 1) * (m + 2) < 2 ^ (3 * n + m + 3) := by
    calc (3 * n + 1) * (m + 2) < 2 ^ (3 * n + 1) * 2 ^ (m + 2) := Nat.mul_lt_mul'' a b
      _ = 2 ^ (3 * n + m + 3) := by rw [← pow_add]; ring_nf
  have hc : 8 * m + 2 ≤ 2 ^ (3 * n + m + 3) := by
    have : 2 ^ (m + 3) ≤ 2 ^ (3 * n + m + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have : 2 ^ (3 * n + m + 4) = 2 ^ (3 * n + m + 3) + 2 ^ (3 * n + m + 3) := by
    rw [pow_succ]; ring
  omega

theorem two_lt_fptWidth (n m : ℕ) : 2 < 2 ^ fptWidth n m := by
  have := fptWidth_fits n m
  omega

/-- The words of one and zero of width `fptWidth n m`, as returned by `consts`. -/
def constsTree (n m : ℕ) : Tree :=
  .pair (bitsTree (GraphReachEncoded.word (fptWidth n m) 1)) (bitsTree (Bits.zero (fptWidth n m)))

theorem constsTree_eq (n m : ℕ) :
    constsTree n m = .pair (Tree.word (fptWidth n m) 1) (Tree.word (fptWidth n m) 0) := by
  have h2 := two_lt_fptWidth n m
  rw [constsTree, bitsTree_zero]
  congr 1
  exact bitsTree_word _ _ (by omega)

/-- The output of the numerical stage for slack bits `s`: the slack words of width
`fptWidth n m`. -/
def outputTree (n m : ℕ) (s : Fin m → ℕ) : Tree :=
  wordsTree ((List.finRange m).map fun e => GraphReachEncoded.word (fptWidth n m) (s e))

/-- The output tree written with `Fun` words, for binary slack bits. -/
theorem outputTree_eq (n m : ℕ) (s : Fin m → ℕ) (hs : ∀ e, s e ≤ 1) :
    outputTree n m s =
      Tree.ofList ((List.finRange m).map fun e => Tree.word (fptWidth n m) (s e)) := by
  have h2 := two_lt_fptWidth n m
  simp only [outputTree, wordsTree, listTree, List.map_map]
  congr 1
  apply List.map_congr_left
  intro e _
  exact bitsTree_word _ _ (by have := hs e; omega)

/-- The number of even faces of a ribbon in canonical flag order. -/
abbrev rowCount (R : EmbeddingFaces.Ribbon left right) : ℕ :=
  (R.evenRootIndices (EmbeddingFaces.Flag.canonicalOrder m)).length

/-- The face-stage columns: the even-face columns in XP's column format, with
state keys of width `fptWidth n m`. -/
def columnsTree (R : EmbeddingFaces.Ribbon left right) : Tree :=
  listTree (columnTree (RegisterFaceColumns.stateKey (fptWidth n m) (rowCount R)))
    ((List.finRange m).map (faceColumns R))

/-- The endpoint records: the pairs of endpoint words. -/
def edgesTree (W : ℕ) (left right : Fin m → Fin n) : Tree :=
  listTree edgeTree (GraphReachEncoded.edgeWords W left right)

/-- The cost words of width `c`. -/
def costsTree (c : ℕ) (cost : Fin m → ℕ) : Tree :=
  wordsTree ((List.finRange m).map fun e => GraphReachEncoded.word c (cost e))

/-- The cost words written with `Fun` words. -/
theorem costTree_eq (c : ℕ) (cost : Fin m → ℕ) (hc : ∀ e, cost e < 2 ^ c) :
    costsTree c cost =
      Tree.ofList ((List.finRange m).map fun e => Tree.word c (cost e)) := by
  simp only [costsTree, wordsTree, listTree, List.map_map]
  congr 1
  apply List.map_congr_left
  intro e _
  exact bitsTree_word _ _ (hc e)

/-- The vertex range words written with `Fun` words. -/
theorem rangeTree_eq (W : ℕ) (hn : n < 2 ^ W) :
    wordsTree (rangeWords W n) = Tree.ofList ((List.range n).map fun i => Tree.word W i) := by
  simp only [wordsTree, listTree, rangeWords, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact bitsTree_word _ _ (lt_trans (List.mem_range.mp hi) hn)

/-! ## The contracts of the two `Fun` stages -/

/-- **Contract of the constants stage.** Called with the cell trees of the vertex
range words and the edge index words, the procedure `consts` returns
`constsTree n m` within `cb W n m` events. -/
def ConstsSpec (code : Code p) (consts : Fin p) (cb : ℕ → ℕ → ℕ → ℕ) : Prop :=
  ∀ (W n m : ℕ) {h : Heap}, Valid h → ∀ {rp ip : Ptr},
    TreeAt h rp (wordsTree (rangeWords W n)) →
    TreeAt h ip (wordsTree (GraphReachEncoded.rangeWords W m)) →
    ∃ out q, Extends h out ∧ Valid out ∧ TreeAt out q (constsTree n m) ∧
      Within code h (initialRegisters [.pointer rp, .pointer ip]) (code consts)
        [.pointer q] out (cb W n m)

/-- **Contract of the numerical stage.** For every index width `W`, cost width `c`
and connected nonbipartite all-half component with nonnegative weights whose XP
integer edge costs fit in `c` bits: called with the cell trees of the face-stage
columns, the endpoint records, the vertex range words, the cost words and the
word of `2 r + 1` (with `r` the number of even faces), the procedure `funStage`
returns `outputTree n m (slackValue coords R w root)` at the canonical root
within `fb W c R w` events. -/
def FunStageSpec (code : Code p) (funStage : Fin p) (coords : CoordFn)
    (fb : ℕ → ℕ → HardBudget) : Prop :=
  ∀ (W c : ℕ) {n m : ℕ} {left right : Fin m → Fin n} (R : EmbeddingFaces.Ribbon left right)
    (w : Fin n → ℚ) (hn0 : 0 < n), n < 2 ^ W → m < 2 ^ W →
    Incidence.Connected left right → ¬ Incidence.Bipartite left right → (∀ v, 0 ≤ w v) →
    Persistence.Optimal (EdgeTransport.Adj left right) w (fun _ => 1 / 2) →
    (∀ e, integerCosts left right w e < 2 ^ c) →
    ∀ {h : Heap}, Valid h → ∀ {kp ep rp cp np : Ptr},
      TreeAt h kp (columnsTree R) → TreeAt h ep (edgesTree W left right) →
      TreeAt h rp (wordsTree (rangeWords W n)) → TreeAt h cp (costsTree c (integerCosts left right w)) →
      TreeAt h np (bitsTree (GraphReachEncoded.word (fptWidth n m) (2 * rowCount R + 1))) →
      ∃ out q, Extends h out ∧ Valid out ∧
        TreeAt out q (outputTree n m (slackValue coords R w ⟨0, hn0⟩)) ∧
        Within code h (initialRegisters [.pointer kp, .pointer ep, .pointer rp, .pointer cp,
          .pointer np]) (code funStage) [.pointer q] out (fb W c R w)

/-! ## Procedures -/

/-- Arguments 0 = vertex range words, 1 = endpoint records, 2 = edge index words,
3 = slack words, 4 = word of one, 5 = word of zero. -/
def stageBody (odd recovery : Fin p) : Command p :=
  .load (.register 0) 6 7 15 { CompiledTrie.failCases with
    cons := .allocate 8 (.bit (.flag true) .null)
      (.call odd [.register 1, .register 2, .register 0, .register 6, .register 8,
          .register 4, .register 5] [9, 10]
      (.call recovery [.register 1, .register 0, .register 6, .register 9, .register 3,
          .register 8, .register 4, .register 5] [11]
      (.ret [.register 11]))) }

/-- Arguments 0 = table, 1 = vertex range words, 2 = stored weights. -/
def hardBody (edges keys costs consts face funStage stage : Fin p) : Command p :=
  .call edges [.register 0, .null] [3]
  (.call keys [.register 0, .null] [4]
  (.call costs [.register 1, .register 3, .register 2] [5, 6]
  (.call consts [.register 1, .register 4] [7]
  (.load (.register 7) 8 9 15 { CompiledTrie.failCases with
    pair := .call face [.register 0, .register 7, .register 8] [10, 11, 12]
      (.call funStage [.register 10, .register 3, .register 1, .register 5, .register 12] [13]
      (.call stage [.register 1, .register 3, .register 4, .register 13, .register 8,
          .register 9] [14]
      (.ret [.register 14]))) }))))

structure Procedures (p : ℕ) where
  hard : Fin p
  stage : Fin p
  edges : Fin p
  edgeItem : Fin p
  keys : Fin p
  key : Fin p
  consts : Fin p
  funStage : Fin p
  costs : RegisterEdgeCostProgram.Procedures p
  face : FaceStageProgram.Procedures p
  odd : RegisterOddRow.Procedures p
  recovery : RegisterHardRecovery.Procedures p

structure Procedures.Matches (ids : Procedures p) (code : Code p) : Prop where
  hard : code ids.hard = hardBody ids.edges ids.keys ids.costs.self ids.consts ids.face.top
    ids.funStage ids.stage
  stage : code ids.stage = stageBody ids.odd.self ids.recovery.self
  edges : code ids.edges = RegisterListMap.body ids.edges ids.edgeItem
  edgeItem : code ids.edgeItem = edgeItemBody
  keys : code ids.keys = RegisterListMap.body ids.keys ids.key
  key : code ids.key = RegisterEdgeWords.keyBody
  costs : ids.costs.Matches code
  face : ids.face.Matches code
  odd : ids.odd.Matches code
  recovery : ids.recovery.Matches code

/-! ## Budgets -/

/-- Events of the stages after the numerical stage. -/
def stageBudget (W n m : ℕ) : ℕ :=
  RegisterOddRow.budget W W (fptWidth n m) n m + RegisterHardRecovery.budget W (fptWidth n m) n m +
    120

/-- Events of the procedure apart from the two `Fun` stages. -/
def fixedBudget (W w0 n m : ℕ) : ℕ :=
  edgesBudget m + RegisterEdgeWords.keysBudget m + RegisterEdgeCostProgram.budget W w0 n m +
    FaceStageProgram.stageBudget W (fptWidth n m) (fptWidth n m) m + stageBudget W n m + 80

/-- The budget of the hard procedure: the fixed stages, the constants stage, and the
numerical stage at the XP cost width `NetworkWeights.width w0 n`. -/
def fptBudget (cb : ℕ → ℕ → ℕ → ℕ) (fb : ℕ → ℕ → HardBudget) (W w0 : ℕ) : HardBudget :=
  fun {n m} {_left _right} R w =>
    fixedBudget W w0 n m + cb W n m + fb W (NetworkWeights.width w0 n) R w

/-! ## The final stages -/

/-- From the slack words and the constant words, the odd row and the recovery
return the words of the threshold set of the recovered potential of the slack. -/
theorem stage_compiled (ids : Procedures p) (code : Code p) (hm : ids.Matches code)
    {W : ℕ} (hn0 : 0 < n) (hn : n < 2 ^ W) (hmW : m < 2 ^ W)
    (hc : Incidence.Connected left right) (hnb : ¬ Incidence.Bipartite left right)
    (s : Fin m → ℕ) (hs : ∀ e, s e ≤ 1)
    (hx : ∃ x : Fin n → ℤ, ∀ e, x (left e) + x (right e) = 1 - (s e : ℤ))
    {h : Heap} (hh : Valid h) {rp ep ip yp op zp : Ptr}
    (hr : WordsAt h rp (rangeWords W n))
    (he : ListRep EdgeAt h ep (GraphReachEncoded.edgeWords W left right))
    (hi : WordsAt h ip (GraphReachEncoded.rangeWords W m))
    (hf : TreeAt h yp (outputTree n m s))
    (hone : BitsAt h op (GraphReachEncoded.word (fptWidth n m) 1))
    (hzero : BitsAt h zp (Bits.zero (fptWidth n m))) :
    ∃ out q, Extends h out ∧ Valid out ∧
      WordsAt out q (GraphReachEncoded.setWords W (HardSolveReference.thresholdFrom left right
        ⟨0, hn0⟩ (ExecutableReduction.parityRow (left := left) (right := right) ⟨0, hn0⟩)
        (fun e => (s e : ℤ)))) ∧
      Within code h (initialRegisters [.pointer rp, .pointer ep, .pointer ip, .pointer yp,
          .pointer op, .pointer zp]) (code ids.stage) [.pointer q] out (stageBudget W n m) := by
  set B := fptWidth n m with hB
  have hfit : (3 * n + 1) * (m + 2) + 8 * m + 2 < 2 ^ B := fptWidth_fits n m
  set yw : Fin m → Bits B := fun e => GraphReachEncoded.word B (s e) with hyw
  have hy : WordsAt h yp ((List.finRange m).map yw) := (wordsAt_iff _).mpr hf
  have hone1 : (GraphReachEncoded.word B 1).value = 1 := GraphReachEncoded.word_value (by omega)
  -- the root word
  obtain ⟨rest, hrest⟩ := RegisterComponentSolve.rangeWords_cons (W := W) hn0
  have hr0 := hr
  rw [hrest] at hr0
  obtain ⟨x0, rt, cell, hx0, -⟩ := WordsAt.cons_iff.mp hr0
  obtain ⟨f1, v1, b1⟩ := alloc_bit hh true (BitsAt.nil hh.1)
  have hone7 : BitsAt (h ++ [.bit true 0]) h.length GraphReachEncoded.one := b1
  -- the odd row
  have hnodes : WordsAt (h ++ [.bit true 0]) rp (GraphReachEncoded.rangeWords W n) := by
    rw [AllHalfEncoded.rangeWords_eq]; exact hr.mono f1
  have h2n : 2 * n < 2 ^ B := by
    have : 2 * n ≤ (3 * n + 1) * (m + 2) := by nlinarith
    omega
  obtain ⟨o2, pp, πw, e2, v2, hπw, hπs, w2⟩ := RegisterOddRow.oddRow_compiled code ids.odd hm.odd
    left right ⟨0, hn0⟩ (GraphReachEncoded.word B 1) (Bits.zero B) hn hmW h2n hone1
    (Bits.value_zero B) v1 (he.mono f1 (fun _ _ hx => hx.mono f1)) (hi.mono f1) hnodes
    (hx0.mono f1) hone7 (hone.mono f1) (hzero.mono f1)
  have e12 := f1.trans e2
  -- the recovery
  have hval : ∀ e, (yw e).value = s e := fun e =>
    GraphReachEncoded.word_value (by have := hs e; omega)
  have hπ : ∀ e, (RegisterPotentialStep.value (πw e)).natAbs < 2 * n := by
    intro e
    rw [hπw]
    have h := ComputedOddRow.oddRow_natAbs_lt left right (List.finRange m)
      (fun e => List.mem_finRange e) (List.finRange n) (fun v => List.mem_finRange v) ⟨0, hn0⟩
      hc hnb e
    simpa [ExecutableReduction.parityRow] using h
  have hsum : ∑ e, (yw e).value ≤ m := by
    calc ∑ e, (yw e).value ≤ ∑ _e : Fin m, 1 := Finset.sum_le_sum (fun e _ => by rw [hval]; exact hs e)
      _ = m := by simp
  have hwf := RegisterHardRecovery.width_of_bounds πw yw m hπ hsum (by
    have : (3 * n + 1) * (m + 1) ≤ (3 * n + 1) * (m + 2) := Nat.mul_le_mul_left _ (by omega)
    omega)
  have hcoeffs : RegisterHardRecovery.coeffs πw =
      ExecutableReduction.parityRow (left := left) (right := right) ⟨0, hn0⟩ := funext hπw
  have hcounts : RegisterHardRecovery.counts yw = fun e => (s e : ℤ) := by
    funext e; simp only [RegisterHardRecovery.counts, hval]
  have hπr : IntegerSlacks.OddRow left right ⟨0, hn0⟩
      (ExecutableReduction.parityRow (left := left) (right := right) ⟨0, hn0⟩) :=
    ComputedOddRow.oddRow_correct left right (List.finRange m) (fun e => List.mem_finRange e)
      (List.finRange n) (fun v => List.mem_finRange v) ⟨0, hn0⟩ hc hnb
  have heven : Even (HardSolveReference.rootNumerator (RegisterHardRecovery.coeffs πw)
      (RegisterHardRecovery.counts yw)) := by
    obtain ⟨x, hx⟩ := hx
    rw [hcoeffs, hcounts, HardSolveReference.rootNumerator_eq_two_mul (left := left)
      (right := right) ⟨0, hn0⟩ _ _ hπr x hx]
    exact even_two_mul _
  have hnodes2 : WordsAt o2 rp (GraphReachEncoded.rangeWords W n) := hnodes.mono e2
  obtain ⟨o3, q, e3, v3, hq, w3⟩ := RegisterHardRecovery.compiled code ids.recovery hm.recovery
    left right ⟨0, hn0⟩ πw yw (GraphReachEncoded.word B 1) hn hone1 hwf heven v2
    (he.mono e12 (fun _ _ hx => hx.mono e12)) hnodes2 ((hx0.mono f1).mono e2) hπs (hy.mono e12)
    (hone7.mono e2) (hone.mono e12) (hzero.mono e12)
  rw [hcoeffs, hcounts] at hq
  refine ⟨o3, q, e12.trans e3, v3, hq, ?_⟩
  rw [hm.stage]
  refine (Within.load (pointer := rp) (c := Cell.cons x0 rt) (by reg_simp) cell
    (Within.allocate (c := Cell.bit true 0) (by reg_simp)
    (call_of (by reg_simp) w2 (call_of (by reg_simp) w3
    (ret_values (by reg_simp) le_rfl))))).mono ?_
  simp only [stageBudget, ← hB, CellExpr.args, List.length_cons, List.length_nil]
  omega

/-! ## The hard procedure -/

theorem keys_eq' {W : ℕ} (R : EmbeddingFaces.Ribbon left right) :
    (encodeRibbon W R).map EdgeRec.key = GraphReachEncoded.rangeWords W m :=
  RegisterHardSolve.keys_eq R

/-- **The fixed-parameter hard procedure meets the generic hard contract** for the
hard function `solverOf coords`, assuming valid coordinates and the contracts of
the two `Fun` stages. -/
theorem hard_spec (ids : Procedures p) (code : Code p) (hm : ids.Matches code)
    {coords : CoordFn} (hco : CoordsValid coords) {cb : ℕ → ℕ → ℕ → ℕ}
    (hconsts : ConstsSpec code ids.consts cb) {fb : ℕ → ℕ → HardBudget}
    (hfun : FunStageSpec code ids.funStage coords fb) (W w0 : ℕ) :
    GenericHardSpec code ids.hard W (RegisterWeightMask.CanonAt w0) (solverOf coords)
      (fptBudget cb fb W w0) := by
  intro n m left right R w hn0 hn hmW hc hnb hw ho h hh tp rp wp hT hr hwp
  set B := fptWidth n m with hB
  have hfit : (3 * n + 1) * (m + 2) + 8 * m + 2 < 2 ^ B := fptWidth_fits n m
  -- endpoint records and index words
  obtain ⟨o1, ep, e1, v1, he, w1⟩ := edges_compiled code ids.edges ids.edgeItem hm.edges
    hm.edgeItem hh hT
  rw [RegisterGraphArcs.edgePairs_encode] at he
  obtain ⟨o2, ip, e2, v2, hi, w2⟩ := RegisterEdgeWords.keys_compiled code ids.keys ids.key
    hm.keys hm.key v1 (hT.mono e1)
  rw [keys_eq'] at hi
  have e12 := e1.trans e2
  -- edge costs
  obtain ⟨q, hq, hval, hrow⟩ := exists_row hwp
  have hv : WordsAt o2 rp (GraphReachEncoded.rangeWords W n) := by
    rw [AllHalfEncoded.rangeWords_eq]; exact hr.mono e12
  obtain ⟨o3, cp, zp, e3, v3, hcs, hlt, -, w3⟩ := RegisterEdgeCostProgram.edgeCosts_compiled code
    ids.costs hm.costs hn left right w hw q hq hval v2 hv
    (edgeWordsAt_of (he.mono e2 (fun _ _ hx => hx.mono e2))) (hrow.mono e12)
  have e13 := e12.trans e3
  -- the constants
  obtain ⟨o4, kp, e4, v4, hk, w4⟩ := hconsts W n m v3 ((wordsAt_iff _).mp (hr.mono e13))
    ((wordsAt_iff _).mp (hi.mono e3))
  have e14 := e13.trans e4
  have hk' := hk
  rw [constsTree] at hk'
  cases hk' with
  | pair ck hO hZ =>
  rename_i Op Zp
  have hone : BitsAt o4 Op (GraphReachEncoded.word B 1) := (bitsAt_iff _).mpr hO
  have hzero : BitsAt o4 Zp (Bits.zero B) := (bitsAt_iff _).mpr hZ
  have hcon : RegisterFaceRow.ConstsAt (GraphReachEncoded.word B 1) (Bits.zero B) o4 kp :=
    (constsAt_iff _ _).mpr hk
  -- the face stage
  obtain ⟨o5, colsP, rowsP, cntP, ws5, e5, v5, hcols, -, -, hcnt, w5⟩ :=
    FaceStageProgram.stage_compiled ids.face code hm.face R hmW (b := B) (wk := B) (by omega)
      (by omega) (GraphReachEncoded.word B 1) (Bits.zero B)
      (GraphReachEncoded.word_value (by omega)) (Bits.value_zero B) v4 (hT.mono e14) hcon hone
  have e15 := e14.trans e5
  -- the numerical stage
  have hcolsT : TreeAt o5 colsP (columnsTree R) := (columnsAt_iff _ _).mp hcols
  have hcntT : TreeAt o5 cntP (bitsTree (GraphReachEncoded.word B (2 * rowCount R + 1))) :=
    (bitsAt_iff _).mp hcnt
  have heT : TreeAt o5 ep (edgesTree W left right) :=
    (listRep_iff (fun _ x => edgeAt_iff x) _).mp (he.mono (e2.trans (e3.trans (e4.trans e5)))
      (fun _ _ hx => hx.mono (e2.trans (e3.trans (e4.trans e5)))))
  obtain ⟨o6, yp, e6, v6, hf, w6⟩ := hfun W (NetworkWeights.width w0 n) R w hn0 hn hmW hc hnb hw ho
    hlt v5 hcolsT heT ((wordsAt_iff _).mp (hr.mono e15))
    ((wordsAt_iff _).mp ((hcs.mono e4).mono e5)) hcntT
  have e16 := e15.trans e6
  -- the slack is the binary slack of an independent set
  obtain ⟨I, hI, hsI⟩ := slack_spec hco R w ⟨0, hn0⟩ hc hnb
  have hs : ∀ e, slackValue coords R w ⟨0, hn0⟩ e ≤ 1 := fun e => by
    rw [hsI]; exact slackBit_le left right I e
  have hx : ∃ x : Fin n → ℤ, ∀ e, x (left e) + x (right e) =
      1 - (slackValue coords R w ⟨0, hn0⟩ e : ℤ) := by
    refine ⟨fun v => if v ∈ I then 1 else 0, fun e => ?_⟩
    have h1 := incidence_add_slack left right hI e
    rw [hsI]
    unfold incidenceCount slackBit at h1
    unfold slackBit
    by_cases hl : left e ∈ I <;> by_cases hr' : right e ∈ I <;> simp_all
  -- the final stages
  have e46 := e5.trans e6
  obtain ⟨o7, res, e7, v7, hres, w7⟩ := stage_compiled ids code hm hn0 hn hmW hc hnb
    (slackValue coords R w ⟨0, hn0⟩) hs hx v6 (hr.mono e16)
    (he.mono (e2.trans (e3.trans (e4.trans e46)))
      (fun _ _ hx => hx.mono (e2.trans (e3.trans (e4.trans e46)))))
    ((hi.mono e3).mono (e4.trans e46)) hf (hone.mono e46) (hzero.mono e46)
  rw [← solverOf_eq] at hres
  refine ⟨o7, res, e16.trans e7, v7, hres, ?_⟩
  rw [hm.hard]
  refine (call_of (by reg_simp) w1 (call_of (by reg_simp) w2 (call_of (by reg_simp) w3
    (call_of (by reg_simp) w4
    (Within.load (pointer := kp) (c := Cell.pair Op Zp) (by reg_simp) ck
    (call_of (by reg_simp) w5 (call_of (by reg_simp) w6 (call_of (by reg_simp) w7
    (ret_values (by reg_simp) le_rfl))))))))).mono ?_
  simp only [fptBudget, fixedBudget, ← hB, List.length_cons, List.length_nil, encodeRibbon_length]
  omega

/-! ## Polynomial bound on the fixed stages -/

theorem fptWidth_le (n m : ℕ) : fptWidth n m ≤ 3 * n + m + 4 := le_rfl

theorem stageBudget_le (W n m : ℕ) :
    stageBudget W n m ≤ 2 ^ 20 * (n + m + W + 2) ^ 7 := by
  have hB := fptWidth_le n m
  have ho := RegisterOddRow.budget_le W W (fptWidth n m) n m
  have hr := RegisterHardRecovery.budget_le W (fptWidth n m) n m
  generalize hX : n + m + W + 2 = X
  have hX1 : 1 ≤ X := by omega
  have ho' : RegisterOddRow.budget W W (fptWidth n m) n m ≤ 2 ^ 19 * X ^ 7 := by
    refine ho.trans ?_
    calc 100000 * (W + W + fptWidth n m + 1) * (m + 1) ^ 2 * (n + 1) ^ 4
        ≤ 100000 * (4 * X) * X ^ 2 * X ^ 4 := by gcongr <;> omega
      _ = 400000 * X ^ 7 := by ring
      _ ≤ 2 ^ 19 * X ^ 7 := by gcongr; norm_num
  have hr' : RegisterHardRecovery.budget W (fptWidth n m) n m ≤ 2 ^ 17 * X ^ 7 := by
    refine hr.trans ?_
    calc 6000 * (W + fptWidth n m + 1) ^ 2 * (m + 1) * (n + 1) ^ 4
        ≤ 6000 * (4 * X) ^ 2 * X * X ^ 4 := by gcongr <;> omega
      _ = 96000 * X ^ 7 := by ring
      _ ≤ 2 ^ 17 * X ^ 7 := by gcongr; norm_num
  have h1 : 1 ≤ X ^ 7 := Nat.one_le_pow _ _ hX1
  unfold stageBudget
  have : 2 ^ 20 * X ^ 7 = 2 ^ 19 * X ^ 7 + 2 ^ 17 * X ^ 7 + 3 * 2 ^ 17 * X ^ 7 := by ring
  omega

/-- The fixed stages are polynomial in the instance size and the widths. -/
theorem fixedBudget_le (W w0 n m : ℕ) :
    fixedBudget W w0 n m ≤ 2 ^ 26 * (n + m + W + w0 + 2) ^ 13 := by
  have hc := RegisterEdgeCostProgram.budget_le W w0 n m
  have hs := stageBudget_le W n m
  have hf := FaceStageProgram.stageBudget_le W (fptWidth n m) (fptWidth n m) m
  have hB := fptWidth_le n m
  generalize hX : n + m + W + w0 + 2 = X
  have hX1 : 1 ≤ X := by omega
  have p13 : ∀ k ≤ 13, X ^ k ≤ X ^ 13 := fun k hk => Nat.pow_le_pow_right hX1 hk
  have hc' : RegisterEdgeCostProgram.budget W w0 n m ≤ 2 ^ 24 * X ^ 13 := by
    refine hc.trans ?_
    calc 610000 * (w0 + 2) ^ 2 * (W + 3) ^ 2 * (n + m + 2) ^ 9
        ≤ 610000 * (2 * X) ^ 2 * (2 * X) ^ 2 * X ^ 9 := by gcongr <;> omega
      _ = 9760000 * X ^ 13 := by ring
      _ ≤ 2 ^ 24 * X ^ 13 := by gcongr; norm_num
  have hf' : FaceStageProgram.stageBudget W (fptWidth n m) (fptWidth n m) m ≤ 2 ^ 24 * X ^ 13 := by
    refine hf.trans ?_
    calc 2 ^ 20 * (W + fptWidth n m + fptWidth n m + 1) * (m + 1) ^ 3
        ≤ 2 ^ 20 * (9 * X) * X ^ 3 := by gcongr <;> omega
      _ = 9 * 2 ^ 20 * X ^ 4 := by ring
      _ ≤ 2 ^ 24 * X ^ 13 := by
        have := p13 4 (by norm_num)
        calc 9 * 2 ^ 20 * X ^ 4 ≤ 2 ^ 24 * X ^ 4 := by gcongr; norm_num
          _ ≤ 2 ^ 24 * X ^ 13 := Nat.mul_le_mul_left _ this
  have hs' : stageBudget W n m ≤ 2 ^ 20 * X ^ 13 := by
    refine hs.trans (Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (by omega) 7).trans
      (p13 7 (by norm_num))))
  have h1 : X ≤ X ^ 13 := by
    calc X = X ^ 1 := (pow_one X).symm
      _ ≤ X ^ 13 := p13 1 (by norm_num)
  unfold fixedBudget edgesBudget RegisterEdgeWords.keysBudget
  have : 2 ^ 26 * X ^ 13 = 2 ^ 24 * X ^ 13 + 2 ^ 24 * X ^ 13 + 2 ^ 20 * X ^ 13 +
      (2 ^ 26 - 2 ^ 25 - 2 ^ 20) * X ^ 13 := by
    rw [show (2 : ℕ) ^ 26 = 2 ^ 24 + 2 ^ 24 + 2 ^ 20 + (2 ^ 26 - 2 ^ 25 - 2 ^ 20) by norm_num]
    ring
  have h2 : 2 ^ 10 * X ≤ (2 ^ 26 - 2 ^ 25 - 2 ^ 20) * X ^ 13 :=
    Nat.mul_le_mul (by norm_num) h1
  omega

end MWIS.FPTRegister

end
