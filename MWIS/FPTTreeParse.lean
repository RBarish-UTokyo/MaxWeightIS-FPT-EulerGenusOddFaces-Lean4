module

public import MWIS.FPTRegister
public import MWIS.FunNetworkLib
public import MWIS.FunNetworkEncode

/-!
# Reading the inputs of the `Fun` stages, and writing their outputs

Closed `Fun` programs that turn the cell trees passed to the two `Fun` stages of
the fixed-parameter hard procedure (`FPTRegister.ConstsSpec`,
`FPTRegister.FunStageSpec`) into plain `Fun` data, and that write the stage
outputs:

* `parseEdges`: the endpoint records, as the list of `(left e, right e)`;
* `parseWords`: a list of words, as the list of their values (the cost words, the
  vertex range words);
* `parseColumns`: the face-stage columns, as the list over edges of
  `FunNetwork.columnCode (faceColumns R e)`, i.e. the stub codes `2 i + 1 + sign`;
* `parseCount`: the row-count word `2 r + 1`, as `r`;
* `formatOutput`: the slack list, as `FPTRegister.outputTree`;
* `consts`: the whole constants stage, from the two word lists to
  `FPTRegister.constsTree`.

Each program has an exact denotation on the trees of the stage contracts and an
explicit cost bound.
-/

@[expose] public section

namespace MWIS.FPTTreeParse

open MWIS.Fun MWIS.FunLP MWIS.FunNetwork MWIS.FPTTrees MWIS.FPTRegister MWIS.EfficientSearch
open MWIS.RibbonTable (rangeWords)

/-! ## Tree lemmas -/

theorem items_ofList (l : List Tree) : (Tree.ofList l).items = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [Tree.ofList, Tree.items, ih]

theorem items_listTree {α : Type*} (f : α → Tree) (xs : List α) :
    (listTree f xs).items = xs.map f := items_ofList _

theorem spine_ofList (l : List Tree) : (Tree.ofList l).spine = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [Tree.ofList, Tree.spine, ih]

theorem bitList_bitsTree : ∀ {n : ℕ} (b : Bits n), (bitsTree b).bitList.length = n
  | _, .nil => rfl
  | _, .cons _ t => by simp [bitsTree, Tree.bitList, bitList_bitsTree t]

theorem foldl_bitsTree : ∀ {n : ℕ} (b : Bits n) (acc : ℕ),
    (bitsTree b).bitList.foldl (fun a x => 2 * a + if x then 1 else 0) acc = acc * 2 ^ n + b.value
  | _, .nil, acc => by simp [bitsTree, Tree.bitList, Bits.value]
  | _, .cons x t, acc => by
    simp only [bitsTree, Tree.bitList, List.foldl_cons, Bits.value]
    rw [foldl_bitsTree t]
    cases x <;> simp <;> ring

/-- The value read from a word tree is the value of the word. -/
theorem wordValue_bitsTree {n : ℕ} (b : Bits n) : (bitsTree b).wordValue = b.value := by
  unfold Tree.wordValue
  rw [foldl_bitsTree]
  simp

theorem wordValue_word (W k : ℕ) (hk : k < 2 ^ W) :
    (bitsTree (GraphReachEncoded.word W k)).wordValue = k := by
  rw [wordValue_bitsTree]
  exact GraphReachEncoded.word_value hk

/-! ## Maps -/

/-- Map a closed function over a list. -/
def mapF {α β : Ty} (f : Fn α β) : Fn (.list α) (.list β) :=
  call (rev β) (.foldl v0 .nil (.cons (call f v0) v1))

theorem mapF_inner {α β : Ty} (f : Fn α β) (l : List α.denote) :
    (Expr.foldl (Γ := [.list α]) v0 .nil (.cons (call f v0) v1)).denote (l, ()) =
      (l.map f.apply).reverse := by
  simp only [Expr.denote, Var.get, denote_call]
  simp

@[simp] theorem mapF_apply {α β : Ty} (f : Fn α β) (l : List α.denote) :
    (mapF f).apply l = l.map f.apply := by
  have h := mapF_inner f l
  unfold mapF
  simp only [Fn.apply] at h ⊢
  rw [denote_call, h]
  exact (rev_apply β _).trans (List.reverse_reverse _)

theorem mapF_cost {α β : Ty} (f : Fn α β) (l : List α.denote) (c0 : ℕ)
    (hf : ∀ a ∈ l, f.costAt a ≤ c0) :
    (mapF f).costAt l ≤ (l.length + 1) * (c0 + 20) := by
  have hfold := cost_foldl_le (Γ := [.list α]) v0 .nil (.cons (call f v0) v1) (l, ())
    (fun _ => True) (c0 + 10) trivial
    (fun acc y hy _ => by
      refine ⟨trivial, ?_⟩
      simp only [Expr.cost, cost_call, Var.index, Expr.denote, Var.get]
      have := hf y hy
      omega)
  have hrev := rev_cost β ((l.map f.apply).reverse)
  simp only [List.length_reverse, List.length_map] at hrev
  have hs : (v0 : Expr [.list α] (.list α)).cost (l, ()) = 1 := rfl
  have hn : (Expr.nil (Γ := [.list α]) (a := β)).cost (l, ()) = 1 := rfl
  have hd : (v0 : Expr [.list α] (.list α)).denote (l, ()) = l := rfl
  rw [hs, hn, hd] at hfold
  calc (mapF f).costAt l = (Expr.foldl (Γ := [.list α]) v0 .nil
        (.cons (call f v0) v1)).cost (l, ()) + (rev β).costAt ((l.map f.apply).reverse) + 1 := by
        unfold mapF; simp only [Fn.costAt]; rw [cost_call, mapF_inner]; rfl
    _ ≤ (1 + 1 + l.length * (c0 + 10 + 1) + 1) + (5 * l.length + 3) + 1 := by omega
    _ ≤ _ := by nlinarith

/-- The items of a cons spine. -/
def itemsF : Fn .tree (.list .tree) := .items v0

@[simp] theorem itemsF_apply (t : Tree) : itemsF.apply t = t.items := rfl

theorem itemsF_cost (t : Tree) : itemsF.costAt t = t.spine + 2 := by
  show 0 + 1 + t.spine + 1 = t.spine + 2
  omega

/-! ## Words -/

/-- The value of a word. -/
def wordF : Fn .tree .int := .wordValue v0

@[simp] theorem wordF_apply (t : Tree) : wordF.apply t = (t.wordValue : ℤ) := rfl

theorem wordF_cost (t : Tree) : wordF.costAt t = t.bitList.length + 2 := by
  show 0 + 1 + t.bitList.length + 1 = t.bitList.length + 2
  omega

/-- The values of a list of words. -/
def parseWords : Fn .tree (.list .int) := (mapF wordF).comp itemsF

theorem parseWords_apply {n : ℕ} (ws : List (Bits n)) :
    parseWords.apply (wordsTree ws) = ws.map fun b => (b.value : ℤ) := by
  simp [parseWords, wordsTree, items_listTree, List.map_map, Function.comp_def,
    wordValue_bitsTree]

/-- The cost words become the costs. -/
theorem parseWords_cost {n : ℕ} (ws : List (Bits n)) :
    parseWords.costAt (wordsTree ws) ≤ (ws.length + 1) * (n + 22) + ws.length + 3 := by
  have hl : (wordsTree ws).items = ws.map bitsTree := items_listTree _ _
  have hs : (wordsTree ws).spine = ws.length := by
    rw [wordsTree, listTree, spine_ofList, List.length_map]
  have hm := mapF_cost wordF ((wordsTree ws).items) (n + 2) (by
    intro a ha
    rw [hl] at ha
    obtain ⟨b, -, rfl⟩ := List.mem_map.mp ha
    rw [wordF_cost, bitList_bitsTree])
  rw [hl, List.length_map] at hm
  have hc : parseWords.costAt (wordsTree ws) =
      itemsF.costAt (wordsTree ws) + (mapF wordF).costAt ((wordsTree ws).items) + 1 :=
    Fn.costAt_comp _ _ _
  rw [hc, itemsF_cost, hs, hl]
  have e : (ws.length + 1) * (n + 2 + 20) = (ws.length + 1) * (n + 22) := by ring
  omega

/-! ## Endpoint records -/

/-- An endpoint record, as the pair of endpoint values. -/
def edgePairF : Fn .tree (.prod .int .int) :=
  .treeCase v0 (.pair (.int 0) (.int 0)) (.pair (.int 0) (.int 0)) (.pair (.int 0) (.int 0))
    (.pair (.int 0) (.int 0)) (.pair (.int 0) (.int 0)) (.pair (.wordValue v0) (.wordValue v1))

theorem edgePairF_apply {W : ℕ} (e : Bits W × Bits W) :
    edgePairF.apply (edgeTree e) = ((e.1.value : ℤ), (e.2.value : ℤ)) := by
  simp [edgePairF, edgeTree, Fn.apply, Expr.denote, Var.get, wordValue_bitsTree]

theorem edgePairF_cost {W : ℕ} (e : Bits W × Bits W) : edgePairF.costAt (edgeTree e) ≤ 2 * W + 10 := by
  simp [edgePairF, edgeTree, Fn.costAt, Expr.cost, Expr.denote, Var.get, Var.index,
    bitList_bitsTree]
  ring_nf
  omega

/-- The endpoint records, as the list of endpoint pairs. -/
def parseEdges : Fn .tree (.list (.prod .int .int)) := (mapF edgePairF).comp itemsF

/-- The endpoint records become the endpoints. -/
theorem parseEdges_apply (W : ℕ) {n m : ℕ} (left right : Fin m → Fin n) (hn : n < 2 ^ W) :
    parseEdges.apply (edgesTree W left right) =
      (List.finRange m).map fun e => (((left e : ℕ) : ℤ), ((right e : ℕ) : ℤ)) := by
  simp only [parseEdges, Fn.apply_comp, itemsF_apply, edgesTree, items_listTree, mapF_apply,
    List.map_map, GraphReachEncoded.edgeWords]
  apply List.map_congr_left
  intro e _
  simp only [Function.comp_apply, edgePairF_apply]
  rw [GraphReachEncoded.word_value (lt_trans (left e).isLt hn),
    GraphReachEncoded.word_value (lt_trans (right e).isLt hn)]

theorem parseEdges_cost (W : ℕ) {n m : ℕ} (left right : Fin m → Fin n) :
    parseEdges.costAt (edgesTree W left right) ≤ (m + 1) * (2 * W + 30) + m + 3 := by
  have hl : (edgesTree W left right).items = (GraphReachEncoded.edgeWords W left right).map edgeTree :=
    items_listTree _ _
  have hlen : (GraphReachEncoded.edgeWords W left right).length = m := by
    rw [GraphReachEncoded.edgeWords, List.length_map, List.length_finRange]
  have hs : (edgesTree W left right).spine = m := by
    rw [edgesTree, listTree, spine_ofList, List.length_map, hlen]
  have hm := mapF_cost edgePairF ((edgesTree W left right).items) (2 * W + 10) (by
    intro a ha
    rw [hl] at ha
    obtain ⟨b, -, rfl⟩ := List.mem_map.mp ha
    exact edgePairF_cost b)
  rw [hl, List.length_map, hlen] at hm
  have hc : parseEdges.costAt (edgesTree W left right) =
      itemsF.costAt (edgesTree W left right) +
        (mapF edgePairF).costAt ((edgesTree W left right).items) + 1 :=
    Fn.costAt_comp _ _ _
  rw [hc, itemsF_cost, hs, hl]
  have e : (m + 1) * (2 * W + 10 + 20) = (m + 1) * (2 * W + 30) := by ring
  omega

/-! ## Face-stage columns -/

/-- The code of a stub: the value of the key of its signed state. -/
def stubF : Fn .tree .int :=
  .treeCase v0 (.int 0)
    (.treeCase v1 (.int 0) (.int 0) (.int 0) (.int 0) (.int 0) (.ite v2 (.wordValue v1) (.wordValue v0)))
    (.int 0) (.int 0) (.int 0) (.int 0)

/-- A column, as the list of the codes of its stubs. -/
def columnF : Fn .tree (.list .int) :=
  .treeCase v0 .nil .nil .nil .nil (.cons (call stubF v0) .nil)
    (.cons (call stubF v0) (.cons (call stubF v1) .nil))

theorem stubF_apply {wk r : ℕ} (s : Walks.Stub (Fin r)) (hk : 2 * r + 1 < 2 ^ wk) :
    stubF.apply (stubTree (RegisterFaceColumns.stateKey wk r) s) = stubCode s := by
  obtain ⟨i, b⟩ := s
  have hi := i.isLt
  have hval : ∀ c : Bool, (bitsTree (RegisterFaceColumns.stateKey wk r (some (i, c)))).wordValue =
      2 * i.val + (if c then 1 else 0) + 1 := by
    intro c
    rw [RegisterFaceColumns.stateKey_some, wordValue_bitsTree]
    exact GraphReachEncoded.word_value (by cases c <;> simp <;> omega)
  simp only [stubF, stubTree, Fn.apply, Expr.denote, Var.get]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hval false]; simp [stubCode]
  · simp only [↓reduceIte]
    rw [hval true]; simp [stubCode]

theorem columnF_apply {wk r : ℕ} (c : Walks.Column (Fin r)) (hk : 2 * r + 1 < 2 ^ wk) :
    columnF.apply (columnTree (RegisterFaceColumns.stateKey wk r) c) = columnCode c := by
  cases c with
  | zero => rfl
  | one s =>
    simp only [columnF, columnTree, Fn.apply, Expr.denote, Var.get, denote_call]
    rw [show Expr.denote stubF (stubTree _ s, ()) = stubCode s from stubF_apply s hk]; rfl
  | two s t =>
    simp only [columnF, columnTree, Fn.apply, Expr.denote, Var.get, denote_call]
    rw [show Expr.denote stubF (stubTree _ s, ()) = stubCode s from stubF_apply s hk,
      show Expr.denote stubF (stubTree _ t, ()) = stubCode t from stubF_apply t hk]; rfl

theorem stubF_cost {wk r : ℕ} (s : Walks.Stub (Fin r)) :
    stubF.costAt (stubTree (RegisterFaceColumns.stateKey wk r) s) ≤ wk + 12 := by
  obtain ⟨i, b⟩ := s
  cases b <;>
  simp [stubF, stubTree, Fn.costAt, Expr.cost, Expr.denote, Var.get, Var.index,
    bitList_bitsTree] <;> ring_nf <;> omega

theorem columnF_cost {wk r : ℕ} (c : Walks.Column (Fin r)) :
    columnF.costAt (columnTree (RegisterFaceColumns.stateKey wk r) c) ≤ 2 * wk + 40 := by
  cases c with
  | zero => simp [columnF, columnTree, Fn.costAt, Expr.cost, Expr.denote, Var.get, Var.index]
  | one s =>
    have := stubF_cost (wk := wk) s
    simp only [Fn.costAt] at this
    simp only [columnF, columnTree, Fn.costAt, Expr.cost, Expr.denote, Var.get, Var.index,
      cost_call, Fn.costAt]
    ring_nf at this ⊢
    omega
  | two s t =>
    have h1 := stubF_cost (wk := wk) s
    have h2 := stubF_cost (wk := wk) t
    simp only [Fn.costAt] at h1 h2
    simp only [columnF, columnTree, Fn.costAt, Expr.cost, Expr.denote, Var.get, Var.index,
      cost_call, Fn.costAt]
    ring_nf at h1 h2 ⊢
    omega

/-- The face-stage columns, as the list over edges of the stub-code lists. -/
def parseColumns : Fn .tree (.list (.list .int)) := (mapF columnF).comp itemsF

/-- The face-stage columns become the stub codes of the even-face columns. -/
theorem parseColumns_apply {n m : ℕ} {left right : Fin m → Fin n}
    (R : EmbeddingFaces.Ribbon left right) :
    parseColumns.apply (columnsTree R) =
      (List.finRange m).map fun e => columnCode (FPTHard.faceColumns R e) := by
  have hr : rowCount R ≤ 4 * m := by
    simpa using R.evenRow_count_le (EmbeddingFaces.Flag.canonicalOrder m)
  have hk : 2 * rowCount R + 1 < 2 ^ fptWidth n m := by
    have := fptWidth_fits n m; omega
  simp only [parseColumns, Fn.apply_comp, itemsF_apply, columnsTree, items_listTree, mapF_apply,
    List.map_map]
  apply List.map_congr_left
  intro e _
  exact columnF_apply _ hk

theorem parseColumns_cost {n m : ℕ} {left right : Fin m → Fin n}
    (R : EmbeddingFaces.Ribbon left right) :
    parseColumns.costAt (columnsTree R) ≤ (m + 1) * (2 * fptWidth n m + 60) + m + 3 := by
  have hl : (columnsTree R).items =
      ((List.finRange m).map (FPTHard.faceColumns R)).map
        (columnTree (RegisterFaceColumns.stateKey (fptWidth n m) (rowCount R))) :=
    items_listTree _ _
  have hs : (columnsTree R).spine = m := by
    rw [columnsTree, listTree, spine_ofList, List.length_map, List.length_map, List.length_finRange]
  have hm := mapF_cost columnF ((columnsTree R).items) (2 * fptWidth n m + 40) (by
    intro a ha
    rw [hl] at ha
    obtain ⟨b, -, rfl⟩ := List.mem_map.mp ha
    exact columnF_cost b)
  rw [hl, List.length_map, List.length_map, List.length_finRange] at hm
  have hc : parseColumns.costAt (columnsTree R) =
      itemsF.costAt (columnsTree R) + (mapF columnF).costAt ((columnsTree R).items) + 1 :=
    Fn.costAt_comp _ _ _
  rw [hc, itemsF_cost, hs, hl]
  have e : (m + 1) * (2 * fptWidth n m + 40 + 20) = (m + 1) * (2 * fptWidth n m + 60) := by ring
  omega

/-! ## The row count -/

/-- The row-count word `2 r + 1`, as `r`. -/
def parseCount : Fn .tree .int := .arith .div (.arith .sub (.wordValue v0) (.int 1)) (.int 2)

theorem parseCount_apply (B r : ℕ) (hr : 2 * r + 1 < 2 ^ B) :
    parseCount.apply (bitsTree (GraphReachEncoded.word B (2 * r + 1))) = r := by
  simp only [parseCount, Fn.apply, Expr.denote, IntOp.eval, Var.get]
  rw [wordValue_word _ _ hr]
  have : ((2 * r + 1 : ℕ) : ℤ) - 1 = 2 * r := by push_cast; ring
  rw [this, Int.mul_ediv_cancel_left _ (by norm_num)]

theorem parseCount_cost (B k : ℕ) :
    parseCount.costAt (bitsTree (GraphReachEncoded.word B k)) ≤ (B + 8) ^ 2 + B + 10 := by
  simp only [parseCount, Fn.costAt, Expr.cost, Var.index, IntOp.charge, Expr.denote, Var.get,
    bitList_bitsTree, IntOp.eval]
  have hv : (bitsTree (GraphReachEncoded.word B k)).wordValue < 2 ^ B := by
    rw [wordValue_bitsTree]; exact Bits.value_lt _
  have hb : bits ((bitsTree (GraphReachEncoded.word B k)).wordValue : ℤ) ≤ B := by
    unfold bits; simp only [Int.natAbs_natCast]; exact Nat.size_le.mpr hv
  have hb2 : bits (((bitsTree (GraphReachEncoded.word B k)).wordValue : ℤ) - 1) ≤ B + 1 := by
    unfold bits
    apply Nat.size_le.mpr
    have : (((bitsTree (GraphReachEncoded.word B k)).wordValue : ℤ) - 1).natAbs ≤ 2 ^ B := by omega
    calc _ ≤ 2 ^ B := this
      _ < 2 ^ (B + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have h1 : bits (1 : ℤ) = 1 := rfl
  have h2 : bits (2 : ℤ) = 2 := rfl
  rw [h1, h2]
  have hsq := Nat.pow_le_pow_left (show bits (((bitsTree (GraphReachEncoded.word B k)).wordValue : ℤ) - 1) +
    2 + 1 ≤ B + 8 by omega) 2
  nlinarith

/-! ## The output and the constants -/

/-- A word of a given width and value. -/
def widthWordF : Fn (.prod .int .int) .tree := .word (.fst v0) (.snd v0)

/-- The slack list, as the list of its words of width `B`. -/
def formatOutput : Fn (.prod .int (.list .int)) .tree := .ofItems (call (mapWith widthWordF) v0)

/-- The slack list becomes the output tree of the numerical stage. -/
theorem formatOutput_apply (n m : ℕ) (s : Fin m → ℕ) (hs : ∀ e, s e ≤ 1) :
    formatOutput.apply ((fptWidth n m : ℤ), (List.finRange m).map fun e => (s e : ℤ)) =
      outputTree n m s := by
  rw [outputTree_eq n m s hs]
  show Tree.ofList ((mapWith widthWordF).apply _) = _
  rw [mapWith_apply]
  simp [Expr.denote, Var.get, List.map_map, widthWordF, Fn.apply, Function.comp_def]

/-- The length of a list. -/
def lengthF (a : Ty) : Fn (.list a) .int := .foldl v0 (.int 0) (.arith .add v1 (.int 1))

theorem lengthF_fold {α : Type*} (l : List α) (k : ℤ) :
    l.foldl (fun acc (_ : α) => acc + 1) k = k + l.length := by
  induction l generalizing k with
  | nil => simp
  | cons a l ih => simp [ih]; ring

@[simp] theorem lengthF_apply (a : Ty) (l : List a.denote) : (lengthF a).apply l = l.length := by
  simp [lengthF, Fn.apply, Expr.denote, Var.get, IntOp.eval, lengthF_fold]

@[simp] theorem lengthF_denote (a : Ty) (l : List a.denote) :
    (lengthF a).denote (l, ()) = l.length := lengthF_apply a l

/-- **The constants stage.** From the vertex range words and the edge index words:
the words of one and zero of width `fptWidth n m = 3 n + m + 4`. -/
def consts : Fn (.prod .tree .tree) .tree :=
  .letE (call (lengthF .tree) (.items (.fst v0)))
    (.letE (call (lengthF .tree) (.items (.snd v1)))
      (.letE (.arith .add (.arith .add (.arith .mul (.int 3) v1) v0) (.int 4))
        (.treePair (.word v0 (.int 1)) (.word v0 (.int 0)))))

theorem consts_apply (W n m : ℕ) :
    consts.apply (wordsTree (rangeWords W n), wordsTree (GraphReachEncoded.rangeWords W m)) =
      constsTree n m := by
  rw [constsTree_eq]
  have hn : (wordsTree (rangeWords W n)).items.length = n := by
    rw [wordsTree, items_listTree, List.length_map, RibbonTable.rangeWords_length]
  have hm : (wordsTree (GraphReachEncoded.rangeWords W m)).items.length = m := by
    rw [wordsTree, items_listTree, List.length_map]; simp [GraphReachEncoded.rangeWords]
  simp only [consts, Fn.apply, Expr.denote, Var.get, denote_call, lengthF, lengthF_fold,
    IntOp.eval, hn, hm, zero_add]
  have : ((3 * (n : ℤ) + m + 4)).toNat = fptWidth n m := by unfold fptWidth; omega
  simp [this]

end MWIS.FPTTreeParse

end
