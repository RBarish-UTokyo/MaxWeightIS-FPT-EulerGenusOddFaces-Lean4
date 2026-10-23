module

public import MWIS.Fun.Heap
public import MWIS.RibbonTable
public import MWIS.ExpandedWords
public import MWIS.RegisterIncidenceRows
public import MWIS.RegisterFaceRow
public import MWIS.CompiledTemplates

/-!
# XP heap data as explicit cell trees

The register procedures of the XP development store binary words, word lists,
edge-endpoint pairs and ribbon tables in specific cell shapes. This file gives
the corresponding explicit trees and proves that each XP representation
predicate is equivalent to `Fun.TreeAt` of that tree. A `Fun` program reading
these data structures as raw trees therefore sees exactly these trees.

* `bitsTree b`: a fixed-width word as a chain of bit cells, most significant
  first, ending in a nil cell (`bitsAt_iff`); for an in-range value it is the
  `Fun` word `Tree.word W k` (`bitsTree_word`).
* `listTree f xs`: a cons spine of items (`listRep_iff`).
* `wordsTree`, `edgeTree`, `edgeRecTree`, `tableTree`: word lists, endpoint
  pairs, ribbon-table records and whole ribbon tables.
-/

@[expose] public section

namespace MWIS.FPTTrees

open MWIS.PointerMemory MWIS.EfficientSearch MWIS.EfficientSearch.Pointer
open MWIS.ExpandedWords MWIS.RibbonTable MWIS.Fun

/-! ## Words -/

/-- A fixed-width word as a bit chain, most significant bit first. -/
def bitsTree : {n : ℕ} → Bits n → Tree
  | _, .nil => .nil
  | _, .cons b t => .bit b (bitsTree t)

theorem bitsAt_iff {h : Heap} {n : ℕ} (b : Bits n) {p : Ptr} :
    BitsAt h p b ↔ TreeAt h p (bitsTree b) := by
  induction b generalizing p with
  | nil =>
    constructor
    · intro hb; cases hb with | nil c => exact .nil c
    · intro ht; cases ht with | nil c => exact .nil c
  | cons b t ih =>
    constructor
    · intro hb
      cases hb with
      | cons c rest => exact .bit c ((ih).mp rest)
    · intro ht
      cases ht with
      | bit c tail => exact .cons c ((ih).mpr tail)

/-- `Fun` words depend only on the low bits. -/
theorem word_mod (W k j : ℕ) (hj : W ≤ j) : Tree.word W (k % 2 ^ j) = Tree.word W k := by
  induction W with
  | zero => rfl
  | succ W ih =>
    simp only [Tree.word, ih (by omega), Nat.testBit_mod_two_pow]
    simp [show W < j by omega]

/-- An in-range XP word is the `Fun` word of its value. -/
theorem bitsTree_word (W k : ℕ) (hk : k < 2 ^ W) :
    bitsTree (SparseSearchGraph.encodeBits W k) = Tree.word W k := by
  induction W generalizing k with
  | zero => rfl
  | succ W ih =>
    simp only [SparseSearchGraph.encodeBits, bitsTree, Tree.word]
    rw [ih _ (Nat.mod_lt _ (by positivity)), word_mod W k W le_rfl]
    congr 1
    rw [Nat.testBit_eq_decide_div_mod_eq]
    have h2 : 0 < 2 ^ W := by positivity
    have hlt : k / 2 ^ W < 2 := by
      rw [Nat.div_lt_iff_lt_mul h2]; rw [pow_succ] at hk; omega
    by_cases hle : 2 ^ W ≤ k
    · have : 1 ≤ k / 2 ^ W := (Nat.le_div_iff_mul_le h2).mpr (by omega)
      have h1 : k / 2 ^ W = 1 := by omega
      simp [hle, h1]
    · have h0 : k / 2 ^ W = 0 := Nat.div_eq_of_lt (by omega)
      simp [hle, h0]

/-- The zero word is the `Fun` word of zero. -/
theorem bitsTree_zero (W : ℕ) : bitsTree (Bits.zero W) = Tree.word W 0 := by
  induction W with
  | zero => rfl
  | succ W ih => simp [Bits.zero, bitsTree, Tree.word, ih]

/-! ## Lists -/

/-- A cons spine of the trees of the items. -/
def listTree {α : Type*} (f : α → Tree) (xs : List α) : Tree := Tree.ofList (xs.map f)

theorem listRep_iff {α : Type*} {R : Heap → Ptr → α → Prop} {f : α → Tree} {h : Heap}
    (hR : ∀ q x, R h q x ↔ TreeAt h q (f x)) (xs : List α) {p : Ptr} :
    ListRep R h p xs ↔ TreeAt h p (listTree f xs) := by
  induction xs generalizing p with
  | nil =>
    constructor
    · rintro ⟨ps, hl, hf⟩
      cases hf
      cases hl with | nil c => exact .nil c
    · intro ht
      cases ht with | nil c => exact ⟨[], .nil c, .nil⟩
  | cons x xs ih =>
    constructor
    · rintro ⟨ps, hl, hf⟩
      cases hf with
      | cons hx hrest =>
        cases hl with
        | cons c tail => exact .cons c ((hR _ _).mp hx) ((ih).mp ⟨_, tail, hrest⟩)
    · intro ht
      cases ht with
      | cons c head tail =>
        obtain ⟨qs, hl, hf⟩ := (ih).mpr tail
        exact ⟨_ :: qs, .cons c hl, .cons ((hR _ _).mpr head) hf⟩

/-- A list of fixed-width words. -/
def wordsTree {n : ℕ} (ws : List (Bits n)) : Tree := listTree bitsTree ws

theorem wordsAt_iff {h : Heap} {n : ℕ} (ws : List (Bits n)) {p : Ptr} :
    WordsAt h p ws ↔ TreeAt h p (wordsTree ws) :=
  listRep_iff (fun _ x => bitsAt_iff x) ws

/-! ## Endpoint pairs and ribbon tables -/

/-- An endpoint pair `.pair leftWord rightWord`. -/
def edgeTree {W : ℕ} (e : Bits W × Bits W) : Tree := .pair (bitsTree e.1) (bitsTree e.2)

theorem edgeAt_iff {h : Heap} {W : ℕ} (e : Bits W × Bits W) {p : Ptr} :
    RegisterIncidenceRows.EdgeAt h p e ↔ TreeAt h p (edgeTree e) := by
  constructor
  · rintro ⟨lp, rp, c, hl, hr⟩
    exact .pair c ((bitsAt_iff _).mp hl) ((bitsAt_iff _).mp hr)
  · intro ht
    cases ht with
    | pair c hl hr => exact ⟨_, _, c, (bitsAt_iff _).mpr hl, (bitsAt_iff _).mpr hr⟩

/-- The record of one edge of a ribbon table. -/
def edgeRecTree {W : ℕ} (r : EdgeRec W) : Tree :=
  .pair (bitsTree r.key) (.pair (bitsTree r.left) (.pair (bitsTree r.right)
    (.pair (.pair (bitsTree r.c00) (bitsTree r.c01)) (.pair (bitsTree r.c10) (bitsTree r.c11)))))

theorem edgeRecAt_iff {h : Heap} {W : ℕ} (r : EdgeRec W) {p : Ptr} :
    EdgeRecAt h p r ↔ TreeAt h p (edgeRecTree r) := by
  constructor
  · rintro ⟨kp, a, lp, b, rp, c, q0, q1, c00p, c01p, c10p, c11p,
      hp, hk, ha, hl, hb, hr, hc, hq0, h00, h01, hq1, h10, h11⟩
    exact .pair hp ((bitsAt_iff _).mp hk) (.pair ha ((bitsAt_iff _).mp hl)
      (.pair hb ((bitsAt_iff _).mp hr) (.pair hc
        (.pair hq0 ((bitsAt_iff _).mp h00) ((bitsAt_iff _).mp h01))
        (.pair hq1 ((bitsAt_iff _).mp h10) ((bitsAt_iff _).mp h11)))))
  · intro ht
    cases ht with
    | pair hp hk ht1 =>
      cases ht1 with
      | pair ha hl ht2 =>
        cases ht2 with
        | pair hb hr ht3 =>
          cases ht3 with
          | pair hc t0 t1 =>
            cases t0 with
            | pair hq0 h00 h01 =>
              cases t1 with
              | pair hq1 h10 h11 =>
                exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, hp, (bitsAt_iff _).mpr hk, ha,
                  (bitsAt_iff _).mpr hl, hb, (bitsAt_iff _).mpr hr, hc, hq0,
                  (bitsAt_iff _).mpr h00, (bitsAt_iff _).mpr h01, hq1,
                  (bitsAt_iff _).mpr h10, (bitsAt_iff _).mpr h11⟩

theorem recordsAt_iff {h : Heap} {W : ℕ} (rs : List (EdgeRec W)) {p : Ptr} :
    RecordsAt h p rs ↔ TreeAt h p (listTree edgeRecTree rs) :=
  listRep_iff (fun _ r => edgeRecAt_iff r) rs

/-- The stored table of a ribbon. -/
def tableTree (W : ℕ) {n m : ℕ} {left right : Fin m → Fin n} (R : EmbeddingFaces.Ribbon left right) :
    Tree := listTree edgeRecTree (encodeRibbon W R)

theorem tableAt_iff {h : Heap} (W : ℕ) {n m : ℕ} {left right : Fin m → Fin n}
    (R : EmbeddingFaces.Ribbon left right) {p : Ptr} :
    RecordsAt h p (encodeRibbon W R) ↔ TreeAt h p (tableTree W R) :=
  recordsAt_iff _

/-- Record trees in explicit form: the edge word, the endpoint words and the
four corner-partner keys. -/
theorem tableTree_eq (W : ℕ) {n m : ℕ} {left right : Fin m → Fin n}
    (R : EmbeddingFaces.Ribbon left right) :
    tableTree W R = Tree.ofList ((List.finRange m).map fun e =>
      edgeRecTree (encodeEdge W left right R.corner e)) := by
  simp [tableTree, listTree, encodeRibbon, List.map_map]
  rfl

/-! ## Columns of the face stage -/

/-- A signed stub `(row, sign)`: a bit cell holding the sign, over the pair of
the keys of the two signed states of the row. -/
def stubTree {Row : Type*} {width : ℕ} (key : Walks.State Row → Bits width) (s : Walks.Stub Row) :
    Tree :=
  .bit s.2 (.pair (bitsTree (key (some (s.1, false)))) (bitsTree (key (some (s.1, true)))))

/-- A column with zero, one or two stubs: a nil cell, a bucket over one stub, or
a pair of two stubs. -/
def columnTree {Row : Type*} {width : ℕ} (key : Walks.State Row → Bits width) :
    Walks.Column Row → Tree
  | .zero => .nil
  | .one s => .bucket (stubTree key s)
  | .two s t => .pair (stubTree key s) (stubTree key t)

theorem stubAt_iff {Row : Type*} {width : ℕ} (key : Walks.State Row → Bits width) {h : Heap}
    (s : Walks.Stub Row) {p : Ptr} :
    CompiledTemplates.StubAt key h p s ↔ TreeAt h p (stubTree key s) := by
  constructor
  · rintro ⟨row, minus, plus, c1, c2, hm, hp⟩
    exact .bit c1 (.pair c2 ((bitsAt_iff _).mp hm) ((bitsAt_iff _).mp hp))
  · intro ht
    cases ht with
    | bit c1 tail =>
      cases tail with
      | pair c2 hm hp => exact ⟨_, _, _, c1, c2, (bitsAt_iff _).mpr hm, (bitsAt_iff _).mpr hp⟩

theorem columnAt_iff {Row : Type*} {width : ℕ} (key : Walks.State Row → Bits width) {h : Heap}
    (c : Walks.Column Row) {p : Ptr} :
    CompiledTemplates.ColumnAt key h p c ↔ TreeAt h p (columnTree key c) := by
  constructor
  · intro hc
    cases hc with
    | zero cell => exact .nil cell
    | one cell stub => exact .bucket cell ((stubAt_iff key _).mp stub)
    | two cell first second =>
      exact .pair cell ((stubAt_iff key _).mp first) ((stubAt_iff key _).mp second)
  · intro ht
    cases c with
    | zero => cases ht with | nil cell => exact .zero cell
    | one s => cases ht with | bucket cell items => exact .one cell ((stubAt_iff key s).mpr items)
    | two s t =>
      cases ht with
      | pair cell hs ht' => exact .two cell ((stubAt_iff key s).mpr hs) ((stubAt_iff key t).mpr ht')

theorem columnsAt_iff {Row : Type*} {width : ℕ} (key : Walks.State Row → Bits width) {h : Heap}
    (cs : List (Walks.Column Row)) {p : Ptr} :
    ListRep (CompiledTemplates.ColumnAt key) h p cs ↔ TreeAt h p (listTree (columnTree key) cs) :=
  listRep_iff (fun _ c => columnAt_iff key c) cs

/-! ## Constant words -/

theorem constsAt_iff {b : ℕ} (one zero : Bits b) {h : Heap} {p : Ptr} :
    RegisterFaceRow.ConstsAt one zero h p ↔ TreeAt h p (.pair (bitsTree one) (bitsTree zero)) := by
  constructor
  · rintro ⟨op, zp, c, ho, hz⟩
    exact .pair c ((bitsAt_iff _).mp ho) ((bitsAt_iff _).mp hz)
  · intro ht
    cases ht with
    | pair c ho hz => exact ⟨_, _, c, (bitsAt_iff _).mpr ho, (bitsAt_iff _).mpr hz⟩

end MWIS.FPTTrees

end
