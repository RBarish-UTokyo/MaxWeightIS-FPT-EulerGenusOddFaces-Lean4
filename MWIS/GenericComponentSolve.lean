module

public import MWIS.GenericEncoded
public import MWIS.RegisterComponentSolve

/-!
# Solving one computed component, for a parametric hard function

This is `RegisterComponentSolve` with the hard-component contract
`GenericHardSpec`: the procedure called on connected nonbipartite all-half
components returns the stored words of `hs R w root` for a hard function `hs`.
The procedure records, bodies and budgets are those of `RegisterComponentSolve`;
only the correctness theorems are restated for the parametric output.
-/

@[expose] public section

namespace MWIS.GenericComponentSolve

open MWIS.PointerMemory MWIS.RegisterMachine MWIS.EfficientSearch.Pointer
open MWIS.EfficientSearch MWIS.RibbonTable MWIS.RegisterFlagKeys
open MWIS.ExpandedWords MWIS.ResidualWords MWIS.EmbeddingFaces
open MWIS.GraphReachEncoded (one reachE parityReachE colorWordsE adjArcs parityArcs
  parityNodeWords parityWord edgeWords setWords)
open MWIS.RegisterComponentSolve

variable {p : ℕ}
variable (hs : Generic.HardFn)

/-- The hard-component contract for the hard function `hs`: on every connected
nonbipartite all-half input with nonnegative weights, the procedure `hard`
returns the stored words of `hs R w root` at the canonical root, within
`hb R w` events. -/
def GenericHardSpec (code : Code p) (hard : Fin p) (W : ℕ) (WeightAt : Heap → Ptr → ℚ → Prop)
    (hs : Generic.HardFn) (hb : HardBudget) : Prop :=
  ∀ {n m : ℕ} {left right : Fin m → Fin n} (R : Ribbon left right) (w : Fin n → ℚ) (hn : 0 < n),
    n < 2 ^ W → m < 2 ^ W → Incidence.Connected left right → ¬Incidence.Bipartite left right →
    (∀ v, 0 ≤ w v) → Persistence.Optimal (EdgeTransport.Adj left right) w (fun _ => 1 / 2) →
    ∀ {h : Heap}, Valid h → ∀ {tp rp wp : Ptr}, RecordsAt h tp (encodeRibbon W R) →
      WordsAt h rp (rangeWords W n) → ListRep WeightAt h wp (List.ofFn w) →
      ∃ out q, Extends h out ∧ Valid out ∧
        WordsAt out q (setWords W (hs R w ⟨0, hn⟩)) ∧
        Within code h (initialRegisters [.pointer tp, .pointer rp, .pointer wp]) (code hard)
          [.pointer q] out (hb R w)

/-- The XP contract is the generic contract for the XP hard solver. -/
theorem hardSpec_xp {code : Code p} {hard : Fin p} {W : ℕ} {WeightAt : Heap → Ptr → ℚ → Prop}
    {hb : HardBudget} (h : HardSpec code hard W WeightAt hb) :
    GenericHardSpec code hard W WeightAt Generic.xpHard hb := h

/-- From the stored table, range words and weights of a connected all-half
graph with nonnegative weights, the procedure returns the stored words of the
canonical-root solver `halfSolve`. -/
theorem local_compiled (ids : Procedures p) (code : Code p) (hm : ids.Matches code)
    {W : ℕ} (WeightAt : Heap → Ptr → ℚ → Prop)
    (weightMono : ∀ {h h' : Heap}, Extends h h' → ∀ ptr x, WeightAt h ptr x → WeightAt h' ptr x)
    (hb : HardBudget) (hard : GenericHardSpec code ids.hard W WeightAt hs hb)
    {k ke : ℕ} (hk : k < 2 ^ W) (hke : ke < 2 ^ W) (hk0 : 0 < k) {left right : Fin ke → Fin k}
    (R : Ribbon left right) (w : Fin k → ℚ) (hc : Incidence.Connected left right)
    (hw : ∀ v, 0 ≤ w v)
    (ho : Persistence.Optimal (EdgeTransport.Adj left right) w (fun _ => 1 / 2))
    {h : Heap} (hh : Valid h) {tp rp wp op : Ptr}
    (hT : RecordsAt h tp (encodeRibbon W R)) (hr : WordsAt h rp (rangeWords W k))
    (hwp : ListRep WeightAt h wp (List.ofFn w)) (hop : BitsAt h op one) :
    ∃ out q, Extends h out ∧ Valid out ∧
      WordsAt out q (setWords W (Generic.halfSolve hs R w ⟨0, hk0⟩)) ∧
      Within code h (initialRegisters [.pointer tp, .pointer rp, .pointer wp, .pointer op])
        (code ids.localSolve) [.pointer q] out (localBudget W k ke + hb R w) := by
  have hm' := hm
  obtain ⟨-, hlocal, -, -, -, hroots, harcs, -⟩ := hm'
  have hroots' := hroots
  obtain ⟨-, -, -, -, -, hres⟩ := hroots'
  obtain ⟨o1, pa, e1, v1, hpa, w1⟩ :=
    RegisterGraphArcs.parityArcs_compiled ids.arcs code harcs hh hT hop
  rw [RegisterGraphArcs.edgePairs_encode] at hpa
  obtain ⟨o2, pn, e2, v2, hpn, w2⟩ :=
    RegisterGraphArcs.parityNodes_compiled ids.arcs code harcs v1 (hr.mono e1)
  have e12 := e1.trans e2
  obtain ⟨rest, hrest⟩ := rangeWords_cons (W := W) hk0
  have hr2 := hr.mono e12
  rw [hrest] at hr2
  obtain ⟨x0, rt, cell, hx0, -⟩ := WordsAt.cons_iff.mp hr2
  obtain ⟨e3, v3, b3⟩ := alloc_bit v2 false hx0
  obtain ⟨o4, ps, rtp, e4, v4, hps, w4⟩ := RegisterComponentRoots.search_compiled ids.roots code
    hroots v3 ((hpa.mono e2).mono e3) ((hop.mono e12).mono e3) (hpn.mono e3) b3
  change WordsAt o4 ps (parityReachE (edgeWords W left right) (rangeWords W k) (word W 0)) at hps
  obtain ⟨e5, v5, b5⟩ := alloc_bit v4 true ((hx0.mono e3).mono e4)
  have w6 := RegisterMembership.compiled code ids.roots.residual.member ids.roots.residual.cmp
    hres.2.2.2.1 hres.2.2.2.2.2.2.2 b5 (hps.mono e5)
  change Within code _ _ _
    [.flag (RegisterMembership.found (parityWord true (word W 0))
      (parityReachE (edgeWords W left right) (rangeWords W k) (word W 0)))] _ _ at w6
  have hpf := GraphReachEncoded.parity_found_iff left right hk ⟨0, hk0⟩ ⟨0, hk0⟩ true
  rw [AllHalfEncoded.rangeWords_eq] at hpf
  change RegisterMembership.found (parityWord true (word W 0))
      (parityReachE (edgeWords W left right) (rangeWords W k) (word W 0)) = true ↔ _ at hpf
  have hlen := RegisterComponentRoots.reachE_length (parityArcs (edgeWords W left right))
    (parityNodeWords (rangeWords W k)) (parityWord false (word W 0))
  rw [parityNodeWords_length, rangeWords_length] at hlen
  change (parityReachE (edgeWords W left right) (rangeWords W k) (word W 0)).length ≤
    2 * k + 1 at hlen
  have hpaLen : (parityArcs (edgeWords W left right)).length = 4 * ke := by
    rw [parityArcs_length]; simp [edgeWords]
  have hpnLen : (parityNodeWords (rangeWords W k)).length = 2 * k := by
    rw [parityNodeWords_length, rangeWords_length]
  have hmb := membershipBudget_mono (k := W + 1) hlen
  have e15 := (((e12.trans e3).trans e4).trans e5)
  by_cases hseen : ((⟨0, hk0⟩ : Fin k), true) ∈
      (ComputedOddRow.paritySearch left right (List.finRange ke) (List.finRange k) ⟨0, hk0⟩).seen
  · have hf := hpf.mpr hseen
    rw [hf] at w6
    obtain ⟨out, q, e6, v6, hq, wH⟩ := hard R w hk0 hk hke hc
      (ComputedOddRow.nonbipartite_of_seen left right (List.finRange ke) (List.finRange k)
        (fun v => List.mem_finRange v) ⟨0, hk0⟩ hseen) hw ho v5 (hT.mono e15) (hr.mono e15)
      (ListRep.mono e15 (weightMono e15) hwp)
    refine ⟨out, q, e15.trans e6, v6, ?_, ?_⟩
    · simpa only [Generic.halfSolve, hseen, ↓reduceIte] using hq
    rw [hlocal]
    refine (call_of (by reg_simp) w1 (call_of (by reg_simp) w2
      (Within.load (pointer := rp) (c := Cell.cons x0 rt) (by reg_simp) cell
      (Within.allocate (c := Cell.bit false x0) (by reg_simp)
      (call_of (by reg_simp) w4
      (Within.allocate (c := Cell.bit true x0) (by reg_simp)
      (call_of (by reg_simp) w6
      (Within.branch (b := true) (by reg_simp)
      (call_of (by reg_simp) wH (ret_values (by reg_simp) le_rfl)))))))))).mono ?_
    simp only [localBudget, hpaLen, hpnLen, CellExpr.args, List.length_cons, List.length_nil,
      encodeRibbon_length, rangeWords_length]
    omega
  · have hf : RegisterMembership.found (parityWord true (word W 0))
        (parityReachE (edgeWords W left right) (rangeWords W k) (word W 0)) = false := by
      rw [← Bool.not_eq_true, hpf]; exact hseen
    rw [hf] at w6
    obtain ⟨out, q, e6, v6, hq, wC⟩ := color_compiled ids code hm v5 (hr.mono e15)
      (hps.mono e5) hlen
    have hcol := GraphReachEncoded.colorClass_encode left right hk ⟨0, hk0⟩
    rw [AllHalfEncoded.rangeWords_eq] at hcol
    change colorWordsE (parityReachE (edgeWords W left right) (rangeWords W k) (word W 0))
      (rangeWords W k) = _ at hcol
    refine ⟨out, q, e15.trans e6, v6, ?_, ?_⟩
    · simp only [Generic.halfSolve, hseen, ↓reduceIte]
      rw [← hcol]
      exact hq
    rw [hlocal]
    refine (call_of (by reg_simp) w1 (call_of (by reg_simp) w2
      (Within.load (pointer := rp) (c := Cell.cons x0 rt) (by reg_simp) cell
      (Within.allocate (c := Cell.bit false x0) (by reg_simp)
      (call_of (by reg_simp) w4
      (Within.allocate (c := Cell.bit true x0) (by reg_simp)
      (call_of (by reg_simp) w6
      (Within.branch (b := false) (by reg_simp)
      (call_of (by reg_simp) wC (ret_values (by reg_simp) le_rfl)))))))))).mono ?_
    simp only [localBudget, hpaLen, hpnLen, CellExpr.args, List.length_cons, List.length_nil,
      encodeRibbon_length, rangeWords_length]
    omega

/-- For a root word and the shared context, the procedure prepends the
reversed original words of the solved component of the root. -/
theorem item_compiled (ids : Procedures p) (code : Code p) (hm : ids.Matches code)
    {W : ℕ} (WeightAt : Heap → Ptr → ℚ → Prop)
    (weightMono : ∀ {h h' : Heap}, Extends h h' → ∀ ptr x, WeightAt h ptr x → WeightAt h' ptr x)
    (hb : HardBudget) (hard : GenericHardSpec code ids.hard W WeightAt hs hb)
    {n m : ℕ} (hn : n < 2 ^ W) (hmW : m < 2 ^ W) {left right : Fin m → Fin n}
    (H : Ribbon left right) (w : Fin n → ℚ) (hw : ∀ v, 0 ≤ w v)
    (ho : Persistence.Optimal (EdgeTransport.Adj left right) w (fun _ => 1 / 2))
    (r : Fin n) {h : Heap} (hh : Valid h) {xp dp acc : Ptr} {as : List (Bits W)}
    (hx : BitsAt h xp (word W r.val)) (hd : CtxAt WeightAt W H w h dp) (ha : WordsAt h acc as) :
    ∃ out q, Extends h out ∧ Valid out ∧ WordsAt out q (GenericEncoded.step hs W H w as r) ∧
      Within code h (initialRegisters [.pointer xp, .pointer dp, .pointer acc]) (code ids.item)
        [.pointer q] out (itemBudget W n m + componentHardBudget hb H w r) := by
  have hm' := hm
  obtain ⟨hitem, -, -, -, hrev, hroots, -, hind⟩ := hm'
  have hind' := hind
  obtain ⟨-, -, -, hfm, -⟩ := hind'
  obtain ⟨tp, a1, rp, a2, wp, a3, ap, op, c1, c2, c3, c4, hT, hr, hwp, hap, hop⟩ := hd
  -- the reached words of the root
  obtain ⟨o1, sp, rtp, e1, v1, hseen, w1⟩ :=
    RegisterComponentRoots.search_compiled ids.roots code hroots hh hap hop hr hx
  have hmemr : ∀ x ∈ reachE (adjArcs (edgeWords W left right)) (rangeWords W n) (word W r.val),
      ∃ v : Fin n, x = word W v.val := by
    intro x hx'
    rw [← AllHalfEncoded.rangeWords_eq] at hx'
    obtain ⟨v, rfl, -⟩ := GraphReachEncoded.mem_reach left right hn r x hx'
    exact ⟨v, rfl⟩
  obtain ⟨S, hSeq⟩ := exists_map_word _ hmemr
  have hS : ∀ v, v ∈ S ↔ v ∈ (ComputedComponents.routes left right r).seen := by
    intro v
    rw [← GraphReachEncoded.found_reach_iff left right hn r v, ResidualListReach.found_iff_mem,
      AllHalfEncoded.rangeWords_eq]
    change v ∈ S ↔ word W v.val ∈ reachE (adjArcs (edgeWords W left right)) (rangeWords W n)
      (word W r.val)
    rw [hSeq, mem_map_word hn]
  have hSlen : S.length ≤ n + 1 := by
    have := RegisterComponentRoots.reachE_length (adjArcs (edgeWords W left right))
      (rangeWords W n) (word W r.val)
    rw [hSeq, List.length_map, rangeWords_length] at this
    exact this
  rw [hSeq] at hseen
  -- the component ribbon
  obtain ⟨o2, q, l, vp, s, e2, v2, hq, hl, hvp, hws, w2⟩ :=
    RegisterInducedRibbon.component_compiled ids.induced code hind WeightAt weightMono hn hmW H r
      S hS w v1 (hT.mono e1) (hr.mono e1) hseen (ListRep.mono e1 (weightMono e1) hwp)
  have e12 := e1.trans e2
  -- the local solver
  have hk : (ComputedComponents.vertices left right r).length < 2 ^ W :=
    lt_of_le_of_lt (ComputedComponents.vertices_length_le left right r) hn
  have hke : (ComputedComponents.edges left right r).length < 2 ^ W :=
    lt_of_le_of_lt (ComputedComponents.edges_length_le left right r) hmW
  obtain ⟨o3, lw, e3, v3, hlw, w3⟩ := local_compiled hs ids code hm WeightAt weightMono hb hard hk hke
    (ComputedComponents.vertices_length_pos left right r)
    (ComputedComponents.componentRibbon left right r H) (AllHalfEncoded.localWeights left right w r)
    (ComputedComponents.local_connected left right r) (fun v => hw _)
    (ComputedComponents.local_half_optimal left right r w ho) v2 hq hl hws (hop.mono e12)
  rw [← GenericEncoded.localSolve_eq hs] at hlw
  -- reading back the original words
  obtain ⟨o4, sel, e4, v4, hsel, w4⟩ := RegisterWordFilter.select_compiled code
    ids.induced.filter.select ids.induced.filter.mem ids.induced.filter.cmp hfm.2.1
    hfm.2.2.2.2.2.1 hfm.2.2.2.2.2.2 (fun h p (w : Bits W) => BitsAt h p w)
    (fun he _ _ hb => hb.mono he) v3 (hl.mono e3) (hvp.mono e3) hlw
  -- prepending to the accumulator
  have e14 := (e12.trans e3).trans e4
  obtain ⟨o5, q5, e5, v5, hq5, w5⟩ := RegisterListReverse.compiled code ids.reverse hrev
    (fun h p (w : Bits W) => BitsAt h p w) (fun he _ _ hb => hb.mono he) v4 hsel (ha.mono e14)
  refine ⟨o5, q5, e14.trans e5, v5, hq5, ?_⟩
  rw [hitem]
  refine (Within.load (pointer := dp) (c := Cell.pair tp a1) (by reg_simp) c1
    (Within.load (pointer := a1) (c := Cell.pair rp a2) (by reg_simp) c2
    (Within.load (pointer := a2) (c := Cell.pair wp a3) (by reg_simp) c3
    (Within.load (pointer := a3) (c := Cell.pair ap op) (by reg_simp) c4
    (call_of (by reg_simp) w1 (call_of (by reg_simp) w2 (call_of (by reg_simp) w3
    (call_of (by reg_simp) w4 (call_of (by reg_simp) w5
    (ret_values (by reg_simp) le_rfl)))))))))).mono ?_
  have hb1 := componentRibbonBudget_mono (W := W) (n := n) (m := m) hSlen
  have hb2 := localBudget_mono (W := W) (ComputedComponents.vertices_length_le left right r)
    (ComputedComponents.edges_length_le left right r)
  have hks := AllHalfEncoded.setWords_length_le (W := W)
    (GenericEncoded.localSolve hs H w r)
  have hb3 := selectBudget_mono (W := W) (l := (ComputedComponents.vertices left right r).length)
    (l' := n) (hks.trans (ComputedComponents.vertices_length_le left right r))
    (ComputedComponents.vertices_length_le left right r)
  have hsl := AllHalfEncoded.selectFilter_length_le
    (rangeWords W (ComputedComponents.vertices left right r).length)
    ((ComputedComponents.vertices left right r).map (fun u => word W u.val))
    (setWords W (GenericEncoded.localSolve hs H w r))
  have hvl := ComputedComponents.vertices_length_le left right r
  simp only [List.length_map] at hsl
  simp only [itemBudget, componentHardBudget, adjArcs_length, rangeWords_length,
    List.length_map, List.length_cons, List.length_nil] at hb1 hb2 hb3 ⊢
  have hel : (edgeWords W left right).length = m := by simp [edgeWords]
  rw [hel]
  have hw2 : ((ComputedComponents.vertices left right r).map (fun u => word W u.val)).length ≤ n :=
    by simpa using hvl
  omega

end MWIS.GenericComponentSolve

end
