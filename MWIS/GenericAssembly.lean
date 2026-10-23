module

public import MWIS.GenericComponentSolve
public import MWIS.RegisterFinalAssembly

/-!
# The all-half solver and the final assembly, for a parametric hard function

These are `RegisterAllHalf.allHalf_compiled` and
`RegisterFinalAssembly.assembly_compiled` with the hard contract
`GenericHardSpec` for a hard function `hs`. The procedure records, bodies and
budgets are unchanged; in particular the summed hard budgets
`RegisterAllHalf.hardSum` and `RegisterFinalAssembly.residualHardSum` depend only
on the budget function. The output is the stored word list of `Generic.solve solver`.
-/

@[expose] public section

namespace MWIS.GenericAssembly

open MWIS.PointerMemory MWIS.RegisterMachine MWIS.EfficientSearch.Pointer
open MWIS.EfficientSearch MWIS.RibbonTable MWIS.RegisterFlagKeys
open MWIS.ExpandedWords MWIS.ResidualWords MWIS.EmbeddingFaces MWIS.RegisterWordFilter
open MWIS.RegisterComponentSolve MWIS.RegisterAllHalf MWIS.RegisterFinalAssembly
open MWIS.GenericComponentSolve (GenericHardSpec)
open MWIS.RegisterCutReadback (classWord)
open MWIS.GraphReachEncoded (one adjArcs edgeWords setWords)

variable {p : ℕ}
variable (solver : Generic.HardFn)

/-! ## The all-half solver -/

theorem allHalf_compiled (ids : RegisterAllHalf.Procedures p) (code : Code p) (hm : ids.Matches code)
    {W : ℕ} (WeightAt : Heap → Ptr → ℚ → Prop)
    (weightMono : ∀ {h h' : Heap}, Extends h h' → ∀ ptr x, WeightAt h ptr x → WeightAt h' ptr x)
    (hb : HardBudget) (hard : GenericHardSpec code ids.component.hard W WeightAt solver hb)
    {n m : ℕ} (hn : n < 2 ^ W) (hmW : m < 2 ^ W) {left right : Fin m → Fin n}
    (H : Ribbon left right) (w : Fin n → ℚ) (hw : ∀ v, 0 ≤ w v)
    (ho : Persistence.Optimal (EdgeTransport.Adj left right) w (fun _ => 1 / 2))
    {h : Heap} (hh : Valid h) {tp rp wp : Ptr}
    (hT : RecordsAt h tp (encodeRibbon W H)) (hr : WordsAt h rp (rangeWords W n))
    (hwp : ListRep WeightAt h wp (List.ofFn w)) :
    ∃ out q, Extends h out ∧ Valid out ∧
      WordsAt out q (setWords W (Generic.allHalfSolve solver H w)) ∧
      Within code h (initialRegisters [.pointer tp, .pointer rp, .pointer wp]) (code ids.allHalf)
        [.pointer q] out (allHalfBudget W n m + hardSum hb H w) := by
  have hm' := hm
  obtain ⟨hall, hfold, hcomp⟩ := hm'
  have hcomp' := hcomp
  obtain ⟨-, -, -, -, -, hroots, harcs, hind⟩ := hcomp'
  have hfm := hind.2.2.2.1
  -- the unit word and the adjacency arcs
  obtain ⟨e0, v0, b0⟩ := RegisterGraphArcs.alloc_one hh
  obtain ⟨o1, ap, e1, v1, hap, w1⟩ :=
    RegisterGraphArcs.adjArcs_compiled ids.component.arcs code harcs v0 (hT.mono e0) b0
  rw [RegisterGraphArcs.edgePairs_encode] at hap
  have e01 := e0.trans e1
  -- the roots
  obtain ⟨o2, rts, e2, v2, hrts, w2⟩ := RegisterComponentRoots.graphRoots_compiled
    ids.component.roots code hroots hn v1 hap (b0.mono e1) (hr.mono e01)
  have e02 := e01.trans e2
  -- the context record
  have hop := b0.mono (e1.trans e2)
  have hap2 := hap.mono e2
  obtain ⟨f3, u3, c3⟩ := alloc_pair v2 hap2.allocated hop.allocated
  set o3 := o2 ++ [Cell.pair ap h.length] with ho3
  have hwp3 : wp < o3.length := lt_of_lt_of_le hwp.allocated (e02.trans f3).length_le
  have hl3 : o2.length < o3.length := by rw [ho3]; simp
  obtain ⟨f4, u4, c4⟩ := alloc_pair u3 hwp3 hl3
  set o4 := o3 ++ [Cell.pair wp o2.length] with ho4
  have hrp4 : rp < o4.length := lt_of_lt_of_le hr.allocated ((e02.trans f3).trans f4).length_le
  have hl4 : o3.length < o4.length := by rw [ho4]; simp
  obtain ⟨f5, u5, c5⟩ := alloc_pair u4 hrp4 hl4
  set o5 := o4 ++ [Cell.pair rp o3.length] with ho5
  have htp5 : tp < o5.length :=
    lt_of_lt_of_le hT.allocated (((e02.trans f3).trans f4).trans f5).length_le
  have hl5 : o4.length < o5.length := by rw [ho5]; simp
  obtain ⟨f6, u6, c6⟩ := alloc_pair u5 htp5 hl5
  set o6 := o5 ++ [Cell.pair tp o4.length] with ho6
  have e26 := ((f3.trans f4).trans f5).trans f6
  have e06 := e02.trans e26
  have hctx : CtxAt WeightAt W H w o6 o5.length :=
    ⟨tp, o4.length, rp, o3.length, wp, o2.length, ap, h.length, c6, f6.lookup c5,
      (f5.trans f6).lookup c4, ((f4.trans f5).trans f6).lookup c3, hT.mono e06, hr.mono e06,
      ListRep.mono e06 (weightMono e06) hwp, hap2.mono e26, hop.mono e26⟩
  -- the fold over the roots
  obtain ⟨o7, cp, e7, v7, hcp, w7⟩ := RegisterListFold.compiled code ids.fold ids.component.item
    hfold (fun h p (r : Fin n) => BitsAt h p (word W r.val))
    (fun h p (_ : Unit) => CtxAt WeightAt W H w h p) WordsAt
    (fun he _ _ hb => hb.mono he) (fun he _ _ hc => CtxAt.mono weightMono he hc)
    (fun _ acc r => GenericEncoded.step solver W H w acc r)
    (fun r => itemBudget W n m + componentHardBudget hb H w r) u6
    (ListRep.mono e26 (fun _ _ hb => hb.mono e26) hrts) (data := ()) hctx
    (WordsAt.nil u6.1 : WordsAt o6 0 ([] : List (Bits W)))
    (fun _ r _ _ _ hv _ _ hx hd hs =>
      GenericComponentSolve.item_compiled solver ids.component code hcomp WeightAt weightMono hb hard hn hmW H w hw ho r hv
        hx hd hs)
  change WordsAt o7 cp (GenericEncoded.collect solver W H w (ComputedComponents.roots left right)) at hcp
  -- the range words that were collected
  obtain ⟨o8, q, e8, v8, hq, w8⟩ := RegisterWordFilter.members_compiled
    ids.component.induced.filter code hfm v7 (hr.mono (e06.trans e7)) hcp
  rw [GenericEncoded.filter_collect solver W hn] at hq
  refine ⟨o8, q, (e06.trans e7).trans e8, v8, hq, ?_⟩
  rw [hall]
  refine (Within.allocate (c := Cell.bit true 0) (by reg_simp)
    (call_of (by reg_simp) w1 (call_of (by reg_simp) w2
    (Within.allocate (c := Cell.pair ap h.length) (by reg_simp)
    (Within.allocate (c := Cell.pair wp o2.length) (by reg_simp)
    (Within.allocate (c := Cell.pair rp o3.length) (by reg_simp [ho3])
    (Within.allocate (c := Cell.pair tp o4.length) (by reg_simp [ho3, ho4])
    (call_of (by reg_simp [ho3, ho4, ho5]) w7 (call_of (by reg_simp) w8
    (ret_values (by reg_simp) le_rfl)))))))))).mono ?_
  have hrl := ComputedComponents.roots_length_le left right
  have hcl := GenericEncoded.collect_length_le solver W H w (ComputedComponents.roots left right)
  have hcl' : (GenericEncoded.collect solver W H w (ComputedComponents.roots left right)).length ≤
      n * n := hcl.trans (Nat.mul_le_mul_left n hrl)
  have hmb : RegisterWordFilter.membersBudget W
      (GenericEncoded.collect solver W H w (ComputedComponents.roots left right)).length n ≤
      RegisterWordFilter.membersBudget W (n * n) n := by
    have := membershipBudget_mono (k := W) hcl'
    simp only [RegisterWordFilter.membersBudget]
    gcongr
  have hfb : (itemBudget W n m) * (ComputedComponents.roots left right).length +
      30 * (ComputedComponents.roots left right).length ≤ (itemBudget W n m + 30) * n := by
    rw [← Nat.add_mul]
    exact Nat.mul_le_mul_left _ hrl
  simp only [sum_map_add, encodeRibbon_length, rangeWords_length, CellExpr.args,
    List.length_cons, List.length_nil, allHalfBudget, hardSum] at hmb ⊢
  omega


/-! ## The solver output -/

section Solve

variable {n m : ℕ} {left right : Fin m → Fin n}

/-- The all-half solution of the induced half graph. -/
abbrev halfSolution (R : Ribbon left right) (weights : Fin n → ℚ) :
    Finset (Fin (ComputedInduced.vertices (halfKeep left right weights)).length) :=
  Generic.allHalfSolve solver (ComputedInduced.ribbon left right (halfKeep left right weights) R)
    (halfWeights left right weights)

theorem mem_solve_iff (R : Ribbon left right) (weights : Fin n → ℚ) (v : Fin n) :
    v ∈ Generic.solve solver R weights ↔ 0 ≤ weights v ∧
      (zPoint left right weights v = 1 ∨ (zPoint left right weights v = 1 / 2 ∧
        ∃ i ∈ halfSolution solver R weights,
          (ComputedInduced.vertices (halfKeep left right weights)).get i = v)) := by
  simp only [Generic.solve, NegativeWeights.prune, Finset.mem_filter,
    Persistence.mem_replacement, InducedReduction.mem_lift, GraphRelabeling.mem_mapSet]
  constructor
  · rintro ⟨h1 | ⟨hk, hk', hJ⟩, hw⟩
    · exact ⟨hw, Or.inl h1⟩
    · exact ⟨hw, Or.inr ⟨hk, _, hJ, by
        rw [show (ComputedInduced.vertices (halfKeep left right weights)).get _ =
          (ComputedInduced.vertexEquiv (halfKeep left right weights) _).val from rfl,
          Equiv.apply_symm_apply]⟩⟩
  · rintro ⟨hw, h1 | ⟨hk, i, hi, hiv⟩⟩
    · exact ⟨Or.inl h1, hw⟩
    · refine ⟨Or.inr ⟨hk, hk, ?_⟩, hw⟩
      have he : (ComputedInduced.vertexEquiv (halfKeep left right weights)).symm ⟨v, hk⟩ = i := by
        rw [Equiv.symm_apply_eq]
        exact Subtype.ext hiv.symm
      rw [he]
      exact hi

/-- The encoded final selection is the stored output of `ExecutableMIS.solve`. -/
theorem finalE_solve {W : ℕ} (hn : n < 2 ^ W) (R : Ribbon left right) (weights : Fin n → ℚ) :
    finalE (selectFilter (rangeWords W (ComputedInduced.vertices (halfKeep left right weights)).length)
        ((ComputedInduced.vertices (halfKeep left right weights)).map (fun u => word W u.val))
        (setWords W (halfSolution solver R weights)))
      (rangeWords W n) ((List.finRange n).map fun v => classWord (zPoint left right weights v))
      (List.ofFn fun v => decide (0 ≤ weights v)) =
      setWords W (Generic.solve solver R weights) := by
  have hz := OriginalReduction.preprocessingPoint_correct (left := left) (right := right)
    weights (List.finRange n) (fun v => List.mem_finRange v)
  have hL : (ComputedInduced.vertices (halfKeep left right weights)).length < 2 ^ W :=
    lt_of_le_of_lt (by simpa [ComputedInduced.vertices] using
      List.length_filter_le _ (List.finRange n)) hn
  rw [← AllHalfEncoded.rangeWords_eq W n, List.ofFn_eq_map]
  change finalE _ ((List.finRange n).map fun v => word W v.val) _ _ = _
  rw [finalE_map]
  conv_rhs => rw [setWords]
  change _ = ((List.finRange n).filter (· ∈ Generic.solve solver R weights)).map
    (fun v => word W v.val)
  congr 1
  apply List.filter_congr
  intro v _
  rw [hiBit_classWord, loBit_classWord (hz.1 v)]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    ResidualListReach.found_iff_mem]
  rw [AllHalfEncoded.mem_selectFilter hn _ hL, mem_solve_iff]

end Solve

/-! ## The assembly -/

/-- **Final assembly.** From the stored preprocessing classes, the
nonnegativity mask of the weights, the stored table and range words of the
ribbon, and the stored truncated weights, the procedure returns the stored
words of the actual output `Generic.solve solver R weights`, within a
polynomial budget plus the hard budgets of the actual components of the
induced all-half instance. -/
theorem assembly_compiled (ids : RegisterFinalAssembly.Procedures p) (code : Code p) (hm : ids.Matches code)
    {W : ℕ} (WeightAt : Heap → Ptr → ℚ → Prop)
    (weightMono : ∀ {h h' : Heap}, Extends h h' → ∀ ptr x, WeightAt h ptr x → WeightAt h' ptr x)
    (hb : HardBudget) (hard : GenericHardSpec code ids.allHalf.component.hard W WeightAt solver hb)
    {n m : ℕ} (hn : n < 2 ^ W) (hmW : m < 2 ^ W) {left right : Fin m → Fin n}
    (R : Ribbon left right) (weights : Fin n → ℚ)
    {h : Heap} (hh : Valid h) {cp np tp rp wp : Ptr}
    (hc : WordsAt h cp ((List.finRange n).map fun v =>
      classWord (OriginalReduction.preprocessingPoint (left := left) (right := right) weights
        (List.finRange n) v)))
    (hnn : MaskAt h np (List.ofFn fun v => decide (0 ≤ weights v)))
    (hT : RecordsAt h tp (encodeRibbon W R)) (hr : WordsAt h rp (rangeWords W n))
    (hw : ListRep WeightAt h wp (List.ofFn (NegativeWeights.nonnegative weights))) :
    ∃ out q, Extends h out ∧ Valid out ∧
      WordsAt out q (setWords W (Generic.solve solver R weights)) ∧
      Within code h
        (initialRegisters [.pointer cp, .pointer np, .pointer tp, .pointer rp, .pointer wp])
        (code ids.assembly) [.pointer q] out
        (assemblyBudget W n m + residualHardSum hb R weights) := by
  have hm' := hm
  obtain ⟨hasm, hkeep, hfinal, hall⟩ := hm'
  have hall' := hall
  obtain ⟨-, -, hcomp⟩ := hall'
  obtain ⟨-, -, -, -, -, hroots, -, hind⟩ := hcomp
  obtain ⟨-, -, -, -, -, hres⟩ := hroots
  have hfm := hind.2.2.2.1
  have hz := OriginalReduction.preprocessingPoint_correct (left := left) (right := right)
    weights (List.finRange n) (fun v => List.mem_finRange v)
  -- the half mask
  obtain ⟨o1, mp, e1, v1, hmp, w1⟩ := keepMask_compiled code ids.keepMask hkeep hh hc
  have hmask : (((List.finRange n).map fun v => classWord (zPoint left right weights v)).map
      loBit) = List.ofFn (fun v => decide (halfKeep left right weights v)) := by
    rw [List.map_map, List.ofFn_eq_map]
    apply List.map_congr_left
    intro v _
    exact loBit_classWord (hz.1 v)
  rw [hmask] at hmp
  -- the induced ribbon
  obtain ⟨o2, q, l, vp, s, e2, v2, hq, hl, hvp, hs, w2⟩ :=
    RegisterInducedRibbon.induced_compiled ids.allHalf.component.induced code hind WeightAt
      weightMono hn hmW R (halfKeep left right weights) (NegativeWeights.nonnegative weights) v1
      (hT.mono e1) (hr.mono e1) hmp (ListRep.mono e1 (weightMono e1) hw)
  have e12 := e1.trans e2
  -- the all-half solver
  have hkn : (ComputedInduced.vertices (halfKeep left right weights)).length ≤ n := by
    simpa [ComputedInduced.vertices] using List.length_filter_le _ (List.finRange n)
  have hkm : (ComputedInduced.edges left right (halfKeep left right weights)).length ≤ m := by
    simpa [ComputedInduced.edges] using List.length_filter_le _ (List.finRange m)
  have hzr := InducedReduction.residual_optimal (EdgeTransport.Adj left right)
    (NegativeWeights.nonnegative weights) (zPoint left right weights) hz.2 hz.1
  have hopt := ComputedInduced.half_optimal left right (halfKeep left right weights)
    (NegativeWeights.nonnegative weights) hzr
  obtain ⟨o3, jp, e3, v3, hj, w3⟩ := GenericAssembly.allHalf_compiled solver ids.allHalf code hall WeightAt weightMono hb
    hard (lt_of_le_of_lt hkn hn) (lt_of_le_of_lt hkm hmW)
    (ComputedInduced.ribbon left right (halfKeep left right weights) R)
    (halfWeights left right weights)
    (fun v => NegativeWeights.nonnegative_nonnegative weights _) hopt v2 hq hl hs
  -- reading the half solution back
  obtain ⟨o4, sel, e4, v4, hsel, w4⟩ := select_compiled code
    ids.allHalf.component.induced.filter.select ids.allHalf.component.induced.filter.mem
    ids.allHalf.component.induced.filter.cmp hfm.2.1 hfm.2.2.2.2.2.1 hfm.2.2.2.2.2.2
    (fun h p (w : Bits W) => BitsAt h p w) (fun he _ _ hb => hb.mono he) v3 (hl.mono e3)
    (hvp.mono e3) hj
  -- the final selection
  have e14 := (e12.trans e3).trans e4
  obtain ⟨o5, q5, e5, v5, hq5, w5⟩ := final_compiled code ids.final
    ids.allHalf.component.roots.residual.member ids.allHalf.component.roots.residual.cmp hfinal
    hres.2.2.2.1 hres.2.2.2.2.2.2.2 v4 hsel (by simp) (by simp) (hr.mono e14) (hc.mono e14)
    (MaskAt.mono e14 hnn)
  rw [finalE_solve solver hn R weights] at hq5
  refine ⟨o5, q5, e14.trans e5, v5, hq5, ?_⟩
  rw [hasm]
  refine (call_of (by reg_simp) w1 (call_of (by reg_simp) w2 (call_of (by reg_simp) w3
    (call_of (by reg_simp) w4 (call_of (by reg_simp) w5 (ret_values (by reg_simp) le_rfl)))))).mono ?_
  have hb3 := allHalfBudget_mono (W := W) hkn hkm
  have hks := AllHalfEncoded.setWords_length_le (W := W) (halfSolution solver R weights)
  have hb4 := selectBudget_mono (W := W) (hks.trans hkn) (show
    ((ComputedInduced.vertices (halfKeep left right weights)).map (fun u => word W u.val)).length
      ≤ n by simpa using hkn)
  have hsl := AllHalfEncoded.selectFilter_length_le
    (rangeWords W (ComputedInduced.vertices (halfKeep left right weights)).length)
    ((ComputedInduced.vertices (halfKeep left right weights)).map (fun u => word W u.val))
    (setWords W (halfSolution solver R weights))
  have hb5 : finalBudget W (selectFilter
      (rangeWords W (ComputedInduced.vertices (halfKeep left right weights)).length)
      ((ComputedInduced.vertices (halfKeep left right weights)).map (fun u => word W u.val))
      (setWords W (halfSolution solver R weights))).length n ≤ finalBudget W n n := by
    have := membershipBudget_mono (k := W) (hsl.trans (by simpa using hkn))
    simp only [finalBudget]
    gcongr
  simp only [assemblyBudget, residualHardSum, halfSolution, rangeWords_length, List.length_map,
    List.length_finRange, List.length_cons, List.length_nil] at hb3 hb4 hb5 ⊢
  omega

end MWIS.GenericAssembly

end
