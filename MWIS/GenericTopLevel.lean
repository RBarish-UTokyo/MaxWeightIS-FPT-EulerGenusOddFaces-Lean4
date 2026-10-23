module

public import MWIS.GenericAssembly
public import MWIS.RegisterTopLevelRun

/-!
# The entry procedure, for a parametric hard function

`RegisterTopLevel.top_compiled`, `RegisterTopLevel.top_runs` and
`RegisterTopLevel.top_correct` with the hard contract `GenericHardSpec` for a
hard function `solver`. The entry procedure and its procedure records are those
of `RegisterTopLevel`. On the encoded input the entry procedure returns the
stored words of `Generic.solve solver R w`; for a correct hard function and a
drawing in a closed-surface map, every run returns a maximum-weight independent
set, within the entry budget plus the hard budgets of the actual hard
components.
-/

@[expose] public section

namespace MWIS.GenericTopLevel

open MWIS.Spec MWIS.SpecEncoding
open MWIS.PointerMemory MWIS.RegisterMachine MWIS.EfficientSearch.Pointer
open MWIS.EfficientSearch MWIS.RegisterFlagKeys MWIS.ExpandedWords
open MWIS.RegisterComponentSolve (HardBudget)
open MWIS.GenericComponentSolve (GenericHardSpec)
open MWIS.RegisterWeightMask (CanonAt)
open MWIS.RegisterFinalAssembly (residualHardSum)
open MWIS.RegisterTopLevel (topBody inputBudget topBudget)

variable {p : ℕ}
variable (solver : Generic.HardFn)

/-- **The entry procedure.** On the encoded input heap, the entry procedure
returns the stored word list of `Generic.solve solver R w`, for every internal
ribbon `R` carrying the corners of `D`, within `topBudget` plus the hard
budgets of the actual hard components. -/
theorem top_compiled (ids : RegisterTopLevel.Procedures p) (code : Code p) (hm : ids.Matches code)
    (hb : HardBudget) (D : Drawing) (w : Fin D.vertices → ℚ)
    (hard : GenericHardSpec code ids.hard (indexWidth D) (CanonAt (weightWidth w)) solver hb)
    {R : EmbeddingFaces.Ribbon D.left D.right}
    (hR : ∀ y, R.corner y = Spec.Flag.equiv _ (D.corner ((Spec.Flag.equiv _).symm y))) :
    ∃ out q, Extends (encode D w).1 out ∧ Valid out ∧
      WordsAt out q (GraphReachEncoded.setWords (indexWidth D) (Generic.solve solver R w)) ∧
      Within code (encode D w).1 (initialRegisters [.pointer (encode D w).2]) (code ids.top)
        [.pointer q] out (inputBudget D w + residualHardSum hb R w) := by
  obtain ⟨htop, hpairs, hpre, hweights, hasm⟩ := hm
  obtain ⟨vp, rest, tp, wp, c0, c1, hv, hT, hw⟩ := encode_root D w hR
  have hh := encode_valid D w
  -- endpoint pairs
  obtain ⟨o1, ep, e1, v1, hep, w1⟩ :=
    RegisterEdgePairs.edgeWords_compiled ids.pairs code hpairs R hh hT
  -- preprocessing
  have hvG : WordsAt (encode D w).1 vp
      (GraphReachEncoded.rangeWords (indexWidth D) D.vertices) := by
    rw [rangeWords_eq]; exact hv
  obtain ⟨o2, zp, tablep, cutp, bigp, e2, v2, hz, -, w2⟩ :=
    RegisterPreprocessing.preprocessing_compiled code ids.pre hpre (vertices_lt D) D.left D.right
      w (fun v => ratWord (weightWidth w) (w v)) (weightRow_canonical w) (weightRow_value w) v1
      (hvG.mono e1) hep (hw.mono e1)
  have e12 := e1.trans e2
  -- nonnegativity mask
  obtain ⟨o3, mp, e3, v3, hmp, w3⟩ := RegisterWeightMask.weightMask_compiled ids.weights code
    hweights w (fun v => ratWord (weightWidth w) (w v)) (weightRow_canonical w)
    (weightRow_value w) v2 (hw.mono e12)
  have e13 := e12.trans e3
  -- truncated weights
  obtain ⟨o4, trp, e4, v4, htr, w4⟩ := RegisterWeightMask.truncate_compiled ids.weights code
    hweights w (fun v => ratWord (weightWidth w) (w v)) (weightRow_canonical w)
    (weightRow_value w) v3 (hw.mono e13)
  have e14 := e13.trans e4
  have e24 := e3.trans e4
  -- assembly
  obtain ⟨o5, q, e5, v5, hq, w5⟩ := GenericAssembly.assembly_compiled solver ids.assembly code hasm
    (CanonAt (weightWidth w)) (fun he _ _ hx => hx.mono he) hb hard (vertices_lt D) (edges_lt D)
    R w v4 (hz.mono e24) (RegisterWordFilter.MaskAt.mono e4 hmp) (hT.mono e14) (hv.mono e14) htr
  refine ⟨o5, q, e14.trans e5, v5, hq, ?_⟩
  rw [htop]
  refine (Within.load (c := Cell.pair vp rest) (by reg_simp) c0
    (Within.load (c := Cell.pair tp wp) (by reg_simp) c1
    (call_of (by reg_simp) w1 (call_of (by reg_simp) w2 (call_of (by reg_simp) w3
    (call_of (by reg_simp) w4 (call_of (by reg_simp) w5
    (ret_values (by reg_simp) le_rfl)))))))).mono ?_
  simp only [inputBudget, topBudget, List.length_cons, List.length_nil]
  omega


/-! ## Runs -/

/-- **Runs of the entry procedure.** There is exactly one framed run on the
encoded input; it outputs `Generic.solve solver R w` and its stack bit cost is
at most `B · (102 + 35 · size (|heap| + B))` for the event budget `B`. -/
theorem top_runs (ids : RegisterTopLevel.Procedures p) (code : Code p) (hm : ids.Matches code)
    (hb : HardBudget) (D : Drawing) (w : Fin D.vertices → ℚ)
    (hard : GenericHardSpec code ids.hard (indexWidth D) (CanonAt (weightWidth w)) solver hb)
    {R : EmbeddingFaces.Ribbon D.left D.right}
    (hR : ∀ y, R.corner y = Spec.Flag.equiv _ (D.corner ((Spec.Flag.equiv _).symm y))) :
    ∃ r₀ t₀, Runs code ids.top D w r₀ t₀ ∧
      ∀ r t, Runs code ids.top D w r t →
        r = r₀ ∧ t = t₀ ∧ Outputs D r (Generic.solve solver R w) ∧
        stackBitCost t.compile ≤ (inputBudget D w + residualHardSum hb R w) *
          (102 + 35 * ((encode D w).1.length + (inputBudget D w + residualHardSum hb R w)).size) := by
  obtain ⟨out, q, -, -, hq, events, hex, hlen⟩ := top_compiled solver ids code hm hb D w hard hR
  obtain ⟨tree, ht⟩ := hex.framed
  refine ⟨_, tree, ht, fun r t hr => ?_⟩
  obtain ⟨rfl, rfl⟩ := FramedExec.deterministic hr ht
  exact ⟨rfl, rfl, outputs_of_setWords D rfl hq,
    ht.bitCost_le_of_length_le (encode_valid D w) (encode_registers_bounded D w) hlen⟩

/-- The binary size of the bit-cost bound, in closed form. -/
theorem cost_factor_le (D : Drawing) (w : Fin D.vertices → ℚ) (B : ℕ) :
    B * (102 + 35 * ((encode D w).1.length + B).size) ≤
      B * (102 + 35 * (100 * D.size ^ 2 * (weightLength w + 1) + B)) := by
  apply Nat.mul_le_mul_left
  have h1 : ((encode D w).1.length + B).size ≤ (encode D w).1.length + B :=
    Nat.size_le.mpr (Nat.lt_two_pow_self)
  have h2 := encode_length_le D w
  omega

/-- **The entry procedure in statement terms.** For a drawing in a
closed-surface map, with the internal ribbon `Drawing.ribbon hA W`: there is a
run on the encoded input, and every run returns a maximum-weight independent
set within the stated stack bit cost. -/
theorem top_correct {solver : Generic.HardFn} (hcor : Generic.HardCorrect solver) (ids : RegisterTopLevel.Procedures p) (code : Code p) (hm : ids.Matches code)
    (hb : HardBudget) (A : Map) (hA : A.IsClosedSurface) (D : Drawing) (W : D.In A)
    (w : Fin D.vertices → ℚ)
    (hard : GenericHardSpec code ids.hard (indexWidth D) (CanonAt (weightWidth w)) solver hb) :
    (∃ r t, Runs code ids.top D w r t) ∧
      ∀ r t, Runs code ids.top D w r t →
        (∃ I, Outputs D r I ∧ D.IsMaximum w I) ∧
        stackBitCost t.compile ≤
          (inputBudget D w + residualHardSum hb (Drawing.ribbon hA W) w) *
            (102 + 35 * (100 * D.size ^ 2 * (weightLength w + 1) +
              (inputBudget D w + residualHardSum hb (Drawing.ribbon hA W) w))) := by
  have hR : ∀ y, (Drawing.ribbon hA W).corner y =
      Spec.Flag.equiv _ (D.corner ((Spec.Flag.equiv _).symm y)) := by
    intro y
    have := Drawing.ribbon_corner hA W ((Spec.Flag.equiv _).symm y)
    rwa [Equiv.apply_symm_apply] at this
  obtain ⟨r₀, t₀, h0, hall⟩ := top_runs solver ids code hm hb D w hard hR
  refine ⟨⟨r₀, t₀, h0⟩, fun r t hr => ?_⟩
  obtain ⟨-, -, hout, hcost⟩ := hall r t hr
  exact ⟨⟨_, hout, Generic.solve_isMaximum hcor A hA D W w⟩, hcost.trans (cost_factor_le D w _)⟩

end MWIS.GenericTopLevel

end
