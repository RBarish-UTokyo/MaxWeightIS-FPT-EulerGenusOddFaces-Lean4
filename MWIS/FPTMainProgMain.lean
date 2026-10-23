module

public import MWIS.FPTMainProgNet

/-!
# The numerical-stage program meets its contract

With a dense-program optimizer `optF` meeting `OptSpec optF` (it computes
`AlgorithmThresholdLP.optimize`) and `OptCost optF a` (polynomial cost), the
program `prog optF` computes the numerical stage within `mainBudget a`
(`progFunStage`), and this budget is a fixed-parameter bound (`mainBudget_bound`).
-/

@[expose] public section

namespace MWIS.FPTMainProg

open MWIS.Fun MWIS.FunLP MWIS.FPTTrees MWIS.FPTRegister MWIS.FPTTreeParse
open MWIS.RegisterComponentSolve (HardBudget)

variable {n m : ℕ} {left right : Fin m → Fin n}

/-! ## The optimization stage -/

theorem netArg_eq (R : EmbeddingFaces.Ribbon left right) (w : Fin n → ℚ) (hn0 : 0 < n) :
    netArg ((n : ℤ), ((rowCount R : ℤ), (((coordsOf R hn0).rank : ℤ), inputOf R w hn0))) =
      FunNetwork.networkInput (FPTHard.faceColumns R) (coordsOf R hn0)
        (FPTHard.integerCosts left right w) := by
  simp only [netArg, muV_nat]
  rfl

theorem opt_le {optF : Fn OptArg .int} {a : ℕ} (hk : OptCost optF a) (Y c : ℕ)
    (R : EmbeddingFaces.Ribbon left right) (w : Fin n → ℚ) (hn0 : 0 < n)
    (hc : Incidence.Connected left right) (hnb : ¬ Incidence.Bipartite left right)
    (hcost : ∀ e, FPTHard.integerCosts left right w e < 2 ^ c) (hYge : n + m + c + 2 ≤ Y) :
    (optStageF optF).costAt ((n : ℤ), ((rowCount R : ℤ), (((coordsOf R hn0).rank : ℤ),
        inputOf R w hn0))) ≤ PB (5 + (a + 40 * a + 336)) (DR R) Y := by
  have hY : 1 ≤ Y := by omega
  have hD := DR_pos R
  have h := optStageF_cost optF ((n : ℤ), ((rowCount R : ℤ), (((coordsOf R hn0).rank : ℤ),
    inputOf R w hn0)))
  rw [netArg_eq] at h
  dsimp only at h
  rw [FunNetwork.networkFn_correct, FunNetwork.offsetFn_correct, FunNetwork.bitsFn_correct] at h
  have ho := hk (programOf R w hn0) (2 * (FPTHard.total (FPTHard.integerCosts left right w) : ℤ))
    (FPTHard.searchBits (FPTHard.integerCosts left right w))
  have hq := query_le Y c R w hn0 hc hnb hcost hYge
    (FunNetwork.rowsEquiv (FPTHard.faceColumns R) (coordsOf R hn0).rank)
    (FunNetwork.colsEquiv (FPTHard.faceColumns R) (coordsOf R hn0).rank)
  have ho' : optF.costAt (FunNetwork.DenseProgram.toFun (programOf R w hn0),
      (2 * (FPTHard.total (FPTHard.integerCosts left right w) : ℤ),
        (FPTHard.searchBits (FPTHard.integerCosts left right w) : ℤ))) ≤
      PB (a + 40 * a) (DR R) Y :=
    ho.trans (poly_le_PB hD hY hq a)
  have hnet := net_le Y c R w hn0 hc hnb hcost hYge
  have hoff := offset_le Y c R w hn0 hcost hYge
  obtain ⟨-, hrm, -, -⟩ := FPTHardConcrete.coordinates_bounds R ⟨0, hn0⟩ hc hnb
  have hbr : bits ((coordsOf R hn0).rank : ℤ) ≤ m := by
    rw [FunLP.bits_natCast]
    exact (Nat.size_le.mpr Nat.lt_two_pow_self).trans hrm
  generalize bits ((coordsOf R hn0).rank : ℤ) = br at h hbr
  have hx : (br + 4) ^ 2 + 10 * br + 90 ≤ PB (8 + 2) (DR R) Y := by
    refine quad_le_PB (k := 8) hD hY ?_
    have : (br + 4) ^ 2 ≤ 25 * Y ^ 2 := by
      have := mul_lin_le (Y := Y) (k := 5) (l := 5) (x := br + 4) (y := br + 4) (by omega)
        (by omega)
      rw [← pow_two] at this; simpa using this
    have : Y ≤ Y ^ 2 := by nlinarith
    omega
  have w1 := PB_weaken (K' := a + 40 * a + 336) hY hnet (by omega)
  have w2 := PB_weaken (K' := a + 40 * a + 336) hY hoff (by omega)
  have w3 := PB_weaken (K' := a + 40 * a + 336) hY ho' (by omega)
  have w4 := PB_weaken (K' := a + 40 * a + 336) hY hx (by omega)
  refine PB_le_of_mul (k := 5) hD hY (h.trans ?_)
  have : programOf R w hn0 = FPTHard.program (FPTHard.faceColumns R) (coordsOf R hn0)
      (FPTHard.integerCosts left right w)
      (FunNetwork.rowsEquiv (FPTHard.faceColumns R) (coordsOf R hn0).rank)
      (FunNetwork.colsEquiv (FPTHard.faceColumns R) (coordsOf R hn0).rank) := rfl
  rw [this] at w3
  omega

/-! ## The final stage -/

theorem final_le (Y c : ℕ) (R : EmbeddingFaces.Ribbon left right) (w : Fin n → ℚ) (hn0 : 0 < n)
    (hc : Incidence.Connected left right) (hnb : ¬ Incidence.Bipartite left right)
    (hcost : ∀ e, FPTHard.integerCosts left right w e < 2 ^ c) (hYge : n + m + c + 2 ≤ Y) :
    finalF.costAt ((n : ℤ), (inputOf R w hn0, (valueOf R w hn0 : ℤ))) ≤
      PB (4 + 34) (DR R) Y := by
  have hY : 1 ≤ Y := by omega
  have hD := DR_pos R
  have h := finalF_cost ((n : ℤ), (inputOf R w hn0, (valueOf R w hn0 : ℤ)))
  dsimp only at h
  have hl := FPTRunFun.lengthF_cost FunNetwork.tE (inputOf R w hn0)
  have hs := slack_le Y c R w hn0 hc hnb hcost hYge
  have hlen := inputOf_length R w hn0
  have hfo := formatOutput_cost (3 * (n : ℤ) + ((inputOf R w hn0).length : ℤ) + 4)
    (FunNetwork.slackFn.apply ((valueOf R w hn0 : ℤ), inputOf R w hn0)) 1 (by
      intro k hk
      rw [FunNetwork.slackFn_correct, List.mem_ofFn] at hk
      obtain ⟨e, rfl⟩ := hk
      unfold FPTHard.decode
      rw [FunLP.bits_natCast]
      refine Nat.size_le.mpr ?_
      have := Nat.mod_lt ((FPTHard.total (FPTHard.integerCosts left right w) - valueOf R w hn0) /
        2 ^ (e : ℕ)) (show 2 > 0 by omega)
      simpa using this)
  have hsl : (FunNetwork.slackFn.apply ((valueOf R w hn0 : ℤ), inputOf R w hn0)).length = m := by
    rw [FunNetwork.slackFn_correct]; simp
  rw [hsl, hlen] at hfo
  rw [hlen] at h hl
  have htn : (3 * (n : ℤ) + (m : ℤ) + 4).toNat = 3 * n + m + 4 := by omega
  rw [htn] at hfo
  unfold Fn.costAt at h hfo hs
  have p1 : (m + 1) * (m + 8) ≤ 2 ^ 4 * Y ^ 2 := by
    have := mul_lin_le (Y := Y) (k := 1) (l := 8) (x := m + 1) (y := m + 8) (by omega) (by omega)
    omega
  have p2 : (m + 1) * (3 * n + m + 4 + 1 + 26) ≤ 2 ^ 5 * Y ^ 2 := by
    have := mul_lin_le (Y := Y) (k := 1) (l := 31) (x := m + 1) (y := 3 * n + m + 4 + 1 + 26)
      (by omega) (by omega)
    omega
  have hYY : Y ≤ Y ^ 2 := by nlinarith
  have hna : ((n : ℤ)).natAbs = n := Int.natAbs_natCast n
  rw [hna] at h
  have e1 := quad_le_PB (k := 7) (x := (m + 1) * (m + 8) + ((m + 1) * (3 * n + m + 4 + 1 + 26) +
    m + 3) + 9 * n + 2 * m + 40) hD hY (by omega)
  have w1 := PB_weaken (K' := 34) hY e1 (by norm_num)
  refine PB_le_of_mul (k := 4) hD hY (h.trans ?_)
  change Expr.cost (lengthF FunNetwork.tE) (inputOf R w hn0, ()) ≤ _ at hl
  omega

/-! ## The whole program -/

theorem prog_cost_le {optF : Fn OptArg .int} {a : ℕ} (hopt : OptSpec optF) (hk : OptCost optF a)
    (W c : ℕ) (R : EmbeddingFaces.Ribbon left right) (w : Fin n → ℚ) (hn0 : 0 < n)
    (hn : n < 2 ^ W) (hc : Incidence.Connected left right)
    (hnb : ¬ Incidence.Bipartite left right)
    (hcost : ∀ e, FPTHard.integerCosts left right w e < 2 ^ c) :
    (prog optF).cost (FPTRunFun.stageEnv W c R w) ≤
      PB (mainK a) (DR R) (n + m + W + c + 2) := by
  have hY : 1 ≤ n + m + W + c + 2 := by omega
  have hD := DR_pos R
  have h0 : (prog optF).cost (FPTRunFun.stageEnv W c R w) ≤
      (mainF optF).costAt (trees W c R w) + 30 := prog_cost optF _
  have h1 := mainF_cost optF (trees W c R w)
  rw [parseF_apply W c R w hn hcost, coordStageF_apply W c R w hn0, inputStageF_apply W c R w hn0,
    optStageF_apply hopt R w hn0 hc hnb] at h1
  have hYge : n + m + c + 2 ≤ n + m + W + c + 2 := by omega
  have q1 := parse_le W c R w
  have q2 := coord_le W c R w hn0
  have q3 := input_le W c R w hn0
  have q4 := opt_le hk _ c R w hn0 hc hnb hcost hYge
  have q5 := final_le _ c R w hn0 hc hnb hcost hYge
  have w1 := PB_weaken (K' := 5 + (a + 40 * a + 336)) hY q1 (by omega)
  have w2 := PB_weaken (K' := 5 + (a + 40 * a + 336)) hY q2 (by omega)
  have w3 := PB_weaken (K' := 5 + (a + 40 * a + 336)) hY q3 (by omega)
  have w5 := PB_weaken (K' := 5 + (a + 40 * a + 336)) hY q5 (by omega)
  have w6 : 34 ≤ PB (5 + (a + 40 * a + 336)) (DR R) (n + m + W + c + 2) :=
    ((show 34 ≤ 2 ^ 6 by norm_num).trans (twoPowK_le_PB hD hY)).trans (PB_mono hY (by omega))
  have hsum := PB_le_of_mul (k := 6) (K := 5 + (a + 40 * a + 336)) hD hY
    (x := (prog optF).cost (FPTRunFun.stageEnv W c R w)) (by omega)
  exact PB_weaken hY hsum (by unfold mainK; omega)

/-! ## The contracts -/

/-- **The numerical-stage program meets its contract.** -/
theorem progFunStage {optF : Fn OptArg .int} {a : ℕ} (hopt : OptSpec optF)
    (hk : OptCost optF a) : FPTRunFun.ProgFunStage (prog optF) faceCoords (mainBudget a) :=
  fun W c _ _ _ _ R w hn0 hn _ hc hnb _ _ hcost =>
    ⟨prog_denote hopt W c R w hn0 hn hc hnb hcost,
      prog_cost_le hopt hk W c R w hn0 hn hc hnb hcost⟩

/-- **The budget of the numerical-stage program is a fixed-parameter bound.** -/
theorem mainBudget_bound (a : ℕ) : FunBudgetBound (3 * mainK a) (mainBudget a) := by
  intro W w0 n m left right R w _ _ _ _
  show PB (mainK a) (DR R) (n + m + W + NetworkWeights.width w0 n + 2) ≤
    GenericAccounting.shape (3 * mainK a) (ComputedEmbeddedMatrices.globalRows R).length
      (n + m + W + w0 + 2)
  have hZ : 2 ≤ n + m + W + w0 + 2 := by omega
  have hY : n + m + W + NetworkWeights.width w0 n + 2 ≤ (n + m + W + w0 + 2) ^ 3 := by
    unfold NetworkWeights.width
    generalize hZd : n + m + W + w0 + 2 = Z at hZ
    have h1 : (w0 + 1) * (n + 1) ≤ Z * Z := Nat.mul_le_mul (by omega) (by omega)
    have h2 : Z * Z * 2 ≤ Z * Z * Z := Nat.mul_le_mul_left _ hZ
    have h3 : 2 * Z ≤ Z * Z := by nlinarith
    have : Z ^ 3 = Z * Z * Z := by ring
    omega
  unfold PB GenericAccounting.shape DR
  generalize (ComputedEmbeddedMatrices.globalRows R).length *
    Nat.size (ComputedEmbeddedMatrices.globalRows R).length + 1 = D
  calc 2 ^ (mainK a * D) * (n + m + W + NetworkWeights.width w0 n + 2) ^ mainK a
      ≤ 2 ^ (3 * mainK a * D) * ((n + m + W + w0 + 2) ^ 3) ^ mainK a :=
        Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (by nlinarith))
          (Nat.pow_le_pow_left hY _)
    _ = 2 ^ (3 * mainK a * D) * (n + m + W + w0 + 2) ^ (3 * mainK a) := by
        rw [← pow_mul]

end MWIS.FPTMainProg

end
