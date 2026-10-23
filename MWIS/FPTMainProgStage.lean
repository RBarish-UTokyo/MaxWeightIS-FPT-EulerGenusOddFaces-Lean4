module

public import MWIS.FPTMainProgBound

/-!
# Stage bounds of the numerical-stage program

Stage-by-stage fixed-parameter bounds `PB K D Y` for the parsing, coordinate and
network-input stages of `FPTMainProg.prog optF`, and for the size of the optimizer
argument (`query_le`).
-/

@[expose] public section

namespace MWIS.FPTMainProg

open MWIS.Fun MWIS.FunLP MWIS.FPTTrees MWIS.FPTRegister MWIS.FPTTreeParse
open MWIS.FunNetwork (tE tOut tL)
open MWIS.RegisterComponentSolve (HardBudget)

variable {n m : ℕ} {left right : Fin m → Fin n}

theorem PB_weaken {x K K' D Y : ℕ} (hY : 1 ≤ Y) (h : x ≤ PB K D Y) (hK : K ≤ K') :
    x ≤ PB K' D Y :=
  h.trans (PB_mono hY hK)

theorem PB_add_le {x y K D Y : ℕ} (hD : 1 ≤ D) (hY : 1 ≤ Y) (hx : x ≤ PB K D Y)
    (hy : y ≤ PB K D Y) : x + y ≤ PB (2 + K) D Y :=
  PB_le_of_mul hD hY (by omega)

theorem DR_pos (R : EmbeddingFaces.Ribbon left right) : 1 ≤ DR R := by
  unfold DR; exact Nat.le_add_left 1 _

/-- A product of two linear bounds in `Y`. -/
theorem mul_lin_le {x y Y k l : ℕ} (hx : x ≤ k * Y) (hy : y ≤ l * Y) : x * y ≤ (k * l) * Y ^ 2 :=
  (Nat.mul_le_mul hx hy).trans (le_of_eq (by ring))

theorem twoPowK_le_PB {K D Y : ℕ} (hD : 1 ≤ D) (hY : 1 ≤ Y) : 2 ^ K ≤ PB K D Y :=
  (Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_right _ hD)).trans
    (twoPowMul_le_PB hY)

theorem sq_le_PB {D Y : ℕ} : Y ^ 2 ≤ PB 2 D Y := by
  have := PB_le_pow (Y_le_PB (D := D) (Y := Y)) 2
  simpa using this

/-! ## Parsing -/

theorem parse_le (W c : ℕ) (R : EmbeddingFaces.Ribbon left right) (w : Fin n → ℚ) :
    parseF.costAt (trees W c R w) ≤ PB 11 (DR R) (n + m + W + c + 2) := by
  have hc := parseF_cost (trees W c R w)
  have h1 := parseColumns_cost R
  have h2 := parseEdges_cost W left right
  have h3 : (wordsTree (RibbonTable.rangeWords W n)).spine = n := by
    rw [FPTRunFun.spine_wordsTree, RibbonTable.rangeWords_length]
  have h4 := FPTRunFun.lengthF_cost .tree (wordsTree (RibbonTable.rangeWords W n)).items
  have hl : (wordsTree (RibbonTable.rangeWords W n)).items.length = n := by
    rw [FPTRunFun.items_length, h3]
  rw [hl] at h4
  have h5 := parseWords_cost ((List.finRange m).map fun e =>
    GraphReachEncoded.word c (FPTHard.integerCosts left right w e))
  rw [List.length_map, List.length_finRange] at h5
  have h6 := parseCount_cost (fptWidth n m) (2 * rowCount R + 1)
  refine le_trans hc ?_
  simp only [trees]
  unfold Fn.costAt at h1 h2 h5 h6 ⊢
  unfold costsTree
  change Expr.cost (lengthF Ty.tree) _ ≤ _ at h4
  rw [h3]
  have hY : 500 * (n + m + W + c + 2) ^ 2 ≤ PB 11 (DR R) (n + m + W + c + 2) := by
    rw [← PB_mul 9 2]
    exact Nat.mul_le_mul ((show 500 ≤ 2 ^ 9 by norm_num).trans
      (twoPowK_le_PB (DR_pos R) (by omega))) sq_le_PB
  have hw : fptWidth n m = 3 * n + m + 4 := rfl
  have e1 := mul_lin_le (Y := n + m + W + c + 2) (k := 1) (l := 68)
    (x := m + 1) (y := 2 * fptWidth n m + 60) (by omega) (by omega)
  have e2 := mul_lin_le (Y := n + m + W + c + 2) (k := 1) (l := 32)
    (x := m + 1) (y := 2 * W + 30) (by omega) (by omega)
  have e3 := mul_lin_le (Y := n + m + W + c + 2) (k := 1) (l := 8)
    (x := n + 1) (y := n + 8) (by omega) (by omega)
  have e4 := mul_lin_le (Y := n + m + W + c + 2) (k := 1) (l := 22)
    (x := m + 1) (y := c + 22) (by omega) (by omega)
  have e5 : (fptWidth n m + 8) ^ 2 ≤ 144 * (n + m + W + c + 2) ^ 2 := by
    have := mul_lin_le (Y := n + m + W + c + 2) (k := 12) (l := 12)
      (x := fptWidth n m + 8) (y := fptWidth n m + 8) (by omega) (by omega)
    rw [← pow_two] at this; simpa using this
  have hY1 : n + m + W + c + 2 ≤ (n + m + W + c + 2) ^ 2 := by nlinarith
  generalize Expr.cost parseColumns (columnsTree R, ()) = A1 at *
  generalize Expr.cost parseEdges (edgesTree W left right, ()) = A2 at *
  generalize Expr.cost (lengthF Ty.tree) ((wordsTree (RibbonTable.rangeWords W n)).items, ()) = A3 at *
  generalize (n + m + W + c + 2) ^ 2 = Y2 at *
  generalize fptWidth n m = B at *
  omega

/-! ## Polynomial pieces -/

theorem poly_le_PB {D Y X : ℕ} (hD : 1 ≤ D) (hY : 1 ≤ Y) (hX : X ≤ PB K D Y) (a : ℕ) :
    a * X ^ a ≤ PB (a + K * a) D Y :=
  PB_le_mul (const_le_PB hD hY a) (PB_le_pow hX a)

theorem lin_le_PB {D Y : ℕ} (hD : 1 ≤ D) (hY : 1 ≤ Y) {x k : ℕ} (hx : x ≤ 2 ^ k * Y) :
    x ≤ PB (k + 1) D Y :=
  hx.trans (PB_le_mul (twoPowK_le_PB hD hY) Y_le_PB)

theorem quad_le_PB {D Y : ℕ} (hD : 1 ≤ D) (hY : 1 ≤ Y) {x k : ℕ} (hx : x ≤ 2 ^ k * Y ^ 2) :
    x ≤ PB (k + 2) D Y :=
  hx.trans (PB_le_mul (twoPowK_le_PB hD hY) sq_le_PB)

/-! ## Coordinates and network input -/

theorem coord_le (W c : ℕ) (R : EmbeddingFaces.Ribbon left right) (w : Fin n → ℚ)
    (hn0 : 0 < n) :
    coordStageF.costAt (parsed W c R w) ≤ PB (2 + 35) (DR R) (n + m + W + c + 2) := by
  have hY : 1 ≤ n + m + W + c + 2 := by omega
  have hD := DR_pos R
  have h := coordStageF_cost (parsed W c R w)
  have h1 : FunCoordinates.coordFn.costAt ((parsed W c R w).2.1, ((parsed W c R w).1,
      ((parsed W c R w).2.2.1, ((parsed W c R w).2.2.2.2, 0)))) ≤
      17000 * (m + n + rowCount R + 5) ^ 5 := coordArg_cost R hn0
  have hf : rowCount R ≤ 4 * m := by
    simpa using R.evenRow_count_le (EmbeddingFaces.Flag.canonicalOrder m)
  generalize rowCount R = f at h1 hf
  have h2 : 17000 * (m + n + f + 5) ^ 5 ≤ PB (15 + (3 + 1) * 5) (DR R) (n + m + W + c + 2) :=
    PB_le_mul (K := 15) ((show 17000 ≤ 2 ^ 15 by norm_num).trans (twoPowK_le_PB hD hY))
      (PB_le_pow (lin_le_PB (k := 3) hD hY (by omega)) 5)
  have h3 : 40 ≤ PB (15 + (3 + 1) * 5) (DR R) (n + m + W + c + 2) :=
    ((show 40 ≤ 2 ^ 6 by norm_num).trans (twoPowK_le_PB hD hY)).trans (PB_mono hY (by norm_num))
  exact h.trans (PB_add_le (K := 15 + (3 + 1) * 5) hD hY (h1.trans h2) h3)

theorem input_le (W c : ℕ) (R : EmbeddingFaces.Ribbon left right) (w : Fin n → ℚ) (hn0 : 0 < n) :
    inputStageF.costAt (parsed W c R w, (((coordsOf R hn0).rank : ℤ),
        List.ofFn (FunCoordinates.coordRow left right (FPTHard.faceColumns R) ⟨0, hn0⟩))) ≤
      PB 10 (DR R) (n + m + W + c + 2) := by
  have hY : 1 ≤ n + m + W + c + 2 := by omega
  have h := inputStageF_cost (parsed W c R w, (((coordsOf R hn0).rank : ℤ),
        List.ofFn (FunCoordinates.coordRow left right (FPTHard.faceColumns R) ⟨0, hn0⟩)))
  have h1 := inputF_cost ((parsed W c R w).1, (List.ofFn (FunCoordinates.coordRow left right
    (FPTHard.faceColumns R) ⟨0, hn0⟩), (parsed W c R w).2.2.2.1))
  have hl : (parsed W c R w).1.length = m := by simp [parsed]
  rw [hl] at h1
  refine h.trans ((Nat.add_le_add_right h1 _).trans (lin_le_PB (k := 9) (DR_pos R) hY ?_))
  omega

/-! ## The optimization stage -/

/-- The dense network program of an instance. -/
noncomputable abbrev programOf (R : EmbeddingFaces.Ribbon left right) (w : Fin n → ℚ) (hn0 : 0 < n) :=
  FPTHard.program (FPTHard.faceColumns R) (coordsOf R hn0) (FPTHard.integerCosts left right w)
    (FunNetwork.rowsEquiv (FPTHard.faceColumns R) (coordsOf R hn0).rank)
    (FunNetwork.colsEquiv (FPTHard.faceColumns R) (coordsOf R hn0).rank)

/-- The optimizer argument size is a fixed-parameter shape. -/
theorem query_le (Y c : ℕ) (R : EmbeddingFaces.Ribbon left right) (w : Fin n → ℚ) (hn0 : 0 < n)
    (hc : Incidence.Connected left right) (hnb : ¬ Incidence.Bipartite left right)
    (hcost : ∀ e, FPTHard.integerCosts left right w e < 2 ^ c) (hYge : n + m + c + 2 ≤ Y)
    {M N : ℕ}
    (rows : AlgorithmNetworkEncoding.InequalityRow (FPTHard.faceColumns R) (G := ResidueJensen.Residue
      (coordsOf R hn0).rank) (coordsOf R hn0).rank ≃ Fin M)
    (cols : FiniteExtension.ExtensionArc (FPTHard.faceColumns R)
      (ResidueJensen.Residue (coordsOf R hn0).rank) ≃ Fin N) :
    M + N + Nat.size (AlgorithmThresholdLP.magnitude (FPTHard.program (FPTHard.faceColumns R)
        (coordsOf R hn0) (FPTHard.integerCosts left right w) rows cols)) +
      bits (2 * (FPTHard.total (FPTHard.integerCosts left right w) : ℤ)) +
      FPTHard.searchBits (FPTHard.integerCosts left right w) + 2 ≤
      PB 40 (DR R) Y := by
  have hY : 1 ≤ Y := by omega
  have hD := DR_pos R
  obtain ⟨hrd, hrm, hfree, -⟩ := FPTHardConcrete.coordinates_bounds R ⟨0, hn0⟩ hc hnb
  have hf : rowCount R ≤ 4 * m := by
    simpa using R.evenRow_count_le (EmbeddingFaces.Flag.canonicalOrder m)
  have hG : GroupSize.residueCount (coordsOf R hn0).rank ≤ PB 4 (DR R) Y :=
    (residueCount_le _ _ hrd).trans (by unfold DR; exact twoPowMul_le_PB hY)
  have hMN := FPTHard.rows_add_columns_le (FPTHard.faceColumns R) (coordsOf R hn0) rows cols
  have hT : M + N ≤ PB 16 (DR R) Y := by
    have h1 : (2 * rowCount R + 2 * m + (coordsOf R hn0).rank + 2) ^ 2 ≤ 2 ^ 7 * Y ^ 2 := by
      have := mul_lin_le (Y := Y) (k := 11) (l := 11)
        (x := 2 * rowCount R + 2 * m + (coordsOf R hn0).rank + 2)
        (y := 2 * rowCount R + 2 * m + (coordsOf R hn0).rank + 2)
        (by simp only [coordsOf, faceCoords] at hrm ⊢; omega)
        (by simp only [coordsOf, faceCoords] at hrm ⊢; omega)
      rw [← pow_two] at this; omega
    have h2 : 6 * GroupSize.residueCount (coordsOf R hn0).rank *
        (2 * rowCount R + 2 * m + (coordsOf R hn0).rank + 2) ^ 2 ≤
        (2 ^ 3 * PB 4 (DR R) Y) * (2 ^ 7 * Y ^ 2) :=
      Nat.mul_le_mul (Nat.mul_le_mul (by norm_num) hG) h1
    have h3 : (2 ^ 3 * PB 4 (DR R) Y) * (2 ^ 7 * Y ^ 2) ≤ PB 16 (DR R) Y := by
      have a1 : 2 ^ 3 * PB 4 (DR R) Y ≤ PB (3 + 4) (DR R) Y :=
        PB_le_mul (twoPowK_le_PB hD hY) le_rfl
      have a2 : 2 ^ 7 * Y ^ 2 ≤ PB (7 + 2) (DR R) Y := PB_le_mul (twoPowK_le_PB hD hY) sq_le_PB
      exact PB_le_mul (K := 3 + 4) (L := 7 + 2) a1 a2
    exact hMN.trans (h2.trans h3)
  have hmag := FPTHard.program_magnitude_le (FPTHard.faceColumns R) (coordsOf R hn0)
    (FPTHard.integerCosts left right w) (4 * n) (2 ^ c)
    (fun e i => by
      have := hfree e i; rw [Int.abs_eq_natAbs] at this; exact_mod_cast this)
    (fun e => (hcost e).le) rows cols
  have hpow : 2 ^ (m + 2) * (2 ^ c + 1) ≤ 2 ^ (m + c + 3) := by
    have : 2 ^ c + 1 ≤ 2 ^ (c + 1) := by rw [pow_succ]; have := @Nat.one_le_two_pow c; omega
    calc 2 ^ (m + 2) * (2 ^ c + 1) ≤ 2 ^ (m + 2) * 2 ^ (c + 1) := Nat.mul_le_mul_left _ this
      _ = 2 ^ (m + c + 3) := by rw [← pow_add]; ring_nf
  have hmag' : AlgorithmThresholdLP.magnitude (FPTHard.program (FPTHard.faceColumns R)
      (coordsOf R hn0) (FPTHard.integerCosts left right w) rows cols) ≤
      1 + M * N * (4 * n + 1) + M + N * 2 ^ (m + c + 3) :=
    hmag.trans (by have := Nat.mul_le_mul_left N hpow; omega)
  have hsz := size_magnitude_le _ (4 * n) (m + c + 3) hmag'
  have hsb := searchBits_small c _ hcost
  have hb2 : bits (2 * (FPTHard.total (FPTHard.integerCosts left right w) : ℤ)) =
      FPTHard.searchBits (FPTHard.integerCosts left right w) := by
    unfold FPTHard.searchBits
    rw [show (2 * (FPTHard.total (FPTHard.integerCosts left right w) : ℤ)) =
      ((2 * FPTHard.total (FPTHard.integerCosts left right w) : ℕ) : ℤ) by push_cast; ring]
    exact FunLP.bits_natCast _
  rw [hb2]
  -- the three summands
  have q1 : (M + N) * (M + N) * (4 * n + 1) ≤ PB 36 (DR R) Y := by
    have : 4 * n + 1 ≤ 2 ^ 3 * Y := by omega
    exact PB_le_mul (K := 16 + 16) (L := 3 + 1) (PB_le_mul (K := 16) (L := 16) hT hT)
      (lin_le_PB (k := 3) hD hY this)
  have q2 : 3 * (M + N) ≤ PB 36 (DR R) Y :=
    PB_weaken hY (PB_le_mul (K := 2) (L := 16)
      ((show 3 ≤ 2 ^ 2 by norm_num).trans (twoPowK_le_PB hD hY)) hT) (by norm_num)
  have q3 : 5 * m + 3 * c + 20 ≤ PB 36 (DR R) Y :=
    PB_weaken hY (lin_le_PB (k := 5) hD hY (by omega)) (by norm_num)
  have hsum : M + N + Nat.size (AlgorithmThresholdLP.magnitude (FPTHard.program
      (FPTHard.faceColumns R) (coordsOf R hn0) (FPTHard.integerCosts left right w) rows cols)) +
      FPTHard.searchBits (FPTHard.integerCosts left right w) +
      FPTHard.searchBits (FPTHard.integerCosts left right w) + 2 ≤
      4 * PB 36 (DR R) Y := by
    have : (M + N) * (M + N) * (4 * n + 1) = (M + N) * (M + N) * (4 * n + 1) := rfl
    omega
  have := PB_le_of_mul (k := 4) (K := 36) hD hY hsum
  exact PB_weaken hY this (by norm_num)

end MWIS.FPTMainProg

end
