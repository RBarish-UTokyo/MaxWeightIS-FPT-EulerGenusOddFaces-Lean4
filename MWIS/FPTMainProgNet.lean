module

public import MWIS.FPTMainProgStage

/-!
# Shapes of the network-program costs

The cost bounds of `MWIS.FunNetworkCost` for the network program, the offset, the
search width and the slack decoder, on the network input of an instance, are
bounded by fixed-parameter shapes `PB K (DR R) Y` with absolute `K`.
-/

@[expose] public section

namespace MWIS.FPTMainProg

open MWIS.Fun MWIS.FunLP MWIS.FPTTrees MWIS.FPTRegister MWIS.FPTTreeParse

variable {n m : ℕ} {left right : Fin m → Fin n}

/-- A bound `k0 · (A · B²)²` with `A ≤ 2^i Y`, `B ≤ 2^j Y` and `k0 ≤ 2^l`. -/
theorem quartic_le_PB {D Y : ℕ} (hD : 1 ≤ D) (hY : 1 ≤ Y) {k0 A B i j l : ℕ}
    (hk : k0 ≤ 2 ^ l) (hA : A ≤ 2 ^ i * Y) (hB : B ≤ 2 ^ j * Y) :
    k0 * (A * B ^ 2) ^ 2 ≤ PB (l + ((i + 1) + (j + 1) * 2) * 2) D Y := by
  have a := lin_le_PB (D := D) hD hY hA
  have b := lin_le_PB (D := D) hD hY hB
  have b2 := PB_le_pow b 2
  have ab := PB_le_mul (K := i + 1) (L := (j + 1) * 2) a b2
  have ab2 := PB_le_pow ab 2
  exact PB_le_mul (K := l) (L := ((i + 1) + (j + 1) * 2) * 2)
    (hk.trans (twoPowK_le_PB hD hY)) ab2

theorem costSize {c : ℕ} (cost : Fin m → ℕ) (hcost : ∀ e, cost e < 2 ^ c) :
    ∀ e, (cost e).size ≤ c := fun e => Nat.size_le.mpr (hcost e)

theorem offset_le (Y c : ℕ) (R : EmbeddingFaces.Ribbon left right) (w : Fin n → ℚ)
    (hn0 : 0 < n) (hcost : ∀ e, FPTHard.integerCosts left right w e < 2 ^ c)
    (hYge : n + m + c + 2 ≤ Y) :
    FunNetwork.offsetFn.costAt (inputOf R w hn0) + FunNetwork.bitsFn.costAt (inputOf R w hn0) ≤
      PB 31 (DR R) Y := by
  have hY : 1 ≤ Y := by omega
  have h1 := FunNetwork.offsetFn_cost (FPTHard.faceColumns R) (coordsOf R hn0)
    (FPTHard.integerCosts left right w) c (costSize _ hcost)
  have h2 := FunNetwork.bitsFn_cost (FPTHard.faceColumns R) (coordsOf R hn0)
    (FPTHard.integerCosts left right w) c (costSize _ hcost)
  have q1 := quartic_le_PB (D := DR R) (DR_pos R) hY (k0 := 95) (l := 7) (i := 0) (j := 4)
    (A := m + 2) (B := 2 * (3 * m + c + 9) + 2) (by norm_num) (by omega) (by omega)
  have q2 := quartic_le_PB (D := DR R) (DR_pos R) hY (k0 := 96) (l := 7) (i := 0) (j := 4)
    (A := m + 2) (B := 2 * (3 * m + c + 9) + 2) (by norm_num) (by omega) (by omega)
  exact PB_weaken hY (PB_add_le (DR_pos R) hY (h1.trans q1) (h2.trans q2)) (by norm_num)

theorem slack_le (Y c : ℕ) (R : EmbeddingFaces.Ribbon left right) (w : Fin n → ℚ)
    (hn0 : 0 < n) (hc : Incidence.Connected left right) (hnb : ¬ Incidence.Bipartite left right)
    (hcost : ∀ e, FPTHard.integerCosts left right w e < 2 ^ c) (hYge : n + m + c + 2 ≤ Y) :
    FunNetwork.slackFn.costAt ((valueOf R w hn0 : ℤ), inputOf R w hn0) ≤ PB 34 (DR R) Y := by
  have hY : 1 ≤ Y := by omega
  have h := FunNetwork.slackFn_cost (FPTHard.faceColumns R) (coordsOf R hn0)
    (FPTHard.integerCosts left right w) c (costSize _ hcost) (valueOf R w hn0)
  have hv : (valueOf R w hn0).size ≤ 2 * m + c + 6 :=
    (Nat.size_le_size (valueOf_le_total R w hn0 hc hnb)).trans
      ((size_total_le _).trans (searchBits_small c _ hcost))
  generalize (valueOf R w hn0).size = V at hv h
  have q := quartic_le_PB (D := DR R) (DR_pos R) hY (k0 := 154) (l := 8) (i := 0) (j := 5)
    (A := m + 2) (B := 2 * (3 * m + c + V + 9) + 2) (by norm_num)
    (by omega) (by omega)
  exact PB_weaken hY (h.trans q) (by norm_num)

theorem net_le (Y c : ℕ) (R : EmbeddingFaces.Ribbon left right) (w : Fin n → ℚ)
    (hn0 : 0 < n) (hc : Incidence.Connected left right) (hnb : ¬ Incidence.Bipartite left right)
    (hcost : ∀ e, FPTHard.integerCosts left right w e < 2 ^ c) (hYge : n + m + c + 2 ≤ Y) :
    FunNetwork.networkFn.costAt (FunNetwork.networkInput (FPTHard.faceColumns R) (coordsOf R hn0)
      (FPTHard.integerCosts left right w)) ≤ PB 336 (DR R) Y := by
  have hY : 1 ≤ Y := by omega
  have hD := DR_pos R
  obtain ⟨hrd, -, hfree, -⟩ := FPTHardConcrete.coordinates_bounds R ⟨0, hn0⟩ hc hnb
  have hf : (R.evenRootIndices (EmbeddingFaces.Flag.canonicalOrder m)).length ≤ 4 * m := by
    simpa using R.evenRow_count_le (EmbeddingFaces.Flag.canonicalOrder m)
  have h := FunNetwork.networkFn_cost (FPTHard.faceColumns R) (coordsOf R hn0)
    (FPTHard.integerCosts left right w) c (4 * n) (fun e i => by
      have := hfree e i; rw [Int.abs_eq_natAbs] at this
      exact (FPTRunFun.bits_le_natAbs _).trans (by exact_mod_cast this)) (costSize _ hcost)
  refine h.trans ?_
  have hG : GroupSize.residueCount (coordsOf R hn0).rank ≤ PB 4 (DR R) Y :=
    (residueCount_le _ _ hrd).trans (by unfold DR; exact twoPowMul_le_PB hY)
  generalize (coordsOf R hn0).rank = r at hG ⊢
  generalize (R.evenRootIndices (EmbeddingFaces.Flag.canonicalOrder m)).length = f at hf ⊢
  clear hfree hrd h
  -- the list-length parameter
  have hL : FunNetwork.netL (f) m r ≤ PB 17 (DR R) Y := by
    unfold FunNetwork.netL
    have a1 : 48 ≤ PB 6 (DR R) Y := (show 48 ≤ 2 ^ 6 by norm_num).trans (twoPowK_le_PB hD hY)
    have a2 : (f + 1) ^ 2 ≤ PB (3 * 2) (DR R) Y :=
      PB_le_pow (lin_le_PB (k := 2) hD hY (by omega)) 2
    have a3 : m + 1 ≤ PB 1 (DR R) Y := (show m + 1 ≤ Y by omega).trans Y_le_PB
    exact PB_le_mul (K := 6 + 3 * 2 + 1) (L := 4)
      (PB_le_mul (K := 6 + 3 * 2) (L := 1) (PB_le_mul (K := 6) (L := 3 * 2) a1 a2) a3) hG
  have hL1 : FunNetwork.netL f m r + 1 ≤ PB (2 + 17) (DR R) Y :=
    PB_add_le (K := 17) hD hY hL (PB_one_le hY 17)
  have hB : 2 * FunNetwork.netB f m r c (4 * n) + 2 ≤ PB (2 + (1 + (2 + (1 + 17)))) (DR R) Y := by
    have b1 : 2 * FunNetwork.netL f m r ≤ PB (1 + 17) (DR R) Y :=
      PB_le_mul (K := 1) (L := 17) ((show 2 ≤ 2 ^ 1 by norm_num).trans (twoPowK_le_PB hD hY)) hL
    have b2 : m + c + 4 * n + 8 ≤ PB (1 + 17) (DR R) Y :=
      PB_weaken hY (lin_le_PB (k := 3) hD hY (by omega)) (by norm_num)
    have b3 := PB_add_le (K := 1 + 17) hD hY b1 b2
    have e : FunNetwork.netB f m r c (4 * n) = 2 * FunNetwork.netL f m r + (m + c + 4 * n + 8) := by
      unfold FunNetwork.netB; ring
    rw [e]
    have b4 := PB_le_mul (K := 1) (L := 2 + (1 + 17))
      ((show 2 ≤ 2 ^ 1 by norm_num).trans (twoPowK_le_PB hD hY)) b3
    exact PB_add_le (K := 1 + (2 + (1 + 17))) hD hY b4 (PB_weaken (K := 1) hY
      ((show 2 ≤ 2 ^ 1 by norm_num).trans (twoPowK_le_PB hD hY)) (by norm_num))
  have hsq := PB_le_pow hB 2
  have hprod := PB_le_mul (K := 2 + 17) (L := (2 + (1 + (2 + (1 + 17)))) * 2) hL1 hsq
  have h5 := PB_le_pow hprod 5
  have h6 := PB_le_mul (K := 11) (L := (2 + 17 + (2 + (1 + (2 + (1 + 17)))) * 2) * 5)
    ((show 2039 ≤ 2 ^ 11 by norm_num).trans (twoPowK_le_PB hD hY)) h5
  exact PB_weaken hY h6 (by norm_num)


end MWIS.FPTMainProg

end
