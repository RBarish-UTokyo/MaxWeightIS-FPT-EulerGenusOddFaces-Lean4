module

public import MWIS.FPTMainProgCost
public import MWIS.FPTMainProgShape
public import MWIS.FPTHardBounds
public import MWIS.FPTRegisterClaim
public import MWIS.FunNetworkCost

/-!
# The fixed-parameter cost bound of the numerical-stage program

`OptCost optF a` is the cost bound of the dense-program optimizer: a polynomial of
degree and coefficient `a` in the dimensions, the bit length of the magnitude, the bit
length of the offset and the search width. The coordinate program is bounded by
`FPTHardConcrete.coordFn_faceColumns_cost`; the network program, the offset and width
functions and the slack decoder by `MWIS.FunNetworkCost`.

From these, `prog_cost_le` bounds the cost of `prog optF` on every instance by
`PB (mainK a) D Y` with `D = d · size d + 1` (`d` the number of XP's global rows)
and `Y = n + m + W + c + 2`. `progFunStage` is `FPTRunFun.ProgFunStage` and
`mainBudget_bound` is `FPTRegisterClaim.FunBudgetBound` for this budget.
-/

@[expose] public section

namespace MWIS.FPTMainProg

open MWIS.Fun MWIS.FunLP MWIS.FPTTrees MWIS.FPTRegister MWIS.FPTTreeParse
open MWIS.FunNetwork (tE tOut tL)
open MWIS.RegisterComponentSolve (HardBudget)

variable {n m : ℕ} {left right : Fin m → Fin n}

/-! ## Component cost hypotheses -/

/-- The argument of the coordinate program on an instance (root `0`). -/
abbrev coordArg (R : EmbeddingFaces.Ribbon left right) : FunCoordinates.CoordArg.denote :=
  ((List.finRange m).map fun e => (((left e : ℕ) : ℤ), ((right e : ℕ) : ℤ)),
    ((List.finRange m).map fun e => FunNetwork.columnCode (FPTHard.faceColumns R e),
      ((n : ℤ), ((rowCount R : ℤ), 0))))

/-- The optimizer runs within a polynomial, of degree and coefficient `a`, in the
dimensions, the bit length of the magnitude, the bit length of the offset and the search
width of the dense program. -/
def OptCost (optF : Fn OptArg .int) (a : ℕ) : Prop :=
  ∀ {M N : ℕ} (P : AlgorithmNetworkEncoding.DenseProgram M N) (offset : ℤ) (b : ℕ),
    optF.costAt (FunNetwork.DenseProgram.toFun P, (offset, (b : ℤ))) ≤
      a * (M + N + Nat.size (AlgorithmThresholdLP.magnitude P) + bits offset + b + 2) ^ a

/-- The coordinate program on an instance, by `FPTHardConcrete.coordFn_faceColumns_cost`. -/
theorem coordArg_cost (R : EmbeddingFaces.Ribbon left right) (hn0 : 0 < n) :
    FunCoordinates.coordFn.costAt (coordArg R) ≤ 17000 * (m + n + rowCount R + 5) ^ 5 := by
  have h := FPTHardConcrete.coordFn_faceColumns_cost R ⟨0, hn0⟩
  have he : FunCoordinates.edgeList left right =
      (List.finRange m).map fun e => (((left e : ℕ) : ℤ), ((right e : ℕ) : ℤ)) := by
    simp [FunCoordinates.edgeList, List.ofFn_eq_map]
  rw [he, List.ofFn_eq_map] at h
  simpa using h

/-! ## Instance facts -/

/-- The exponent unit `d · size d + 1` of a ribbon, `d` the number of XP's global rows. -/
def DR (R : EmbeddingFaces.Ribbon left right) : ℕ :=
  (ComputedEmbeddedMatrices.globalRows R).length *
    Nat.size (ComputedEmbeddedMatrices.globalRows R).length + 1

theorem muV_nat (k : ℕ) : muV (k : ℤ) = (GroupSize.modulus k : ℤ) := by
  unfold muV GroupSize.modulus
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · have h1 : (1 : ℤ) / ((k : ℤ) + 1) = 0 := Int.ediv_eq_zero_of_lt (by norm_num) (by omega)
    have hk0 : k ≠ 0 := by omega
    simp only [h1, hk0, ↓reduceIte]
    push_cast; ring

theorem searchBits_small (c : ℕ) (cost : Fin m → ℕ) (hcost : ∀ e, cost e < 2 ^ c) :
    FPTHard.searchBits cost ≤ 2 * m + c + 6 := by
  have h := FPTHard.searchBits_le cost (2 ^ c) (fun e => (hcost e).le)
  have h1 : m.size ≤ m := Nat.size_le.mpr Nat.lt_two_pow_self
  have h2 : (2 ^ c + 1).size ≤ c + 2 := Nat.size_le.mpr (by
    have e : 2 ^ (c + 2) = 4 * 2 ^ c := by rw [pow_add]; ring
    have := @Nat.one_le_two_pow c
    omega)
  omega

theorem size_total_le (cost : Fin m → ℕ) :
    Nat.size (FPTHard.total cost) ≤ FPTHard.searchBits cost :=
  Nat.size_le_size (by omega)

/-- The magnitude bit length of a dense program bounded entrywise. -/
theorem size_magnitude_le {M N : ℕ} (P : AlgorithmNetworkEncoding.DenseProgram M N) (K k : ℕ)
    (hmag : AlgorithmThresholdLP.magnitude P ≤ 1 + M * N * (K + 1) + M + N * 2 ^ k) :
    Nat.size (AlgorithmThresholdLP.magnitude P) ≤
      1 + (M + N) * (M + N) * (K + 1) + 2 * (M + N) + k := by
  set A := 1 + (M + N) * (M + N) * (K + 1) + 2 * (M + N)
  have hA : AlgorithmThresholdLP.magnitude P ≤ A * 2 ^ k := by
    have hp : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have h1 : M * N * (K + 1) ≤ (M + N) * (M + N) * (K + 1) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul (by omega) (by omega))
    have h2 : N * 2 ^ k ≤ (M + N) * 2 ^ k := Nat.mul_le_mul_right _ (by omega)
    have h3 : (1 + (M + N) * (M + N) * (K + 1) + M) ≤
        (1 + (M + N) * (M + N) * (K + 1) + M) * 2 ^ k := Nat.le_mul_of_pos_right _ hp
    calc AlgorithmThresholdLP.magnitude P ≤ 1 + M * N * (K + 1) + M + N * 2 ^ k := hmag
      _ ≤ (1 + (M + N) * (M + N) * (K + 1) + M) * 2 ^ k + (M + N) * 2 ^ k := by omega
      _ ≤ A * 2 ^ k := by rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ (by omega)
  refine Nat.size_le.mpr (lt_of_le_of_lt hA ?_)
  rw [pow_add]
  exact Nat.mul_lt_mul_of_pos_right Nat.lt_two_pow_self (Nat.two_pow_pos _)

/-! ## The bound -/

/-- The exponent of the bound. -/
def mainK (a : ℕ) : ℕ := 41 * a + 350

/-- The budget of the numerical-stage program. -/
def mainBudget (a : ℕ) : ℕ → ℕ → HardBudget :=
  fun W c {n m} {_left _right} R _w => PB (mainK a) (DR R) (n + m + W + c + 2)

theorem twoPowMul_le_PB {K D Y : ℕ} (hY : 1 ≤ Y) : 2 ^ (K * D) ≤ PB K D Y :=
  Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ hY)

end MWIS.FPTMainProg

end
