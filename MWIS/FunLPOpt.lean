module

public import MWIS.FunLPThresholdCost
public import MWIS.FPTMainProgBound

/-!
# The dense-program optimizer for the main program

`FunLP.optF` satisfies the optimizer contract `FPTMainProg.OptSpec` and the cost
contract `FPTMainProg.OptCost` with the numeral `288`: on the encoding of a dense
program with `M` rows and `N` columns it returns `AlgorithmThresholdLP.optimize`,
and it costs at most `288 (M + N + size (magnitude P) + bits offset + b + 2)^288`.
-/

@[expose] public section

namespace MWIS.FunLP

open MWIS.Fun

/-- The optimizer computes `AlgorithmThresholdLP.optimize` on every encoded program. -/
theorem optF_spec : FPTMainProg.OptSpec optF := by
  intro M N P offset b
  exact optF_apply P offset b

/-- The optimizer runs within `288 X^288`. -/
theorem optF_cost : FPTMainProg.OptCost optF 288 := by
  intro M N P offset b
  have h := optF_cost_le P offset b
  have hX : 2 ≤ optBase P offset b := by unfold optBase; omega
  have h1 : 2 ^ 252 ≤ optBase P offset b ^ 252 := Nat.pow_le_pow_left hX 252
  have h2 : 2 ^ 252 * optBase P offset b ^ 36 ≤ 288 * optBase P offset b ^ 288 := by
    have e : optBase P offset b ^ 288 = optBase P offset b ^ 252 * optBase P offset b ^ 36 := by
      rw [← pow_add]
    rw [e]
    have : 2 ^ 252 ≤ 288 * optBase P offset b ^ 252 :=
      calc (2 : ℕ) ^ 252 ≤ optBase P offset b ^ 252 := h1
        _ ≤ 288 * optBase P offset b ^ 252 := Nat.le_mul_of_pos_left _ (by norm_num)
    calc 2 ^ 252 * optBase P offset b ^ 36 ≤ (288 * optBase P offset b ^ 252) * optBase P offset b ^ 36 :=
          Nat.mul_le_mul_right _ this
      _ = 288 * (optBase P offset b ^ 252 * optBase P offset b ^ 36) := Nat.mul_assoc _ _ _
  unfold optBase at h h2
  exact le_trans h h2

end MWIS.FunLP

end
