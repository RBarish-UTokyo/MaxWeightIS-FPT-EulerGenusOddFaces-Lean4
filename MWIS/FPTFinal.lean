module

public import MWIS.FPTMainTheorem
public import MWIS.FPTMainProgMain

/-!
# The fixed-parameter main claim from the exact LP optimizer

The numerical stage `FPTMainProg.prog optF` computes the coordinate tables,
the finite-group network LP, its exact optimum through the optimizer `optF`,
and the decoded slack. If `optF` computes `AlgorithmThresholdLP.optimize`
(`OptSpec`) within a polynomial cost (`OptCost`), the concrete program table
`FPTProgram.fptProgram` proves `Spec.FPTClaim`.
-/

@[expose] public section

namespace MWIS.FPTFinal

open MWIS.FPTMainProg

/-- `Spec.FPTClaim` from any `Fun` optimizer that computes the exact threshold
LP optimum within a polynomial cost. -/
theorem fptClaim_of_optimizer {optF : FunLP.Fn OptArg .int} {a : ℕ}
    (hopt : OptSpec optF) (hcost : OptCost optF a) : Spec.FPTClaim :=
  FPTMainTheorem.fptClaim_of_prog (prog optF) (mainBudget a) (3 * mainK a)
    (progFunStage hopt hcost) (mainBudget_bound a)

end MWIS.FPTFinal

end
