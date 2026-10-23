module

public import MWIS.FPTFinal
public import MWIS.FunLPOpt

/-!
# Solution: the proved fixed-parameter main claim

`MWIS.Spec.fpt_claim` is the fixed-parameter theorem of *Maximum-weight
independent set in embedded graphs parameterized by Euler genus and number of
odd faces* (forthcoming), stated in `Challenge.lean` for the
sixteen-register pointer machine with its explicit bit-stack cost. The witness
program is the concrete 402-procedure table `MWIS.FPTProgram.fptProgram`
instantiated with the two constant `Fun` programs: the constants stage and the
numerical stage `MWIS.FPTMainProg.prog MWIS.FunLP.optF`, which computes the
exact quotient coordinates, the finite-group network LP, its exact optimum by
threshold search with a rounded ellipsoid method, and the decoded optimal slack.
-/

@[expose] public section

/-- **The fixed-parameter theorem**: a fixed program computes a maximum-weight independent set in
`2^(c(p size p + 1)) (N size M)^c` bit operations for an absolute constant `c`. -/
theorem MWIS.Spec.fpt_claim : MWIS.Spec.FPTClaim :=
  MWIS.FPTFinal.fptClaim_of_optimizer MWIS.FunLP.optF_spec MWIS.FunLP.optF_cost

end
