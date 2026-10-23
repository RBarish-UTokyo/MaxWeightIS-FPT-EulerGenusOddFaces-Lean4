module

public import MWIS.FPTMainProg

/-!
# Cost decomposition of the numerical-stage program

The cost of `FPTMainProg.prog optF` is bounded by the sum of the costs of its
component functions on their actual arguments, plus explicit overhead for the
glue code: projections, the zips and maps assembling the network input, the
modulus, the width and slack arithmetic, the list lengths and the output words.
-/

@[expose] public section

namespace MWIS.FPTMainProg

open MWIS.Fun MWIS.FunLP MWIS.FPTTrees MWIS.FPTRegister MWIS.FPTTreeParse
open MWIS.FunNetwork (tE tOut tL)

/-! ## Glue functions -/

theorem edgeRecF_cost (x : (Ty.prod (.prod (.list .int) FunCoordinates.RowTy) .int).denote) :
    edgeRecF.costAt x ≤ 40 := by
  simp only [edgeRecF, Fn.costAt, Expr.cost, Var.index]
  omega

theorem inputF_cost
    (x : (Ty.prod (.list (.list .int)) (.prod (.list FunCoordinates.RowTy) (.list .int))).denote) :
    inputF.costAt x ≤ 200 * (x.1.length + 1) + 30 := by
  simp only [inputF, Fn.costAt, Expr.cost, cost_call, Var.index, Expr.denote, Var.get,
    denote_call, zipFn_apply]
  have h1 := zipFn_cost (.list .int) FunCoordinates.RowTy x.1 x.2.1
  have h2 := zipFn_cost (.prod (.list .int) FunCoordinates.RowTy) .int (x.1.zip x.2.1) x.2.2
  have h3 := mapF_cost edgeRecF ((x.1.zip x.2.1).zip x.2.2) 40 (fun a _ => edgeRecF_cost a)
  have l1 : (x.1.zip x.2.1).length ≤ x.1.length := by simp
  have l2 : ((x.1.zip x.2.1).zip x.2.2).length ≤ x.1.length := by simp
  unfold Fn.costAt at h1 h2 h3
  have h2' : (x.1.zip x.2.1).length * 62 ≤ x.1.length * 62 := Nat.mul_le_mul_right _ l1
  have h3' : ((x.1.zip x.2.1).zip x.2.2).length * 60 ≤ x.1.length * 60 :=
    Nat.mul_le_mul_right _ l2
  nlinarith

theorem widthWordF_cost (x : (Ty.prod .int .int).denote) :
    widthWordF.costAt x = x.1.toNat + bits x.2 + 5 := by
  simp only [widthWordF, Fn.costAt, Expr.cost, Var.index, Expr.denote, Var.get]
  omega

theorem formatOutput_cost (w : ℤ) (l : List ℤ) (B : ℕ) (hl : ∀ k ∈ l, bits k ≤ B) :
    formatOutput.costAt (w, l) ≤ (l.length + 1) * (w.toNat + B + 26) + l.length + 3 := by
  simp only [formatOutput, Fn.costAt, Expr.cost, cost_call, Var.index, Expr.denote, Var.get,
    denote_call, FunNetwork.mapWith_apply, List.length_map]
  have h := FunNetwork.mapWith_cost widthWordF (w, l) (w.toNat + B + 6) (fun a ha => by
    rw [widthWordF_cost]; have := hl a ha; simp only at this ⊢; omega)
  unfold Fn.costAt at h
  simp only at h
  have e : (l.length + 1) * (w.toNat + B + 6 + 20) = (l.length + 1) * (w.toNat + B + 26) := by
    ring
  omega

/-! ## Stages -/

theorem parseF_cost (x : Trees5.denote) :
    parseF.costAt x ≤ parseColumns.costAt x.1 + parseEdges.costAt x.2.1 + x.2.2.1.spine +
      (lengthF .tree).costAt x.2.2.1.items + parseWords.costAt x.2.2.2.1 +
      parseCount.costAt x.2.2.2.2 + 40 := by
  simp only [parseF, Fn.costAt, Expr.cost, cost_call, Var.index, Expr.denote, Var.get]
  omega

theorem coordStageF_cost (x : ParsedTy.denote) :
    coordStageF.costAt x ≤
      FunCoordinates.coordFn.costAt (x.2.1, (x.1, (x.2.2.1, (x.2.2.2.2, 0)))) + 40 := by
  simp only [coordStageF, Fn.costAt, Expr.cost, cost_call, Var.index, Expr.denote, Var.get]
  omega

theorem inputStageF_cost (x : S1.denote) :
    inputStageF.costAt x ≤ inputF.costAt (x.1.1, (x.2.2, x.1.2.2.2.1)) + 40 := by
  simp only [inputStageF, Fn.costAt, Expr.cost, cost_call, Var.index, Expr.denote, Var.get]
  omega

/-- The modulus as an integer function. -/
def muV (r : ℤ) : ℤ := 4 * r + 2 * (1 / (r + 1))

/-- The argument of the network program in the optimization stage. -/
abbrev netArg (x : S2.denote) : FunNetwork.tIn.denote := (x.2.1, (x.2.2.1, (muV x.2.2.1, x.2.2.2)))

theorem optStageF_cost (optF : Fn OptArg .int) (x : S2.denote) :
    (optStageF optF).costAt x ≤ FunNetwork.networkFn.costAt (netArg x) +
      FunNetwork.offsetFn.costAt x.2.2.2 + FunNetwork.bitsFn.costAt x.2.2.2 +
      optF.costAt (FunNetwork.networkFn.apply (netArg x),
        (FunNetwork.offsetFn.apply x.2.2.2, FunNetwork.bitsFn.apply x.2.2.2)) +
      (bits x.2.2.1 + 4) ^ 2 + 10 * bits x.2.2.1 + 90 := by
  simp only [optStageF, muE, Fn.costAt, Expr.cost, cost_call, Var.index, Expr.denote, Var.get,
    denote_call, IntOp.charge, IntOp.eval, netArg, muV]
  have h4 : bits 4 = 3 := by decide
  have h2 : bits 2 = 2 := by decide
  have h1 : bits 1 = 1 := by decide
  have hd : bits (1 / (x.2.2.1 + 1)) ≤ 1 := by
    have : (1 / (x.2.2.1 + 1)).natAbs ≤ 1 := by
      have := Int.natAbs_ediv_le_natAbs 1 (x.2.2.1 + 1); simpa using this
    exact (FPTRunFun.bits_le_natAbs _).trans this
  have hr1 : bits (x.2.2.1 + 1) ≤ bits x.2.2.1 + 2 := by
    have := FunLP.bits_add_le x.2.2.1 1; rw [h1] at this; omega
  have hm1 : bits (4 * x.2.2.1) ≤ bits x.2.2.1 + 3 := by
    have := FunLP.bits_mul_le 4 x.2.2.1; omega
  have hm2 : bits (2 * (1 / (x.2.2.1 + 1))) ≤ 3 := by
    have := FunLP.bits_mul_le 2 (1 / (x.2.2.1 + 1)); omega
  have hsq : (1 + bits (x.2.2.1 + 1) + 1) ^ 2 ≤ (bits x.2.2.1 + 4) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  rw [h4, h2, h1]
  omega

theorem finalF_cost (x : S3.denote) :
    finalF.costAt x ≤ (lengthF tE).costAt x.2.1 + FunNetwork.slackFn.costAt (x.2.2, x.2.1) +
      formatOutput.costAt (3 * x.1 + x.2.1.length + 4, FunNetwork.slackFn.apply (x.2.2, x.2.1)) +
      9 * x.1.natAbs + 2 * x.2.1.length + 40 := by
  simp only [finalF, Fn.costAt, Expr.cost, cost_call, Var.index, Expr.denote, Var.get,
    denote_call, lengthF_apply, IntOp.charge, IntOp.eval]
  have h3 : bits 3 = 2 := by decide
  have h4 : bits 4 = 3 := by decide
  have b1 := FPTRunFun.bits_le_natAbs x.1
  have b2 := FPTRunFun.bits_le_natAbs (3 * x.1)
  have b3 := FPTRunFun.bits_le_natAbs (3 * x.1 + (x.2.1.length : ℤ))
  have b4 := FPTRunFun.bits_le_natAbs (x.2.1.length : ℤ)
  have n1 : (3 * x.1).natAbs = 3 * x.1.natAbs := by
    rw [Int.natAbs_mul]; rfl
  have n2 : (3 * x.1 + (x.2.1.length : ℤ)).natAbs ≤ 3 * x.1.natAbs + x.2.1.length := by
    have := Int.natAbs_add_le (3 * x.1) (x.2.1.length : ℤ)
    rw [n1] at this
    simpa using this
  have n3 : ((x.2.1.length : ℤ)).natAbs = x.2.1.length := Int.natAbs_natCast _
  rw [h3, h4]
  omega

/-! ## The whole program -/

theorem mainF_cost (optF : Fn OptArg .int) (x : Trees5.denote) :
    (mainF optF).costAt x ≤ parseF.costAt x + coordStageF.costAt (parseF.apply x) +
      inputStageF.costAt (coordStageF.apply (parseF.apply x)) +
      (optStageF optF).costAt (inputStageF.apply (coordStageF.apply (parseF.apply x))) +
      finalF.costAt ((optStageF optF).apply
        (inputStageF.apply (coordStageF.apply (parseF.apply x)))) + 4 := by
  simp only [mainF, Fn.costAt_comp, Fn.apply_comp]
  omega

theorem prog_cost (optF : Fn OptArg .int) (env : Env [.tree, .tree, .tree, .tree, .tree]) :
    (prog optF).cost env ≤
      (mainF optF).costAt (env.1, (env.2.1, (env.2.2.1, (env.2.2.2.1, env.2.2.2.2.1)))) + 30 := by
  simp only [prog, cost_call, Expr.cost, Var.index, Expr.denote, Var.get]
  omega

end MWIS.FPTMainProg

end
