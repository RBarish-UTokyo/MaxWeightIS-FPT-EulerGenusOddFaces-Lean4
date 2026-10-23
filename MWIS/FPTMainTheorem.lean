module

public import MWIS.FPTProgram
public import MWIS.FPTRegisterClaim
public import MWIS.FPTRunFunInterp
public import MWIS.Fun.InterpMain
public import MWIS.TreeCotreeFPT

/-!
# The fixed-parameter claim from the numerical-stage program

`fptClaim_of_prog` assembles the operational proof of `Spec.FPTClaim`: the concrete
program `fptProgram constsProg.encode prog.encode` carries XP's top level, the
fixed-parameter hard procedure with the tree–cotree coordinates
`TreeCotree.faceCoordinates`, the `Fun` interpreter and the two builders. The only
remaining hypotheses concern the five-input `Fun` program `prog` of the numerical
stage: it computes the decoded slack (`FPTRunFun.ProgFunStage`) within a budget of
fixed-parameter shape (`FPTRegister.FunBudgetBound`).
-/

@[expose] public section

namespace MWIS.FPTMainTheorem

open MWIS.RegisterMachine MWIS.FPTProgram MWIS.FPTRegister

/-- The coordinate construction of the fixed-parameter hard procedure. -/
def coords : CoordFn := fun {_ _} {left right} R root =>
  TreeCotree.faceCoordinates left right R root

theorem coords_valid : CoordsValid coords := fun R root hc hn =>
  TreeCotree.faceCoordinates_valid R root hc hn

theorem consts_mono {c c' : ℕ} {cb : ℕ → ℕ → ℕ → ℕ} (hc : c ≤ c')
    (h : ConstsBudgetBound c cb) : ConstsBudgetBound c' cb := fun W n m =>
  (h W n m).trans (Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hc)
    (Nat.pow_le_pow_right (by omega) hc))

theorem fun_mono {c c' : ℕ} {fb : ℕ → ℕ → RegisterComponentSolve.HardBudget} (hc : c ≤ c')
    (h : FunBudgetBound c fb) : FunBudgetBound c' fb :=
  fun W w0 _ _ _ _ R w hco hnb hw ho =>
    (h W w0 R w hco hnb hw ho).trans (shape_mono_c hc (by omega))

/-- **The fixed-parameter claim.** A numerical-stage program computing the decoded
slack within a fixed-parameter budget gives `Spec.FPTClaim`. -/
theorem fptClaim_of_prog (prog : Fun.Expr [.tree, .tree, .tree, .tree, .tree] .tree)
    (pb : ℕ → ℕ → RegisterComponentSolve.HardBudget) (c : ℕ)
    (hprog : FPTRunFun.ProgFunStage prog coords pb)
    (hpb : FunBudgetBound c pb) : Spec.FPTClaim := by
  let code := fptProgram FPTRunFun.constsProg.encode prog.encode
  have heval : FPTRunFun.EvalSpec code fptInterp.eval Fun.Interp.K :=
    FPTRunFun.evalSpec_of_interp fun e => Fun.Interp.evalSpec (fptInterp_matches _ _) e
  have hconsts := FPTBuild.constsSpec_built code fptHardIds.consts fptBuild1 fptInterp.eval
    (fptProgram_consts _ _) heval (fptProgram_build1 _ _)
  have hfun := FPTBuild.funStageSpec_built code fptHardIds.funStage fptBuild2 fptInterp.eval
    (fptProgram_funStage _ _) heval prog (fptProgram_build2 _ _) hprog
  have hcb := FPTRunFun.constsBudgetBound Fun.Interp.K
    (FPTBuild.buildBudget FPTRunFun.constsProg.encode)
  have hfb := FPTRunFun.stageBudget_bound (K := Fun.Interp.K)
    (B := FPTBuild.buildBudget prog.encode) hpb
  exact fptClaim_of_funStage code fptTop (fptTop_matches _ _) fptHardIds
    (fptHardIds_matches _ _) fptTop_hard coords_valid hconsts hfun
    (consts_mono (le_max_left _ _) hcb)
    (fun_mono (le_max_right _ _) hfb)

end MWIS.FPTMainTheorem

end
