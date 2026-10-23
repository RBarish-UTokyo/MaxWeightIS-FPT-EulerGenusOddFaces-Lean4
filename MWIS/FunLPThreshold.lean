module

public import MWIS.FunLPSolver
public import MWIS.FunNetworkEncode
public import MWIS.AlgorithmThresholdLP

/-!
# Threshold feasibility and the optimizer as `Fun` programs

`feasLPFn` computes `AlgorithmThresholdLP.feasible P` on the list encoding
`FunNetwork.DenseProgram.toFun P` (`feasLPFn_apply`): it computes the magnitude,
its bit length, the column count and the negated system, and calls `feasibleFn`.
`optF` runs the threshold search of `AlgorithmThresholdSearch` with the test
`atLeast P offset`, and computes `AlgorithmThresholdLP.optimize P offset bits`
(`optF_apply`).
-/

@[expose] public section

namespace MWIS.FunLP

open MWIS.Fun AlgorithmNetworkEncoding

/-! ## Magnitude -/

/-- Absolute value. Argument `((), x)`. -/
def absFn : Fn (.prod .unit .int) .int :=
  .ite (.cmp .lt (.snd v0) (.int 0)) (.arith .sub (.int 0) (.snd v0)) (.snd v0)

@[simp] theorem absFn_apply (p : (Ty.prod .unit .int).denote) : absFn.apply p = |p.2| := by
  rw [Fn.apply]
  simp only [absFn, Expr.denote, Var.get, CmpOp.eval, IntOp.eval]
  by_cases h : p.2 < 0
  · simp [h, abs_of_neg h]
  · simp [h, abs_of_nonneg (le_of_not_gt h)]

/-- Sum of absolute values of a list. -/
def absSumFn : Fn (.list .int) .int := call sumFn (call (mapFn absFn) (.pair .unit v0))

@[simp] theorem absSumFn_apply (l : (Ty.list .int).denote) :
    absSumFn.apply l = (l.map (fun x => |x|)).sum := by
  rw [Fn.apply]; simp [absSumFn, Expr.denote, Var.get]

/-- Row sum of absolute values. Argument `((), row)`. -/
def rowAbsFn : Fn (.prod .unit (.list .int)) .int := call absSumFn (.snd v0)

@[simp] theorem rowAbsFn_apply (p : (Ty.prod .unit (.list .int)).denote) :
    rowAbsFn.apply p = (p.2.map (fun x => |x|)).sum := by
  rw [Fn.apply]; simp [rowAbsFn, Expr.denote, Var.get]

/-- The encoded dense program `(rows, (rhs, objective))`. -/
abbrev DPTy : Ty := .prod (.list (.list .int)) (.prod (.list .int) (.list .int))

/-- `AlgorithmThresholdLP.magnitude` on the encoding. -/
def magFn : Fn DPTy .int :=
  .arith .add (.arith .add (.arith .add (.int 1)
    (call sumFn (call (mapFn rowAbsFn) (.pair .unit (.fst v0)))))
    (call absSumFn (.fst (.snd v0)))) (call absSumFn (.snd (.snd v0)))

theorem sum_abs_ofFn {k : ℕ} (v : Fin k → ℤ) :
    ((List.ofFn v).map (fun x => |x|)).sum = ((∑ i, (v i).natAbs : ℕ) : ℤ) := by
  rw [List.map_ofFn, List.sum_ofFn]
  push_cast
  rfl

open AlgorithmThresholdLP in
theorem magFn_apply {M N : ℕ} (P : DenseProgram M N) :
    magFn.apply (FunNetwork.DenseProgram.toFun P) = (magnitude P : ℤ) := by
  rw [Fn.apply]
  simp only [magFn, Expr.denote, Var.get, denote_call, sumFn_apply, mapFn_apply, rowAbsFn_apply,
    absSumFn_apply, IntOp.eval, FunNetwork.DenseProgram.toFun]
  rw [sum_abs_ofFn, sum_abs_ofFn, List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp, sum_abs_ofFn, magnitude]
  push_cast
  ring

/-! ## Threshold feasibility -/

/-- The length of a list. -/
def lenFn (a : Ty) : Fn (.list a) .int := .foldl v0 (.int 0) (.arith .add v1 (.int 1))

theorem foldl_len {α : Type*} (l : List α) (s : ℤ) :
    l.foldl (fun acc _ => acc + 1) s = s + l.length := by
  induction l generalizing s with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih]; simp; ring

@[simp] theorem lenFn_apply (a : Ty) (l : (Ty.list a).denote) : (lenFn a).apply l = l.length := by
  rw [Fn.apply]
  simp only [lenFn, Expr.denote, Var.get, IntOp.eval]
  rw [foldl_len]; simp

/-- Negate a row. Argument `((), row)`. -/
def negRowFn : Fn (.prod .unit (.list .int)) (.list .int) := call negFn (.snd v0)

@[simp] theorem negRowFn_apply (p : (Ty.prod .unit (.list .int)).denote) :
    negRowFn.apply p = p.2.map (fun x => -x) := by
  rw [Fn.apply]; simp [negRowFn, Expr.denote, Var.get]

/-- `AlgorithmThresholdLP.feasible` on the encoding. -/
def feasLPFn : Fn DPTy .bool :=
  .letE (call magFn v0)
    (call feasibleFn (.pair v0 (.pair (.size v0) (.pair (call (lenFn .int) (.snd (.snd v1)))
      (.pair (call (mapFn negRowFn) (.pair .unit (.fst v1))) (call negFn (.fst (.snd v1))))))))

open AlgorithmThresholdLP in
theorem feasLPFn_apply {M N : ℕ} (P : DenseProgram M N) :
    feasLPFn.apply (FunNetwork.DenseProgram.toFun P) = AlgorithmThresholdLP.feasible P := by
  rw [Fn.apply]
  simp only [feasLPFn, Expr.denote, Var.get, denote_call, lenFn_apply, mapFn_apply,
    negRowFn_apply, negFn_apply]
  rw [magFn_apply]
  have h1 : (bits ((magnitude P : ℕ) : ℤ) : ℤ) = (((magnitude P).size : ℕ) : ℤ) := by
    rw [bits_natCast]
  have h2 : ((FunNetwork.DenseProgram.toFun P).2.2.length : ℤ) = (N : ℤ) := by
    simp [FunNetwork.DenseProgram.toFun]
  have h3 : (FunNetwork.DenseProgram.toFun P).1.map (fun y => y.map (fun x => -x)) =
      matE (fun i j => -P.coefficient i j) := by
    simp only [FunNetwork.DenseProgram.toFun, matE, List.map_ofFn]
    congr 1; funext i
    simp only [Function.comp, List.map_ofFn]; rfl
  have h4 : (FunNetwork.DenseProgram.toFun P).2.1.map (fun x => -x) = vecE (fun i => -P.rhs i) := by
    simp only [FunNetwork.DenseProgram.toFun, vecE, List.map_ofFn]; rfl
  rw [h1, h2, h3, h4, feasibleFn_apply_encode]
  rfl

/-- The encoding of the thresholded program. -/
theorem toFun_withThreshold {M N : ℕ} (P : DenseProgram M N) (t : ℤ) :
    FunNetwork.DenseProgram.toFun (P.withThreshold t) =
      ((FunNetwork.DenseProgram.toFun P).2.2 :: (FunNetwork.DenseProgram.toFun P).1,
        t :: (FunNetwork.DenseProgram.toFun P).2.1, (FunNetwork.DenseProgram.toFun P).2.2) := by
  simp [FunNetwork.DenseProgram.toFun, DenseProgram.withThreshold, List.ofFn_succ]

/-! ## The threshold search -/

/-- Argument `(program, (offset, bits))`. -/
abbrev OptTy : Ty := .prod DPTy (.prod .int .int)

/-- One search round on `(remaining, lower)`. Context `[state, argument]`. -/
def optStepE : Expr [.prod .int .int, OptTy] (.prod .int .int) :=
  .letE (.arith .add (.snd v0) (call pow2Fn (.arith .sub (.fst v0) (.int 1))))
    (.pair (.arith .sub (.fst v1) (.int 1))
      (.ite (call feasLPFn (.pair (.cons (.snd (.snd (.fst v2))) (.fst (.fst v2)))
            (.pair (.cons (.arith .sub (.fst (.snd v2)) (.arith .mul (.int 2) v0))
              (.fst (.snd (.fst v2)))) (.snd (.snd (.fst v2))))))
        v0 (.snd v1)))

/-- The optimizer: `bits` rounds of the threshold search from `(bits, 0)`. -/
def optF : Fn OptTy .int :=
  .snd (.iter (.snd (.snd v0)) (.pair (.snd (.snd v0)) (.int 0)) optStepE)

theorem iterate_search (test : ℕ → Bool) (F : ℤ × ℤ → ℤ × ℤ)
    (hF : ∀ s lower : ℕ, F (((s + 1 : ℕ) : ℤ), (lower : ℤ)) =
      ((s : ℤ), if test (lower + 2 ^ s) then ((lower + 2 ^ s : ℕ) : ℤ) else (lower : ℤ))) :
    ∀ r lower : ℕ, (F^[r] ((r : ℤ), (lower : ℤ))).2 =
      ((AlgorithmThresholdSearch.run test r lower).value : ℤ) := by
  intro r
  induction r with
  | zero => intro lower; rfl
  | succ s ih =>
    intro lower
    rw [Function.iterate_succ_apply, hF]
    have : (if test (lower + 2 ^ s) then ((lower + 2 ^ s : ℕ) : ℤ) else (lower : ℤ)) =
        ((if test (lower + 2 ^ s) then lower + 2 ^ s else lower : ℕ) : ℤ) := by
      split_ifs <;> rfl
    rw [this, ih]
    rfl

open AlgorithmThresholdLP in
theorem optF_apply {M N : ℕ} (P : DenseProgram M N) (offset : ℤ) (b : ℕ) :
    optF.apply (FunNetwork.DenseProgram.toFun P, (offset, (b : ℤ))) =
      (AlgorithmThresholdLP.optimize P offset b : ℤ) := by
  rw [Fn.apply]
  simp only [optF, Expr.denote, Var.get, Int.toNat_natCast]
  unfold AlgorithmThresholdLP.optimize AlgorithmThresholdSearch.solve
  refine iterate_search (atLeast P offset) _ (fun s lower => ?_) b 0
  simp only [optStepE, Expr.denote, Var.get, denote_call, pow2Fn_apply, IntOp.eval]
  have h1 : (((s + 1 : ℕ) : ℤ) - 1) = (s : ℤ) := by push_cast; ring
  have h2 : ((s : ℤ)).toNat = s := Int.toNat_natCast s
  rw [h1, h2]
  have h3 : ((lower : ℤ) + 2 ^ s) = ((lower + 2 ^ s : ℕ) : ℤ) := by push_cast; ring
  rw [h3]
  have ht := toFun_withThreshold P (offset - 2 * ((lower + 2 ^ s : ℕ) : ℤ))
  have hf := feasLPFn_apply (P.withThreshold (offset - 2 * ((lower + 2 ^ s : ℕ) : ℤ)))
  rw [ht] at hf
  rw [hf]
  rfl

end MWIS.FunLP

end
