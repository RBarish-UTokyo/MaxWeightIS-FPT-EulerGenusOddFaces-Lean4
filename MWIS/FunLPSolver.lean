module

public import MWIS.FunLPRunCost
public import MWIS.IntegerFeasibilityGeneral

/-!
# The integer feasibility solver as a `Fun` program

`feasibleFn` takes `(U, B, n, A, b)` with `A` a list of rows and computes the
padding by two zero columns, the perturbed integer system of
`IntegerFeasibilityEncoding`, the iteration budget, the grid exponent, the
initial ball and then runs the rounded ellipsoid loop. Its value is
`IntegerFeasibilityGeneral.feasible U B A b` (`feasibleFn_apply_encode`).
-/

@[expose] public section

namespace MWIS.FunLP

open MWIS.Fun

/-! ## List builders -/

/-- `replicate N v`. Argument `(N, v)`. -/
def repFn : Fn (.prod .int .int) (.list .int) := .iter (.fst v0) .nil (.cons (.snd v1) v0)

theorem iterate_cons_rep (v : ℤ) (N : ℕ) (l : List ℤ) :
    (fun acc : List ℤ => v :: acc)^[N] l = List.replicate N v ++ l := by
  induction N generalizing l with
  | zero => rfl
  | succ N ih => rw [Function.iterate_succ_apply', ih]; simp [List.replicate_succ]

@[simp] theorem repFn_apply (p : (Ty.prod .int .int).denote) :
    repFn.apply p = List.replicate p.1.toNat p.2 := by
  rw [Fn.apply]
  simp only [repFn, Expr.denote, Var.get]
  rw [iterate_cons_rep]; simp

/-- Entry of a scaled unit row. Argument `((i, v), (j, _))`. -/
def unitEntryFn : Fn (.prod (.prod .int .int) (.prod .int .int)) .int :=
  .ite (.cmp .eq (.fst (.snd v0)) (.fst (.fst v0))) (.snd (.fst v0)) (.int 0)

@[simp] theorem unitEntryFn_apply (p : (Ty.prod (.prod .int .int) (.prod .int .int)).denote) :
    unitEntryFn.apply p = if p.2.1 = p.1.1 then p.1.2 else 0 := by
  rw [Fn.apply]
  simp only [unitEntryFn, Expr.denote, Var.get, CmpOp.eval]
  by_cases h : p.2.1 = p.1.1 <;> simp [h]

/-- The row `v e_i` of the length of `zs`. Argument `((i, v), zs)`. -/
def unitRowFn : Fn (.prod (.prod .int .int) (.list .int)) (.list .int) := mapIdxFn unitEntryFn

/-- `v e_i` on lists. -/
def unitL (i v : ℤ) (zs : List ℤ) : List ℤ := zs.mapIdx (fun j _ => if (j : ℤ) = i then v else 0)

@[simp] theorem unitRowFn_apply (p : (Ty.prod (.prod .int .int) (.list .int)).denote) :
    unitRowFn.apply p = unitL p.1.1 p.1.2 p.2 := by
  simp [unitRowFn, unitL]

/-- Row `i` of `v I`. Argument `((v, zs), (i, _))`. -/
def blockEntryFn : Fn (.prod (.prod .int (.list .int)) (.prod .int .int)) (.list .int) :=
  call unitRowFn (.pair (.pair (.fst (.snd v0)) (.fst (.fst v0))) (.snd (.fst v0)))

/-- The matrix `v I` with as many rows as `zs` has entries. Argument `((v, zs), zs')`. -/
def blockFn : Fn (.prod (.prod .int (.list .int)) (.list .int)) (.list (.list .int)) :=
  mapIdxFn blockEntryFn

/-- `v I` on lists. -/
def blockL (v : ℤ) (zs : List ℤ) : List (List ℤ) := zs.mapIdx (fun i _ => unitL i v zs)

/-- The rows `v e_i` for the positions `i` of `zs'`. -/
def blockLw (v : ℤ) (zs zs' : List ℤ) : List (List ℤ) := zs'.mapIdx (fun i _ => unitL i v zs)

theorem blockLw_self (v : ℤ) (zs : List ℤ) : blockLw v zs zs = blockL v zs := rfl

@[simp] theorem blockFn_apply (p : (Ty.prod (.prod .int (.list .int)) (.list .int)).denote) :
    blockFn.apply p = blockLw p.1.1 p.1.2 p.2 := by
  simp only [blockFn, mapIdxFn_apply]
  congr 1; funext i y
  rw [blockEntryFn, Fn.apply]
  simp [Expr.denote, Var.get]

/-- Scale one entry. Argument `(d, x)`. -/
def scaleEntryFn : Fn (.prod .int .int) .int := .arith .mul (.fst v0) (.snd v0)

@[simp] theorem scaleEntryFn_apply (p : (Ty.prod .int .int).denote) :
    scaleEntryFn.apply p = p.1 * p.2 := rfl

/-- Pad a row by two zeros and scale it. Argument `(d, row)`. -/
def padRowFn : Fn (.prod .int (.list .int)) (.list .int) :=
  call (mapFn scaleEntryFn)
    (.pair (.fst v0) (call (appendFn .int) (.pair (.snd v0) (.cons (.int 0) (.cons (.int 0) .nil)))))

@[simp] theorem padRowFn_apply (p : (Ty.prod .int (.list .int)).denote) :
    padRowFn.apply p = (p.2 ++ [0, 0]).map (fun x => p.1 * x) := by
  rw [Fn.apply]; simp [padRowFn, Expr.denote, Var.get]

/-- One perturbed right-hand side entry. Argument `(d, x)`. -/
def bEntryFn : Fn (.prod .int .int) .int :=
  .arith .add (.arith .mul (.arith .sub (.int 0) (.fst v0)) (.snd v0)) (.int 1)

@[simp] theorem bEntryFn_apply (p : (Ty.prod .int .int).denote) :
    bEntryFn.apply p = (0 - p.1) * p.2 + 1 := rfl

/-! ## Agreement with the explicit encoding -/

theorem unitL_replicate (N : ℕ) (i : ℕ) (v : ℤ) :
    unitL i v (List.replicate N 0) = List.ofFn (fun j : Fin N => if (j : ℕ) = i then v else 0) := by
  apply List.ext_getElem
  · simp [unitL]
  · intro j h1 h2
    simp only [unitL, List.getElem_mapIdx, List.getElem_ofFn, Nat.cast_inj]

theorem blockL_replicate (N : ℕ) (v : ℤ) :
    blockL v (List.replicate N 0) =
      List.ofFn (fun i : Fin N => List.ofFn (fun j : Fin N => if (j : ℕ) = i then v else 0)) := by
  apply List.ext_getElem
  · simp [blockL]
  · intro i h1 h2
    simp only [blockL, List.getElem_mapIdx, List.getElem_ofFn]
    exact unitL_replicate N i v

theorem ofFn_pad {n : ℕ} (v : Fin n → ℤ) :
    List.ofFn v ++ [0, 0] = List.ofFn (Fin.addCases v (fun _ : Fin 2 => (0 : ℤ))) := by
  rw [List.ofFn_add]
  congr 1
  · congr 1; funext i
    exact (Fin.addCases_left (motive := fun _ => ℤ) i).symm
  · simp [List.ofFn_succ]

open IntegerFeasibilityEncoding IntegerFeasibilityGeneral in
/-- The encoded rows: scaled padded rows, then `-D I`, then `D I`. -/
theorem rows_encode {m n : ℕ} (U : ℕ) (A : Fin m → Fin n → ℤ) :
    ((matE A).map (fun row => (row ++ [0, 0]).map (fun x => (0 - (denominator (n + 2) U : ℤ)) * x)) ++
        blockL (0 - (denominator (n + 2) U : ℤ)) (List.replicate (n + 2) 0)) ++
        blockL (denominator (n + 2) U : ℤ) (List.replicate (n + 2) 0) =
      matE (matrix U (paddedMatrix A)) := by
  rw [blockL_replicate, blockL_replicate]
  conv_rhs => unfold matE
  rw [List.ofFn_add (f := fun i : Fin (m + (n + 2) + (n + 2)) => List.ofFn (matrix U (paddedMatrix A) i)),
    List.ofFn_add (f := fun i : Fin (m + (n + 2)) =>
      List.ofFn (matrix U (paddedMatrix A) (Fin.castLE (by omega) i)))]
  congr 1
  congr 1
  · rw [matE, List.map_ofFn]
    congr 1; funext i
    simp only [Function.comp, ofFn_pad, List.map_ofFn]
    congr 1; funext j
    simp [matrix, augmentedMatrix, paddedMatrix]
  · congr 1; funext i
    congr 1; funext j
    simp only [matrix, augmentedMatrix, Fin.val_castLE, Fin.val_natAdd]
    split_ifs <;> omega
  · congr 1; funext i
    congr 1; funext j
    simp only [matrix, augmentedMatrix, Fin.val_natAdd]
    split_ifs <;> omega

open IntegerFeasibilityEncoding in
/-- The encoded right-hand side. -/
theorem bound_encode {m : ℕ} (N U : ℕ) (b : Fin m → ℤ) :
    (vecE b).map (fun x => (0 - (denominator N U : ℤ)) * x + 1) ++
        List.replicate (N + N) ((denominator N U : ℤ) * (box N U : ℤ)) = vecE (bound N U b) := by
  apply List.ext_getElem
  · simp [vecE]; omega
  · intro i h1 h2
    simp only [vecE, List.getElem_ofFn, bound]
    rw [List.getElem_append]
    split_ifs with h h'
    · simp only [List.getElem_map, List.getElem_ofFn]; ring
    · simp at h; omega
    · simp at h; omega
    · simp

open AlgorithmEllipsoid in
theorem initial_encode (N k B : ℕ) :
    encSt (initial N k B) = (List.replicate N 0,
      blockL ((2 : ℤ) ^ (k + 2 * B)) (List.replicate N 0)) := by
  rw [blockL_replicate]
  simp only [encSt, vecE, matE, initial, List.ofFn_const]
  congr 1
  congr 1; funext i
  congr 1; funext j
  by_cases h : (j : ℕ) = i
  · have : i = j := Fin.ext h.symm
    simp [this]
  · have : i ≠ j := fun e => h (congrArg Fin.val e).symm
    simp [this, h]

/-! ## The solver -/

/-- Input `(U, (B, (n, (A, b))))`. -/
abbrev InTy : Ty := .prod .int (.prod .int (.prod .int (.prod (.list (.list .int)) (.list .int))))

/-- Scalars `(N, (T, (k, (B0, (D, box)))))`. -/
abbrev SclTy : Ty := .prod .int (.prod .int (.prod .int (.prod .int (.prod .int .int))))

abbrev sN {Γ : List Ty} (s : Expr Γ SclTy) : Expr Γ .int := .fst s
abbrev sT {Γ : List Ty} (s : Expr Γ SclTy) : Expr Γ .int := .fst (.snd s)
abbrev sK {Γ : List Ty} (s : Expr Γ SclTy) : Expr Γ .int := .fst (.snd (.snd s))
abbrev sB0 {Γ : List Ty} (s : Expr Γ SclTy) : Expr Γ .int := .fst (.snd (.snd (.snd s)))
abbrev sD {Γ : List Ty} (s : Expr Γ SclTy) : Expr Γ .int := .fst (.snd (.snd (.snd (.snd s))))
abbrev sBox {Γ : List Ty} (s : Expr Γ SclTy) : Expr Γ .int := .snd (.snd (.snd (.snd (.snd s))))

/-- Dimensions `(N, (T, (k, B0)))`. -/
abbrev DimTy : Ty := .prod .int (.prod .int (.prod .int .int))

/-- The padded dimension `N = n + 2`, the budget `T = feasibilityIterations N B`, the grid
exponent `k = precision N T` and the outer radius exponent `B0 = outerExponent N B`. -/
def dimsFn : Fn InTy DimTy :=
  .letE (.arith .add (.fst (.snd (.snd v0))) (.int 2))
  (.letE (.arith .add (.arith .mul (.arith .mul (.arith .mul (.int 4) (.arith .add v0 (.int 1))) v0)
        (.arith .mul (.arith .mul (.arith .mul (.int 8) (.arith .add v0 (.int 2))) (.arith .add v0 (.int 2)))
          (.arith .add (.fst (.snd v1)) (.int 1)))) (.int 1))
  (.letE (.arith .add (.arith .add (.arith .mul (.int 2) v0) (.arith .mul (.int 4) v1)) (.int 32))
  (.letE (.arith .add v2 (.arith .add (.arith .add (.arith .mul v2 v2) (.arith .mul (.fst (.snd v3)) v2))
      (.int 1)))
  (.pair v3 (.pair v2 (.pair v1 v0))))))

/-- All scalars, with the perturbation denominator `D` and the box radius. -/
def scalFn : Fn InTy SclTy :=
  .letE (call dimsFn v0)
  (.letE (call factFn (.arith .add (.fst v0) (.int 1)))
  (.letE (call powFn (.pair (.fst v2) (.arith .add (.fst v1) (.int 1))))
  (.letE (call factFn (.fst v2))
  (.letE (call powFn (.pair (.fst v4) (.fst v3)))
  (.pair (.fst v4) (.pair (.fst (.snd v4)) (.pair (.fst (.snd (.snd v4))) (.pair (.snd (.snd (.snd v4)))
     (.pair (.arith .mul (.arith .mul (.arith .mul (.int 2) (.arith .add (.fst v4) (.int 1))) v3) v2)
            (.arith .add (.arith .mul v1 v0) (.int 1)))))))))))

open AlgorithmPrecision IntegerFeasibility in
theorem dimsFn_apply_nat (U B n : ℕ) (A : List (List ℤ)) (b : List ℤ) :
    dimsFn.apply ((U : ℤ), (B : ℤ), (n : ℤ), A, b) =
      (((n + 2 : ℕ) : ℤ), (feasibilityIterations (n + 2) B : ℤ),
        (precision (n + 2) (feasibilityIterations (n + 2) B) : ℤ), (outerExponent (n + 2) B : ℤ)) := by
  rw [Fn.apply]
  simp only [dimsFn, Expr.denote, Var.get, IntOp.eval]
  simp only [feasibilityIterations, radiusExponent, precision, outerExponent]
  push_cast
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp only <;> ring

open IntegerFeasibilityEncoding AlgorithmPrecision IntegerFeasibility in
theorem scalFn_apply_nat (U B n : ℕ) (A : List (List ℤ)) (b : List ℤ) :
    scalFn.apply ((U : ℤ), (B : ℤ), (n : ℤ), A, b) =
      (((n + 2 : ℕ) : ℤ), (feasibilityIterations (n + 2) B : ℤ),
        (precision (n + 2) (feasibilityIterations (n + 2) B) : ℤ),
        (outerExponent (n + 2) B : ℤ), (denominator (n + 2) U : ℤ), (box (n + 2) U : ℤ)) := by
  rw [Fn.apply]
  simp only [scalFn, Expr.denote, Var.get, IntOp.eval, denote_call, factFn_apply, powFn_apply]
  rw [dimsFn_apply_nat]
  have h1 : (((n + 2 : ℕ) : ℤ) + 1).toNat = n + 2 + 1 := by omega
  have h2 : (((n + 2 : ℕ) : ℤ)).toNat = n + 2 := by omega
  simp only [h1, h2]
  simp only [denominator, box]
  push_cast
  refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ ?_)))) <;> simp only

/-- The rows of the encoded system. Context `[zs, scalars, input]`. -/
def rowsE : Expr [.list .int, SclTy, InTy] (.list (.list .int)) :=
  call (appendFn (.list .int)) (.pair
    (call (appendFn (.list .int)) (.pair
      (call (mapFn padRowFn) (.pair (.arith .sub (.int 0) (sD v1)) (.fst (.snd (.snd (.snd v2))))))
      (call blockFn (.pair (.pair (.arith .sub (.int 0) (sD v1)) v0) v0))))
    (call blockFn (.pair (.pair (sD v1) v0) v0)))

/-- The right-hand side of the encoded system. Context `[rows, zs, scalars, input]`. -/
def boundE : Expr [.list (.list .int), .list .int, SclTy, InTy] (.list .int) :=
  call (appendFn .int) (.pair (call (mapFn bEntryFn) (.pair (sD v2) (.snd (.snd (.snd (.snd v3))))))
    (call repFn (.pair (.arith .add (sN v2) (sN v2)) (.arith .mul (sD v2) (sBox v2)))))

/-- The initial shape `2^{k + 2 B0} I`. Context `[bv, rows, zs, scalars, input]`. -/
def shape0E : Expr [.list .int, .list (.list .int), .list .int, SclTy, InTy] (.list (.list .int)) :=
  call blockFn (.pair (.pair (call pow2Fn (.arith .add (sK v3) (.arith .mul (.int 2) (sB0 v3)))) v2) v2)

/-- The loop and the final test. Context `[S0, bv, rows, zs, scalars, input]`. -/
def finalE : Expr [.list (.list .int), .list .int, .list (.list .int), .list .int, SclTy, InTy] .bool :=
  .cmp .eq (.fst (call loopFn (.pair (.pair (sN v4) (.pair (call pow2Fn (sK v4)) (.pair v2 v1)))
      (.pair (.int 0) (.pair (sT v4) (.pair v3 v0)))))) (.int 1)

/-- Integer linear feasibility of `A x ≥ b` for list inputs `(U, (B, (n, (A, b))))`. -/
def feasibleFn : Fn InTy .bool :=
  .letE (call scalFn v0) (.letE (call repFn (.pair (sN v0) (.int 0)))
    (.letE rowsE (.letE boundE (.letE shape0E finalE))))

open IntegerFeasibilityEncoding IntegerFeasibilityGeneral AlgorithmPrecision IntegerFeasibility
  AlgorithmEllipsoid in
/-- The `Fun` solver computes `IntegerFeasibilityGeneral.feasible` on the list encodings. -/
theorem feasibleFn_apply_encode {m n : ℕ} (U B : ℕ) (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) :
    feasibleFn.apply ((U : ℤ), (B : ℤ), (n : ℤ), matE A, vecE b) =
      IntegerFeasibilityGeneral.feasible U B A b := by
  rw [Fn.apply]
  simp only [feasibleFn, rowsE, boundE, shape0E, finalE, Expr.denote, Var.get, denote_call,
    repFn_apply, appendFn_apply, mapFn_apply, padRowFn_apply, blockFn_apply,
    bEntryFn_apply, pow2Fn_apply, loopFn_apply, IntOp.eval, CmpOp.eval, blockLw_self]
  rw [scalFn_apply_nat]
  simp only [Int.toNat_natCast]
  set T := feasibilityIterations (n + 2) B
  set k := precision (n + 2) T
  set B0 := outerExponent (n + 2) B
  have hz : ((((n + 2 : ℕ) : ℤ)) + ((n + 2 : ℕ) : ℤ)).toNat = (n + 2) + (n + 2) := by omega
  have hk : ((k : ℤ) + 2 * (B0 : ℤ)).toNat = k + 2 * B0 := by omega
  have hT : ((T : ℤ) + 1).toNat = T + 1 := by omega
  rw [hz, hk, hT]
  simp only [rows_encode, bound_encode]
  rw [show (List.replicate (n + 2) (0 : ℤ), blockL (2 ^ (k + 2 * B0)) (List.replicate (n + 2) 0)) =
    encSt (initial (n + 2) k B0) from (initial_encode _ _ _).symm]
  rw [loop_status (matrix U (paddedMatrix A)) (bound (n + 2) U b) k (by omega) T]
  unfold IntegerFeasibilityGeneral.feasible IntegerFeasibilitySolver.feasible
    IntegerFeasibilitySolver.solve
  simp only
  cases run (matrix U (paddedMatrix A)) (bound (n + 2) U b) k (inflation (n + 2)) T
    (initial (n + 2) k B0) <;> rfl

end MWIS.FunLP

end
