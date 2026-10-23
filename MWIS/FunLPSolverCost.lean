module

public import MWIS.FunLPSolver

/-!
# Cost of the `Fun` integer feasibility solver

`solverWidth m n U B β` is an explicit polynomial in `m`, `n`, `B`, `size U` and
`β` (a bound on the bit lengths of all input entries). It bounds every row count,
dimension, grid exponent and stored integer length of the run, and the whole
solver costs at most `2^64 (solverWidth m n U B β + 1)^5` (`feasibleFn_cost`).
-/

@[expose] public section

namespace MWIS.FunLP

open MWIS.Fun

/-! ## The list builders -/

theorem bits_natCast_le (N : ℕ) : bits (N : ℤ) ≤ N := by
  have := bits_le_self_natAbs (N : ℤ); simpa using this

theorem repFn_cost (N v : ℤ) (W : ℕ) (hN : N.toNat ≤ W) (hb : bits N ≤ W) :
    repFn.costAt (N, v) ≤ 20 * (W + 1) ^ 2 := by
  unfold Fn.costAt repFn
  have h := cost_iter_le (Γ := [.prod .int .int]) (.fst v0) .nil (.cons (.snd v1) v0)
    ((N, v), ()) (fun _ => True) 6 trivial (fun _ _ => ⟨trivial, by
      simp [Expr.cost, Var.index]⟩)
  refine le_trans h ?_
  simp only [Expr.cost, Var.index, Expr.denote, Var.get]
  have : N.toNat * (6 + bits N + 1) ≤ W * (W + 7) := Nat.mul_le_mul hN (by omega)
  nlinarith

theorem unitEntryFn_cost (i v j x : ℤ) :
    unitEntryFn.costAt ((i, v), (j, x)) ≤ bits j + bits i + 12 := by
  unfold Fn.costAt unitEntryFn
  simp only [Expr.cost, Var.index, Expr.denote, Var.get, CmpOp.charge]
  rcases Bool.eq_false_or_eq_true (CmpOp.eq.eval j i) with h | h <;>
    simp only [h, ite_true, Bool.false_eq_true, ite_false] <;> omega

theorem unitRowFn_cost (i v : ℤ) (zs : List ℤ) (W : ℕ) (hi : bits i ≤ W) (hl : zs.length ≤ W) :
    unitRowFn.costAt ((i, v), zs) ≤ 60 * (W + 1) ^ 2 := by
  unfold unitRowFn
  have h := mapIdxFn_cost unitEntryFn (i, v) zs (2 * W + 12) (by
    intro j hj x _
    have := unitEntryFn_cost i v j x
    have hj' : bits (j : ℤ) ≤ W := le_trans (bits_natCast_le j) (by omega)
    omega)
  refine le_trans h ?_
  have : (zs.length + 1) * (2 * W + 12 + 3 * zs.length + 40) ≤ (W + 1) * (60 * (W + 1)) :=
    Nat.mul_le_mul (by omega) (by omega)
  nlinarith

theorem blockFn_cost (v : ℤ) (zs zs' : List ℤ) (W : ℕ) (hl : zs.length ≤ W) (hl' : zs'.length ≤ W) :
    blockFn.costAt ((v, zs), zs') ≤ 120 * (W + 1) ^ 3 := by
  unfold blockFn
  have h := mapIdxFn_cost blockEntryFn (v, zs) zs' (60 * (W + 1) ^ 2 + 20) (by
    intro j hj x _
    have hj' : bits (j : ℤ) ≤ W := le_trans (bits_natCast_le j) (by omega)
    have hu := unitRowFn_cost (j : ℤ) v zs W hj' hl
    unfold Fn.costAt blockEntryFn
    rw [cost_call]
    simp only [Expr.cost, Var.index, Expr.denote, Var.get]
    omega)
  refine le_trans h ?_
  have p1 : W + 1 ≤ (W + 1) ^ 2 := by nlinarith
  have : (zs'.length + 1) * (60 * (W + 1) ^ 2 + 20 + 3 * zs'.length + 40) ≤
      (W + 1) * (120 * (W + 1) ^ 2) := Nat.mul_le_mul (by omega) (by nlinarith)
  nlinarith

theorem padRowFn_cost (d : ℤ) (row : List ℤ) (W : ℕ) (hd : bits d ≤ W)
    (hr : ∀ x ∈ row, bits x ≤ W) (hl : row.length + 2 ≤ W) :
    padRowFn.costAt (d, row) ≤ 70 * (W + 1) ^ 3 := by
  unfold Fn.costAt padRowFn
  rw [cost_call]
  have ha := appendFn_cost .int row [0, 0]
  have hm := mapFn_cost scaleEntryFn d (row ++ [0, 0]) ((W + 1) * (W + 1) + 7) (by
    intro x hx
    have hx' : bits x ≤ W := by
      rcases List.mem_append.mp hx with h | h
      · exact hr x h
      · simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at h; subst h; simp
    unfold Fn.costAt scaleEntryFn
    simp only [Expr.cost, Var.index, Expr.denote, Var.get, IntOp.charge]
    have : (bits d + 1) * (bits x + 1) ≤ (W + 1) * (W + 1) := Nat.mul_le_mul (by omega) (by omega)
    omega)
  simp only [Expr.cost, cost_call, Var.index, Expr.denote, Var.get, denote_call, appendFn_apply]
  simp only [List.length_append, List.length_cons, List.length_nil] at hm
  have : (row.length + 2 + 1) * ((W + 1) * (W + 1) + 7 + 17) ≤ (W + 1) * (25 * (W + 1) ^ 2) :=
    Nat.mul_le_mul (by omega) (by nlinarith)
  have p1 : W + 1 ≤ (W + 1) ^ 3 := by nlinarith
  nlinarith

theorem bEntryFn_cost (d x : ℤ) (W : ℕ) (hd : bits d ≤ W) (hx : bits x ≤ W) :
    bEntryFn.costAt (d, x) ≤ 22 * (W + 1) ^ 2 := by
  have h := (Fn.loopFree_bound bEntryFn (by decide) (d, x) W ⟨hd, hx⟩).2
  have : bEntryFn.kbc = 22 := by decide
  rw [this] at h
  exact h

/-! ## The scalars -/

theorem dimsFn_kbc : dimsFn.kbc = 5416758636 := by decide

theorem dimsFn_loopFree : dimsFn.loopFree = true := by decide

open IntegerFeasibilityEncoding AlgorithmPrecision IntegerFeasibility in
theorem scalFn_cost (U B n : ℕ) (A : List (List ℤ)) (b : List ℤ) (W : ℕ)
    (hU : bits (U : ℤ) ≤ W) (hB : bits (B : ℤ) ≤ W) (hn : bits (n : ℤ) ≤ W)
    (hA : ∀ row ∈ A, ∀ x ∈ row, bits x ≤ W) (hb : ∀ x ∈ b, bits x ≤ W)
    (hX : 2 * (n + 3) ^ 2 + (n + 3) * bits (U : ℤ) + n + 10 ≤ W) :
    scalFn.costAt ((U : ℤ), (B : ℤ), (n : ℤ), A, b) ≤ 2 ^ 34 * (W + 1) ^ 5 := by
  have hd := (Fn.loopFree_bound dimsFn dimsFn_loopFree ((U : ℤ), (B : ℤ), (n : ℤ), A, b) W
    ⟨hU, hB, hn, hA, hb⟩).2
  rw [dimsFn_kbc] at hd
  unfold Fn.costAt scalFn
  simp only [Expr.cost, cost_call, Var.index, Expr.denote, Var.get, denote_call, IntOp.charge,
    IntOp.eval, factFn_apply, powFn_apply]
  rw [dimsFn_apply_nat]
  simp only [Nat.reduceAdd, Nat.zero_add]
  have h1 : (((n + 2 : ℕ) : ℤ) + 1).toNat = n + 3 := by omega
  have h2 : (((n + 2 : ℕ) : ℤ)).toNat = n + 2 := by omega
  have hf1 := factFn_cost (((n + 2 : ℕ) : ℤ) + 1)
  have hf0 := factFn_cost (((n + 2 : ℕ) : ℤ))
  have hp1 := powFn_cost (U : ℤ) (((n + 2 : ℕ) : ℤ) + 1)
  have hp0 := powFn_cost (U : ℤ) (((n + 2 : ℕ) : ℤ))
  rw [h1] at hf1 hp1 ⊢
  rw [h2] at hf0 hp0 ⊢
  have hb1 : bits (1 : ℤ) = 1 := by decide
  have hb2 : bits (2 : ℤ) = 2 := by decide
  have hN : bits ((n + 2 : ℕ) : ℤ) ≤ n + 2 := bits_natCast_le _
  have hN1 : bits (((n + 2 : ℕ) : ℤ) + 1) ≤ n + 3 := bits_le_natAbs_bound _ _ (by omega)
  have hf1b := bits_factorial_le (n + 3)
  have hf0b := bits_factorial_le (n + 2)
  have hp1b := bits_pow_le (U : ℤ) (n + 3)
  have hp0b := bits_pow_le (U : ℤ) (n + 2)
  have h2N : bits (2 * (((n + 2 : ℕ) : ℤ) + 1)) ≤ n + 5 := by
    have := bits_mul_le 2 (((n + 2 : ℕ) : ℤ) + 1); omega
  have h2Nf : bits (2 * (((n + 2 : ℕ) : ℤ) + 1) * (((n + 3).factorial : ℕ) : ℤ)) ≤
      n + 5 + ((n + 3) * (n + 3) + 1) := by
    have := bits_mul_le (2 * (((n + 2 : ℕ) : ℤ) + 1)) (((n + 3).factorial : ℕ) : ℤ); omega
  have hfp0 : bits ((((n + 2).factorial : ℕ) : ℤ) * (U : ℤ) ^ (n + 2)) ≤
      (n + 2) * (n + 2) + 1 + ((n + 2) * bits (U : ℤ) + 1) := by
    have := bits_mul_le (((n + 2).factorial : ℕ) : ℤ) ((U : ℤ) ^ (n + 2)); omega
  have hsq1 : (n + 3) * (n + 3) ≤ (n + 3) ^ 2 := le_of_eq (by ring)
  have hsq0 : (n + 2) * (n + 2) ≤ (n + 3) ^ 2 := by
    rw [show (n + 3) ^ 2 = (n + 3) * (n + 3) by ring]; exact Nat.mul_le_mul (by omega) (by omega)
  have hUb : (n + 2) * bits (U : ℤ) ≤ (n + 3) * bits (U : ℤ) := Nat.mul_le_mul_right _ (by omega)
  have P1 : (bits (2 : ℤ) + 1) * (bits (((n + 2 : ℕ) : ℤ) + 1) + 1) ≤ (W + 1) * (W + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have P2 : (bits (2 * (((n + 2 : ℕ) : ℤ) + 1)) + 1) * (bits (((n + 3).factorial : ℕ) : ℤ) + 1) ≤
      (W + 1) * (W + 1) := Nat.mul_le_mul (by omega) (by omega)
  have P3 : (bits (2 * (((n + 2 : ℕ) : ℤ) + 1) * (((n + 3).factorial : ℕ) : ℤ)) + 1) *
      (bits ((U : ℤ) ^ (n + 3)) + 1) ≤ (W + 1) * (W + 1) := Nat.mul_le_mul (by omega) (by omega)
  have P4 : (bits (((n + 2).factorial : ℕ) : ℤ) + 1) * (bits ((U : ℤ) ^ (n + 2)) + 1) ≤
      (W + 1) * (W + 1) := Nat.mul_le_mul (by omega) (by omega)
  have Q1 : (n + 3 + 1) ^ 4 * (bits (((n + 2 : ℕ) : ℤ) + 1) + 30) ≤ (W + 1) ^ 4 * (30 * (W + 1)) :=
    Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) 4) (by omega)
  have Q0 : (n + 2 + 1) ^ 4 * (bits ((n + 2 : ℕ) : ℤ) + 30) ≤ (W + 1) ^ 4 * (30 * (W + 1)) :=
    Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) 4) (by omega)
  have R1 : (n + 3 + 1) * (((n + 3) * bits (U : ℤ) + 2) * (bits (U : ℤ) + 1) +
      bits (((n + 2 : ℕ) : ℤ) + 1) + 12) ≤ (W + 1) * ((W + 1) * (W + 1) + 13 * (W + 1)) :=
    Nat.mul_le_mul (by omega) (by
      have : ((n + 3) * bits (U : ℤ) + 2) * (bits (U : ℤ) + 1) ≤ (W + 1) * (W + 1) :=
        Nat.mul_le_mul (by omega) (by omega)
      omega)
  have R0 : (n + 2 + 1) * (((n + 2) * bits (U : ℤ) + 2) * (bits (U : ℤ) + 1) +
      bits ((n + 2 : ℕ) : ℤ) + 12) ≤ (W + 1) * ((W + 1) * (W + 1) + 13 * (W + 1)) :=
    Nat.mul_le_mul (by omega) (by
      have : ((n + 2) * bits (U : ℤ) + 2) * (bits (U : ℤ) + 1) ≤ (W + 1) * (W + 1) :=
        Nat.mul_le_mul (by omega) (by omega)
      omega)
  have e1 : (W + 1) ^ 4 * (30 * (W + 1)) = 30 * (W + 1) ^ 5 := by ring
  have e2 : (W + 1) * ((W + 1) * (W + 1) + 13 * (W + 1)) ≤ 14 * (W + 1) ^ 5 := by
    have : 1 ≤ W + 1 := by omega
    have a1 : (W + 1) ^ 3 ≤ (W + 1) ^ 5 := pow_mono_one this 3 5 (by norm_num)
    have a2 : (W + 1) ^ 2 ≤ (W + 1) ^ 5 := pow_mono_one this 2 5 (by norm_num)
    have eq : (W + 1) * ((W + 1) * (W + 1) + 13 * (W + 1)) = (W + 1) ^ 3 + 13 * (W + 1) ^ 2 := by ring
    rw [eq]; omega
  have e3 : (W + 1) * (W + 1) ≤ (W + 1) ^ 5 := by
    have := pow_mono_one (show 1 ≤ W + 1 by omega) 2 5 (by norm_num)
    have eq : (W + 1) * (W + 1) = (W + 1) ^ 2 := by ring
    rw [eq]; exact this
  have e4 : (W + 1) ^ 2 ≤ (W + 1) ^ 5 := pow_mono_one (show 1 ≤ W + 1 by omega) 2 5 (by norm_num)
  have e5 : 1 ≤ (W + 1) ^ 5 := Nat.one_le_pow _ _ (by omega)
  have e6 : W + 1 ≤ (W + 1) ^ 5 := by
    simpa using pow_mono_one (show 1 ≤ W + 1 by omega) 1 5 (by norm_num)
  rw [hb1, hb2]
  rw [hb2] at P1
  have hfpW : bits ((((n + 2).factorial : ℕ) : ℤ) * (U : ℤ) ^ (n + 2)) ≤ W := by omega
  have hNW : bits ((n + 2 : ℕ) : ℤ) ≤ W := by omega
  linarith only [hd, hf1, hf0, hp1, hp0, Q1, Q0, R1, R0, e1, e2, e3, e4, e5, e6, P1, P2, P3, P4,
    hfpW, hNW]

/-! ## The whole solver -/

open IntegerFeasibilityEncoding AlgorithmPrecision IntegerFeasibility

/-- An explicit polynomial in `m`, `n`, `B`, `size U` and the input entry length `β`
bounding all lengths and stored integers of the solver. -/
def solverWidth (m n U B β : ℕ) : ℕ :=
  (m + 2 * (n + 2) + precision (n + 2) (feasibilityIterations (n + 2) B) +
      2 * outerExponent (n + 2) B + 1) +
    ((n + 2) * (precision (n + 2) (feasibilityIterations (n + 2) B) +
        2 * feasibilityIterations (n + 2) B + outerExponent (n + 2) B + 3) +
      (n + 2) ^ 2 * (precision (n + 2) (feasibilityIterations (n + 2) B) +
        2 * feasibilityIterations (n + 2) B + 2 * outerExponent (n + 2) B + 2)) +
    4 * (n + 4) ^ 2 * (U.size + 1) + B + β + 10

theorem bits_denominator_le (N U : ℕ) :
    bits (denominator N U : ℤ) ≤ (N + 3) + ((N + 1) * (N + 1) + 1) + ((N + 1) * U.size + 1) := by
  unfold denominator
  push_cast
  have h1 := bits_mul_le (2 * ((N : ℤ) + 1) * ((N + 1).factorial : ℤ)) ((U : ℤ) ^ (N + 1))
  have h2 := bits_mul_le (2 * ((N : ℤ) + 1)) ((N + 1).factorial : ℤ)
  have h3 := bits_mul_le 2 ((N : ℤ) + 1)
  have h4 := bits_factorial_le (N + 1)
  have h5 := bits_pow_le (U : ℤ) (N + 1)
  have h6 : bits ((N : ℤ) + 1) ≤ N + 1 := bits_le_natAbs_bound _ _ (by omega)
  have h7 : bits (2 : ℤ) = 2 := by decide
  rw [bits_natCast] at h5
  omega

theorem bits_box_le (N U : ℕ) : bits (box N U : ℤ) ≤ (N * N + 1) + (N * U.size + 1) + 1 := by
  unfold box
  push_cast
  have h1 := bits_add_le ((N.factorial : ℤ) * (U : ℤ) ^ N) 1
  have h2 := bits_mul_le (N.factorial : ℤ) ((U : ℤ) ^ N)
  have h4 := bits_factorial_le N
  have h5 := bits_pow_le (U : ℤ) N
  have h7 : bits (1 : ℤ) = 1 := by decide
  rw [bits_natCast] at h5
  omega

theorem bits_matrix_le {m n : ℕ} (U : ℕ) (A : Fin m → Fin n → ℤ) (β : ℕ)
    (hA : ∀ i j, bits (A i j) ≤ β) (i : Fin (m + (n + 2) + (n + 2))) (j : Fin (n + 2)) :
    bits (matrix U (IntegerFeasibilityGeneral.paddedMatrix A) i j) ≤
      bits (denominator (n + 2) U : ℤ) + β + 1 := by
  unfold matrix
  have h := bits_mul_le (-(denominator (n + 2) U : ℤ))
    (augmentedMatrix (IntegerFeasibilityGeneral.paddedMatrix A) i j)
  have ha : bits (augmentedMatrix (IntegerFeasibilityGeneral.paddedMatrix A) i j) ≤ β + 1 := by
    unfold augmentedMatrix
    split_ifs with h1 h2 h3 h4
    · unfold IntegerFeasibilityGeneral.paddedMatrix
      refine Fin.addCases (fun r => ?_) (fun r => ?_) j
      · rw [Fin.addCases_left]; have := hA ⟨i, h1⟩ r; omega
      · rw [Fin.addCases_right]; simp
    all_goals
      have h1' : bits (1 : ℤ) = 1 := by decide
      have h1'' : bits (-1 : ℤ) = 1 := by decide
      simp only [bits_zero, h1', h1'']
      omega
  rw [bits_neg] at h
  omega

theorem bits_bound_le {m : ℕ} (N U : ℕ) (b : Fin m → ℤ) (β : ℕ) (hb : ∀ i, bits (b i) ≤ β)
    (i : Fin (m + N + N)) :
    bits (bound N U b i) ≤ bits (denominator N U : ℤ) + bits (box N U : ℤ) + β + 2 := by
  unfold bound
  split_ifs with h
  · have h1 := bits_add_le (-(denominator N U : ℤ) * b ⟨i, h⟩) 1
    have h2 := bits_mul_le (-(denominator N U : ℤ)) (b ⟨i, h⟩)
    have h3 := hb ⟨i, h⟩
    have h4 : bits (1 : ℤ) = 1 := by decide
    have h5 : bits (-(denominator N U : ℤ)) = bits (denominator N U : ℤ) := bits_neg _
    omega
  · have := bits_mul_le (denominator N U : ℤ) (box N U : ℤ)
    omega

/-- The `Fun` feasibility solver runs in time `2^64 (W + 1)^5` for
`W = solverWidth m n U B β`, where `β` bounds the bit lengths of the input entries. -/
theorem feasibleFn_cost {m n : ℕ} (U B β : ℕ) (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ)
    (hA : ∀ i j, bits (A i j) ≤ β) (hb : ∀ i, bits (b i) ≤ β) :
    feasibleFn.costAt ((U : ℤ), (B : ℤ), (n : ℤ), matE A, vecE b) ≤
      2 ^ 64 * (solverWidth m n U B β + 1) ^ 5 := by
  unfold Fn.costAt feasibleFn
  simp only [rowsE, boundE, shape0E, finalE, Expr.cost, cost_call, Var.index, Expr.denote, Var.get,
    denote_call, repFn_apply, appendFn_apply, mapFn_apply, padRowFn_apply, blockFn_apply,
    bEntryFn_apply, pow2Fn_apply, loopFn_apply, IntOp.eval, IntOp.charge, CmpOp.charge,
    blockLw_self]
  rw [scalFn_apply_nat]
  simp only [Int.toNat_natCast, Nat.reduceAdd, Nat.zero_add]
  -- the abbreviations of the run
  have hz : ((((n + 2 : ℕ) : ℤ)) + ((n + 2 : ℕ) : ℤ)).toNat = n + 2 + (n + 2) := by omega
  have hk : ((precision (n + 2) (feasibilityIterations (n + 2) B) : ℕ) + 2 *
      ((outerExponent (n + 2) B : ℕ) : ℤ)).toNat =
      precision (n + 2) (feasibilityIterations (n + 2) B) + 2 * outerExponent (n + 2) B := by omega
  have hT : (((feasibilityIterations (n + 2) B : ℕ) : ℤ) + 1).toNat =
      feasibilityIterations (n + 2) B + 1 := by omega
  rw [hz, hk, hT]
  simp only [rows_encode, bound_encode]
  rw [show (List.replicate (n + 2) (0 : ℤ), blockL (2 ^ (precision (n + 2) (feasibilityIterations
      (n + 2) B) + 2 * outerExponent (n + 2) B)) (List.replicate (n + 2) 0)) =
    encSt (AlgorithmEllipsoid.initial (n + 2) (precision (n + 2) (feasibilityIterations (n + 2) B))
      (outerExponent (n + 2) B)) from (initial_encode _ _ _).symm]
  obtain ⟨t, -, code, fuel, hc0, hc3, -, -, -, he⟩ :=
    loop_reach (matrix U (IntegerFeasibilityGeneral.paddedMatrix A)) (bound (n + 2) U b)
      (precision (n + 2) (feasibilityIterations (n + 2) B)) (by omega)
      (feasibilityIterations (n + 2) B)
      (AlgorithmEllipsoid.initial (n + 2) (precision (n + 2) (feasibilityIterations (n + 2) B))
        (outerExponent (n + 2) B)) (feasibilityIterations (n + 2) B + 1)
  rw [he]
  -- the width
  have hWa : m + 2 * (n + 2) + precision (n + 2) (feasibilityIterations (n + 2) B) + 2 * outerExponent (n + 2) B + 1 ≤ solverWidth m n U B β := by unfold solverWidth; omega
  have hWb : (n + 2) * (precision (n + 2) (feasibilityIterations (n + 2) B) + 2 * feasibilityIterations (n + 2) B + outerExponent (n + 2) B + 3) + (n + 2) ^ 2 * (precision (n + 2) (feasibilityIterations (n + 2) B) + 2 * feasibilityIterations (n + 2) B +
      2 * outerExponent (n + 2) B + 2) ≤ solverWidth m n U B β := by unfold solverWidth; omega
  have hWc : 4 * (n + 4) ^ 2 * (U.size + 1) + β + 10 ≤ solverWidth m n U B β := by
    unfold solverWidth; omega
  have hWB : B + β + 10 ≤ solverWidth m n U B β := by unfold solverWidth; omega
  have hkT : 2 * feasibilityIterations (n + 2) B + 32 ≤ precision (n + 2) (feasibilityIterations (n + 2) B) := by unfold precision; omega
  -- bit lengths of the scalars
  have hD := bits_denominator_le (n + 2) U
  have hbx := bits_box_le (n + 2) U
  have hpoly : (n + 2 + 3) + ((n + 2 + 1) * (n + 2 + 1) + 1) + ((n + 2 + 1) * U.size + 1) +
      (((n + 2) * (n + 2) + 1) + ((n + 2) * U.size + 1) + 1) + 2 ≤ 4 * (n + 4) ^ 2 * (U.size + 1) := by
    have e : 4 * (n + 4) ^ 2 * (U.size + 1) = 4 * (n + 4) ^ 2 + 4 * (n + 4) ^ 2 * U.size := by ring
    have h1 : (n + 2 + 1) * U.size + (n + 2) * U.size ≤ 4 * (n + 4) ^ 2 * U.size := by
      have : (n + 2 + 1) * U.size + (n + 2) * U.size = (2 * n + 5) * U.size := by ring
      rw [this]; exact Nat.mul_le_mul_right _ (by nlinarith)
    have h2 : (n + 2 + 3) + ((n + 2 + 1) * (n + 2 + 1) + 1) + ((n + 2) * (n + 2) + 1) + 6 ≤
        4 * (n + 4) ^ 2 := by nlinarith
    omega
  have hDW : bits (denominator (n + 2) U : ℤ) + bits (box (n + 2) U : ℤ) + β + 2 ≤ solverWidth m n U B β := by linarith
  have hUs : bits (U : ℤ) = U.size := bits_natCast U
  have hX : 2 * (n + 3) ^ 2 + (n + 3) * bits (U : ℤ) + n + 10 ≤ solverWidth m n U B β := by
    rw [hUs]
    have : (n + 3) * U.size ≤ 4 * (n + 4) ^ 2 * U.size := Nat.mul_le_mul_right _ (by nlinarith)
    have : 2 * (n + 3) ^ 2 + n + 10 ≤ 4 * (n + 4) ^ 2 := by nlinarith
    have e : 4 * (n + 4) ^ 2 * (U.size + 1) = 4 * (n + 4) ^ 2 + 4 * (n + 4) ^ 2 * U.size := by ring
    omega
  -- powers of `W + 1`
  have w1 : 1 ≤ (solverWidth m n U B β) + 1 := by omega
  have q1 : ((solverWidth m n U B β) + 1) ≤ ((solverWidth m n U B β) + 1) ^ 5 := by simpa using pow_mono_one w1 1 5 (by norm_num)
  have q2 : ((solverWidth m n U B β) + 1) ^ 2 ≤ ((solverWidth m n U B β) + 1) ^ 5 := pow_mono_one w1 2 5 (by norm_num)
  have q3 : ((solverWidth m n U B β) + 1) ^ 3 ≤ ((solverWidth m n U B β) + 1) ^ 5 := pow_mono_one w1 3 5 (by norm_num)
  have q4 : ((solverWidth m n U B β) + 1) ^ 4 ≤ ((solverWidth m n U B β) + 1) ^ 5 := pow_mono_one w1 4 5 (by norm_num)
  have q0 : 1 ≤ ((solverWidth m n U B β) + 1) ^ 5 := Nat.one_le_pow _ _ (by omega)
  -- entry bounds
  have hUW : bits (U : ℤ) ≤ (solverWidth m n U B β) := by
    rw [hUs]
    have : U.size + 1 ≤ 4 * (n + 4) ^ 2 * (U.size + 1) := Nat.le_mul_of_pos_left _ (by positivity)
    omega
  have hAW : ∀ row ∈ matE A, ∀ x ∈ row, bits x ≤ (solverWidth m n U B β) := fun row hr x hx => by
    obtain ⟨i, rfl⟩ := mem_matE hr
    obtain ⟨j, rfl⟩ := mem_vecE hx
    have := hA i j; omega
  have hbW : ∀ x ∈ vecE b, bits x ≤ (solverWidth m n U B β) := fun x hx => by
    obtain ⟨i, rfl⟩ := mem_vecE hx
    have := hb i; omega
  have hb0 : bits (0 : Ty.int.denote) = 0 := bits_zero
  have hb1 : bits (1 : Ty.int.denote) = 1 := by decide
  have hb2 : bits (2 : Ty.int.denote) = 2 := by decide
  have hDn : bits (0 - (denominator (n + 2) U : ℤ)) ≤ (solverWidth m n U B β) := by rw [zero_sub, bits_neg]; omega
  have hDp : bits (denominator (n + 2) U : ℤ) ≤ (solverWidth m n U B β) := by omega
  have hN2 : bits (((n + 2 : ℕ) : ℤ)) ≤ n + 2 := bits_natCast_le _
  have hlen : (List.replicate (n + 2) (0 : ℤ)).length ≤ (solverWidth m n U B β) := by simp; omega
  -- the pieces
  have c1 := scalFn_cost U B n (matE A) (vecE b) (solverWidth m n U B β) hUW
    (le_trans (bits_natCast_le B) (by omega)) (le_trans (bits_natCast_le n) (by omega)) hAW hbW hX
  have c2 := repFn_cost ((n + 2 : ℕ) : ℤ) 0 (solverWidth m n U B β) (by simp; omega) (by omega)
  have c3 := mapFn_cost padRowFn (0 - (denominator (n + 2) U : ℤ)) (matE A) (70 * ((solverWidth m n U B β) + 1) ^ 3) (fun row hr => by
    have := padRowFn_cost (0 - (denominator (n + 2) U : ℤ)) row (solverWidth m n U B β) hDn (hAW row hr) (by
      obtain ⟨i, rfl⟩ := mem_matE hr; simp [vecE]; omega)
    exact this)
  have c4 := blockFn_cost (0 - (denominator (n + 2) U : ℤ)) (List.replicate (n + 2) 0) (List.replicate (n + 2) 0) (solverWidth m n U B β) hlen hlen
  have c5 := blockFn_cost (denominator (n + 2) U : ℤ) (List.replicate (n + 2) 0) (List.replicate (n + 2) 0) (solverWidth m n U B β) hlen hlen
  have c6 := blockFn_cost ((2 : ℤ) ^ (precision (n + 2) (feasibilityIterations (n + 2) B) + 2 * outerExponent (n + 2) B)) (List.replicate (n + 2) 0)
    (List.replicate (n + 2) 0) (solverWidth m n U B β) hlen hlen
  have c7 := appendFn_cost (.list .int)
    ((matE A).map (fun y => (y ++ [0, 0]).map (fun x => (0 - (denominator (n + 2) U : ℤ)) * x)))
    (blockL (0 - (denominator (n + 2) U : ℤ)) (List.replicate (n + 2) 0))
  have c8 := appendFn_cost (.list .int)
    ((matE A).map (fun y => (y ++ [0, 0]).map (fun x => (0 - (denominator (n + 2) U : ℤ)) * x)) ++
      blockL (0 - (denominator (n + 2) U : ℤ)) (List.replicate (n + 2) 0))
    (blockL (denominator (n + 2) U : ℤ) (List.replicate (n + 2) 0))
  have c9 := mapFn_cost bEntryFn (denominator (n + 2) U : ℤ) (vecE b) (22 * ((solverWidth m n U B β) + 1) ^ 2) (fun x hx =>
    bEntryFn_cost (denominator (n + 2) U : ℤ) x (solverWidth m n U B β) hDp (hbW x hx))
  have c10 := repFn_cost (((n + 2 : ℕ) : ℤ) + ((n + 2 : ℕ) : ℤ)) ((denominator (n + 2) U : ℤ) * (box (n + 2) U : ℤ)) (solverWidth m n U B β) (by omega)
    (bits_le_natAbs_bound _ _ (by omega))
  have c11 := appendFn_cost .int ((vecE b).map (fun y => (0 - (denominator (n + 2) U : ℤ)) * y + 1))
    (List.replicate (n + 2 + (n + 2)) ((denominator (n + 2) U : ℤ) * (box (n + 2) U : ℤ)))
  have c12 := pow2Fn_cost (((precision (n + 2) (feasibilityIterations (n + 2) B) : ℕ) : ℤ) + 2 * ((outerExponent (n + 2) B : ℕ) : ℤ))
  rw [hk] at c12
  have c13 := pow2Fn_cost ((precision (n + 2) (feasibilityIterations (n + 2) B) : ℕ) : ℤ)
  rw [Int.toNat_natCast] at c13
  have c14 := loopFn_cost (by omega : 2 ≤ n + 2) (matrix U (IntegerFeasibilityGeneral.paddedMatrix A))
    (bound (n + 2) U b) (feasibilityIterations (n + 2) B) (outerExponent (n + 2) B) (solverWidth m n U B β) (by omega) (by omega) (by omega)
    (fun i j => le_trans (bits_matrix_le U A β hA i j) (by omega))
    (fun i => le_trans (bits_bound_le (n + 2) U b β hb i) (by omega))
  have hcode : bits code ≤ 3 := bits_le_natAbs_bound _ _ (by omega)
  have lA : (matE A).length = m := by simp [matE]
  have lb : (vecE b).length = m := by simp [vecE]
  have lB : (blockL (0 - (denominator (n + 2) U : ℤ)) (List.replicate (n + 2) 0)).length = n + 2 := by
    simp [blockL]
  simp only [List.length_append, List.length_map, lA, lB, lb] at c7 c8 c11
  rw [lA] at c3
  rw [lb] at c9
  have d3 : (m + 1) * (70 * ((solverWidth m n U B β) + 1) ^ 3 + 17) ≤ ((solverWidth m n U B β) + 1) * (87 * ((solverWidth m n U B β) + 1) ^ 3) :=
    Nat.mul_le_mul (by omega) (by
      have : 1 ≤ ((solverWidth m n U B β) + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
      omega)
  have e3 : ((solverWidth m n U B β) + 1) * (87 * ((solverWidth m n U B β) + 1) ^ 3) = 87 * ((solverWidth m n U B β) + 1) ^ 4 := by ring
  have d9 : (m + 1) * (22 * ((solverWidth m n U B β) + 1) ^ 2 + 17) ≤ ((solverWidth m n U B β) + 1) * (39 * ((solverWidth m n U B β) + 1) ^ 2) :=
    Nat.mul_le_mul (by omega) (by
      have : 1 ≤ ((solverWidth m n U B β) + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
      omega)
  have e9 : ((solverWidth m n U B β) + 1) * (39 * ((solverWidth m n U B β) + 1) ^ 2) = 39 * ((solverWidth m n U B β) + 1) ^ 3 := by ring
  have hKb : bits (((precision (n + 2) (feasibilityIterations (n + 2) B) : ℕ) : ℤ) +
      2 * ((outerExponent (n + 2) B : ℕ) : ℤ)) ≤ (solverWidth m n U B β) := bits_le_natAbs_bound _ _ (by omega)
  have d12 : (precision (n + 2) (feasibilityIterations (n + 2) B) + 2 * outerExponent (n + 2) B + 1) *
      (4 * (precision (n + 2) (feasibilityIterations (n + 2) B) + 2 * outerExponent (n + 2) B) +
        bits (((precision (n + 2) (feasibilityIterations (n + 2) B) : ℕ) : ℤ) +
          2 * ((outerExponent (n + 2) B : ℕ) : ℤ)) + 16) ≤ ((solverWidth m n U B β) + 1) * (21 * ((solverWidth m n U B β) + 1)) :=
    Nat.mul_le_mul (by omega) (by omega)
  have d13 : (precision (n + 2) (feasibilityIterations (n + 2) B) + 1) *
      (4 * precision (n + 2) (feasibilityIterations (n + 2) B) +
        bits ((precision (n + 2) (feasibilityIterations (n + 2) B) : ℕ) : ℤ) + 16) ≤
      ((solverWidth m n U B β) + 1) * (21 * ((solverWidth m n U B β) + 1)) :=
    Nat.mul_le_mul (by omega) (by have := bits_natCast_le (precision (n + 2) (feasibilityIterations (n + 2) B)); omega)
  have e12 : ((solverWidth m n U B β) + 1) * (21 * ((solverWidth m n U B β) + 1)) = 21 * ((solverWidth m n U B β) + 1) ^ 2 := by ring
  have pDB : (bits (denominator (n + 2) U : ℤ) + 1) * (bits (box (n + 2) U : ℤ) + 1) ≤ ((solverWidth m n U B β) + 1) * ((solverWidth m n U B β) + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have p2B : (bits (2 : Ty.int.denote) + 1) * (bits ((outerExponent (n + 2) B : ℕ) : ℤ) + 1) ≤
      ((solverWidth m n U B β) + 1) * ((solverWidth m n U B β) + 1) := Nat.mul_le_mul (by rw [hb2]; omega)
        (by have := bits_natCast_le (outerExponent (n + 2) B); omega)
  have eWW : ((solverWidth m n U B β) + 1) * ((solverWidth m n U B β) + 1) = ((solverWidth m n U B β) + 1) ^ 2 := by ring
  have h2B0 : bits (2 * ((outerExponent (n + 2) B : ℕ) : ℤ)) ≤ (solverWidth m n U B β) :=
    bits_le_natAbs_bound _ _ (by omega)
  have hKn : bits ((precision (n + 2) (feasibilityIterations (n + 2) B) : ℕ) : ℤ) ≤ (solverWidth m n U B β) :=
    le_trans (bits_natCast_le _) (by omega)
  linarith only [c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, d3, e3, d9, e9,
    d12, d13, e12, pDB, p2B, eWW, h2B0, hKn, hcode, hb0, hb1, hb2, hDp, hDn, hN2, q0, q1, q2, q3, q4, hWa]

end MWIS.FunLP

end
