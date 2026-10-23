module

public import MWIS.FunLPThreshold
public import MWIS.FunLPSolverCost

/-!
# Cost of the threshold feasibility test and of the optimizer
-/

@[expose] public section

namespace MWIS.FunLP

open MWIS.Fun AlgorithmNetworkEncoding

theorem absFn_cost (x : ℤ) : absFn.costAt ((), x) ≤ 2 * bits x + 12 := by
  unfold Fn.costAt absFn
  simp only [Expr.cost, Var.index, Expr.denote, Var.get, CmpOp.charge, IntOp.charge, bits_zero]
  rcases Bool.eq_false_or_eq_true (CmpOp.lt.eval x 0) with h | h <;>
    simp only [h, ite_true, Bool.false_eq_true, ite_false] <;> omega

theorem absSumFn_cost (l : List ℤ) (W : ℕ) (hl : ∀ x ∈ l, bits x ≤ W) (hlen : l.length ≤ W) :
    absSumFn.costAt l ≤ 60 * (W + 1) ^ 2 := by
  unfold Fn.costAt absSumFn
  rw [cost_call]
  have hm := mapFn_cost absFn () l (2 * W + 12) (fun x hx => by
    have := absFn_cost x; have := hl x hx; omega)
  have hs := sumFn_cost (l.map (fun x => |x|)) W (fun y hy => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    have : bits |x| = bits x := by simp only [bits, Int.natAbs_abs]
    rw [this]; exact hl x hx)
  simp only [Expr.cost, cost_call, Var.index, Expr.denote, Var.get, denote_call, mapFn_apply,
    absFn_apply, List.length_map] at hm hs ⊢
  have a1 : (l.length + 1) * (2 * W + 12 + 17) ≤ (W + 1) * (29 * (W + 1)) :=
    Nat.mul_le_mul (by omega) (by omega)
  have a2 : (l.length + 1) * (2 * W + l.length + 10) ≤ (W + 1) * (13 * (W + 1)) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e : (W + 1) * (29 * (W + 1)) + (W + 1) * (13 * (W + 1)) = 42 * (W + 1) ^ 2 := by ring
  have : 1 ≤ (W + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  linarith

open AlgorithmThresholdLP

theorem bits_le_size_of_abs_le (x : ℤ) (U : ℕ) (h : |x| ≤ (U : ℤ)) : bits x ≤ U.size := by
  rw [← bits_natCast]
  apply bits_mono
  have := abs_le.mp h
  simp only [Int.natAbs_natCast]
  omega

theorem bits_le_size_of_le (x : ℤ) (U : ℕ) (h0 : 0 ≤ x) (h : x ≤ (U : ℤ)) : bits x ≤ U.size :=
  bits_le_size_of_abs_le x U (by rw [abs_of_nonneg h0]; exact h)

theorem magFn_cost {M N : ℕ} (P : DenseProgram M N) (W : ℕ) (hM : M ≤ W) (hN : N ≤ W)
    (hU : (magnitude P).size ≤ W) :
    magFn.costAt (FunNetwork.DenseProgram.toFun P) ≤ 300 * (W + 1) ^ 3 := by
  unfold Fn.costAt magFn
  simp only [Expr.cost, cost_call, Var.index, Expr.denote, Var.get, denote_call, IntOp.charge,
    mapFn_apply, rowAbsFn_apply, sumFn_apply, absSumFn_apply, IntOp.eval]
  have hS1 : (List.map (fun y => (List.map (fun x => |x|) y).sum) (FunNetwork.DenseProgram.toFun P).1).sum =
      ((∑ i, ∑ j, (P.coefficient i j).natAbs : ℕ) : ℤ) := by
    simp only [FunNetwork.DenseProgram.toFun, List.map_ofFn, Function.comp, List.sum_ofFn]
    push_cast; rfl
  have hS2 : (List.map (fun x => |x|) (FunNetwork.DenseProgram.toFun P).2.1).sum =
      ((∑ i, (P.rhs i).natAbs : ℕ) : ℤ) := by
    simp only [FunNetwork.DenseProgram.toFun, sum_abs_ofFn]
  have hS3 : (List.map (fun x => |x|) (FunNetwork.DenseProgram.toFun P).2.2).sum =
      ((∑ j, (P.objective j).natAbs : ℕ) : ℤ) := by
    simp only [FunNetwork.DenseProgram.toFun, sum_abs_ofFn]
  have hmag : magnitude P = 1 + (∑ i, ∑ j, (P.coefficient i j).natAbs) + (∑ i, (P.rhs i).natAbs) +
      ∑ j, (P.objective j).natAbs := rfl
  rw [hS1, hS2, hS3]
  have b1 : bits ((∑ i, ∑ j, (P.coefficient i j).natAbs : ℕ) : ℤ) ≤ W :=
    le_trans (bits_le_size_of_le _ _ (by positivity) (by exact_mod_cast (show _ ≤ magnitude P by rw [hmag]; omega))) hU
  have b2 : bits ((∑ i, (P.rhs i).natAbs : ℕ) : ℤ) ≤ W :=
    le_trans (bits_le_size_of_le _ _ (by positivity) (by exact_mod_cast (show _ ≤ magnitude P by rw [hmag]; omega))) hU
  have b3 : bits ((∑ j, (P.objective j).natAbs : ℕ) : ℤ) ≤ W :=
    le_trans (bits_le_size_of_le _ _ (by positivity) (by exact_mod_cast (show _ ≤ magnitude P by rw [hmag]; omega))) hU
  have b4 : bits (1 + ((∑ i, ∑ j, (P.coefficient i j).natAbs : ℕ) : ℤ)) ≤ W :=
    le_trans (bits_le_size_of_le _ _ (by positivity) (by exact_mod_cast (show _ ≤ magnitude P by rw [hmag]; omega))) hU
  have b5 : bits (1 + ((∑ i, ∑ j, (P.coefficient i j).natAbs : ℕ) : ℤ) +
      ((∑ i, (P.rhs i).natAbs : ℕ) : ℤ)) ≤ W :=
    le_trans (bits_le_size_of_le _ _ (by positivity) (by exact_mod_cast (show _ ≤ magnitude P by rw [hmag]; omega))) hU
  have hb1 : bits (1 : ℤ) = 1 := by decide
  have ecoef : ∀ i j, bits (P.coefficient i j) ≤ W := fun i j =>
    le_trans (bits_le_size_of_abs_le _ _ (coefficient_abs_le P i j)) hU
  have erhs : ∀ i, bits (P.rhs i) ≤ W := fun i =>
    le_trans (bits_le_size_of_abs_le _ _ (rhs_abs_le P i)) hU
  have eobj : ∀ j, bits (P.objective j) ≤ W := fun j => by
    have : |P.objective j| ≤ (magnitude P : ℤ) := by
      have h1 : (P.objective j).natAbs ≤ ∑ k, (P.objective k).natAbs :=
        Finset.single_le_sum (f := fun k => (P.objective k).natAbs) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ j)
      rw [← Int.natCast_natAbs]
      exact_mod_cast (show (P.objective j).natAbs ≤ magnitude P by rw [hmag]; omega)
    exact le_trans (bits_le_size_of_abs_le _ _ this) hU
  have c1 := mapFn_cost rowAbsFn () (FunNetwork.DenseProgram.toFun P).1 (60 * (W + 1) ^ 2 + 10)
    (fun row hr => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
      have := absSumFn_cost (List.ofFn (P.coefficient i)) W (fun x hx => by
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx; exact ecoef i j) (by simp; omega)
      unfold Fn.costAt rowAbsFn
      rw [cost_call]
      simp only [Expr.cost, Var.index, Expr.denote, Var.get]
      omega)
  have c2 := sumFn_cost
    (List.map (fun y => (List.map (fun x => |x|) y).sum) (FunNetwork.DenseProgram.toFun P).1) W
    (fun y hy => by
      obtain ⟨row, hr, rfl⟩ := List.mem_map.mp hy
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
      rw [sum_abs_ofFn]
      have : ∑ j, (P.coefficient i j).natAbs ≤ ∑ a, ∑ j, (P.coefficient a j).natAbs :=
        Finset.single_le_sum (f := fun a => ∑ j, (P.coefficient a j).natAbs)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      exact le_trans (bits_le_size_of_le _ _ (by positivity) (by exact_mod_cast (show _ ≤ magnitude P by rw [hmag]; omega))) hU)
  have c3 := absSumFn_cost (FunNetwork.DenseProgram.toFun P).2.1 W (fun x hx => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx; exact erhs i) (by simp [FunNetwork.DenseProgram.toFun]; omega)
  have c4 := absSumFn_cost (FunNetwork.DenseProgram.toFun P).2.2 W (fun x hx => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx; exact eobj i) (by simp [FunNetwork.DenseProgram.toFun]; omega)
  have l1 : (FunNetwork.DenseProgram.toFun P).1.length = M := by simp [FunNetwork.DenseProgram.toFun]
  simp only [List.length_map, l1] at c1 c2
  have d1 : (M + 1) * (60 * (W + 1) ^ 2 + 10 + 17) ≤ (W + 1) * (87 * (W + 1) ^ 2) :=
    Nat.mul_le_mul (by omega) (by have : 1 ≤ (W + 1) ^ 2 := Nat.one_le_pow _ _ (by omega); omega)
  have d2 : (M + 1) * (2 * W + M + 10) ≤ (W + 1) * (13 * (W + 1)) := Nat.mul_le_mul (by omega) (by omega)
  have e1 : (W + 1) * (87 * (W + 1) ^ 2) = 87 * (W + 1) ^ 3 := by ring
  have e2 : (W + 1) * (13 * (W + 1)) = 13 * (W + 1) ^ 2 := by ring
  have p2 : (W + 1) ^ 2 ≤ (W + 1) ^ 3 := pow_mono_one (by omega) 2 3 (by norm_num)
  have p1 : W + 1 ≤ (W + 1) ^ 3 := by simpa using pow_mono_one (show 1 ≤ W + 1 by omega) 1 3 (by norm_num)
  have p0 : 1 ≤ (W + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  linarith

theorem lenFn_cost (l : List ℤ) : (lenFn .int).costAt l ≤ (l.length + 1) * (l.length + 10) := by
  unfold Fn.costAt lenFn
  have h := cost_foldl_le_prefix (Γ := [.list .int]) v0 (.int 0) (.arith .add v1 (.int 1)) (l, ())
    (l.length + 8) (by
      intro j hj
      simp only [Expr.cost, Var.index, Expr.denote, Var.get, IntOp.charge, IntOp.eval]
      rw [foldl_len]
      have : bits ((0 : ℤ) + ((l.take j).length : ℤ)) ≤ l.length :=
        bits_le_natAbs_bound _ _ (by simp at hj ⊢; omega)
      have h1 : bits (1 : ℤ) = 1 := by decide
      rw [h1]; omega)
  refine le_trans h ?_
  simp only [Expr.cost, Var.index, Expr.denote, Var.get]
  nlinarith

/-- One threshold feasibility test costs `2^65 (W + 1)^5` for
`W = solverWidth M N U (size U) (size U)`, `U = magnitude P`. -/
theorem feasLPFn_cost {M N : ℕ} (P : DenseProgram M N) :
    feasLPFn.costAt (FunNetwork.DenseProgram.toFun P) ≤ 2 ^ 65 * ((solverWidth M N (magnitude P) (magnitude P).size (magnitude P).size) + 1) ^ 5 := by
  have hMW : M + N + (magnitude P).size + 1 ≤ (solverWidth M N (magnitude P) (magnitude P).size (magnitude P).size) := by unfold solverWidth; omega
  have cm := magFn_cost P (solverWidth M N (magnitude P) (magnitude P).size (magnitude P).size) (by omega) (by omega) (by omega)
  have ecoef : ∀ i j, bits (-P.coefficient i j) ≤ (magnitude P).size := fun i j => by
    rw [bits_neg]; exact bits_le_size_of_abs_le _ _ (coefficient_abs_le P i j)
  have erhs : ∀ i, bits (-P.rhs i) ≤ (magnitude P).size := fun i => by
    rw [bits_neg]; exact bits_le_size_of_abs_le _ _ (rhs_abs_le P i)
  have cf := feasibleFn_cost (magnitude P) (magnitude P).size (magnitude P).size
    (fun i j => -P.coefficient i j) (fun i => -P.rhs i) ecoef erhs
  unfold Fn.costAt feasLPFn
  simp only [Expr.cost, cost_call, Var.index, Expr.denote, Var.get, denote_call, lenFn_apply,
    mapFn_apply, negRowFn_apply, negFn_apply]
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
  rw [h1, h2, h3, h4]
  have cl := lenFn_cost (FunNetwork.DenseProgram.toFun P).2.2
  have cn := mapFn_cost negRowFn () (FunNetwork.DenseProgram.toFun P).1 ((N + 1) * ((solverWidth M N (magnitude P) (magnitude P).size (magnitude P).size) + 30) + 10)
    (fun row hr => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
      have := negFn_cost (List.ofFn (P.coefficient i)) (solverWidth M N (magnitude P) (magnitude P).size (magnitude P).size) (fun x hx => by
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
        have := bits_le_size_of_abs_le _ _ (coefficient_abs_le P i j); omega)
      simp only [List.length_ofFn] at this
      unfold Fn.costAt negRowFn
      rw [cost_call]
      simp only [Expr.cost, Var.index, Expr.denote, Var.get]
      omega)
  have cr := negFn_cost (FunNetwork.DenseProgram.toFun P).2.1 (solverWidth M N (magnitude P) (magnitude P).size (magnitude P).size) (fun x hx => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    have := bits_le_size_of_abs_le _ _ (rhs_abs_le P i); omega)
  have l1 : (FunNetwork.DenseProgram.toFun P).1.length = M := by simp [FunNetwork.DenseProgram.toFun]
  have l2 : (FunNetwork.DenseProgram.toFun P).2.1.length = M := by simp [FunNetwork.DenseProgram.toFun]
  have l3 : (FunNetwork.DenseProgram.toFun P).2.2.length = N := by simp [FunNetwork.DenseProgram.toFun]
  rw [l1] at cn
  rw [l2] at cr
  rw [l3] at cl
  have hUb : bits ((magnitude P : ℕ) : ℤ) ≤ (solverWidth M N (magnitude P) (magnitude P).size (magnitude P).size) := by rw [bits_natCast]; omega
  set w := (solverWidth M N (magnitude P) (magnitude P).size (magnitude P).size) + 1 with hw
  have w1 : 1 ≤ w := by omega
  have q2 : w ^ 2 ≤ w ^ 5 := pow_mono_one w1 2 5 (by norm_num)
  have q3 : w ^ 3 ≤ w ^ 5 := pow_mono_one w1 3 5 (by norm_num)
  have q1 : w ≤ w ^ 5 := by simpa using pow_mono_one w1 1 5 (by norm_num)
  have d1 : (N + 1) * (N + 10) ≤ w * (10 * w) := Nat.mul_le_mul (by omega) (by omega)
  have d2 : (M + 1) * ((N + 1) * ((solverWidth M N (magnitude P) (magnitude P).size (magnitude P).size) + 30) + 10 + 17) ≤ w * (w * (30 * w) + 27 * w) :=
    Nat.mul_le_mul (by omega) (by
      have : (N + 1) * ((solverWidth M N (magnitude P) (magnitude P).size (magnitude P).size) + 30) ≤ w * (30 * w) := Nat.mul_le_mul (by omega) (by omega)
      omega)
  have d3 : (M + 1) * ((solverWidth M N (magnitude P) (magnitude P).size (magnitude P).size) + 30) ≤ w * (30 * w) := Nat.mul_le_mul (by omega) (by omega)
  have e1 : w * (10 * w) = 10 * w ^ 2 := by ring
  have e2 : w * (w * (30 * w) + 27 * w) = 30 * w ^ 3 + 27 * w ^ 2 := by ring
  have e3 : w * (30 * w) = 30 * w ^ 2 := by ring
  linarith

/-! ## A single-variable polynomial bound on the solver width -/

open IntegerFeasibility AlgorithmPrecision in
theorem solverWidth_le (m n U B β y : ℕ) (hy : m + n + U.size + B + β + 4 ≤ y) :
    solverWidth m n U B β + 1 ≤ 2 ^ 9 * y ^ 7 := by
  have y1 : 1 ≤ y := by omega
  have p15 : y ≤ y ^ 5 := by simpa using pow_mono_one y1 1 5 (by norm_num)
  have p25 : y ^ 2 ≤ y ^ 5 := pow_mono_one y1 2 5 (by norm_num)
  have p05 : 1 ≤ y ^ 5 := Nat.one_le_pow _ _ (by omega)
  have p37 : y ^ 3 ≤ y ^ 7 := pow_mono_one y1 3 7 (by norm_num)
  have p67 : y ^ 6 ≤ y ^ 7 := pow_mono_one y1 6 7 (by norm_num)
  have p57 : y ^ 5 ≤ y ^ 7 := pow_mono_one y1 5 7 (by norm_num)
  have p07 : 1 ≤ y ^ 7 := Nat.one_le_pow _ _ (by omega)
  have p17 : y ≤ y ^ 7 := by simpa using pow_mono_one y1 1 7 (by norm_num)
  have hT : feasibilityIterations (n + 2) B ≤ 33 * y ^ 5 := by
    unfold feasibilityIterations radiusExponent
    have h : 4 * (n + 2 + 1) * (n + 2) * (8 * (n + 2 + 2) ^ 2 * (B + 1)) ≤
        4 * y * y * (8 * y ^ 2 * y) := by
      gcongr <;> omega
    have e : 4 * y * y * (8 * y ^ 2 * y) = 32 * y ^ 5 := by ring
    omega
  have hK : precision (n + 2) (feasibilityIterations (n + 2) B) ≤ 102 * y ^ 5 := by
    unfold precision; omega
  have hB0 : outerExponent (n + 2) B ≤ 4 * y ^ 5 := by
    unfold outerExponent
    have h1 : (n + 2) * (n + 2) ≤ y * y := Nat.mul_le_mul (by omega) (by omega)
    have h2 : B * (n + 2) ≤ y * y := Nat.mul_le_mul (by omega) (by omega)
    have e : y * y = y ^ 2 := by ring
    omega
  have g2 : (n + 2) * (precision (n + 2) (feasibilityIterations (n + 2) B) +
      2 * feasibilityIterations (n + 2) B + outerExponent (n + 2) B + 3) ≤ y * (175 * y ^ 5) :=
    Nat.mul_le_mul (by omega) (by omega)
  have g3 : (n + 2) ^ 2 * (precision (n + 2) (feasibilityIterations (n + 2) B) +
      2 * feasibilityIterations (n + 2) B + 2 * outerExponent (n + 2) B + 2) ≤ y ^ 2 * (180 * y ^ 5) :=
    Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) 2) (by omega)
  have g4 : 4 * (n + 4) ^ 2 * (U.size + 1) ≤ 4 * y ^ 2 * y :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)) (by omega)
  have e2 : y * (175 * y ^ 5) = 175 * y ^ 6 := by ring
  have e3 : y ^ 2 * (180 * y ^ 5) = 180 * y ^ 7 := by ring
  have e4 : 4 * y ^ 2 * y = 4 * y ^ 3 := by ring
  unfold solverWidth
  omega

/-! ## Magnitude of a thresholded program -/

theorem magnitude_withThreshold {M N : ℕ} (P : DenseProgram M N) (t : ℤ) :
    magnitude (P.withThreshold t) ≤ 2 * magnitude P + t.natAbs := by
  unfold magnitude
  simp only [DenseProgram.withThreshold, Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ]
  omega

theorem size_magnitude_withThreshold {M N : ℕ} (P : DenseProgram M N) (t : ℤ) :
    (magnitude (P.withThreshold t)).size ≤ (magnitude P).size + bits t + 2 := by
  rw [Nat.size_le]
  have h1 := magnitude_withThreshold P t
  have h2 : magnitude P < 2 ^ (magnitude P).size := Nat.lt_size_self _
  have h3 : t.natAbs < 2 ^ bits t := natAbs_lt_of_bits t
  have h4 : 2 ^ (magnitude P).size ≤ 2 ^ ((magnitude P).size + bits t) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h5 : 2 ^ bits t ≤ 2 ^ ((magnitude P).size + bits t) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have e : 2 ^ ((magnitude P).size + bits t + 2) = 4 * 2 ^ ((magnitude P).size + bits t) := by
    rw [pow_add]; ring
  omega

/-! ## One search round -/

theorem optStep_apply {M N : ℕ} (P : DenseProgram M N) (offset : ℤ) (b s lower : ℕ) :
    optStepE.denote ((((s + 1 : ℕ) : ℤ), (lower : ℤ)),
        ((FunNetwork.DenseProgram.toFun P, (offset, (b : ℤ))), ())) =
      ((s : ℤ), if atLeast P offset (lower + 2 ^ s) then ((lower + 2 ^ s : ℕ) : ℤ) else (lower : ℤ)) := by
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

theorem search_reach (test : ℕ → Bool) (F : ℤ × ℤ → ℤ × ℤ)
    (hF : ∀ s lower : ℕ, F (((s + 1 : ℕ) : ℤ), (lower : ℤ)) =
      ((s : ℤ), if test (lower + 2 ^ s) then ((lower + 2 ^ s : ℕ) : ℤ) else (lower : ℤ)))
    (r lower : ℕ) : ∀ j ≤ r, ∃ l : ℕ, F^[j] ((r : ℤ), (lower : ℤ)) = (((r - j : ℕ) : ℤ), (l : ℤ)) ∧
      l + 2 ^ (r - j) ≤ lower + 2 ^ r := by
  intro j
  induction j with
  | zero => intro _; exact ⟨lower, rfl, le_rfl⟩
  | succ j ih =>
    intro hj
    obtain ⟨l, he, hl⟩ := ih (by omega)
    rw [Function.iterate_succ_apply', he]
    have hr : r - j = (r - (j + 1)) + 1 := by omega
    rw [hr, hF]
    have hp : 2 ^ (r - (j + 1) + 1) = 2 * 2 ^ (r - (j + 1)) := by rw [pow_succ]; ring
    rw [hr, hp] at hl
    by_cases hc : test (l + 2 ^ (r - (j + 1)))
    · refine ⟨l + 2 ^ (r - (j + 1)), by simp [hc], by omega⟩
    · refine ⟨l, by simp [hc], by omega⟩

/-- The base of the optimizer's cost polynomial. -/
def optBase {M N : ℕ} (P : DenseProgram M N) (offset : ℤ) (b : ℕ) : ℕ :=
  M + N + (magnitude P).size + bits offset + b + 2

theorem optStep_cost {M N : ℕ} (P : DenseProgram M N) (offset : ℤ) (b s lower : ℕ)
    (hl : lower + 2 ^ (s + 1) ≤ 2 ^ b) :
    optStepE.cost ((((s + 1 : ℕ) : ℤ), (lower : ℤ)),
        ((FunNetwork.DenseProgram.toFun P, (offset, (b : ℤ))), ())) ≤
      2 ^ 251 * optBase P offset b ^ 35 := by
  simp only [optStepE, Expr.cost, cost_call, Var.index, Expr.denote, Var.get, denote_call,
    pow2Fn_apply, IntOp.eval, IntOp.charge]
  have h1 : (((s + 1 : ℕ) : ℤ) - 1) = (s : ℤ) := by push_cast; ring
  have h2 : ((s : ℤ)).toNat = s := Int.toNat_natCast s
  have h3 : ((lower : ℤ) + 2 ^ s) = ((lower + 2 ^ s : ℕ) : ℤ) := by push_cast; ring
  rw [h1, h2, h3]
  simp only [← toFun_withThreshold]
  set X := optBase P offset b with hX
  have hpow : 2 ^ (s + 1) = 2 * 2 ^ s := by rw [pow_succ]; ring
  have hs : s + 1 ≤ b := by
    by_contra hc
    have : 2 ^ b < 2 ^ (s + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    linarith
  have hqb : lower + 2 ^ s < 2 ^ b := by
    have h' : lower + 2 * 2 ^ s ≤ 2 ^ b := hpow ▸ hl
    have : 0 < 2 ^ s := by positivity
    linarith
  have hbq : bits ((lower + 2 ^ s : ℕ) : ℤ) ≤ b := bits_le_of_natAbs_le (by rw [Int.natAbs_natCast]; exact hqb)
  have hbl : bits (lower : ℤ) ≤ b := bits_le_of_natAbs_le (by
    rw [Int.natAbs_natCast]; have : 0 < 2 ^ s := by positivity
    linarith)
  have hb2q : bits (2 * ((lower + 2 ^ s : ℕ) : ℤ)) ≤ b + 2 := by
    have := bits_mul_le 2 ((lower + 2 ^ s : ℕ) : ℤ); have h2 : bits (2 : ℤ) = 2 := by decide
    omega
  have hbt : bits (offset - 2 * ((lower + 2 ^ s : ℕ) : ℤ)) ≤ bits offset + b + 3 := by
    have := bits_sub_le offset (2 * ((lower + 2 ^ s : ℕ) : ℤ)); omega
  have hXb : bits offset + b + 2 ≤ X := by rw [hX]; unfold optBase; omega
  have hX2 : 2 ≤ X := by rw [hX]; unfold optBase; omega
  have hXM : M + N + (magnitude P).size ≤ X := by rw [hX]; unfold optBase; omega
  -- the feasibility test
  have hU := size_magnitude_withThreshold P (offset - 2 * ((lower + 2 ^ s : ℕ) : ℤ))
  have hW := solverWidth_le (M + 1) N (magnitude (P.withThreshold (offset - 2 * ((lower + 2 ^ s : ℕ) : ℤ))))
    (magnitude (P.withThreshold (offset - 2 * ((lower + 2 ^ s : ℕ) : ℤ)))).size (magnitude (P.withThreshold (offset - 2 * ((lower + 2 ^ s : ℕ) : ℤ)))).size (16 * X) (by omega)
  have hW5 := Nat.pow_le_pow_left hW 5
  have e5 : (2 ^ 9 * (16 * X) ^ 7) ^ 5 = 2 ^ 185 * X ^ 35 := by ring
  rw [e5] at hW5
  have cf := feasLPFn_cost (P.withThreshold (offset - 2 * ((lower + 2 ^ s : ℕ) : ℤ)))
  -- the remaining terms
  have cp := pow2Fn_cost (s : ℤ)
  rw [Int.toNat_natCast] at cp
  have hsb : bits (s : ℤ) ≤ s := bits_natCast_le s
  have hs1 : bits ((s + 1 : ℕ) : ℤ) ≤ s + 1 := bits_natCast_le _
  have hps : bits ((2 : ℤ) ^ s) = s + 1 := bits_pow_two s
  have cp' : (s + 1) * (4 * s + bits (s : ℤ) + 16) ≤ X * (21 * X) := Nat.mul_le_mul (by omega) (by omega)
  have cm : (bits (2 : ℤ) + 1) * (bits ((lower + 2 ^ s : ℕ) : ℤ) + 1) ≤ X * (2 * X) := by
    have h2 : bits (2 : ℤ) = 2 := by decide
    rw [h2]; exact Nat.mul_le_mul (by omega) (by omega)
  have x1 : 1 ≤ X := by omega
  have r2 : X * (21 * X) = 21 * X ^ 2 := by ring
  have r3 : X * (2 * X) = 2 * X ^ 2 := by ring
  have q2 : X ^ 2 ≤ X ^ 35 := pow_mono_one x1 2 35 (by norm_num)
  have q1 : X ≤ X ^ 35 := by simpa using pow_mono_one x1 1 35 (by norm_num)
  have q0 : 1 ≤ X ^ 35 := Nat.one_le_pow _ _ (by omega)
  have hb1 : bits (1 : ℤ) = 1 := by decide
  have hif : ∀ c : Bool, (if c = true then 0 + 1 else 0 + 1 + 1 + 1) ≤ 3 := by
    intro c; cases c <;> simp
  have hif' := hif (feasLPFn.apply (FunNetwork.DenseProgram.toFun (P.withThreshold (offset - 2 * ((lower + 2 ^ s : ℕ) : ℤ)))))
  rw [hps, hb1]
  linarith

/-- The optimizer costs at most `2^252 X^36`, `X = M + N + size (magnitude P) + bits offset + b + 2`. -/
theorem optF_cost_le {M N : ℕ} (P : DenseProgram M N) (offset : ℤ) (b : ℕ) :
    optF.costAt (FunNetwork.DenseProgram.toFun P, (offset, (b : ℤ))) ≤
      2 ^ 252 * optBase P offset b ^ 36 := by
  set env : Env [OptTy] := ((FunNetwork.DenseProgram.toFun P, (offset, (b : ℤ))), ()) with henv
  have hF : ∀ s lower : ℕ, (fun st => optStepE.denote (st, env)) (((s + 1 : ℕ) : ℤ), (lower : ℤ)) =
      ((s : ℤ), if atLeast P offset (lower + 2 ^ s) then ((lower + 2 ^ s : ℕ) : ℤ) else (lower : ℤ)) :=
    fun s lower => optStep_apply P offset b s lower
  have hit := cost_iter_le_prefix (Γ := [OptTy]) (.snd (.snd v0)) (.pair (.snd (.snd v0)) (.int 0))
    optStepE env (2 ^ 251 * optBase P offset b ^ 35) (by
      intro j hj
      have hj' : j < b := by simpa [Expr.denote, Var.get, henv] using hj
      have hi : (Expr.pair (.snd (.snd v0)) (.int 0) : Expr [OptTy] (.prod .int .int)).denote env =
          ((b : ℤ), ((0 : ℕ) : ℤ)) := by simp [Expr.denote, Var.get, henv]
      rw [hi]
      obtain ⟨l, he, hl⟩ := search_reach (atLeast P offset) (fun st => optStepE.denote (st, env))
        hF b 0 j hj'.le
      rw [he]
      have hr : b - j = (b - j - 1) + 1 := by omega
      rw [hr] at hl ⊢
      exact optStep_cost P offset b (b - j - 1) l (by omega))
  unfold Fn.costAt optF
  simp only [Expr.cost]
  refine le_trans (Nat.add_le_add_right hit 1) ?_
  simp only [Expr.cost, Var.index, Expr.denote, Var.get, henv, Int.toNat_natCast]
  have hb : bits (b : ℤ) ≤ b := bits_natCast_le b
  have hX : b + 2 ≤ optBase P offset b := by unfold optBase; omega
  have x1 : 1 ≤ optBase P offset b := by omega
  have q0 : 1 ≤ optBase P offset b ^ 35 := Nat.one_le_pow _ _ (by omega)
  have q1 : optBase P offset b ≤ optBase P offset b ^ 35 := by
    simpa using pow_mono_one x1 1 35 (by norm_num)
  have hm : b * (2 ^ 251 * optBase P offset b ^ 35 + bits (b : ℤ) + 1) ≤
      optBase P offset b * (2 ^ 251 * optBase P offset b ^ 35 + 2 * optBase P offset b ^ 35) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e : optBase P offset b * (2 ^ 251 * optBase P offset b ^ 35 + 2 * optBase P offset b ^ 35) =
      (2 ^ 251 + 2) * optBase P offset b ^ 36 := by ring
  have q36 : 1 ≤ optBase P offset b ^ 36 := Nat.one_le_pow _ _ (by omega)
  omega

end MWIS.FunLP

end
