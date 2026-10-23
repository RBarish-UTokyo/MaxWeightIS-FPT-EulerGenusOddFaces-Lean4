module

public import MWIS.FunLPRun

/-!
# Cost of the rounded ellipsoid loop

Each round costs `O((W + 1)^4)` when every stored integer, every input entry,
the dimension, the number of rows and the grid exponent are bounded by `W`
(`stepFn_cost`). Along the actual run every stored state is a trajectory state,
so `AlgorithmStateBounds.trajectory_payloadBits` bounds its entries, and the
whole loop costs at most `2^62 (W + 1)^5` (`loopFn_cost`).
-/

@[expose] public section

namespace MWIS.FunLP

open MWIS.Fun

theorem sepTestFn_cost (k2 : ℤ) (c row : List ℤ) (bi : ℤ) (W : ℕ) (hk : bits k2 ≤ W)
    (hb : bits bi ≤ W) (hc : ∀ x ∈ c, bits x ≤ W) (hr : ∀ x ∈ row, bits x ≤ W)
    (hl : row.length ≤ W) :
    sepTestFn.costAt ((k2, c), (row, bi)) ≤ 420 * (W + 1) ^ 3 := by
  unfold Fn.costAt sepTestFn
  simp only [Expr.cost, cost_call, Var.index, Expr.denote, Var.get, denote_call, dotFn_apply,
    IntOp.charge, CmpOp.charge, IntOp.eval]
  have hd := dotFn_cost row c W W hl hr hc
  have hbd := bits_dotL_le row c W W hl hr hc
  have hm := bits_mul_le bi k2
  have h1 : (W + W + 10) ^ 2 ≤ (10 * 10) * (W + 1) ^ 2 := sq_le_of (by omega)
  have h2 : 4 * (W + 1) * (W + W + 10) ^ 2 ≤ 400 * (W + 1) ^ 3 := by
    calc _ ≤ 4 * (W + 1) * ((10 * 10) * (W + 1) ^ 2) := Nat.mul_le_mul_left _ h1
      _ = 400 * (W + 1) ^ 3 := by ring
  have h3 : (bits bi + 1) * (bits k2 + 1) ≤ (W + 1) ^ 2 := by
    calc _ ≤ (W + 1) * (W + 1) := Nat.mul_le_mul (by omega) (by omega)
      _ = (W + 1) ^ 2 := by ring
  have p23 : (W + 1) ^ 2 ≤ (W + 1) ^ 3 := pow_mono_one (by omega) 2 3 (by norm_num)
  have p13 : W + 1 ≤ (W + 1) ^ 3 := by
    simpa using pow_mono_one (show 1 ≤ W + 1 by omega) 1 3 (by norm_num)
  dsimp only [Ty.denote] at hd hbd hm h3 ⊢
  omega

theorem sepFn_cost (k2 : ℤ) (A : List (List ℤ)) (b c : List ℤ) (W : ℕ) (hk : bits k2 ≤ W)
    (hAl : A.length ≤ W) (hrows : ∀ row ∈ A, row.length ≤ W)
    (hA : ∀ row ∈ A, ∀ x ∈ row, bits x ≤ W) (hb : ∀ x ∈ b, bits x ≤ W)
    (hc : ∀ x ∈ c, bits x ≤ W) :
    sepFn.costAt (k2, A, b, c) ≤ 500 * (W + 1) ^ 4 := by
  unfold Fn.costAt sepFn
  have h := cost_foldl_le (Γ := [.prod .int (.prod (.list (.list .int)) (.prod (.list .int) (.list .int)))])
    (call (zipFn (.list .int) .int) (.pair (.fst (.snd v0)) (.fst (.snd (.snd v0))))) .nil sepStepE
    ((k2, A, b, c), ()) (fun _ => True) (420 * (W + 1) ^ 3 + 30) trivial (by
      rintro acc ⟨row, bi⟩ hy -
      refine ⟨trivial, ?_⟩
      simp only [Expr.denote, Var.get, denote_call, zipFn_apply] at hy
      have hrow := (List.of_mem_zip hy).1
      have hbi := (List.of_mem_zip hy).2
      have ht := sepTestFn_cost k2 c row bi W hk (hb bi hbi) hc (hA row hrow) (hrows row hrow)
      cases acc with
      | nil =>
        simp only [sepStepE, Expr.cost, cost_call, Var.index, Expr.denote, Var.get]
        split_ifs <;> linarith
      | cons y ys =>
        simp only [sepStepE, Expr.cost, Var.index, Expr.denote, Var.get]
        have : 0 ≤ (W + 1) ^ 3 := Nat.zero_le _
        linarith)
  have hz := zipFn_cost (.list .int) .int A b
  refine le_trans h ?_
  simp only [Expr.cost, cost_call, Var.index, Expr.denote, Var.get, denote_call, zipFn_apply]
  have hzl : (A.zip b).length ≤ W := by simp; omega
  have h4 : (A.zip b).length * (420 * (W + 1) ^ 3 + 30 + 1) ≤ W * (451 * (W + 1) ^ 3) := by
    have : 1 ≤ (W + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
    exact Nat.mul_le_mul hzl (by omega)
  have p34 : (W + 1) ^ 3 ≤ (W + 1) ^ 4 := pow_mono_one (by omega) 3 4 (by norm_num)
  have h5 : W * (451 * (W + 1) ^ 3) + 62 * (W + 1) + 100 ≤ 500 * (W + 1) ^ 4 := by
    have e : (W + 1) * (W + 1) ^ 3 = (W + 1) ^ 4 := by ring
    have p14 : W + 1 ≤ (W + 1) ^ 3 := by
      simpa using pow_mono_one (show 1 ≤ W + 1 by omega) 1 3 (by norm_num)
    have : 1 ≤ (W + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
    nlinarith
  have : (A.zip b).length + 1 ≤ W + 1 := by omega
  have hz' : (A.length + 1) * 62 ≤ (W + 1) * 62 := Nat.mul_le_mul_right _ (by omega)
  linarith

theorem zeroFn_cost (row : List ℤ) (W : ℕ) (hr : ∀ x ∈ row, bits x ≤ W) (hl : row.length ≤ W) :
    zeroFn.costAt row ≤ 420 * (W + 1) ^ 3 := by
  unfold Fn.costAt zeroFn
  simp only [Expr.cost, cost_call, Var.index, Expr.denote, Var.get, denote_call, dotFn_apply,
    CmpOp.charge]
  have hd := dotFn_cost row row W W hl hr hr
  have hbd := bits_dotL_le row row W W hl hr hr
  have h1 : (W + W + 10) ^ 2 ≤ (10 * 10) * (W + 1) ^ 2 := sq_le_of (by omega)
  have h2 : 4 * (W + 1) * (W + W + 10) ^ 2 ≤ 400 * (W + 1) ^ 3 := by
    calc _ ≤ 4 * (W + 1) * ((10 * 10) * (W + 1) ^ 2) := Nat.mul_le_mul_left _ h1
      _ = 400 * (W + 1) ^ 3 := by ring
  have p13 : W + 1 ≤ (W + 1) ^ 3 := by
    simpa using pow_mono_one (show 1 ≤ W + 1 by omega) 1 3 (by norm_num)
  dsimp only [Ty.denote] at hd hbd ⊢
  simp only [bits_zero]
  omega

theorem sepL_mem {k2 : ℤ} {A : List (List ℤ)} {b c : List ℤ} {row : List ℤ}
    (h : sepL k2 A b c = some row) : row ∈ A := by
  unfold sepL at h
  obtain ⟨rb, hrb, rfl⟩ := Option.map_eq_some_iff.mp h
  exact (List.of_mem_zip (List.mem_of_find?_eq_some hrb)).1

/-- One round costs `O((W+1)^4)`. -/
theorem stepFn_cost (N k W : ℕ) (A : List (List ℤ)) (b : List ℤ)
    (code fuel : ℤ) (c : List ℤ) (S : List (List ℤ))
    (hNW : N ≤ W) (hkW : k + 1 ≤ W) (hAl : A.length ≤ W) (hrows : ∀ row ∈ A, row.length ≤ N)
    (hA : ∀ row ∈ A, ∀ x ∈ row, bits x ≤ W) (hb : ∀ x ∈ b, bits x ≤ W)
    (hcode : bits code ≤ W) (hfuel : bits fuel ≤ W)
    (hc : c.length ≤ N) (hS : S.length ≤ N) (hSr : ∀ row ∈ S, row.length ≤ N)
    (bc : ∀ x ∈ c, bits x ≤ W) (bS : ∀ row ∈ S, ∀ x ∈ row, bits x ≤ W) :
    stepFn.costAt (((N : ℤ), (2 : ℤ) ^ k, A, b), (code, fuel, c, S)) ≤ 2 ^ 61 * (W + 1) ^ 4 := by
  have hk2 : bits ((2 : ℤ) ^ k) ≤ W := by rw [bits_pow_two]; omega
  have hsep := sepFn_cost ((2 : ℤ) ^ k) A b c W hk2 hAl (fun r hr => le_trans (hrows r hr) hNW)
    hA hb bc
  have p34 : (W + 1) ^ 3 ≤ (W + 1) ^ 4 := pow_mono_one (by omega) 3 4 (by norm_num)
  have p14 : W + 1 ≤ (W + 1) ^ 4 := by
    simpa using pow_mono_one (show 1 ≤ W + 1 by omega) 1 4 (by norm_num)
  unfold Fn.costAt stepFn
  simp only [Expr.cost, cost_call, Var.index, Expr.denote, Var.get, denote_call, sepFn_apply,
    CmpOp.charge, CmpOp.eval]
  by_cases h0 : code = 0
  · simp only [h0, decide_true, ite_true, bits_zero]
    cases hs : sepL ((2 : ℤ) ^ k) A b c with
    | none =>
      simp only [Option.toList_none]
      dsimp only [Ty.denote] at hsep ⊢
      simp only [Nat.reduceAdd, Nat.zero_add, Nat.add_zero]
      omega
    | some row =>
      have hrow := sepL_mem hs
      have hz := zeroFn_cost row W (hA row hrow) (le_trans (hrows row hrow) hNW)
      simp only [Option.toList_some, foundE, Expr.cost, cost_call, Var.index, Expr.denote,
        Var.get, denote_call, zeroFn_apply, CmpOp.charge, CmpOp.eval, IntOp.charge, negFn_apply]
      have p1 : 1 ≤ (W + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
      have hb0 : bits (0 : Ty.int.denote) = 0 := bits_zero
      split_ifs with hz0 hf0
      · linarith
      · linarith
      · have hu := updFn_cost N k W c (row.map (fun x => -x)) S hNW hkW hc hS hSr
          (by simp; exact hrows row hrow) bc bS (fun x hx => by
            obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
            rw [bits_neg]; exact hA row hrow y hy)
        have hn := negFn_cost row W (hA row hrow)
        have hrl : row.length + 1 ≤ W + 1 := by have := hrows row hrow; omega
        have hn' : (row.length + 1) * (W + 30) ≤ (W + 1) * (30 * (W + 1)) :=
          Nat.mul_le_mul hrl (by omega)
        have e : (W + 1) * (30 * (W + 1)) = 30 * (W + 1) ^ 2 := by ring
        have p24 : (W + 1) ^ 2 ≤ (W + 1) ^ 4 := pow_mono_one (by omega) 2 4 (by norm_num)
        have h1 : bits (1 : ℤ) = 1 := by decide
        rw [h1]
        linarith
  · simp only [h0, decide_false, Bool.false_eq_true, ite_false]
    have p1 : 1 ≤ (W + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
    have hb0 : bits (0 : Ty.int.denote) = 0 := bits_zero
    have : (2 : ℕ) ^ 61 * (W + 1) ^ 4 ≥ 2 ^ 61 * (W + 1) := Nat.mul_le_mul_left _ p14
    linarith

/-! ## The whole loop along the trajectory -/

open AlgorithmEllipsoid AlgorithmPrecision

theorem centerNumerator_bits_le {n : ℕ} (s : State n) (i : Fin n) :
    bits (s.centerNumerator i) ≤ payloadBits s := by
  unfold payloadBits bits
  have := Finset.single_le_sum (f := fun i => 1 + (s.centerNumerator i).natAbs.size)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  omega

theorem shapeNumerator_bits_le {n : ℕ} (s : State n) (i j : Fin n) :
    bits (s.shapeNumerator i j) ≤ payloadBits s := by
  unfold payloadBits bits
  have h1 := Finset.single_le_sum (f := fun j => 1 + (s.shapeNumerator i j).natAbs.size)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have h2 := Finset.single_le_sum (f := fun i => ∑ j, (1 + (s.shapeNumerator i j).natAbs.size))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  omega

theorem mem_vecE {n : ℕ} {v : Fin n → ℤ} {x : ℤ} (h : x ∈ vecE v) : ∃ i, v i = x :=
  List.mem_ofFn.mp h

theorem mem_matE {m n : ℕ} {M : Fin m → Fin n → ℤ} {row : List ℤ} (h : row ∈ matE M) :
    ∃ i, vecE (M i) = row :=
  List.mem_ofFn.mp h

theorem bits_le_natAbs_bound (x : ℤ) (B : ℕ) (h : x.natAbs ≤ B) : bits x ≤ B :=
  le_trans (bits_le_self_natAbs x) h

/-- The complete loop costs at most `2^63 (W + 1)^5`, where `W` bounds the row count,
the grid exponent, the input bit lengths and the stored-payload bound of
`trajectory_payloadBits`. -/
theorem loopFn_cost {m n : ℕ} (hn : 2 ≤ n) (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ)
    (T B W : ℕ)
    (hW : n * (precision n T + 2 * T + B + 3) + n ^ 2 * (precision n T + 2 * T + 2 * B + 2) ≤ W)
    (hm : m ≤ W) (hk : precision n T + 1 ≤ W)
    (hA : ∀ i j, bits (A i j) ≤ W) (hb : ∀ i, bits (b i) ≤ W) :
    loopFn.costAt (((n : ℤ), (2 : ℤ) ^ precision n T, matE A, vecE b),
      (0, (T : ℤ), encSt (initial n (precision n T) B))) ≤ 2 ^ 63 * (W + 1) ^ 5 := by
  set k := precision n T with hkdef
  have hnW : n ≤ W := by
    have : n ≤ n * (k + 2 * T + B + 3) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hTW : T + 1 ≤ W := by have : 2 * T ≤ k := by rw [hkdef]; unfold precision; omega
                             omega
  have h3W : 3 ≤ W := by have : 32 ≤ k := by rw [hkdef]; unfold precision; omega
                         omega
  set env : Env [.prod ParTy StTy] := ((((n : ℤ), (2 : ℤ) ^ k, matE A, vecE b),
      (0, (T : ℤ), encSt (initial n k B))), ()) with henv
  have hstep : ∀ st : StTy.denote,
      (call stepFn (.pair (.fst v1) v0) : Expr [StTy, .prod ParTy StTy] StTy).denote (st, env) =
        stepL n (2 ^ k) (matE A) (vecE b) st := by
    intro st; simp [Expr.denote, Var.get, henv]
  have hit := cost_iter_le_prefix (Γ := [.prod ParTy StTy])
    (.arith .add (.fst (.snd (.snd v0))) (.int 1)) (.snd v0)
    (call stepFn (.pair (.fst v1) v0)) env (2 ^ 61 * (W + 1) ^ 4 + 20) (by
      intro j _
      have hf : (fun st => (call stepFn (.pair (.fst v1) v0) :
          Expr [StTy, .prod ParTy StTy] StTy).denote (st, env)) = stepL n (2 ^ k) (matE A) (vecE b) :=
        funext hstep
      rw [hf]
      have hinit : (Expr.snd v0 : Expr [.prod ParTy StTy] StTy).denote env =
          (0, (T : ℤ), encSt (initial n k B)) := by simp [Expr.denote, Var.get, henv]
      rw [hinit]
      obtain ⟨t, ht, code, fuel, hc0, hc3, hf0, hfT, -, he⟩ := loop_reach A b k hn T (initial n k B) j
      rw [he]
      set s := AlgorithmTrajectory.trajectory A b k (inflation n) (initial n k B) t
      have hpay : payloadBits s ≤ W :=
        le_trans (AlgorithmStateBounds.trajectory_payloadBits hn A b B T t ht) (by rw [← hkdef]; exact hW)
      have hsc := stepFn_cost n k W (matE A) (vecE b) code fuel (encSt s).1 (encSt s).2
        hnW (by omega) (by simp [matE]; omega)
        (fun row hr => by obtain ⟨i, rfl⟩ := mem_matE hr; simp [vecE])
        (fun row hr x hx => by
          obtain ⟨i, rfl⟩ := mem_matE hr
          obtain ⟨j, rfl⟩ := mem_vecE hx
          exact hA i j)
        (fun x hx => by obtain ⟨i, rfl⟩ := mem_vecE hx; exact hb i)
        (bits_le_natAbs_bound _ _ (by omega)) (bits_le_natAbs_bound _ _ (by omega))
        (by simp [encSt, vecE]) (by simp [encSt, matE])
        (fun row hr => by obtain ⟨i, rfl⟩ := mem_matE hr; simp [vecE])
        (fun x hx => by
          obtain ⟨i, rfl⟩ := mem_vecE hx
          exact le_trans (centerNumerator_bits_le s i) hpay)
        (fun row hr x hx => by
          obtain ⟨i, rfl⟩ := mem_matE hr
          obtain ⟨j, rfl⟩ := mem_vecE hx
          exact le_trans (shapeNumerator_bits_le s i j) hpay)
      simp only [Expr.cost, cost_call, Var.index, Expr.denote, Var.get, henv]
      simp only [Nat.reduceAdd, Nat.zero_add]
      linarith)
  unfold Fn.costAt loopFn
  refine le_trans hit ?_
  simp only [Expr.cost, Var.index, Expr.denote, Var.get, henv, IntOp.eval, IntOp.charge]
  have hT1 : ((T : ℤ) + 1).toNat = T + 1 := by omega
  rw [hT1]
  have hb1 : bits ((T : ℤ) + 1) ≤ W := bits_le_natAbs_bound _ _ (by omega)
  have hbT : bits (T : ℤ) ≤ W := bits_le_natAbs_bound _ _ (by omega)
  have hone : bits (1 : ℤ) = 1 := by decide
  rw [hone]
  have p45 : (W + 1) ^ 4 ≤ (W + 1) ^ 5 := pow_mono_one (by omega) 4 5 (by norm_num)
  have p15 : W + 1 ≤ (W + 1) ^ 4 := by
    simpa using pow_mono_one (show 1 ≤ W + 1 by omega) 1 4 (by norm_num)
  have hmain : (T + 1) * (2 ^ 61 * (W + 1) ^ 4 + 20 + bits ((T : ℤ) + 1) + 1) ≤
      (W + 1) * (2 ^ 62 * (W + 1) ^ 4) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e : (W + 1) * (2 ^ 62 * (W + 1) ^ 4) = 2 ^ 62 * (W + 1) ^ 5 := by ring
  have p1 : 1 ≤ (W + 1) ^ 5 := Nat.one_le_pow _ _ (by omega)
  have p15' : W + 1 ≤ (W + 1) ^ 5 := le_trans p15 p45
  omega

end MWIS.FunLP

end
