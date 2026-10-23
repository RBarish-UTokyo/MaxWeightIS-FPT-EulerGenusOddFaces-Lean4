module

public import MWIS.FunCoordinatesCostElim

/-!
# Cost of the elimination program

Removed rows of the elimination vanish, so every state reached from `columnState` has
entries at most `2` in absolute value. With this, the encoded face matrix, the non-tree
flags and the `f` elimination rounds of `freeFn` cost at most `K * N ^ 5` when `N ≥ 5`
bounds the numbers of vertices, edges and face rows.
-/

@[expose] public section

namespace MWIS.FunCoordinates

open MWIS.Fun MWIS.FunLP MWIS.TreeCotree

variable {f m : ℕ}

/-! ## Removed rows vanish -/

/-- Every removed row is zero. -/
def Dead (S : ElimState f m) : Prop := ∀ r ∉ S.rows, ∀ e, S.M r e = 0

theorem dead_pivotAt {S : ElimState f m} (hD : Dead S) {r : Fin f} {c : Fin m}
    (hs : S.M r c = 1 ∨ S.M r c = -1) : Dead (S.pivotAt r c) := by
  intro r' hr' e
  simp only [ElimState.pivotAt, Finset.mem_erase, not_and_or, not_not] at hr' ⊢
  by_cases h : r' = r
  · subst h
    have h1 := ElimState.unit_sq hs
    have : S.M r' c * S.M r' c * S.M r' e = S.M r' e := by rw [h1, one_mul]
    rw [this, sub_self]
  · have hr'' : r' ∉ S.rows := by tauto
    rw [hD r' hr'' e, hD r' hr'' c]
    ring

theorem dead_halve {S : ElimState f m} (hD : Dead S) {r : Fin f} (hr : r ∈ S.rows) :
    Dead (S.halve r) := by
  intro r' hr' e
  simp only [ElimState.halve] at hr' ⊢
  have : r' ≠ r := fun h => hr' (h ▸ hr)
  rw [ite_eq_right_iff.mpr (fun h => absurd h this)]
  exact hD r' hr' e

theorem step_eq_halve {S : ElimState f m} {r : Fin f} (hu : S.unitAt = none)
    (hn : S.nonzeroRow = some r) (hc : (S.halve r).unitIn r = none) : S.step = S.halve r := by
  simp only [ElimState.step, hu, hn, hc]

theorem dead_step {S : ElimState f m} (hD : Dead S) : Dead S.step := by
  cases hu : S.unitAt with
  | some p =>
    obtain ⟨r, c⟩ := p
    obtain ⟨_, hc⟩ := ElimState.unitAt_some hu
    rw [ElimState.step_eq_pivot hu]
    exact dead_pivotAt hD (ElimState.unitIn_some hc).2
  | none =>
    cases hn : S.nonzeroRow with
    | none => rw [ElimState.step_eq_self hu hn]; exact hD
    | some r =>
      have hr := (ElimState.nonzeroRow_some hn).1
      cases hc : (S.halve r).unitIn r with
      | none => rw [step_eq_halve hu hn hc]; exact dead_halve hD hr
      | some c =>
        rw [ElimState.step_eq_halve_pivot hu hn hc]
        exact dead_pivotAt (dead_halve hD hr) (ElimState.unitIn_some hc).2

theorem entries_iterate (C : Fin m → Walks.Column (Fin f)) (A : Finset (Fin m)) (k : ℕ)
    (r : Fin f) (e : Fin m) : |(ElimState.step^[k] (columnState C A)).M r e| ≤ 2 := by
  have hI := (ElimState.iterate_progress (columnState_inv C A) k).1
  have hD : Dead (ElimState.step^[k] (columnState C A)) := by
    induction k with
    | zero => intro r hr; simp [columnState] at hr
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact dead_step (ih (ElimState.iterate_progress (columnState_inv C A) k).1)
  by_cases hr : r ∈ (ElimState.step^[k] (columnState C A)).rows
  · exact ElimState.entry_abs_le hI hr e
  · rw [hD r hr e]; simp

theorem smallSt_encS {N : ℕ} (S : ElimState f m) (hM : ∀ r e, |S.M r e| ≤ 2) (hf : f ≤ N)
    (hm : m ≤ N) : SmallSt N (encS S) := by
  refine ⟨by simpa [encS] using hf, by simpa [encS] using hm, by simpa [encS] using hf, ?_⟩
  intro row hrow
  simp only [encS, List.mem_ofFn] at hrow
  obtain ⟨r, rfl⟩ := hrow
  refine ⟨by simpa using hm, ?_⟩
  intro x hx
  simp only [List.mem_ofFn] at hx
  obtain ⟨e, rfl⟩ := hx
  exact hM r e

/-! ## The face matrix -/

variable {N : ℕ}

theorem stubVal_abs (r c : ℤ) : |stubVal r c| ≤ 1 := by
  unfold stubVal
  split_ifs <;> simp

theorem colVal_take_abs (codes : List ℤ) (r : ℤ) (j : ℕ) :
    |(codes.take j).foldl (fun acc c => acc + stubVal r c) 0| ≤ j := by
  have key : ∀ (l : List ℤ) (a : ℤ), |l.foldl (fun acc c => acc + stubVal r c) a| ≤ |a| + l.length := by
    intro l
    induction l with
    | nil => intro a; simp
    | cons c l ih =>
      intro a
      rw [List.foldl_cons]
      refine (ih _).trans ?_
      have := abs_add_le a (stubVal r c)
      have := stubVal_abs r c
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      linarith
  refine (key _ 0).trans ?_
  simp only [abs_zero, zero_add, Nat.cast_le]
  exact List.length_take_le _ _

theorem sq_bound {a N : ℕ} (ha : a ≤ N) (hN : 1 ≤ N) : (a + 2 + 1) ^ 2 ≤ 16 * N ^ 2 := by
  nlinarith

theorem bits_ite3 (p q : Prop) [Decidable p] [Decidable q] :
    bits (if p then (if q then (1 : ℤ) else -1) else 0) ≤ 1 := by
  split_ifs <;> simp

theorem stubValE_denote (c acc : ℤ) (x : (Ty.prod (.list .int) .int).denote) :
    stubValE.denote (c, acc, (x, ())) = stubVal x.2 c := by
  by_cases h1 : (c - 1) / 2 = x.2 <;> by_cases h2 : (c - 1) % 2 = 1 <;>
    simp [stubValE, stubVal, Expr.denote, Var.get, IntOp.eval, CmpOp.eval, h1, h2]

theorem bits_stubVal (r c : ℤ) : bits (stubVal r c) ≤ 1 := by
  unfold stubVal
  split_ifs <;> simp

theorem stubValE_cost (hN : 5 ≤ N) (c acc : ℤ) (x : (Ty.prod (.list .int) .int).denote)
    (hc1 : 1 ≤ c) (hc2 : c ≤ 4 * N) (hr : bits x.2 ≤ N) :
    stubValE.cost (c, acc, (x, ())) ≤ 60 * N ^ 2 := by
  have hN1 : 1 ≤ N := by omega
  have b2 : bits (c - 1) ≤ N := bits_small hN (by rw [abs_of_nonneg (by omega)]; omega)
  have b3 : bits ((c - 1) / 2) ≤ N := bits_small hN (by
    rw [abs_of_nonneg (Int.ediv_nonneg (by omega) (by norm_num))]; omega)
  have b4 : bits ((c - 1) % 2) ≤ 1 := by
    have h0 := Int.emod_nonneg (c - 1) (show (2 : ℤ) ≠ 0 by norm_num)
    have h1 := Int.emod_lt_of_pos (c - 1) (show (0 : ℤ) < 2 by norm_num)
    have : (c - 1) % 2 = 0 ∨ (c - 1) % 2 = 1 := by omega
    rcases this with h | h <;> rw [h] <;> simp
  have b1 : bits c ≤ N := bits_small hN (by rw [abs_of_pos (by omega)]; exact hc2)
  have s1 := sq_bound b2 hN1
  have p1 := pow_mono hN1 (show 1 ≤ 2 by norm_num)
  have p2 := const_le_pow hN1 40 2
  simp only [pow_one] at p1
  simp only [stubValE, Expr.cost, Var.index, IntOp.charge, CmpOp.charge]
  repeat' split
  all_goals (try simp only [Expr.denote, Var.get, IntOp.eval, bits_one', bits_two', bits_zero',
    bits_neg_one'] at *)
  all_goals omega

theorem stubStep_cost (hN : 5 ≤ N) (c acc : ℤ) (x : (Ty.prod (.list .int) .int).denote)
    (hc1 : 1 ≤ c) (hc2 : c ≤ 4 * N) (hacc : |acc| ≤ 1) (hr : bits x.2 ≤ N) :
    (Expr.arith (Γ := [.int, .int, .prod (.list .int) .int]) .add v1 stubValE).cost
      (c, acc, (x, ())) ≤ 70 * N ^ 2 := by
  have hN1 : 1 ≤ N := by omega
  have h1 := stubValE_cost hN c acc x hc1 hc2 hr
  have h2 := bits_stubVal x.2 c
  have h3 := bits_le_two (show |acc| ≤ 2 by linarith)
  have p2 := const_le_pow hN1 10 2
  have h4 : bits (stubValE.denote (c, acc, (x, ()))) ≤ 1 := by rw [stubValE_denote]; exact h2
  simp only [Expr.cost, Var.index, IntOp.charge, Expr.denote, Var.get]
  omega

theorem colValFn_cost (hN : 5 ≤ N) (codes : List ℤ) (r : ℤ) (hl : codes.length ≤ 2)
    (hc : ∀ c ∈ codes, 1 ≤ c ∧ c ≤ 4 * N) (hr : bits r ≤ N) :
    colValFn.costAt (codes, r) ≤ 150 * N ^ 2 := by
  have hN1 : 1 ≤ N := by omega
  have hs : (fun acc y => (Expr.arith (Γ := [.int, .int, .prod (.list .int) .int]) .add v1
      stubValE).denote (y, acc, ((codes, r), ()))) = fun acc c => acc + stubVal r c := by
    funext acc c
    simp only [Expr.denote, Var.get, IntOp.eval]
    rw [stubValE_denote]
  have h := cost_foldl_le_prefix (Γ := [.prod (.list .int) .int]) (.fst v0) (.int 0)
    (.arith .add v1 stubValE) ((codes, r), ()) (70 * N ^ 2) (by
      intro j hj
      have hj' : j < codes.length := hj
      change (Expr.arith (Γ := [.int, .int, .prod (.list .int) .int]) .add v1 stubValE).cost
        (codes[j], (codes.take j).foldl (fun acc y => (Expr.arith (Γ := [.int, .int,
          .prod (.list .int) .int]) .add v1 stubValE).denote (y, acc, ((codes, r), ()))) 0,
            ((codes, r), ())) ≤ _
      rw [hs]
      have ha := colVal_take_abs codes r j
      exact stubStep_cost hN _ _ (codes, r) (hc _ (List.getElem_mem hj')).1
        (hc _ (List.getElem_mem hj')).2 (by
          have : (j : ℤ) ≤ 1 := by omega
          linarith) hr)
  change (Expr.foldl (Γ := [.prod (.list .int) .int]) (.fst v0) (.int 0)
    (.arith .add v1 stubValE)).cost ((codes, r), ()) ≤ _
  change _ ≤ 2 + 1 + codes.length * (70 * N ^ 2 + 1) + 1 at h
  have p := const_le_pow hN1 10 2
  have : codes.length * (70 * N ^ 2 + 1) ≤ 2 * (70 * N ^ 2 + 1) := Nat.mul_le_mul_right _ hl
  omega

/-- Encoded columns: at most two codes, each in `[1, 4N]`. -/
def ColsOK (N : ℕ) (cols : List (List ℤ)) : Prop :=
  cols.length ≤ N ∧ ∀ codes ∈ cols, codes.length ≤ 2 ∧ ∀ c ∈ codes, 1 ≤ c ∧ c ≤ 4 * N

theorem entryItem_cost (hN : 5 ≤ N) (act : List Bool) (r : ℤ) (kc : ℤ × List ℤ)
    (hl : act.length ≤ N) (hr : bits r ≤ N) (hk : bits kc.1 ≤ N) (hc1 : kc.2.length ≤ 2)
    (hc2 : ∀ c ∈ kc.2, 1 ≤ c ∧ c ≤ 4 * N) :
    entryItem.costAt ((act, r), kc) ≤ 260 * N ^ 2 := by
  have hN1 : 1 ≤ N := by omega
  have h1 := getBoolFn_costN hN1 act kc.1 hl hk
  have h2 := colValFn_cost hN kc.2 r hc1 hc2 hr
  have p := const_le_pow hN1 20 2
  rw [Fn.costAt]
  simp only [entryItem, Expr.cost, cost_call, Var.index]
  repeat' split
  all_goals (try simp only [Expr.denote, Var.get] at *)
  all_goals omega

theorem rowFn_cost (hN : 5 ≤ N) (act : List Bool) (cols : List (List ℤ)) (r : ℤ)
    (hl : act.length ≤ N) (hc : ColsOK N cols) (hr : bits r ≤ N) :
    rowFn.costAt ((act, cols), r) ≤ 620 * N ^ 3 := by
  have hN1 : 1 ≤ N := by omega
  have h := mapIdxFn_costN entryItem (act, r) cols (K := 260) (d := 2) hN1 (by norm_num) hc.1
    (fun j hj => entryItem_cost hN act r _ hl hr (bits_index hN1 (by have := hc.1; omega))
      (hc.2 _ (List.getElem_mem hj)).1 (hc.2 _ (List.getElem_mem hj)).2)
  simp only [Nat.reduceAdd] at h
  have p := const_le_pow hN1 20 3
  rw [Fn.costAt]
  simp only [rowFn, Expr.cost, cost_call, Var.index, Expr.denote, Var.get]
  omega

theorem matrixFn_cost (hN : 5 ≤ N) (act : List Bool) (cols : List (List ℤ)) (f : ℕ)
    (hl : act.length ≤ N) (hc : ColsOK N cols) (hf : f ≤ N) :
    matrixFn.costAt (act, (cols, (f : ℤ))) ≤ 1400 * N ^ 4 := by
  have hN1 : 1 ≤ N := by omega
  have h1 := crange_costN hN1 f hf (bits_nat_small hN (by omega))
  have h2 := cmapFn_costN rowFn (act, cols) ((List.range f).map fun i : ℕ => (i : ℤ)) (K := 620)
    (d := 3) hN1 (by norm_num) (by simpa using hf) (fun r hr => by
      simp only [List.mem_map, List.mem_range] at hr
      obtain ⟨i, hi, rfl⟩ := hr
      exact rowFn_cost hN act cols _ hl hc (bits_index hN1 (by omega)))
  simp only [Nat.reduceAdd] at h2
  have p1 := pow_mono hN1 (show 2 ≤ 4 by norm_num)
  have p := const_le_pow hN1 20 4
  rw [Fn.costAt]
  simp only [matrixFn, Expr.cost, cost_call, Var.index, Expr.denote, Var.get, denote_call,
    crange_apply, Int.toNat_natCast]
  omega

theorem actInitFn_cost (hN : 5 ≤ N) (T edges : List (ℤ × ℤ)) (hT : T.length ≤ N)
    (he : edges.length ≤ N) (hb : ∀ y ∈ T, bits y.2 ≤ N) :
    actInitFn.costAt (T, edges) ≤ 200 * N ^ 3 := by
  have hN1 : 1 ≤ N := by omega
  have h1 := cmapFn_costN (trueFn (.prod .int .int)) () edges (K := 1) (d := 1) hN1 le_rfl he
    (fun _ _ => by rw [Fn.costAt]; simp [trueFn, Expr.cost]; omega)
  simp only [Nat.reduceAdd] at h1
  rw [Fn.costAt]
  have h := cost_foldl_le (Γ := [.prod (.list (.prod .int .int)) (.list (.prod .int .int))])
    (.fst v0) (call (cmapFn (trueFn (.prod .int .int))) (.pair .unit (.snd v0)))
    (call clearFn (.pair (.snd v0) v1)) ((T, edges), ()) (fun acc => acc.length ≤ N)
    (130 * N ^ 2 + 10) (by simp [Expr.denote, Var.get, he]) (fun acc y hy hacc => by
      have hy' : y ∈ T := hy
      refine ⟨?_, ?_⟩
      · simp only [Expr.denote, Var.get, denote_call, clearFn_apply, clearS, List.length_mapIdx]
        exact hacc
      · simp only [Expr.cost, cost_call, Var.index, Expr.denote, Var.get]
        have := clearFn_costN hN1 y.2 acc (hb y hy') hacc
        omega)
  have hlen : ((Expr.fst (Γ := [.prod (.list (.prod .int .int)) (.list (.prod .int .int))]) v0).denote
    ((T, edges), ())).length ≤ N := hT
  refine h.trans ?_
  simp only [Expr.cost, cost_call, Var.index, Expr.denote, Var.get] at hlen ⊢
  have p1 := pow_mono hN1 (show 2 ≤ 3 by norm_num)
  have p := const_le_pow hN1 20 3
  have : T.length * (130 * N ^ 2 + 10 + 1) ≤ N * (130 * N ^ 2 + 11) := Nat.mul_le_mul_right _ hT
  have : N * (130 * N ^ 2 + 11) = 130 * N ^ 3 + 11 * N := by ring
  have : N ≤ N ^ 3 := by simpa using pow_mono hN1 (show 1 ≤ 3 by norm_num)
  omega

/-! ## The elimination program on the encoded face columns -/

theorem elimInit_denote (x : ElimArg.denote) :
    elimInit.denote (actInitFn.apply (x.1, x.2.1), (x, ())) = initS x := by
  simp only [elimInit, Expr.denote, Var.get, denote_call, cmapFn_apply', crange_apply,
    List.map_map, actInitFn_apply, matrixFn_apply]
  rfl

theorem elimStep_fun {Γ : List Ty} (env : Env Γ) :
    (fun st => (call (Γ := ElimTy :: Γ) elimStepFn v0).denote (st, env)) = stepS := by
  funext st
  simp only [denote_call, Expr.denote, Var.get, elimStepFn_apply]

variable {n : ℕ} (left right : Fin m → Fin n) (C : Fin m → Walks.Column (Fin f))

theorem tree_length_lt (root : Fin n) (k : ℕ) :
    ((TreeCotree.grow left right root)^[k] []).length < n :=
  (TreeCotree.grow_progress left right root k).1.length_lt left right

theorem treeCode_length (root : Fin n) : (treeCode (tree left right root)).length ≤ n := by
  have := tree_length_lt left right root n
  simp only [treeCode, List.length_map]
  exact le_of_lt this

theorem treeCode_snd (root : Fin n) (hN : 1 ≤ N) (hm : m ≤ N) :
    ∀ y ∈ treeCode (tree left right root), bits y.2 ≤ N := by
  intro y hy
  simp only [treeCode, List.mem_map] at hy
  obtain ⟨p, _, rfl⟩ := hy
  exact bits_index hN (by have := p.2.2; omega)

theorem colList_ok (hN : 1 ≤ N) (hf : f ≤ N) (hm : m ≤ N) : ColsOK N (colList C) := by
  refine ⟨by simpa [colList] using hm, ?_⟩
  intro codes hc
  simp only [colList, List.mem_ofFn] at hc
  obtain ⟨e, rfl⟩ := hc
  have hs : ∀ s : Walks.Stub (Fin f), 1 ≤ stubCodeC s ∧ stubCodeC s ≤ 4 * N := by
    rintro ⟨k, b⟩
    have := k.2
    unfold stubCodeC
    cases b <;> simp <;> omega
  cases C e with
  | zero => simp [columnCodeC]
  | one s => simpa [columnCodeC] using hs s
  | two s t =>
    refine ⟨by simp [columnCodeC], ?_⟩
    intro c hc
    simp only [columnCodeC, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact hs s
    · exact hs t

/-- **Cost of the elimination program.** -/
theorem freeFn_cost (hN : 5 ≤ N) (hm : m ≤ N) (hn : n ≤ N) (hf : f ≤ N) (root : Fin n) :
    freeFn.costAt (treeCode (tree left right root), (edgeList left right, (colList C, (f : ℤ)))) ≤
      9000 * N ^ 5 := by
  have hN1 : 1 ≤ N := by omega
  have p1 := pow_mono hN1 (show 2 ≤ 5 by norm_num)
  have p2 := pow_mono hN1 (show 3 ≤ 5 by norm_num)
  have p3 := pow_mono hN1 (show 4 ≤ 5 by norm_num)
  have p4 := const_le_pow hN1 100 5
  have p5 : N ≤ N ^ 5 := by simpa using pow_mono hN1 (show 1 ≤ 5 by norm_num)
  set x : ElimArg.denote :=
    (treeCode (tree left right root), (edgeList left right, (colList C, (f : ℤ)))) with hx
  have hT := treeCode_length left right root
  have hE : (edgeList left right).length ≤ N := by simpa [edgeList] using hm
  have kA := actInitFn_cost hN x.1 x.2.1 (le_trans hT hn) hE (treeCode_snd left right root hN1 hm)
  rw [Fn.costAt, freeFn]
  refine (cost_letE_le _ _ _ (fun act => act = actInitFn.apply (x.1, x.2.1))
    (A := 200 * N ^ 3 + 20) (B := 8000 * N ^ 5) ?_ ?_ ?_).trans (by omega)
  · simp only [Expr.cost, cost_call, Var.index, Expr.denote, Var.get]
    omega
  · simp only [Expr.denote, Var.get, denote_call]
  intro act hact
  subst hact
  have hlen : (actInitFn.apply (x.1, x.2.1)).length ≤ N := by
    have h := congrArg (fun st : List Bool × List Bool × List (List ℤ) => st.2.1.length)
      (elimInit_denote x)
    simp only [elimInit, Expr.denote, Var.get] at h
    rw [h, hx, initS_eq]
    simpa [encS] using hm
  have kI1 := crange_costN hN1 f hf (bits_nat_small hN (by omega))
  have kI2 := cmapFn_costN (trueFn .int) () ((List.range f).map fun i : ℕ => (i : ℤ)) (K := 1)
    (d := 1) hN1 le_rfl (by simpa using hf) (fun _ _ => by
      rw [Fn.costAt]; simp [trueFn, Expr.cost]; omega)
  have kI3 := matrixFn_cost hN (actInitFn.apply (x.1, x.2.1)) (colList C) f hlen
    (colList_ok C hN1 hf hm) hf
  simp only [Nat.reduceAdd] at kI2
  have hit := cost_iter_le_prefix (Γ := [.list .bool, ElimArg]) (.snd (.snd (.snd v1))) elimInit
    (call elimStepFn v0) (actInitFn.apply (x.1, x.2.1), (x, ())) (6000 * N ^ 4 + 5) (by
      intro j _
      rw [elimStep_fun, elimInit_denote, hx, initS_eq, iterate_stepS_enc]
      simp only [cost_call, Expr.cost, Var.index, Expr.denote, Var.get]
      have := elimStepFn_costN hN1 _ (smallSt_encS _ (entries_iterate C (nonTree left right root) j) hf hm)
      omega)
  have hInit : elimInit.cost (actInitFn.apply (x.1, x.2.1), (x, ())) ≤ 1600 * N ^ 4 := by
    simp only [elimInit, Expr.cost, cost_call, Var.index, Expr.denote, Var.get, denote_call,
      crange_apply]
    rw [hx] at kI3 ⊢
    simp only [Int.toNat_natCast] at kI1 kI2 kI3 ⊢
    have p6 := pow_mono hN1 (show 2 ≤ 4 by norm_num)
    have p7 := const_le_pow hN1 100 4
    omega
  have hcount : ((Expr.snd (Γ := [.list .bool, ElimArg]) (.snd (.snd v1))).denote
      (actInitFn.apply (x.1, x.2.1), (x, ()))) = (f : ℤ) := by
    simp only [Expr.denote, Var.get, hx]
  have hcc : (Expr.snd (Γ := [.list .bool, ElimArg]) (.snd (.snd v1))).cost
      (actInitFn.apply (x.1, x.2.1), (x, ())) = 5 := by
    simp [Expr.cost, Var.index]
  rw [hcount, hcc, Int.toNat_natCast] at hit
  have e1 : ∀ (e : Expr [.list .bool, ElimArg] ElimTy) env,
      (Expr.fst (Expr.snd e)).cost env = e.cost env + 1 + 1 := fun _ _ => rfl
  rw [e1]
  have hb := bits_nat_small (k := f) hN (by omega)
  have : f * (6000 * N ^ 4 + 5 + bits (f : ℤ) + 1) ≤ N * (6000 * N ^ 4 + 6 + N) :=
    Nat.mul_le_mul hf (by omega)
  have : N * (6000 * N ^ 4 + 6 + N) = 6000 * N ^ 5 + 6 * N + N ^ 2 := by ring
  omega

end MWIS.FunCoordinates

end
