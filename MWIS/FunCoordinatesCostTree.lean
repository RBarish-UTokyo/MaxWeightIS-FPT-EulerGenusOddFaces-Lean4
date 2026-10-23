module

public import MWIS.FunCoordinatesCostElim

/-!
# Cost of the spanning-tree search and of the tree potentials

When `N ≥ 5` bounds the numbers of vertices and edges, the tree search `treeFn` costs at most
`K * N ^ 4` and each tree potential `potFn` of a unit edge vector (or of zero, with root value
`±1`) costs at most `K * N ^ 3`.
-/

@[expose] public section

namespace MWIS.FunCoordinates

open MWIS.Fun MWIS.FunLP MWIS.TreeCotree

variable {N : ℕ}

theorem getI_mem_or {α : Type*} (l : List α) (d : α) (i : ℤ) : getI l d i ∈ l ∨ getI l d i = d := by
  unfold getI
  split_ifs
  · rw [List.getD_eq_getElem?_getD]
    cases hx : l[i.toNat]? with
    | none => right; rfl
    | some x => left; exact List.mem_of_getElem? hx
  · right; rfl

/-- Integer pairs with both components of binary length at most `N`. -/
def PairsOK (N : ℕ) (l : List (ℤ × ℤ)) : Prop :=
  l.length ≤ N ∧ ∀ p ∈ l, bits p.1 ≤ N ∧ bits p.2 ≤ N

theorem PairsOK.getI {l : List (ℤ × ℤ)} (h : PairsOK N l) (i : ℤ) :
    bits (getI l (0, 0) i).1 ≤ N ∧ bits (getI l (0, 0) i).2 ≤ N := by
  rcases getI_mem_or l (0, 0) i with hm | hm
  · exact h.2 _ hm
  · rw [hm]; simp

/-! ## The search -/

theorem frontierPred_cost (hN : 1 ≤ N) (disc : List Bool) (lr : ℤ × ℤ) (hd : disc.length ≤ N)
    (h1 : bits lr.1 ≤ N) (h2 : bits lr.2 ≤ N) : frontierPred.costAt (disc, lr) ≤ 170 * N ^ 2 := by
  have k1 := getBoolFn_costN hN disc lr.1 hd h1
  have k2 := getBoolFn_costN hN disc lr.2 hd h2
  have p := const_le_pow hN 12 2
  rw [Fn.costAt]
  simp only [frontierPred, Expr.cost, cost_call, Var.index]
  repeat' split
  all_goals (try simp only [Expr.denote, Var.get] at *)
  all_goals omega

theorem setTrueFn_cost (hN : 1 ≤ N) (v : ℤ) (disc : List Bool) (hv : bits v ≤ N)
    (hd : disc.length ≤ N) : setTrueFn.costAt (v, disc) ≤ 130 * N ^ 2 := by
  show (mapIdxFn setTrueItem).costAt (v, disc) ≤ _
  have h := mapIdxFn_costN setTrueItem v disc (K := 20) (d := 1) hN le_rfl hd (fun j hj => by
    rw [Fn.costAt]
    simp only [setTrueItem, Expr.cost, Var.index, CmpOp.charge]
    have hj' := bits_index hN (show j < N by omega)
    rw [pow_one]
    repeat' split
    all_goals (try simp only [Expr.denote, Var.get] at *)
    all_goals omega)
  simp only [Nat.reduceAdd] at h
  omega

theorem searchStep_cost (hN : 1 ≤ N) (st : List Bool × List (ℤ × ℤ)) (arg : SearchArg.denote)
    (hd : st.1.length ≤ N) (he : PairsOK N arg.1) :
    searchStep.cost (st, (arg, ())) ≤ 850 * N ^ 3 := by
  have p1 := pow_mono hN (show 2 ≤ 3 by norm_num)
  have p2 := const_le_pow hN 40 3
  have p3 : N ≤ N ^ 3 := by simpa using pow_mono hN (show 1 ≤ 3 by norm_num)
  unfold searchStep
  refine (cost_letE_le _ _ _ (fun e : ℤ => bits e ≤ N) (A := 424 * N ^ 3 + 10)
    (B := 380 * N ^ 3) ?_ ?_ ?_).trans (by omega)
  · have h := findIdxFn_costN frontierPred st.1 arg.1 (K := 170) (d := 2) hN (by norm_num) he.1
      (fun lr hlr => frontierPred_cost hN st.1 lr hd (he.2 lr hlr).1 (he.2 lr hlr).2)
    simp only [Nat.reduceAdd] at h
    simp only [Expr.cost, cost_call, Var.index, Expr.denote, Var.get]
    omega
  · simp only [Expr.denote, Var.get, denote_call, findIdxFn_apply']
    exact bits_findIdx _ _ hN he.1
  intro e hbe
  refine (cost_ite_le _ _ _ _ (A := N + 5) (B := 370 * N ^ 3) ?_ ?_ ?_).trans (by omega)
  · exact (cost_ltZero _ _ (a := 2) (by simp [Expr.cost, Var.index]) hbe).trans (by omega)
  · intro _; simp only [Expr.cost, Var.index]; omega
  intro _
  refine (cost_letE_le _ _ _ (fun lr : ℤ × ℤ => bits lr.1 ≤ N ∧ bits lr.2 ≤ N)
    (A := 74 * N ^ 2 + 10) (B := 280 * N ^ 3) ?_ ?_ ?_).trans (by omega)
  · have := getPairFn_costN hN arg.1 e he.1 hbe
    simp only [Expr.cost, cost_call, Var.index, Expr.denote, Var.get]
    omega
  · simp only [Expr.denote, Var.get, denote_call, getPairFn_apply']
    exact he.getI e
  intro lr hlr
  refine (cost_letE_le _ _ _ (fun v : ℤ => bits v ≤ N)
    (A := 74 * N ^ 2 + 20) (B := 150 * N ^ 2 + 20) ?_ ?_ ?_).trans (by omega)
  · have := getBoolFn_costN hN st.1 lr.1 hd hlr.1
    simp only [Expr.cost, cost_call, Var.index]
    repeat' split
    all_goals (try simp only [Expr.denote, Var.get] at *)
    all_goals omega
  · simp only [Expr.denote, Var.get, denote_call]
    split
    · exact hlr.2
    · exact hlr.1
  intro v hv
  have := setTrueFn_cost hN v st.1 hv hd
  simp only [Expr.cost, cost_call, Var.index, Expr.denote, Var.get]
  omega

theorem searchStep_length (st : List Bool × List (ℤ × ℤ)) (arg : SearchArg.denote) :
    (searchStep.denote (st, (arg, ()))).1.length = st.1.length := by
  have := congrFun (searchStep_denote arg) st
  rw [this]
  unfold stepSpec
  dsimp only
  split_ifs <;> simp

variable {m n : ℕ} (left right : Fin m → Fin n)

theorem edgeList_ok (hN : 1 ≤ N) (hm : m ≤ N) (hn : n ≤ N) : PairsOK N (edgeList left right) := by
  refine ⟨by simpa [edgeList] using hm, ?_⟩
  intro p hp
  simp only [edgeList, List.mem_ofFn] at hp
  obtain ⟨e, rfl⟩ := hp
  exact ⟨bits_index hN (by have := (left e).2; omega), bits_index hN (by have := (right e).2; omega)⟩

theorem treeCode_tree_length (root : Fin n) : (treeCode (tree left right root)).length ≤ n := by
  simp only [treeCode, List.length_map]
  exact le_of_lt ((tree_good left right root).length_lt left right)

/-- **Cost of the spanning-tree search.** -/
theorem treeFn_cost (hN : 5 ≤ N) (hm : m ≤ N) (hn : n ≤ N) (root : Fin n) :
    treeFn.costAt (edgeList left right, ((n : ℤ), ((root : ℕ) : ℤ))) ≤ 1100 * N ^ 4 := by
  have hN1 : 1 ≤ N := by omega
  have he := edgeList_ok left right hN1 hm hn
  have p1 := pow_mono hN1 (show 2 ≤ 4 by norm_num)
  have p2 := pow_mono hN1 (show 3 ≤ 4 by norm_num)
  have p3 := const_le_pow hN1 40 4
  have p4 : N ≤ N ^ 4 := by simpa using pow_mono hN1 (show 1 ≤ 4 by norm_num)
  have p5 := const_le_pow hN1 1 2
  have p6 := const_le_pow hN1 1 3
  set arg : SearchArg.denote := (edgeList left right, ((n : ℤ), ((root : ℕ) : ℤ))) with harg
  have hit := cost_iter_le (Γ := [SearchArg]) (.fst (.snd v0)) searchInit searchStep (arg, ())
    (fun st => st.1.length ≤ N) (850 * N ^ 3) (by
      rw [searchInit_denote]; simp [harg]; omega)
    (fun st hst => ⟨by rw [searchStep_length]; exact hst, searchStep_cost hN1 st arg hst he⟩)
  have hinit : searchInit.cost (arg, ()) ≤ 140 * N ^ 2 := by
    have k1 := crange_costN hN1 n hn (bits_nat_small hN (by omega))
    have k2 := cmapFn_costN eqRootFn ((root : ℕ) : ℤ)
      ((List.range n).map fun i : ℕ => (i : ℤ)) (K := 8) (d := 1) hN1 le_rfl (by simpa using hn)
      (fun i hi => by
        simp only [List.mem_map, List.mem_range] at hi
        obtain ⟨i, hi, rfl⟩ := hi
        have b1 := bits_index hN1 (show i < N by omega)
        have b2 := bits_index hN1 (show (root : ℕ) < N by have := root.2; omega)
        rw [Fn.costAt]
        simp only [eqRootFn, Expr.cost, Var.index, CmpOp.charge, Expr.denote, Var.get, pow_one]
        omega)
    simp only [Nat.reduceAdd] at k2
    simp only [searchInit, Expr.cost, cost_call, Var.index, Expr.denote, Var.get, denote_call,
      crange_apply, harg, Int.toNat_natCast]
    omega
  have hval : ((Expr.snd (Expr.iter (Γ := [SearchArg]) (.fst (.snd v0)) searchInit
      searchStep)).denote (arg, ())).length ≤ N := by
    have h1 := treeFn_tree left right root
    rw [← harg, treeFn, Fn.apply, denote_call, crevFn_apply] at h1
    have h2 := congrArg List.length h1
    rw [List.length_reverse] at h2
    rw [h2]
    exact le_trans (treeCode_tree_length left right root) hn
  have hrev := crevFn_costN hN1 (.prod .int .int) _ hval
  have hcount : ((Expr.fst (Γ := [SearchArg]) (.snd v0)).denote (arg, ())) = (n : ℤ) := by
    simp [Expr.denote, Var.get, harg]
  rw [hcount, Int.toNat_natCast] at hit
  have hb := bits_nat_small (k := n) hN (by omega)
  have : n * (850 * N ^ 3 + bits (n : ℤ) + 1) ≤ N * (850 * N ^ 3 + N + 1) :=
    Nat.mul_le_mul hn (by omega)
  have : N * (850 * N ^ 3 + N + 1) = 850 * N ^ 4 + N ^ 2 + N := by ring
  rw [Fn.costAt, treeFn, cost_call]
  have e1 : ∀ (e : Expr [SearchArg] SearchState) env,
      (Expr.snd e).cost env = e.cost env + 1 := fun _ _ => rfl
  rw [e1]
  have hcc : (Expr.fst (Γ := [SearchArg]) (.snd v0)).cost (arg, ()) = 3 := rfl
  rw [hcc] at hit
  simp only [pow_one] at hrev
  omega

/-! ## Tree potentials -/

theorem setIntFn_cost (hN : 1 ≤ N) (pv : ℤ × ℤ) (x : List ℤ) (hp : bits pv.1 ≤ N)
    (hx : x.length ≤ N) : setIntFn.costAt (pv, x) ≤ 130 * N ^ 2 := by
  show (mapIdxFn setItem).costAt (pv, x) ≤ _
  have h := mapIdxFn_costN setItem pv x (K := 20) (d := 1) hN le_rfl hx (fun j hj => by
    rw [Fn.costAt]
    simp only [setItem, Expr.cost, Var.index, CmpOp.charge]
    have hj' := bits_index hN (show j < N by omega)
    rw [pow_one]
    repeat' split
    all_goals (try simp only [Expr.denote, Var.get] at *)
    all_goals omega)
  simp only [Nat.reduceAdd] at h
  omega

theorem bits_unitAt (u k : ℤ) : bits (unitAt u k) ≤ 1 := by
  unfold unitAt; split_ifs <;> simp

theorem denote_ite_cond {Γ : List Ty} {τ : Ty} (c : Expr Γ .bool) (t e : Expr Γ τ) (env : Env Γ) :
    (Expr.ite c t e).denote env = cond (c.denote env) (t.denote env) (e.denote env) := by
  simp only [Expr.denote]
  cases c.denote env <;> rfl

theorem bits_cond01 (b : Bool) : bits (cond b (1 : ℤ) 0) ≤ 1 := by cases b <;> simp

theorem bits_ite_le {c : Prop} [Decidable c] {a b : ℤ} (ha : bits a ≤ N) (hb : bits b ≤ N) :
    bits (if c then a else b) ≤ N := by
  split <;> assumption

theorem potStep_cost (hN5 : 5 ≤ N) (p : ℤ × ℤ) (x : List ℤ) (arg : PotArg.denote)
    (hp1 : bits p.1 ≤ N) (hp2 : bits p.2 ≤ N) (hx : x.length ≤ N) (hxa : ∀ y ∈ x, |y| ≤ 2 * N)
    (he : PairsOK N arg.2.1) (hu : bits arg.2.2.2.2.1 ≤ N) :
    potStep.cost (p, x, (arg, ())) ≤ 400 * N ^ 2 := by
  have hN : 1 ≤ N := by omega
  have q1 := const_le_pow hN 100 2
  have q2 : N ≤ N ^ 2 := by simpa using pow_mono hN (show 1 ≤ 2 by norm_num)
  unfold potStep
  refine (cost_letE_le _ _ _ (fun lr : ℤ × ℤ => bits lr.1 ≤ N ∧ bits lr.2 ≤ N)
    (A := 74 * N ^ 2 + 10) (B := 300 * N ^ 2) ?_ ?_ ?_).trans (by omega)
  · have := getPairFn_costN hN arg.2.1 p.2 he.1 hp2
    simp only [Expr.cost, cost_call, Var.index, Expr.denote, Var.get]
    omega
  · simp only [Expr.denote, Var.get, denote_call, getPairFn_apply']
    exact he.getI p.2
  intro lr hlr
  refine (cost_letE_le _ _ _ (fun o : ℤ => bits o ≤ N)
    (A := 2 * N + 20) (B := 280 * N ^ 2) ?_ ?_ ?_).trans (by omega)
  · simp only [Expr.cost, Var.index, CmpOp.charge]
    repeat' split
    all_goals (try simp only [Expr.denote, Var.get] at *)
    all_goals omega
  · simp only [Expr.denote, Var.get]
    exact bits_ite_le hlr.2 hlr.1
  intro o ho
  have hxo : |getI x 0 o| ≤ 2 * N := getI_abs_le (by omega) hxa o
  refine (cost_letE_le _ _ _ (fun v : ℤ => bits v ≤ N)
    (A := 74 * N ^ 2 + 3 * N + 40) (B := 140 * N ^ 2) ?_ ?_ ?_).trans (by omega)
  · have k1 := getIntFn_costN hN x o hx ho
    have k2 : bits (getI x 0 o) ≤ N := bits_small hN5 (by linarith)
    have k3 := bits_cond01 (CmpOp.eq.eval p.2 arg.2.2.2.2.1)
    simp only [Expr.cost, cost_call, Var.index, CmpOp.charge, IntOp.charge]
    repeat' split
    all_goals (try simp only [denote_ite_cond] at *)
    all_goals (try simp only [Expr.denote, Var.get, denote_call, getIntFn_apply', bits_one',
      bits_zero'] at *)
    all_goals omega
  · simp only [Expr.denote, Var.get, denote_call, getIntFn_apply', IntOp.eval]
    apply bits_small hN5
    have : |(if CmpOp.eq.eval p.2 arg.2.2.2.2.1 = true then (1 : ℤ) else 0)| ≤ 1 := by
      split <;> simp
    calc _ ≤ |(if CmpOp.eq.eval p.2 arg.2.2.2.2.1 = true then (1 : ℤ) else 0)| + |getI x 0 o| :=
          abs_sub _ _
      _ ≤ 4 * N := by linarith
  intro v hv
  have := setIntFn_cost hN (p.1, v) x hp1 hx
  simp only [Expr.cost, cost_call, Var.index, Expr.denote, Var.get]
  omega

theorem potInit_cost (hN5 : 5 ≤ N) (arg : PotArg.denote) (n : ℕ) (hn : arg.2.2.1 = n)
    (hnN : n ≤ N) (hr : bits arg.2.2.2.1 ≤ N) : potInit.cost (arg, ()) ≤ 180 * N ^ 2 := by
  have hN : 1 ≤ N := by omega
  have k1 := crange_costN hN n hnN (bits_nat_small hN5 (by omega))
  have k2 := cmapFn_costN rootItem (arg.2.2.2.1, arg.2.2.2.2.2)
    ((List.range n).map fun i : ℕ => (i : ℤ)) (K := 20) (d := 1) hN le_rfl (by simpa using hnN)
    (fun i hi => by
      simp only [List.mem_map, List.mem_range] at hi
      obtain ⟨i, hi, rfl⟩ := hi
      have b1 := bits_index hN (show i < N by omega)
      rw [Fn.costAt]
      simp only [rootItem, Expr.cost, Var.index, CmpOp.charge, pow_one]
      repeat' split
      all_goals (try simp only [Expr.denote, Var.get] at *)
      all_goals omega)
  simp only [Nat.reduceAdd] at k2
  have q := const_le_pow hN 40 2
  simp only [potInit, Expr.cost, cost_call, Var.index, Expr.denote, Var.get, denote_call,
    crange_apply, hn, Int.toNat_natCast]
  omega

theorem take_treeCode {k : ℕ} (s : List (Fin n × Fin k)) (j : ℕ) :
    (treeCode s).take j = treeCode (s.take j) := by
  simp [treeCode, List.map_take]

/-- **Cost of a tree potential.** -/
theorem potFn_cost (hN5 : 5 ≤ N) (hm : m ≤ N) (hn : n ≤ N) (root : Fin n) (u c : ℤ)
    (hc : |c| ≤ 1) (hu : bits u ≤ N) :
    potFn.costAt (treeCode (tree left right root),
      (edgeList left right, ((n : ℤ), (((root : ℕ) : ℤ), (u, c))))) ≤ 600 * N ^ 3 := by
  have hN : 1 ≤ N := by omega
  have he := edgeList_ok left right hN hm hn
  set arg : PotArg.denote := (treeCode (tree left right root),
      (edgeList left right, ((n : ℤ), (((root : ℕ) : ℤ), (u, c))))) with harg
  have hT := treeCode_tree_length left right root
  have hroot : bits arg.2.2.2.1 ≤ N := bits_index hN (by have := root.2; simp [harg]; omega)
  have hI := potInit_cost hN5 arg n rfl hn hroot
  have h := cost_foldl_le_prefix (Γ := [PotArg]) (.fst v0) potInit potStep (arg, ()) (400 * N ^ 2)
    (by
      intro j hj
      have hj' : j < (treeCode (tree left right root)).length := hj
      change potStep.cost ((treeCode (tree left right root))[j],
        ((treeCode (tree left right root)).take j).foldl
          (fun acc y => potStep.denote (y, acc, (arg, ()))) (potInit.denote (arg, ())),
          (arg, ())) ≤ _
      rw [potStep_denote, potInit_denote, take_treeCode]
      simp only [harg, Int.toNat_natCast]
      rw [potSpec_eq]
      have hj2 : j < (tree left right root).length := by simpa [treeCode] using hj'
      have hb : bits ((treeCode (tree left right root))[j]).1 ≤ N ∧
          bits ((treeCode (tree left right root))[j]).2 ≤ N := by
        simp only [treeCode, List.getElem_map]
        exact ⟨bits_index hN (by have := ((tree left right root)[j]).1.2; omega),
          bits_index hN (by have := ((tree left right root)[j]).2.2; omega)⟩
      apply potStep_cost hN5
      · exact hb.1
      · exact hb.2
      · simpa [vertexList] using hn
      · intro y hy
        simp only [vertexList, List.mem_ofFn] at hy
        obtain ⟨w, rfl⟩ := hy
        have := potential_abs_le left right (root := root)
          (s := (tree left right root).take j) c (fun d : Fin m => unitAt u d) 1
          (fun d => by unfold unitAt; split_ifs <;> simp) (by norm_num) w
        have hl : (((tree left right root).take j).length : ℤ) ≤ n := by
          have := List.length_take_le j (tree left right root)
          have := treeCode_tree_length left right root
          simp only [treeCode, List.length_map] at this
          omega
        linarith
      · exact he
      · exact hu)
  rw [Fn.costAt, potFn]
  refine h.trans ?_
  have hlen : ((Expr.fst (Γ := [PotArg]) v0).denote (arg, ())).length ≤ n := hT
  have : ((Expr.fst (Γ := [PotArg]) v0).denote (arg, ())).length * (400 * N ^ 2 + 1) ≤
      N * (400 * N ^ 2 + 1) := Nat.mul_le_mul_right _ (le_trans hlen hn)
  have : N * (400 * N ^ 2 + 1) = 400 * N ^ 3 + N := by ring
  have q1 := pow_mono hN (show 2 ≤ 3 by norm_num)
  have q2 : N ≤ N ^ 3 := by simpa using pow_mono hN (show 1 ≤ 3 by norm_num)
  have q3 := const_le_pow hN 10 3
  have hc0 : (Expr.fst (Γ := [PotArg]) v0).cost (arg, ()) = 2 := rfl
  omega

end MWIS.FunCoordinates

end
