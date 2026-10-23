module

public import MWIS.FunCoordinatesCostRun
public import MWIS.FunCoordinatesCostTree

/-!
# Cost of the coordinate program

`coordFn_cost`: on the encoded input of a graph with `m` edges, `n` vertices and `f` face rows,
the coordinate program `coordFn` costs at most `20000 * (m + n + f + 5) ^ 5`.
-/

@[expose] public section

namespace MWIS.FunCoordinates

open MWIS.Fun MWIS.FunLP MWIS.TreeCotree

variable {N : ℕ}

/-! ## Row items -/

theorem residItem_cost (hN5 : 5 ≤ N) (P : List ℤ) (u : ℤ) (klr : ℤ × (ℤ × ℤ))
    (hP : P.length ≤ N) (hPa : ∀ y ∈ P, |y| ≤ N) (hu : bits u ≤ N) (hk : bits klr.1 ≤ N)
    (hl : bits klr.2.1 ≤ N) (hr : bits klr.2.2 ≤ N) :
    residItem.costAt ((P, u), klr) ≤ 200 * N ^ 2 := by
  have hN : 1 ≤ N := by omega
  have k1 := getIntFn_costN hN P klr.2.1 hP hl
  have k2 := getIntFn_costN hN P klr.2.2 hP hr
  have a1 := getI_abs_le (by omega) hPa klr.2.1
  have a2 := getI_abs_le (by omega) hPa klr.2.2
  have b1 : bits (getI P 0 klr.2.1) ≤ N := bits_small hN5 (by linarith)
  have b2 : bits (getI P 0 klr.2.2) ≤ N := bits_small hN5 (by linarith)
  have b3 : bits (getI P 0 klr.2.1 + getI P 0 klr.2.2) ≤ N :=
    bits_small hN5 (by have := abs_add_le (getI P 0 klr.2.1) (getI P 0 klr.2.2); linarith)
  have k3 := bits_cond01 (CmpOp.eq.eval klr.1 u)
  have q1 := const_le_pow hN 40 2
  have q2 : N ≤ N ^ 2 := by simpa using pow_mono hN (show 1 ≤ 2 by norm_num)
  rw [Fn.costAt]
  simp only [residItem, Expr.cost, cost_call, Var.index, CmpOp.charge, IntOp.charge]
  repeat' split
  all_goals (try simp only [denote_ite_cond] at *)
  all_goals (try simp only [Expr.denote, Var.get, denote_call, getIntFn_apply', IntOp.eval,
    bits_one', bits_zero'] at *)
  all_goals omega

theorem freeItem_cost (hN5 : 5 ≤ N) (res H : List ℤ) (lead c : ℤ) (hr : res.length ≤ N)
    (hra : ∀ y ∈ res, |y| ≤ 2 * N) (hH : H.length ≤ N) (hHa : ∀ y ∈ H, |y| ≤ 1)
    (hlead : |lead| ≤ 2 * N) (hc : bits c ≤ N) :
    freeItem.costAt ((res, (lead, H)), c) ≤ 200 * N ^ 2 := by
  have hN : 1 ≤ N := by omega
  have k1 := getIntFn_costN hN res c hr hc
  have k2 := getIntFn_costN hN H c hH hc
  have a1 := getI_abs_le (by omega) hra c
  have a2 := getI_abs_le (by norm_num) hHa c
  have b1 : bits (getI res 0 c) ≤ N := bits_small hN5 (by linarith)
  have b2 : bits (getI H 0 c) ≤ 1 := by
    have := bits_mono (x := getI H 0 c) (y := 1) (by simpa using a2); simpa using this
  have b3 : bits lead ≤ N := bits_small hN5 (by linarith)
  have hm : |lead * getI H 0 c| ≤ 2 * N := by
    rw [abs_mul]; nlinarith [abs_nonneg lead, abs_nonneg (getI H 0 c)]
  have b4 : bits (lead * getI H 0 c) ≤ N := bits_small hN5 (by linarith)
  have b5 : (bits lead + 1) * (bits (getI H 0 c) + 1) ≤ 2 * N + 2 := by nlinarith
  have q1 := const_le_pow hN 40 2
  have q2 : N ≤ N ^ 2 := by simpa using pow_mono hN (show 1 ≤ 2 by norm_num)
  rw [Fn.costAt]
  simp only [freeItem, Expr.cost, cost_call, Var.index, IntOp.charge, Expr.denote, Var.get,
    denote_call, getIntFn_apply', IntOp.eval]
  omega

theorem modItem_cost (hN5 : 5 ≤ N) (M x : ℤ) (hM : bits M ≤ N) (hx : bits x ≤ N) :
    modItem.costAt (M, x) ≤ 20 * N ^ 2 := by
  have hN : 1 ≤ N := by omega
  have : (bits x + bits M + 1) ^ 2 ≤ 9 * N ^ 2 := by nlinarith
  have q1 := const_le_pow hN 10 2
  rw [Fn.costAt]
  simp only [modItem, Expr.cost, Var.index, IntOp.charge, Expr.denote, Var.get]
  omega

/-! ## Searching, filtering and counting -/

theorem cost_call_le {Γ : List Ty} {σ τ : Ty} (g : Fn σ τ) (x : Expr Γ σ) (env : Env Γ)
    (v : σ.denote) (hv : x.denote env = v) {A B : ℕ} (hx : x.cost env ≤ A)
    (hg : g.costAt v ≤ B) : (call g x).cost env ≤ A + B + 1 := by
  rw [cost_call, hv]
  omega

theorem halfItem_cost (hN5 : 5 ≤ N) (P : List ℤ) (lr : ℤ × ℤ) (hP : P.length ≤ N)
    (hPa : ∀ y ∈ P, |y| ≤ N) (hl : bits lr.1 ≤ N) (hr : bits lr.2 ≤ N) :
    halfItem.costAt (P, lr) ≤ 200 * N ^ 2 := by
  have hN : 1 ≤ N := by omega
  have k1 := getIntFn_costN hN P lr.1 hP hl
  have k2 := getIntFn_costN hN P lr.2 hP hr
  have a1 := getI_abs_le (by omega) hPa lr.1
  have a2 := getI_abs_le (by omega) hPa lr.2
  have b1 : bits (getI P 0 lr.1) ≤ N := bits_small hN5 (by linarith)
  have b2 : bits (getI P 0 lr.2) ≤ N := bits_small hN5 (by linarith)
  have b3 : bits (getI P 0 lr.1 + getI P 0 lr.2) ≤ N :=
    bits_small hN5 (by have := abs_add_le (getI P 0 lr.1) (getI P 0 lr.2); linarith)
  have s1 : (bits (getI P 0 lr.1 + getI P 0 lr.2) + 2 + 1) ^ 2 ≤ 16 * N ^ 2 := by nlinarith
  have q1 := const_le_pow hN 40 2
  have q2 : N ≤ N ^ 2 := by simpa using pow_mono hN (show 1 ≤ 2 by norm_num)
  rw [Fn.costAt]
  simp only [halfItem, Expr.cost, cost_call, Var.index, IntOp.charge, Expr.denote, Var.get,
    denote_call, getIntFn_apply', IntOp.eval, bits_two']
  omega

theorem coordEdgesS_length (j : ℤ) (F : List Bool) : (coordEdgesS j F).length ≤ F.length := by
  unfold coordEdgesS
  simp only [List.length_map]
  exact (List.length_filter_le _ _).trans (by rw [length_indexed])

theorem coordEdgesFn_cost (hN : 1 ≤ N) (j : ℤ) (F : List Bool) (hF : F.length ≤ N)
    (hj : bits j ≤ N) : coordEdgesFn.costAt (j, F) ≤ 130 * N ^ 2 := by
  have hlen : (indexed F).length ≤ N := by rw [length_indexed]; exact hF
  have k1 := indexedFn_costN hN .bool F hF
  have h := cost_foldl_le (Γ := [.prod .int (.list .bool)]) (call (indexedFn .bool) (.snd v0))
    .nil ceStep ((j, F), ()) (fun _ => True) (2 * N + 20) trivial (fun acc y hy _ => ⟨trivial, by
      simp only [Expr.denote, Var.get, denote_call, indexedFn_apply] at hy
      obtain ⟨k, hk, rfl⟩ := mem_indexed hy
      have hb := bits_index hN (show k < N by omega)
      simp only [ceStep, Expr.cost, Var.index, CmpOp.charge]
      repeat' split
      all_goals (try simp only [Expr.denote, Var.get] at *)
      all_goals omega⟩)
  have hval : ((Expr.foldl (Γ := [.prod .int (.list .bool)]) (call (indexedFn .bool) (.snd v0))
      .nil ceStep).denote ((j, F), ())).length ≤ N := by
    have h1 := coordEdgesFn_apply (j, F)
    rw [coordEdgesFn, Fn.apply, denote_call, crevFn_apply] at h1
    have h2 := congrArg List.length h1
    rw [List.length_reverse] at h2
    rw [h2]
    exact (coordEdgesS_length j F).trans hF
  have hr := crevFn_costN hN .int _ hval
  rw [Fn.costAt, coordEdgesFn, cost_call]
  have hxs : (call (Γ := [.prod .int (.list .bool)]) (indexedFn .bool) (.snd v0)).cost
      ((j, F), ()) = 2 + (indexedFn .bool).costAt F + 1 := by rw [cost_call]; rfl
  have hxd : ((call (Γ := [.prod .int (.list .bool)]) (indexedFn .bool) (.snd v0)).denote
      ((j, F), ())).length = F.length := by
    simp only [denote_call, Expr.denote, Var.get, indexedFn_apply, length_indexed]
  rw [hxs, hxd] at h
  have hn0 : (Expr.nil (Γ := [.prod .int (.list .bool)]) (a := .int)).cost ((j, F), ()) = 1 := rfl
  rw [hn0] at h
  have : F.length * (2 * N + 20 + 1) ≤ N * (2 * N + 21) := Nat.mul_le_mul_right _ hF
  have : N * (2 * N + 21) = 2 * N ^ 2 + 21 * N := by ring
  have q2 : N ≤ N ^ 2 := by simpa using pow_mono hN (show 1 ≤ 2 by norm_num)
  have q1 := const_le_pow hN 10 2
  simp only [pow_one] at hr
  omega

theorem lengthFn_cost (hN : 1 ≤ N) (l : List ℤ) (hl : l.length ≤ N) :
    (lengthFn .int).costAt l ≤ 12 * N ^ 2 := by
  have key : ∀ (l : List ℤ) (k : ℤ), l.foldl (fun acc _ => acc + 1) k = k + l.length := by
    intro l
    induction l with
    | nil => simp
    | cons y l ih => intro k; rw [List.foldl_cons, ih]; simp; ring
  have h := cost_foldl_le_prefix (Γ := [.list .int]) v0 (.int 0) (.arith .add v1 (.int 1)) (l, ())
    (N + 6) (by
      intro j hj
      have hj' : j < l.length := hj
      change (Expr.arith (Γ := [.int, .int, .list .int]) .add v1 (.int 1)).cost
        (l[j], (l.take j).foldl (fun acc y => (Expr.arith (Γ := [.int, .int, .list .int]) .add v1
          (.int 1)).denote (y, acc, (l, ()))) 0, (l, ())) ≤ _
      have hs : (fun acc y => (Expr.arith (Γ := [.int, .int, .list .int]) .add v1
          (.int 1)).denote (y, acc, (l, ()))) = fun (acc : ℤ) (_ : ℤ) => acc + 1 := by
        funext acc y; simp [Expr.denote, Var.get, IntOp.eval]
      rw [hs, key]
      have hb : bits ((0 : ℤ) + ((l.take j).length : ℕ)) ≤ N := by
        rw [zero_add]; exact bits_index hN (by simp; omega)
      simp only [Expr.cost, Var.index, IntOp.charge, Expr.denote, Var.get, bits_one']
      omega)
  rw [Fn.costAt, lengthFn]
  change _ ≤ 1 + 1 + l.length * (N + 6 + 1) + 1 at h
  have : l.length * (N + 6 + 1) ≤ N * (N + 7) := Nat.mul_le_mul_right _ hl
  have : N * (N + 7) = N ^ 2 + 7 * N := by ring
  have q2 : N ≤ N ^ 2 := by simpa using pow_mono hN (show 1 ≤ 2 by norm_num)
  have q1 := const_le_pow hN 10 2
  omega

/-! ## The row of one edge -/

variable {f m n : ℕ} (left right : Fin m → Fin n) (C : Fin m → Walks.Column (Fin f))
  (root : Fin n)

/-- The shared row data of the coordinate program. -/
def edgeParam : EdgeParam.denote :=
  ((treeCode (tree left right root), edgeList left right),
    (((n : ℤ), ((root : ℕ) : ℤ)),
      ((List.ofFn fun e => half left right root e, optInt ((pivotEdge left right C root).map Fin.val)),
        ((coordEdges left right C root).map (fun e : Fin m => ((e : ℕ) : ℤ)),
          if ((rank left right C root : ℕ) : ℤ) = 0 then 2
            else 4 * ((rank left right C root : ℕ) : ℤ)))))

theorem treePotential_abs (e : Fin m) (w : Fin n) :
    |treePotential left right root (Pi.single e 1) w| ≤ n := by
  have h := potential_abs_le left right (root := root) (s := tree left right root) 0
    (Pi.single e 1) 1 (fun d => by by_cases h : d = e <;> simp [h]) (by norm_num) w
  have hl := (tree_good left right root).length_lt left right
  have : ((tree left right root).length : ℤ) ≤ n := by exact_mod_cast hl.le
  unfold treePotential
  simp only [abs_zero, zero_add, mul_one] at h
  linarith

theorem edgeItem_cost (hN5 : 5 ≤ N) (hm : m ≤ N) (hn : n ≤ N) (e : Fin m) :
    edgeItem.costAt (edgeParam left right C root, ((e : ℕ) : ℤ), (edgeList left right)[(e : ℕ)]'
      (by simp [edgeList])) ≤ 2000 * N ^ 3 := by
  have hN : 1 ≤ N := by omega
  have q1 := pow_mono hN (show 2 ≤ 3 by norm_num)
  have q2 : N ≤ N ^ 3 := by simpa using pow_mono hN (show 1 ≤ 3 by norm_num)
  have q3 := const_le_pow hN 100 3
  have q4 : N ≤ N ^ 2 := by simpa using pow_mono hN (show 1 ≤ 2 by norm_num)
  have he := edgeList_ok left right hN hm hn
  have hbe : bits ((e : ℕ) : ℤ) ≤ N := bits_index hN (by have := e.2; omega)
  have hHlen : (List.ofFn fun e => half left right root e).length ≤ N := by simpa using hm
  have hHa : ∀ y ∈ List.ofFn (fun e => half left right root e), |y| ≤ 1 := by
    intro y hy
    simp only [List.mem_ofFn] at hy
    obtain ⟨d, rfl⟩ := hy
    exact half_abs d
  have hJ : bits (optInt ((pivotEdge left right C root).map Fin.val)) ≤ N := by
    apply bits_optInt hN
    intro k hk
    cases hp : pivotEdge left right C root with
    | none => rw [hp] at hk; simp at hk
    | some j => rw [hp] at hk; simp at hk; have := j.2; omega
  have hRank := rank_le (left := left) (right := right) (C := C) (root := root)
  rw [Fn.costAt, edgeItem]
  refine (cost_letE_le _ _ _
    (fun P => P = vertexList (treePotential left right root (Pi.single e 1)))
    (A := 600 * N ^ 3 + 40) (B := 1300 * N ^ 3) ?_ ?_ ?_).trans (by omega)
  · have := potFn_cost left right hN5 hm hn root ((e : ℕ) : ℤ) 0 (by simp) hbe
    simp only [Expr.cost, cost_call, Var.index, Expr.denote, Var.get]
    simp only [edgeParam]
    omega
  · simp only [Expr.denote, Var.get, denote_call, edgeParam]
    exact potFn_single left right root e
  intro P hP
  subst hP
  have hPlen : (vertexList (treePotential left right root (Pi.single e 1))).length ≤ N := by
    simpa [vertexList] using hn
  have hPa : ∀ y ∈ vertexList (treePotential left right root (Pi.single e 1)), |y| ≤ N := by
    intro y hy
    simp only [vertexList, List.mem_ofFn] at hy
    obtain ⟨w, rfl⟩ := hy
    have := treePotential_abs left right root e w
    have : (n : ℤ) ≤ N := by exact_mod_cast hn
    linarith
  refine (cost_letE_le _ _ _
    (fun res => res = List.ofFn fun e' => residual left right root (Pi.single e 1) e')
    (A := 500 * N ^ 3) (B := 790 * N ^ 3) ?_ ?_ ?_).trans (by omega)
  · have := mapIdxFn_costN residItem
      (vertexList (treePotential left right root (Pi.single e 1)), ((e : ℕ) : ℤ))
      (edgeList left right) (K := 200) (d := 2) hN (by norm_num) he.1 (fun j hj =>
        residItem_cost hN5 _ _ _ hPlen hPa hbe (bits_index hN (by have := he.1; omega))
          (he.2 _ (List.getElem_mem hj)).1 (he.2 _ (List.getElem_mem hj)).2)
    simp only [Nat.reduceAdd] at this
    simp only [Expr.cost, cost_call, Var.index, Expr.denote, Var.get, edgeParam]
    omega
  · simp only [Expr.denote, Var.get, denote_call, edgeParam, mapIdxFn_apply', residItem_apply]
    exact residS_eq left right root e
  intro res hres
  subst hres
  have hRlen : (List.ofFn fun e' => residual left right root (Pi.single e 1) e').length ≤ N := by
    simpa using hm
  have hRa : ∀ y ∈ List.ofFn (fun e' => residual left right root (Pi.single e 1) e'),
      |y| ≤ 2 * N := by
    intro y hy
    simp only [List.mem_ofFn] at hy
    obtain ⟨w, rfl⟩ := hy
    have := residual_single_abs (left := left) (right := right) (root := root) e w
    have : (n : ℤ) ≤ N := by exact_mod_cast hn
    linarith
  refine (cost_letE_le _ _ _
    (fun par => par = parityRow left right C root (Pi.single e 1))
    (A := 74 * N ^ 2 + N + 30) (B := 700 * N ^ 3) ?_ ?_ ?_).trans (by omega)
  · have := getIntFn_costN hN _ (optInt ((pivotEdge left right C root).map Fin.val)) hRlen hJ
    simp only [Expr.cost, cost_call, Var.index, CmpOp.charge, edgeParam]
    repeat' split
    all_goals (try simp only [Expr.denote, Var.get, bits_zero'] at *)
    all_goals omega
  · simp only [Expr.denote, Var.get, denote_call, edgeParam, getIntFn_apply', CmpOp.eval]
    rw [← parity_eq left right C root e]
    by_cases h : optInt ((pivotEdge left right C root).map Fin.val) < 0 <;> simp [h]
  intro par hpar
  subst hpar
  have hpa := parityRow_single_abs (left := left) (right := right) (C := C) (root := root) e
  have hbp : bits (parityRow left right C root (Pi.single e 1)) ≤ N :=
    bits_small hN5 (by have h' : (n : ℤ) ≤ N := (by exact_mod_cast hn); linarith)
  refine (cost_letE_le _ _ _
    (fun ld => ld = lead left right C root (Pi.single e 1))
    (A := 74 * N ^ 2 + 4 * N + 30) (B := 600 * N ^ 3) ?_ ?_ ?_).trans (by omega)
  · have k1 := getIntFn_costN hN _ (optInt ((pivotEdge left right C root).map Fin.val)) hHlen hJ
    have a1 := getI_abs_le (by norm_num) hHa (optInt ((pivotEdge left right C root).map Fin.val))
    have b1 : bits (getI (List.ofFn fun e => half left right root e) 0
        (optInt ((pivotEdge left right C root).map Fin.val))) ≤ 1 := by
      have := bits_mono (y := 1) (by simpa using a1); simpa using this
    have b2 : (bits (getI (List.ofFn fun e => half left right root e) 0
        (optInt ((pivotEdge left right C root).map Fin.val))) + 1) *
        (bits (parityRow left right C root (Pi.single e 1)) + 1) ≤ 2 * N + 2 := by nlinarith
    simp only [Expr.cost, cost_call, Var.index, IntOp.charge, Expr.denote, Var.get, denote_call,
      edgeParam, getIntFn_apply']
    omega
  · simp only [Expr.denote, Var.get, denote_call, edgeParam, getIntFn_apply', IntOp.eval]
    exact lead_eq' left right C root e
  intro ld hld
  subst hld
  have hla : |lead left right C root (Pi.single e 1)| ≤ 2 * N := by
    simp only [lead, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    have : (n : ℤ) ≤ N := by exact_mod_cast hn
    cases pivotEdge left right C root with
    | none => simp
    | some j =>
      simp only [Option.elim_some, abs_mul]
      have := half_abs (left := left) (right := right) (root := root) j
      have := residual_single_abs (left := left) (right := right) (root := root) e j
      nlinarith [abs_nonneg (residual left right root (Pi.single e 1) j),
        abs_nonneg (half left right root j)]
  have hCE : ((coordEdges left right C root).map (fun e : Fin m => ((e : ℕ) : ℤ))).length ≤ N := by
    simp only [List.length_map]; exact le_trans (by exact hRank) hm
  refine (cost_letE_le _ _ _
    (fun fr => fr = List.ofFn fun i => freeMap left right C root (Pi.single e 1) i)
    (A := 470 * N ^ 3) (B := 120 * N ^ 3) ?_ ?_ ?_).trans (by omega)
  · have := cmapFn_costN freeItem ((List.ofFn fun e' => residual left right root (Pi.single e 1) e'),
      (lead left right C root (Pi.single e 1), List.ofFn fun e => half left right root e))
      ((coordEdges left right C root).map (fun e : Fin m => ((e : ℕ) : ℤ))) (K := 200) (d := 2)
      hN (by norm_num) hCE (fun c hc => by
        simp only [List.mem_map] at hc
        obtain ⟨d, _, rfl⟩ := hc
        exact freeItem_cost hN5 _ _ _ _ hRlen hRa hHlen hHa hla
          (bits_index hN (by have := d.2; omega)))
    simp only [Nat.reduceAdd] at this
    simp only [Expr.cost, cost_call, Var.index, Expr.denote, Var.get, edgeParam]
    omega
  · simp only [Expr.denote, Var.get, denote_call, edgeParam, cmapFn_apply', freeItem_apply]
    exact freeRow_eq left right C root e
  intro fr hfr
  subst hfr
  have hFlen : (List.ofFn fun i => freeMap left right C root (Pi.single e 1) i).length ≤ N := by
    simp only [List.length_ofFn]; exact le_trans hRank hm
  have hMb : bits (if ((rank left right C root : ℕ) : ℤ) = 0 then 2
      else 4 * ((rank left right C root : ℕ) : ℤ)) ≤ N := by
    apply bits_ite_le
    · simp; omega
    · apply bits_small hN5
      rw [abs_of_nonneg (by positivity)]
      have : (rank left right C root : ℤ) ≤ N := by exact_mod_cast le_trans hRank hm
      linarith
  have k1 := cmapFn_costN modItem (if ((rank left right C root : ℕ) : ℤ) = 0 then 2
      else 4 * ((rank left right C root : ℕ) : ℤ))
    (List.ofFn fun i => freeMap left right C root (Pi.single e 1) i) (K := 20) (d := 2) hN
    (by norm_num) hFlen (fun x hx => by
      simp only [List.mem_ofFn] at hx
      obtain ⟨i, rfl⟩ := hx
      apply modItem_cost hN5 _ _ hMb
      apply bits_small hN5
      have := freeMap_single_abs (left := left) (right := right) (C := C) (root := root) e i
      have : (n : ℤ) ≤ N := by exact_mod_cast hn
      linarith)
  simp only [Nat.reduceAdd] at k1
  have s1 : (bits (parityRow left right C root (Pi.single e 1)) + 2 + 1) ^ 2 ≤ 16 * N ^ 2 := by
    nlinarith
  simp only [Expr.cost, cost_call, Var.index, IntOp.charge, Expr.denote, Var.get, edgeParam,
    bits_two']
  omega

/-! ## The whole program -/

theorem cost_pair {Γ : List Ty} {α β : Ty} (a : Expr Γ α) (b : Expr Γ β) (env : Env Γ) :
    (Expr.pair a b).cost env = a.cost env + b.cost env + 1 := rfl

theorem coordFn_costN (hN5 : 5 ≤ N) (hm : m ≤ N) (hn : n ≤ N) (hf : f ≤ N) :
    coordFn.costAt (edgeList left right, (colList C, ((n : ℤ), ((f : ℤ), ((root : ℕ) : ℤ))))) ≤
      17000 * N ^ 5 := by
  have hN : 1 ≤ N := by omega
  have q1 := pow_mono hN (show 2 ≤ 5 by norm_num)
  have q2 := pow_mono hN (show 3 ≤ 5 by norm_num)
  have q3 := pow_mono hN (show 4 ≤ 5 by norm_num)
  have q4 : N ≤ N ^ 5 := by simpa using pow_mono hN (show 1 ≤ 5 by norm_num)
  have q5 := const_le_pow hN 300 5
  have r1 := pow_mono hN (show 2 ≤ 4 by norm_num)
  have r2 := pow_mono hN (show 3 ≤ 4 by norm_num)
  have r3 : N ≤ N ^ 4 := by simpa using pow_mono hN (show 1 ≤ 4 by norm_num)
  have r4 := const_le_pow hN 300 4
  have r5 := pow_mono hN (show 2 ≤ 3 by norm_num)
  have r6 := const_le_pow hN 100 3
  have he := edgeList_ok left right hN hm hn
  have hRank := rank_le (left := left) (right := right) (C := C) (root := root)
  have q6 : 5 * N ^ 4 ≤ N ^ 5 := by
    calc 5 * N ^ 4 ≤ N * N ^ 4 := Nat.mul_le_mul_right _ hN5
      _ = N ^ 5 := by ring
  rw [Fn.costAt, coordFn]
  refine (cost_letE_le _ _ _ (fun T => T = treeCode (tree left right root))
    (A := 1100 * N ^ 4 + 30) (B := 15000 * N ^ 5) ?_ ?_ ?_).trans (by omega)
  · have := treeFn_cost left right hN5 hm hn root
    simp only [Expr.cost, cost_call, Var.index, Expr.denote, Var.get]
    omega
  · simp only [Expr.denote, Var.get, denote_call]
    exact treeFn_tree left right root
  intro T hT
  subst hT
  refine (cost_letE_le _ _ _ (fun F => F = freeList left right C root)
    (A := 9000 * N ^ 5 + 30) (B := 6400 * N ^ 4) ?_ ?_ ?_).trans (by omega)
  · have := freeFn_cost left right C hN5 hm hn hf root
    simp only [Expr.cost, cost_call, Var.index, Expr.denote, Var.get]
    omega
  · simp only [Expr.denote, Var.get, denote_call]
    exact freeFn_free left right C root
  intro F hF
  subst hF
  have hFlen : (freeList left right C root).length ≤ N := by simpa [freeList] using hm
  have hHlen : (List.ofFn fun e => half left right root e).length ≤ N := by simpa using hm
  have hHa : ∀ y ∈ List.ofFn (fun e => half left right root e), |y| ≤ 2 := by
    intro y hy
    simp only [List.mem_ofFn] at hy
    obtain ⟨d, rfl⟩ := hy
    have := half_abs (left := left) (right := right) (root := root) d
    linarith
  refine (cost_letE_le _ _ _ (fun H => H = List.ofFn fun e => half left right root e)
    (A := 1100 * N ^ 3 + 60) (B := 5200 * N ^ 4) ?_ ?_ ?_).trans (by omega)
  · have hP := potFn_cost left right hN5 hm hn root (-1) 1 (by simp) (by simp; omega)
    have hPv := potFn_parity left right root
    have hPlen : (vertexList (parityPotential left right root)).length ≤ N := by
      simpa [vertexList] using hn
    have hPa : ∀ y ∈ vertexList (parityPotential left right root), |y| ≤ N := by
      intro y hy
      simp only [vertexList, List.mem_ofFn] at hy
      obtain ⟨w, rfl⟩ := hy
      have := potential_abs_le left right (root := root) (s := tree left right root) 1 0 0
        (fun _ => by simp) le_rfl w
      unfold parityPotential
      simp only [abs_one, mul_zero, add_zero] at this
      have : (1 : ℤ) ≤ N := by exact_mod_cast hN
      linarith
    have hc := cmapFn_costN halfItem (vertexList (parityPotential left right root))
      (edgeList left right) (K := 200) (d := 2) hN (by norm_num) he.1 (fun lr hlr =>
        halfItem_cost hN5 _ lr hPlen hPa (he.2 lr hlr).1 (he.2 lr hlr).2)
    simp only [Nat.reduceAdd] at hc
    refine (cost_call_le _ _ _ (vertexList (parityPotential left right root), edgeList left right)
      ?_ (A := 600 * N ^ 3 + 40) ?_ hc).trans (by omega)
    · simp only [Expr.denote, Var.get, denote_call]
      rw [hPv]
    · simp only [Expr.cost, cost_call, Var.index, Expr.denote, Var.get]
      omega
  · simp only [Expr.denote, Var.get, denote_call, cmapFn_apply', halfItem_apply]
    rw [potFn_parity left right root]
    exact halfList_eq left right root
  intro H hH
  subst hH
  refine (cost_letE_le _ _ _ (fun j => j = optInt ((pivotEdge left right C root).map Fin.val))
    (A := 500 * N ^ 3 + 10) (B := 4600 * N ^ 4) ?_ ?_ ?_).trans (by omega)
  · have := nonzeroInFn_costN hN (freeList left right C root) _ hFlen hHlen hHa
    simp only [Expr.cost, cost_call, Var.index, Expr.denote, Var.get]
    omega
  · simp only [Expr.denote, Var.get, denote_call, nonzeroInFn_apply]
    exact pivot_eq left right C root
  intro j hj
  subst hj
  have hJ : bits (optInt ((pivotEdge left right C root).map Fin.val)) ≤ N := by
    apply bits_optInt hN
    intro k hk
    cases hp : pivotEdge left right C root with
    | none => rw [hp] at hk; simp at hk
    | some j => rw [hp] at hk; simp at hk; have := j.2; omega
  refine (cost_letE_le _ _ _
    (fun CE => CE = (coordEdges left right C root).map fun e : Fin m => ((e : ℕ) : ℤ))
    (A := 130 * N ^ 2 + 10) (B := 4400 * N ^ 4) ?_ ?_ ?_).trans (by omega)
  · have := coordEdgesFn_cost hN _ (freeList left right C root) hFlen hJ
    simp only [Expr.cost, cost_call, Var.index, Expr.denote, Var.get]
    omega
  · simp only [Expr.denote, Var.get, denote_call, coordEdgesFn_apply]
    exact coordEdges_eq left right C root
  intro CE hCE
  subst hCE
  have hCElen : ((coordEdges left right C root).map fun e : Fin m => ((e : ℕ) : ℤ)).length ≤ N := by
    simp only [List.length_map]; exact le_trans hRank hm
  refine (cost_letE_le _ _ _ (fun R => R = ((rank left right C root : ℕ) : ℤ))
    (A := 12 * N ^ 2 + 5) (B := 4300 * N ^ 4) ?_ ?_ ?_).trans (by omega)
  · have := lengthFn_cost hN _ hCElen
    simp only [Expr.cost, cost_call, Var.index, Expr.denote, Var.get]
    omega
  · simp only [Expr.denote, Var.get, denote_call, lengthFn_apply, List.length_map]
    rfl
  intro R hR
  subst hR
  have hbR : bits ((rank left right C root : ℕ) : ℤ) ≤ N :=
    bits_nat_small hN5 (by have := le_trans hRank hm; omega)
  rw [cost_pair]
  have hmap := mapIdxFn_costN edgeItem (edgeParam left right C root) (edgeList left right)
    (K := 2000) (d := 3) hN (by norm_num) he.1 (fun j hj => by
      have hj' : j < m := by simpa [edgeList] using hj
      exact edgeItem_cost left right C root hN5 hm hn ⟨j, hj'⟩)
  simp only [Nat.reduceAdd] at hmap
  refine le_trans (Nat.add_le_add_right (Nat.add_le_add_left (cost_call_le (mapIdxFn edgeItem) _ _
    (edgeParam left right C root, edgeList left right) ?_ (A := 5 * N + 150) ?_ hmap) _) 1) ?_
  · simp only [Expr.denote, Var.get, edgeParam]
    by_cases h0 : ((rank left right C root : ℕ) : ℤ) = 0 <;> simp [CmpOp.eval, IntOp.eval, h0]
  · simp only [Expr.cost, Var.index, CmpOp.charge, IntOp.charge]
    repeat' split
    all_goals (try simp only [Expr.denote, Var.get, bits_zero', bits_four'] at *)
    all_goals omega
  · simp only [Expr.cost, Var.index]
    omega

/-- **Cost of the coordinate program**, as an explicit polynomial in the numbers of edges,
vertices and face rows. -/
theorem coordFn_cost :
    coordFn.costAt (edgeList left right, (colList C, ((n : ℤ), ((f : ℤ), ((root : ℕ) : ℤ))))) ≤
      17000 * (m + n + f + 5) ^ 5 :=
  coordFn_costN left right C root (by omega) (by omega) (by omega) (by omega)

end MWIS.FunCoordinates

end
