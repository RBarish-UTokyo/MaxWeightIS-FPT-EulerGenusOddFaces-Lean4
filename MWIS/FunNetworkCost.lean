module

public import MWIS.FunNetworkCostProgram
public import MWIS.FunNetworkDecode

/-!
# Cost of the `Fun` network program

`networkFn_cost` bounds the cost of `networkFn` on the encoded network input of
`(C, D, c)` by an explicit polynomial in the number of rows `f`, the number of
edges `m`, the residue count `GroupSize.residueCount D.rank`, a bound `Cb` on the
binary lengths of the costs and a bound `K` on the binary lengths of the free
coordinates of the unit vectors. `offsetFn_cost`, `bitsFn_cost` and
`decodeFn_cost` bound the other three programs.

Prepared 2026-10-23.
-/

@[expose] public section

namespace MWIS.FunNetwork

open MWIS.Fun MWIS.FunLP FPTHard

/-! ## Binary lengths -/

theorem lt_two_pow_bits (z : ℤ) : z.natAbs < 2 ^ bits z := Nat.lt_size_self _

theorem bits_mul_le (x y : ℤ) : bits (x * y) ≤ bits x + bits y := by
  rw [bits_le_iff, Int.natAbs_mul, pow_add]
  exact Nat.mul_lt_mul'' (lt_two_pow_bits x) (lt_two_pow_bits y)

theorem bits_add_le (x y : ℤ) : bits (x + y) ≤ max (bits x) (bits y) + 1 := by
  rw [bits_le_iff, pow_succ]
  have h1 := lt_two_pow_bits x
  have h2 := lt_two_pow_bits y
  have h3 : 2 ^ bits x ≤ 2 ^ max (bits x) (bits y) :=
    Nat.pow_le_pow_right (by omega) (le_max_left _ _)
  have h4 : 2 ^ bits y ≤ 2 ^ max (bits x) (bits y) :=
    Nat.pow_le_pow_right (by omega) (le_max_right _ _)
  have h5 := Int.natAbs_add_le x y
  omega

/-! ## Membership in the encoded lists -/

theorem mem_indexPow {α : Type*} : ∀ (l : List α) (k p : ℤ) (y : ℤ × ℤ × α),
    y ∈ indexPow k p l → ∃ i : ℕ, i < l.length ∧ y.1 = k + i ∧ y.2.1 = p * 2 ^ i ∧ y.2.2 ∈ l
  | [], _, _, _, h => by simp [indexPow] at h
  | a :: l, k, p, y, h => by
    simp only [indexPow, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨0, by simp, by simp, by simp, by simp⟩
    · obtain ⟨i, hi, h1, h2, h3⟩ := mem_indexPow l (k + 1) (2 * p) y h
      refine ⟨i + 1, by simp <;> omega, by rw [h1]; push_cast; ring, by rw [h2, pow_succ]; ring,
        by simp [h3]⟩

theorem mem_indexFrom {α : Type*} : ∀ (l : List α) (k : ℤ) (y : ℤ × α),
    y ∈ indexFrom k l → ∃ i : ℕ, i < l.length ∧ y.1 = k + i ∧ y.2 ∈ l
  | [], _, _, h => by simp [indexFrom] at h
  | a :: l, k, y, h => by
    simp only [indexFrom, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨0, by simp, by simp, by simp⟩
    · obtain ⟨i, hi, h1, h2⟩ := mem_indexFrom l (k + 1) y h
      exact ⟨i + 1, by simp <;> omega, by rw [h1]; push_cast; ring, by simp [h2]⟩

theorem mem_arcsE (P : ℤ) (edges : List EdgeIn) (a : ArcRec) (h : a ∈ arcsE P edges) :
    ∃ y ∈ indexPow 0 1 edges, ∃ b : Bool,
      a = (y.1, b, srcE y.2.2.1 b, tgtE y.2.2.1 b, y.2.2.2.2.1, y.2.2.2.1,
        2 * (P * y.2.2.2.2.2 + y.2.1)) := by
  simp only [arcsE, List.mem_flatMap, edgeArcs, List.mem_map] at h
  obtain ⟨y, hy, b, _, rfl⟩ := h
  exact ⟨y, hy, b, rfl⟩

theorem length_arcsE (P : ℤ) (edges : List EdgeIn) :
    (arcsE P edges).length ≤ 2 * edges.length := by
  unfold arcsE
  refine (length_flatMap_le _ _ 2 (fun y _ => length_edgeArcs P y)).trans ?_
  rw [length_indexPow]; omega

theorem oppE_bounds (s : ℤ) : s - 1 ≤ oppE s ∧ oppE s ≤ s + 1 := by
  unfold oppE; split_ifs <;> omega

theorem srcE_bounds (col : List ℤ) (b : Bool) (F : ℤ) (hF : 0 ≤ F)
    (h : ∀ z ∈ col, 1 ≤ z ∧ z ≤ F) :
    0 ≤ srcE col b ∧ srcE col b ≤ F + 1 := by
  rcases col with _ | ⟨s, _ | ⟨t, rest⟩⟩
  · simp [srcE]; omega
  · have hs := h s (by simp)
    have := oppE_bounds s
    cases b <;> simp [srcE] <;> omega
  · have hs := h s (by simp)
    have ht := h t (by simp)
    have := oppE_bounds s
    have := oppE_bounds t
    cases b <;> simp [srcE] <;> omega

theorem tgtE_bounds (col : List ℤ) (b : Bool) (F : ℤ) (hF : 0 ≤ F)
    (h : ∀ z ∈ col, 1 ≤ z ∧ z ≤ F) :
    0 ≤ tgtE col b ∧ tgtE col b ≤ F := by
  rcases col with _ | ⟨s, _ | ⟨t, rest⟩⟩
  · simp [tgtE]; omega
  · have hs := h s (by simp)
    cases b <;> simp [tgtE] <;> omega
  · have hs := h s (by simp)
    have ht := h t (by simp)
    cases b <;> simp [tgtE] <;> omega

theorem zipWith_mod_bounds (μ : ℤ) (hμ : 0 < μ) : ∀ (g h : List ℤ),
    ∀ z ∈ List.zipWith (fun x y => (x + y) % μ) g h, 0 ≤ z ∧ z < μ
  | [], _, z, hz => by simp at hz
  | _ :: _, [], z, hz => by simp at hz
  | a :: g, b :: h, z, hz => by
    simp only [List.zipWith_cons_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ hμ⟩
    · exact zipWith_mod_bounds μ hμ g h z hz

theorem addE_bounds (μ : ℤ) (hμ : 2 ≤ μ) (g h : List ℤ) :
    (addE μ g h).length ≤ g.length ∧ ∀ z ∈ addE μ g h, 0 ≤ z ∧ z < μ := by
  rcases g with _ | ⟨a, g⟩
  · simp [addE]
  · rcases h with _ | ⟨b, h⟩
    · simp [addE]
    · simp only [addE, List.length_cons, List.length_zipWith, List.mem_cons]
      refine ⟨by omega, ?_⟩
      rintro z (rfl | hz)
      · have := Int.emod_nonneg (a + b) (by norm_num : (2 : ℤ) ≠ 0)
        have := Int.emod_lt_of_pos (a + b) (by norm_num : (0 : ℤ) < 2)
        omega
      · exact zipWith_mod_bounds μ (by omega) g h z hz

theorem mem_colsE (μ : ℤ) (S : List ℤ) (A : List ArcRec) (G : List (List ℤ)) (c : ColRec)
    (h : c ∈ colsE μ S A G) :
    ∃ v ∈ S, ∃ a ∈ A, ∃ g ∈ G, c = (v, a, g, addE μ g a.2.2.2.2.1) := by
  simp only [colsE, List.mem_flatMap, List.mem_map] at h
  obtain ⟨v, hv, a, ha, g, hg, rfl⟩ := h
  exact ⟨v, hv, a, ha, g, hg, rfl⟩

theorem length_colsE (μ : ℤ) (S : List ℤ) (A : List ArcRec) (G : List (List ℤ)) :
    (colsE μ S A G).length = S.length * (A.length * G.length) := by
  unfold colsE
  rw [length_flatMap_const _ _ (A.length * G.length) (fun v _ => by
    rw [length_flatMap_const _ _ G.length (fun a _ => by rw [List.length_map])])]

theorem length_nodesE (S : List ℤ) (G : List (List ℤ)) :
    (nodesE S G).length ≤ G.length + S.length * (S.length * G.length) := by
  unfold nodesE
  rw [List.length_append, List.length_map]
  have : (S.flatMap fun v => S.flatMap fun u =>
      if u = v then [] else G.map fun g => ((v, u, g) : NodeE)).length ≤
      S.length * (S.length * G.length) := by
    refine length_flatMap_le _ _ _ (fun v _ => length_flatMap_le _ _ _ (fun u _ => ?_))
    split_ifs <;> simp
  omega

theorem nodesE_small (L : ℕ) (S : List ℤ) (G : List (List ℤ)) (hS : ∀ v ∈ S, v.natAbs ≤ L)
    (hG : ∀ g ∈ G, SmallList L L g) (hL : 1 ≤ L) : ∀ n ∈ nodesE S G, NodeSmall L n := by
  intro n hn
  simp only [nodesE, List.mem_append, List.mem_map, List.mem_flatMap] at hn
  rcases hn with ⟨g, hg, rfl⟩ | ⟨v, hv, u, hu, hn⟩
  · exact ⟨by simp <;> omega, by simp <;> omega, hG g hg⟩
  · split_ifs at hn
    · simp at hn
    · simp only [List.mem_map] at hn
      obtain ⟨g, hg, rfl⟩ := hn
      exact ⟨hS v hv, hS u hu, hG g hg⟩

theorem length_rowsE (N : ℤ) (nodes : List NodeE) (r : ℤ) :
    (rowsE N nodes r).length = N.toNat + 2 * (nodes.length + r.toNat) := by
  unfold rowsE eqE
  rw [List.length_append, List.length_map, length_zrange,
    length_flatMap_const _ _ 2 (fun _ _ => rfl)]
  simp [length_zrange]
  ring

theorem rowsE_small (L : ℕ) (N : ℤ) (nodes : List NodeE) (r : ℤ)
    (hn : ∀ n ∈ nodes, NodeSmall L n) (hN : N.toNat ≤ L) (hr : r.toNat ≤ L) (hL : 2 ≤ L) :
    ∀ ρ ∈ rowsE N nodes r, RowSmall L ρ := by
  have hd : NodeSmall L dummyNode := ⟨by simp [dummyNode] <;> omega, by simp [dummyNode] <;> omega,
    by simp [SmallList, dummyNode]⟩
  intro ρ hρ
  simp only [rowsE, eqE, List.mem_append, List.mem_map, List.mem_flatMap] at hρ
  rcases hρ with ⟨i, hi, rfl⟩ | ⟨σ, hσ, hρ⟩
  · have := mem_zrange hi
    exact ⟨by simp, by simp, by dsimp only; omega, hd⟩
  · simp only [signedRows, List.mem_cons, List.not_mem_nil, or_false] at hρ
    rcases hσ with ⟨u, hu, rfl⟩ | ⟨d, hd', rfl⟩
    · rcases hρ with rfl | rfl <;> exact ⟨by simp <;> omega, by simp, by simp, hn u hu⟩
    · have := mem_zrange hd'
      rcases hρ with rfl | rfl <;> exact ⟨by simp <;> omega, by simp, by dsimp only; omega, hd⟩

/-! ## The side condition of the network program -/

/-- The conditions on one encoded edge record used by the cost bound. -/
structure EdgeGood (F r μ Cb K : ℕ) (e : EdgeIn) : Prop where
  col : ∀ z ∈ e.1, 1 ≤ z ∧ z ≤ 2 * (F : ℤ)
  free_len : e.2.1.length = r
  free_bits : ∀ z ∈ e.2.1, bits z ≤ K
  res : ∀ z ∈ e.2.2.1, 0 ≤ z ∧ z < (μ : ℤ)
  cost_nonneg : 0 ≤ e.2.2.2
  cost_bits : bits e.2.2.2 ≤ Cb

/-- The polynomial size facts used by the side condition. -/
theorem network_sizes (L F m r μ : ℕ) (hμ : 2 ≤ μ)
    (hL : 16 * (F + 1) ^ 2 * (m + 1) * (2 * μ ^ r + r + μ) ≤ L) (A : ℕ) (hA : A ≤ 2 * m) :
    2 * F + 1 ≤ L ∧ μ ≤ L ∧ r + 1 ≤ L ∧ 2 * μ ^ r ≤ L ∧ 2 * m + 2 ≤ L ∧
      A * (2 * μ ^ r) ≤ L ∧ (2 * F + 1) * (A * (2 * μ ^ r)) ≤ L ∧
      (2 * F + 1) * (2 * μ ^ r) ≤ L ∧ (2 * F + 1) * ((2 * F + 1) * (2 * μ ^ r)) ≤ L ∧
      (2 * F + 1) * (A * (2 * μ ^ r)) +
        2 * (2 * μ ^ r + (2 * F + 1) * ((2 * F + 1) * (2 * μ ^ r)) + r) ≤ L := by
  set a := F + 1
  set b := m + 1
  set c := 2 * μ ^ r + r + μ
  set R := 2 * μ ^ r
  have ha : 1 ≤ a := by omega
  have hb : 1 ≤ b := by omega
  have hR : 2 ≤ R := by
    have : 1 ≤ μ ^ r := Nat.one_le_pow _ _ (by omega)
    omega
  have hc : R + r + 2 ≤ c := by omega
  have hc1 : 1 ≤ c := by omega
  set X := a * a * b * c
  have hX : 16 * X ≤ L := by
    have e : 16 * X = 16 * a ^ 2 * b * c := by ring
    rw [e]; exact hL
  have haX : a ≤ X := by
    calc a = a * 1 * 1 * 1 := by ring
      _ ≤ a * a * b * c := by gcongr
  have hbX : b ≤ X := by
    calc b = 1 * 1 * b * 1 := by ring
      _ ≤ a * a * b * c := by gcongr
  have hcX : c ≤ X := by
    calc c = 1 * 1 * 1 * c := by ring
      _ ≤ a * a * b * c := by gcongr
  have habc : a * b * c ≤ X := by
    calc a * b * c = 1 * a * b * c := by ring
      _ ≤ a * a * b * c := by gcongr
  have hac : a * a * c ≤ X := by
    calc a * a * c = a * a * 1 * c := by ring
      _ ≤ a * a * b * c := by gcongr
  have hAR : A * R ≤ 2 * (b * c) := by
    calc A * R ≤ (2 * b) * c := Nat.mul_le_mul (by omega) (by omega)
      _ = 2 * (b * c) := by ring
  have hbc : b * c ≤ X := by
    calc b * c = 1 * 1 * b * c := by ring
      _ ≤ a * a * b * c := by gcongr
  have h1 : (2 * F + 1) * (A * R) ≤ 4 * X := by
    calc (2 * F + 1) * (A * R) ≤ (2 * a) * (2 * (b * c)) := Nat.mul_le_mul (by omega) hAR
      _ = 4 * (a * b * c) := by ring
      _ ≤ 4 * X := by omega
  have h2 : (2 * F + 1) * R ≤ 2 * X := by
    calc (2 * F + 1) * R ≤ (2 * a) * c := Nat.mul_le_mul (by omega) (by omega)
      _ = 2 * (a * 1 * c) := by ring
      _ ≤ 2 * (a * a * c) := by gcongr
      _ ≤ 2 * X := by omega
  have h3 : (2 * F + 1) * ((2 * F + 1) * R) ≤ 4 * X := by
    calc (2 * F + 1) * ((2 * F + 1) * R) ≤ (2 * a) * ((2 * a) * c) :=
          Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by omega) (by omega))
      _ = 4 * (a * a * c) := by ring
      _ ≤ 4 * X := by omega
  have hRc : R ≤ X := by omega
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega⟩

theorem networkFn_ok (L B Cb K F r μ : ℕ) (edges : List EdgeIn) (hμ : 2 ≤ μ)
    (he : ∀ e ∈ edges, EdgeGood F r μ Cb K e)
    (hL : 16 * (F + 1) ^ 2 * (edges.length + 1) * (2 * μ ^ r + r + μ) ≤ L)
    (hB : 2 * L + edges.length + Cb + K + 8 ≤ B) :
    OkAt L B networkFn ((F : ℤ), (r : ℤ), (μ : ℤ), edges) := by
  have hP : ((edges.length : ℤ) + 1).toNat = edges.length + 1 := by omega
  simp only [OkAt, networkFn, Ok, ok_call, Expr.denote, Var.get, denote_call, IntOp.eval,
    statesFn_apply, groupFn_apply, powFn_apply, lengthFn_apply, arcsFn_apply, colsFn_apply,
    indexFromFn_apply, nodesFn_apply, rowsFn_apply, replFn_apply, true_and, and_true, bits_one,
    Int.toNat_natCast, hP]
  set m := edges.length with hm
  set P : ℤ := 2 ^ (m + 1) with hPdef
  set states := statesE (F : ℤ) with hstates
  set groups := groupE (r : ℤ) (μ : ℤ) with hgroups
  set arcs := arcsE P edges with harcs
  set cols := colsE (μ : ℤ) states arcs groups with hcols
  set nodes := nodesE states groups with hnodes
  have hsl : states.length = 2 * F + 1 := by rw [hstates, length_statesE, Int.toNat_natCast]
  have hgl : groups.length = 2 * μ ^ r := by rw [hgroups, length_groupE]; simp
  have hal : arcs.length ≤ 2 * m := length_arcsE P edges
  have hcl : cols.length = (2 * F + 1) * (arcs.length * (2 * μ ^ r)) := by
    rw [hcols, length_colsE, hsl, hgl]
  have hnl : nodes.length ≤ 2 * μ ^ r + (2 * F + 1) * ((2 * F + 1) * (2 * μ ^ r)) := by
    have := length_nodesE states groups
    rw [hsl, hgl] at this; exact this
  obtain ⟨hFL, hμL, hrL, hRL, hmL, hARL, hcolL, hSRL, hSSRL, hrowL⟩ :=
    network_sizes L F m r μ hμ hL arcs.length hal
  have hLB : 2 * L + 2 ≤ B := by omega
  have hL1 : 1 ≤ L := by omega
  have hL2 : 2 ≤ L := by omega
  -- facts on the lists
  have hstate_mem : ∀ v ∈ states, 0 ≤ v ∧ v ≤ 2 * (F : ℤ) := fun v hv =>
    mem_statesE (F : ℤ) (by omega) v hv
  have hstate_abs : ∀ v ∈ states, v.natAbs ≤ L := fun v hv => by
    have := hstate_mem v hv; omega
  have hgroup_mem : ∀ g ∈ groups, g.length = r + 1 ∧ ∀ z ∈ g, 0 ≤ z ∧ z < (μ : ℤ) := by
    intro g hg
    have := mem_groupE (r : ℤ) (μ : ℤ) (by omega) g hg
    simpa using this
  have hgroup_small : ∀ g ∈ groups, SmallList L L g := fun g hg => by
    obtain ⟨h1, h2⟩ := hgroup_mem g hg
    exact ⟨by omega, fun z hz => by have := h2 z hz; omega⟩
  have hgroup_abs : ∀ g ∈ groups, g.length ≤ L ∧ ∀ z ∈ g, z.natAbs ≤ μ := fun g hg => by
    obtain ⟨h1, h2⟩ := hgroup_mem g hg
    exact ⟨by omega, fun z hz => by have := h2 z hz; omega⟩
  have harc_mem : ∀ a ∈ arcs, ∃ e ∈ edges, ∃ i : ℕ, i < m ∧ ∃ b : Bool,
      a = ((i : ℤ), b, srcE e.1 b, tgtE e.1 b, e.2.2.1, e.2.1,
        2 * (P * e.2.2.2 + 2 ^ i)) := by
    intro a ha
    obtain ⟨y, hy, b, rfl⟩ := mem_arcsE P edges a ha
    obtain ⟨i, hi, h1, h2, h3⟩ := mem_indexPow edges 0 1 y hy
    refine ⟨y.2.2, h3, i, hi, b, ?_⟩
    rw [h1, h2]; simp
  have harc_lab : ∀ a ∈ arcs, ∀ z ∈ a.2.2.2.2.1, z.natAbs ≤ μ := by
    intro a ha z hz
    obtain ⟨e, he', i, hi, b, rfl⟩ := harc_mem a ha
    have := (he e he').res z hz
    omega
  -- the numbered edges
  have harcin : ∀ y ∈ indexPow 0 1 edges, ArcInputOk B (P, y) := by
    intro y hy
    obtain ⟨i, hi, h1, h2, h3⟩ := mem_indexPow edges 0 1 y hy
    have hg := he _ h3
    have hc := hg.cost_bits
    have hbP : bits P = m + 2 := by rw [hPdef, bits_two_pow]
    have hbp : bits y.2.1 ≤ m := by
      rw [h2, one_mul, bits_two_pow]; omega
    have hPc : bits (P * y.2.2.2.2.2) ≤ m + 2 + Cb := (bits_mul_le _ _).trans (by omega)
    have hPcp : bits (P * y.2.2.2.2.2 + y.2.1) ≤ m + 3 + Cb := by
      refine (bits_add_le _ _).trans ?_
      have : max (bits (P * y.2.2.2.2.2)) (bits y.2.1) ≤ m + 2 + Cb := max_le hPc (by omega)
      omega
    unfold ArcInputOk
    dsimp only
    refine ⟨fun z hz => ?_, by omega, by omega, by omega, by omega, by omega⟩
    have := hg.col z hz
    omega
  -- the columns
  have hcol_small : ∀ jc ∈ indexFrom 0 cols, ColSmall L K jc := by
    intro jc hjc
    obtain ⟨j, hj, hj1, hj2⟩ := mem_indexFrom cols 0 jc hjc
    obtain ⟨v, hv, a, ha, g, hg, hcg⟩ := mem_colsE (μ : ℤ) states arcs groups jc.2 hj2
    obtain ⟨e, he', i, hi, b, rfl⟩ := harc_mem a ha
    have hge := he e he'
    have hsrc := srcE_bounds e.1 b (2 * (F : ℤ)) (by omega) hge.col
    have htgt := tgtE_bounds e.1 b (2 * (F : ℤ)) (by omega) hge.col
    obtain ⟨hadd1, hadd2⟩ := addE_bounds (μ : ℤ) (by omega) g e.2.2.1
    obtain ⟨hgl1, hgl2⟩ := hgroup_mem g hg
    have hjL : j < L := by omega
    rcases jc with ⟨j', c'⟩
    simp only at hj1 hcg
    subst hcg
    refine ⟨by omega, hstate_abs v hv, by dsimp only; omega, by dsimp only; omega,
      hgroup_small g hg, ⟨by dsimp only; omega, fun z hz => ?_⟩, ?_, hge.free_bits⟩
    · have := hadd2 z hz; omega
    · dsimp only; rw [hge.free_len]; omega
  -- the nodes and rows
  have hnode_small : ∀ n ∈ nodes, NodeSmall L n :=
    nodesE_small L states groups hstate_abs hgroup_small hL1
  have hrow_small : ∀ ρ ∈ rowsE (cols.length : ℤ) nodes (r : ℤ), RowSmall L ρ :=
    rowsE_small L _ nodes _ hnode_small (by rw [Int.toNat_natCast, hcl]; exact hcolL)
      (by simp; omega) hL2
  have hrows_len : (rowsE (cols.length : ℤ) nodes (r : ℤ)).length ≤ L := by
    rw [length_rowsE, Int.toNat_natCast, Int.toNat_natCast, hcl]
    omega
  have hcolsI_len : (indexFrom 0 cols).length ≤ L := by
    rw [length_indexFrom, hcl]; exact hcolL
  have bitsNat : ∀ n : ℕ, n ≤ L → bits (n : ℤ) ≤ B := fun n hn =>
    bits_le_of_natAbs (by simp; omega)
  refine ⟨statesFn_ok L B _ (by simp; omega) hLB (bitsNat F (by omega)),
    groupFn_ok L B _ (by omega) (by simp; omega) (bitsNat μ hμL) (by simp; omega)
      (bitsNat r (by omega)) (by simpa using hRL) (by omega),
    ⟨⟨lengthFn_ok L B _ _ (by omega) (by omega), bitsNat m (by omega), by omega⟩,
      powFn_ok L B _ (by omega) (bits_le_of_natAbs (by omega)) (by omega)⟩,
    arcsFn_ok L B _ (by dsimp only; omega) (by omega) hL2 harcin,
    colsFn_ok L B μ _ hgroup_abs harc_lab (by omega) (bitsNat μ hμL) (by omega)
      (by rw [hgl]; exact hRL) (by dsimp only; omega) (by rw [hgl]; exact hARL) (by rw [hsl]; omega)
      (by rw [hsl, hgl]; exact hcolL),
    indexFromFn_ok L B _ _ (by rw [hcl]; exact hcolL) (by omega),
    nodesFn_ok L B _ (fun u hu => bits_le_of_natAbs ((hstate_abs u hu).trans (by omega)))
      (by rw [hgl]; exact hRL) (by rw [hsl]; omega) (by rw [hsl, hgl]; exact hSRL)
      (by rw [hsl, hgl]; exact hSSRL),
    ⟨lengthFn_ok L B _ _ (by rw [hcl]; exact hcolL) (by omega),
      rowsFn_ok L B _ (by simp; rw [hcl]; exact hcolL) (bitsNat _ (by rw [hcl]; exact hcolL))
        (by dsimp only; omega) (by simp; omega) (bitsNat r (by omega)) (by omega)
        (by simp only [Int.toNat_natCast]; omega) hL2⟩,
    replFn_ok L B _ (by simp; omega) (bitsNat r (by omega)),
    mapWith_ok L B _ _ hrows_len (fun ρ hρ => rowMatFn_ok L B K _ hcolsI_len (hrow_small ρ hρ)
      hcol_small hLB (by omega) hL1),
    mapWith_ok L B _ _ hrows_len (fun ρ hρ => rhsFn_ok L B _ (hrow_small ρ hρ)
      ⟨by simp; omega, by intro z hz; simp at hz; omega⟩
      ⟨by simp; omega, by intro z hz; simp at hz; omega⟩ hLB hL1),
    mapWith_ok L B _ _ hcolsI_len (fun jc _ => objFn_ok L B _)⟩

/-! ## The network program on actual inputs -/

theorem weight_networkFn : weight networkFn = 2039 := by decide

theorem depth_networkFn : depth networkFn = 4 := by decide

theorem two_le_modulus (r : ℕ) : 2 ≤ GroupSize.modulus r := by
  unfold GroupSize.modulus; split_ifs <;> omega

theorem modulus_add_le (r : ℕ) :
    2 * GroupSize.modulus r ^ r + r + GroupSize.modulus r ≤ 3 * GroupSize.residueCount r := by
  unfold GroupSize.residueCount
  have h2 := two_le_modulus r
  have h1 : r < 2 ^ r := Nat.lt_two_pow_self
  have h3 : 2 ^ r ≤ GroupSize.modulus r ^ r := Nat.pow_le_pow_left h2 r
  have h4 : GroupSize.modulus r ≤ 2 * GroupSize.modulus r ^ r := by
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · simp [GroupSize.modulus]
    · have := Nat.le_self_pow (Nat.pos_iff_ne_zero.mp hr) (GroupSize.modulus r)
      omega
  omega

theorem stubCode_bounds {f : ℕ} (s : Walks.Stub (Fin f)) :
    1 ≤ stubCode s ∧ stubCode s ≤ 2 * (f : ℤ) := by
  rcases s with ⟨k, b⟩
  have := k.isLt
  cases b <;> simp [stubCode] <;> omega

theorem edgeInput_good {f m : ℕ} (C : Fin m → Walks.Column (Fin f)) (D : CoordinateData m)
    (c : Fin m → ℕ) (Cb K : ℕ) (hK : ∀ e d, bits (D.free (Pi.single e 1) d) ≤ K)
    (hc : ∀ e, (c e).size ≤ Cb) :
    ∀ x ∈ edgeInput C D c, EdgeGood f D.rank (GroupSize.modulus D.rank) Cb K x := by
  intro x hx
  simp only [edgeInput, List.mem_ofFn] at hx
  obtain ⟨e, rfl⟩ := hx
  refine ⟨?_, by simp, ?_, ?_, by simp, by simpa [bits] using hc e⟩
  · intro z hz
    cases h : C e with
    | zero => simp [h, columnCode] at hz
    | one s =>
      simp only [h, columnCode, List.mem_cons, List.not_mem_nil, or_false] at hz
      subst hz; exact stubCode_bounds s
    | two s t =>
      simp only [h, columnCode, List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      · exact stubCode_bounds s
      · exact stubCode_bounds t
  · intro z hz
    simp only [List.mem_ofFn] at hz
    obtain ⟨d, rfl⟩ := hz
    exact hK e d
  · intro z hz
    have h2 := two_le_modulus D.rank
    simp only [residueCode, List.mem_cons, List.mem_ofFn] at hz
    rcases hz with rfl | ⟨i, rfl⟩
    · have := ZMod.val_lt (D.residue (Pi.single e 1)).1
      omega
    · have := ZMod.val_lt ((D.residue (Pi.single e 1)).2 i)
      omega

/-- The list-length parameter of the network program. -/
def netL (f m r : ℕ) : ℕ := 48 * (f + 1) ^ 2 * (m + 1) * GroupSize.residueCount r

/-- The binary-length parameter of the network program. -/
def netB (f m r Cb K : ℕ) : ℕ := 2 * netL f m r + m + Cb + K + 8

/-- **Cost of the network program.** For costs of binary length at most `Cb` and
free coordinates of the unit vectors of binary length at most `K`, `networkFn`
runs on the encoded input within an explicit polynomial in `f`, `m`,
`residueCount D.rank`, `Cb` and `K`. -/
theorem networkFn_cost {f m : ℕ} (C : Fin m → Walks.Column (Fin f)) (D : CoordinateData m)
    (c : Fin m → ℕ) (Cb K : ℕ) (hK : ∀ e d, bits (D.free (Pi.single e 1) d) ≤ K)
    (hc : ∀ e, (c e).size ≤ Cb) :
    networkFn.costAt (networkInput C D c) ≤
      2039 * ((netL f m D.rank + 1) * (2 * netB f m D.rank Cb K + 2) ^ 2) ^ 5 := by
  have hlen : (edgeInput C D c).length = m := by simp [edgeInput]
  have hok := networkFn_ok (netL f m D.rank) (netB f m D.rank Cb K) Cb K f D.rank
    (GroupSize.modulus D.rank) (edgeInput C D c) (two_le_modulus _)
    (edgeInput_good C D c Cb K hK hc) (by
      rw [hlen, netL]
      have := modulus_add_le D.rank
      calc 16 * (f + 1) ^ 2 * (m + 1) *
            (2 * GroupSize.modulus D.rank ^ D.rank + D.rank + GroupSize.modulus D.rank) ≤
          16 * (f + 1) ^ 2 * (m + 1) * (3 * GroupSize.residueCount D.rank) :=
            Nat.mul_le_mul_left _ this
        _ = 48 * (f + 1) ^ 2 * (m + 1) * GroupSize.residueCount D.rank := by ring)
    (by rw [hlen, netB])
  have := costAt_le_weight _ _ networkFn _ hok
  rw [weight_networkFn, depth_networkFn] at this
  exact this

/-! ## Offset, search width and decoding -/

theorem total_terms (Cb : ℕ) (edges : List EdgeIn)
    (hc : ∀ e ∈ edges, 0 ≤ e.2.2.2 ∧ bits e.2.2.2 ≤ Cb) :
    ∀ y ∈ indexPow 0 1 edges,
      0 ≤ (2 : ℤ) ^ (edges.length + 1) * y.2.2.2.2.2 + y.2.1 ∧
      (2 : ℤ) ^ (edges.length + 1) * y.2.2.2.2.2 + y.2.1 ≤ 2 ^ (edges.length + 2 + Cb) ∧
      bits y.2.1 ≤ edges.length ∧
      bits ((2 : ℤ) ^ (edges.length + 1) * y.2.2.2.2.2) ≤ edges.length + 2 + Cb ∧
      bits y.2.2.2.2.2 ≤ Cb := by
  intro y hy
  set m := edges.length
  obtain ⟨i, hi, h1, h2, h3⟩ := mem_indexPow edges 0 1 y hy
  obtain ⟨hc0, hcb⟩ := hc _ h3
  rw [h2, one_mul]
  have hci : y.2.2.2.2.2 < 2 ^ Cb := by
    have := lt_two_pow_bits y.2.2.2.2.2
    have h' : (2 : ℕ) ^ bits y.2.2.2.2.2 ≤ 2 ^ Cb := Nat.pow_le_pow_right (by omega) hcb
    have : (y.2.2.2.2.2.natAbs : ℤ) < 2 ^ Cb := by exact_mod_cast lt_of_lt_of_le this h'
    omega
  have hpi : (2 : ℤ) ^ i ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hi.le
  have hP0 : (0 : ℤ) < 2 ^ (m + 1) := by positivity
  have hbP : bits ((2 : ℤ) ^ (m + 1)) = m + 2 := bits_two_pow _
  refine ⟨by positivity, ?_, by rw [bits_two_pow]; omega, (bits_mul_le _ _).trans (by omega), hcb⟩
  have e1 : (2 : ℤ) ^ (m + 1) * y.2.2.2.2.2 ≤ 2 ^ (m + 1) * (2 ^ Cb - 1) := by
    apply mul_le_mul_of_nonneg_left (by omega) hP0.le
  have e2 : (2 : ℤ) ^ (m + 2 + Cb) = 2 ^ (m + 1) * 2 ^ Cb * 2 := by ring
  have e3 : (2 : ℤ) ^ m ≤ 2 ^ (m + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  nlinarith

theorem total_prefix_bits (Cb : ℕ) (edges : List EdgeIn)
    (hc : ∀ e ∈ edges, 0 ≤ e.2.2.2 ∧ bits e.2.2.2 ≤ Cb) (i : ℕ) :
    bits (((indexPow 0 1 edges).take i).foldl
      (fun acc y => acc + ((2 : ℤ) ^ (edges.length + 1) * y.2.2.2.2.2 + y.2.1)) 0) ≤
      2 * edges.length + Cb + 3 := by
  have hterm := total_terms Cb edges hc
  set m := edges.length
  set T : ℤ := 2 ^ (m + 2 + Cb) with hT
  rw [foldl_add_eq, zero_add]
  have hmem : ∀ y ∈ (indexPow 0 1 edges).take i, y ∈ indexPow 0 1 edges :=
    fun y hy => List.mem_of_mem_take hy
  have h0 : 0 ≤ (((indexPow 0 1 edges).take i).map
      (fun y => (2 : ℤ) ^ (m + 1) * y.2.2.2.2.2 + y.2.1)).sum :=
    List.sum_nonneg (by
      intro z hz
      simp only [List.mem_map] at hz
      obtain ⟨y, hy, rfl⟩ := hz
      exact (hterm y (hmem y hy)).1)
  have h1 : (((indexPow 0 1 edges).take i).map
      (fun y => (2 : ℤ) ^ (m + 1) * y.2.2.2.2.2 + y.2.1)).sum ≤
      (((indexPow 0 1 edges).take i).map
        (fun y => (2 : ℤ) ^ (m + 1) * y.2.2.2.2.2 + y.2.1)).length • T :=
    List.sum_le_card_nsmul _ _ (by
      intro z hz
      simp only [List.mem_map] at hz
      obtain ⟨y, hy, rfl⟩ := hz
      exact (hterm y (hmem y hy)).2.1)
  rw [List.length_map, List.length_take, length_indexPow, nsmul_eq_mul] at h1
  have hmin : ((min i m : ℕ) : ℤ) ≤ m := by exact_mod_cast min_le_right _ _
  have hT0 : 0 ≤ T := by positivity
  have h2 := h1.trans (mul_le_mul_of_nonneg_right hmin hT0)
  refine (bits_mono (y := (m : ℤ) * T) ?_).trans ?_
  · have : 0 ≤ (m : ℤ) * T := by positivity
    omega
  · refine (bits_mul_le _ _).trans ?_
    have : bits (m : ℤ) ≤ m := bits_le_of_natAbs (by simp)
    rw [hT, bits_two_pow]; omega

theorem totalE_bits (Cb : ℕ) (edges : List EdgeIn)
    (hc : ∀ e ∈ edges, 0 ≤ e.2.2.2 ∧ bits e.2.2.2 ≤ Cb) :
    bits (totalE edges) ≤ 2 * edges.length + Cb + 3 := by
  have := total_prefix_bits Cb edges hc (indexPow 0 1 edges).length
  rwa [List.take_length] at this

theorem totalFn_ok (L B Cb : ℕ) (edges : List EdgeIn)
    (hc : ∀ e ∈ edges, 0 ≤ e.2.2.2 ∧ bits e.2.2.2 ≤ Cb)
    (hL : edges.length + 1 ≤ L) (hB : L + 2 * edges.length + Cb + 8 ≤ B) :
    OkAt L B totalFn edges := by
  have hterm := total_terms Cb edges hc
  have hsum := total_prefix_bits Cb edges hc
  have hP : ((edges.length : ℤ) + 1).toNat = edges.length + 1 := by omega
  have hbP : bits ((2 : ℤ) ^ (edges.length + 1)) = edges.length + 2 := bits_two_pow _
  simp only [OkAt, totalFn, Ok, ok_call, Expr.denote, Var.get, denote_call, IntOp.eval,
    powFn_apply, lengthFn_apply, indexPowFn_apply, true_and, bits_one, hP]
  refine ⟨⟨⟨lengthFn_ok L B _ _ (by omega) (by omega), bits_le_of_natAbs (by simp; omega),
    by omega⟩, powFn_ok L B _ (by omega) (bits_le_of_natAbs (by omega)) (by omega)⟩,
    indexPowFn_ok L B _ (by omega) (by omega), by rw [length_indexPow]; omega,
    FoldOK.of_prefix _ _ _ _ (fun i hi => ?_)⟩
  obtain ⟨_, _, hb1, hb2, hb4⟩ := hterm _ (List.getElem_mem hi)
  have hb3 : bits ((2 : ℤ) ^ (edges.length + 1) * ((indexPow 0 1 edges)[i]).2.2.2.2.2 +
      ((indexPow 0 1 edges)[i]).2.1) ≤ edges.length + 3 + Cb := by
    refine (bits_add_le _ _).trans ?_
    have : max (bits ((2 : ℤ) ^ (edges.length + 1) * ((indexPow 0 1 edges)[i]).2.2.2.2.2))
      (bits ((indexPow 0 1 edges)[i]).2.1) ≤ edges.length + 2 + Cb := max_le hb2 (by omega)
    omega
  exact ⟨⟨⟨by omega, by omega⟩, by omega, by omega⟩, (hsum i).trans (by omega), by omega⟩

theorem weight_offsetFn : weight offsetFn = 95 := by decide
theorem depth_offsetFn : depth offsetFn = 1 := by decide
theorem weight_bitsFn : weight bitsFn = 96 := by decide
theorem depth_bitsFn : depth bitsFn = 1 := by decide
theorem weight_decodeFn : weight decodeFn = 33 := by decide
theorem depth_decodeFn : depth decodeFn = 1 := by decide

theorem edgeInput_costs {f m : ℕ} (C : Fin m → Walks.Column (Fin f)) (D : CoordinateData m)
    (c : Fin m → ℕ) (Cb : ℕ) (hc : ∀ e, (c e).size ≤ Cb) :
    ∀ x ∈ edgeInput C D c, 0 ≤ x.2.2.2 ∧ bits x.2.2.2 ≤ Cb := by
  intro x hx
  simp only [edgeInput, List.mem_ofFn] at hx
  obtain ⟨e, rfl⟩ := hx
  exact ⟨by simp, by simpa [bits] using hc e⟩

theorem length_edgeInput {f m : ℕ} (C : Fin m → Walks.Column (Fin f)) (D : CoordinateData m)
    (c : Fin m → ℕ) : (edgeInput C D c).length = m := by simp [edgeInput]

/-- **Cost of the offset.** -/
theorem offsetFn_cost {f m : ℕ} (C : Fin m → Walks.Column (Fin f)) (D : CoordinateData m)
    (c : Fin m → ℕ) (Cb : ℕ) (hc : ∀ e, (c e).size ≤ Cb) :
    offsetFn.costAt (edgeInput C D c) ≤
      95 * ((m + 2) * (2 * (3 * m + Cb + 9) + 2) ^ 2) ^ 2 := by
  have hcs := edgeInput_costs C D c Cb hc
  have hlen := length_edgeInput C D c
  have hok : OkAt (m + 1) (3 * m + Cb + 9) offsetFn (edgeInput C D c) := by
    have h1 := totalFn_ok (m + 1) (3 * m + Cb + 9) Cb _ hcs (by omega) (by omega)
    have h2 := totalE_bits Cb _ hcs
    simp only [OkAt, offsetFn, Ok, ok_call, Expr.denote, Var.get, denote_call, totalFn_apply,
      true_and, bits_two]
    exact ⟨h1, by omega, by omega⟩
  have := costAt_le_weight _ _ offsetFn _ hok
  rw [weight_offsetFn, depth_offsetFn] at this
  exact this

/-- **Cost of the search width.** -/
theorem bitsFn_cost {f m : ℕ} (C : Fin m → Walks.Column (Fin f)) (D : CoordinateData m)
    (c : Fin m → ℕ) (Cb : ℕ) (hc : ∀ e, (c e).size ≤ Cb) :
    bitsFn.costAt (edgeInput C D c) ≤
      96 * ((m + 2) * (2 * (3 * m + Cb + 9) + 2) ^ 2) ^ 2 := by
  have hcs := edgeInput_costs C D c Cb hc
  have hlen := length_edgeInput C D c
  have hok : OkAt (m + 1) (3 * m + Cb + 9) bitsFn (edgeInput C D c) := by
    have h1 := totalFn_ok (m + 1) (3 * m + Cb + 9) Cb _ hcs (by omega) (by omega)
    have h2 := totalE_bits Cb _ hcs
    have h3 : bits (2 * totalE (edgeInput C D c)) ≤ 2 * m + Cb + 5 :=
      (bits_mul_le _ _).trans (by rw [bits_two]; omega)
    simp only [OkAt, bitsFn, Ok, ok_call, Expr.denote, Var.get, denote_call, totalFn_apply,
      true_and, bits_two, IntOp.eval]
    exact ⟨⟨h1, by omega, by omega⟩, by omega⟩
  have := costAt_le_weight _ _ bitsFn _ hok
  rw [weight_bitsFn, depth_bitsFn] at this
  exact this

theorem decodeFn_ok (L B m M : ℕ) (hm : m ≤ L) (hB : m + M.size + 2 ≤ B) :
    OkAt L B decodeFn ((M : ℤ), (m : ℤ)) := by
  have happ := decodeFn_apply ((M : ℤ), (m : ℤ))
  unfold decodeFn at happ ⊢
  apply ok_rev_call
  · simp only [Ok, Expr.denote, Var.get, IntOp.eval, true_and, bits_two, Int.toNat_natCast]
    refine ⟨hm, bits_le_of_natAbs (by simp; omega),
      IterOK.of_inv _ _ (fun i (s : ℤ × List ℤ) => s.1 = 2 ^ i) _ _ (by simp) ?_⟩
    intro i c hi hc
    have hbp : bits c.1 ≤ m := by rw [hc, bits_two_pow]; omega
    have hpos : (0 : ℤ) < c.1 := by rw [hc]; positivity
    have hM : bits (M : ℤ) = M.size := by simp [bits]
    have hdiv : bits ((M : ℤ) / c.1) ≤ M.size := by
      refine (bits_mono (y := (M : ℤ)) ?_).trans hM.le
      have h0 : 0 ≤ (M : ℤ) / c.1 := Int.ediv_nonneg (by omega) hpos.le
      have h1 : (M : ℤ) / c.1 ≤ M := Int.ediv_le_self _ (by omega)
      simp only [Int.natAbs_natCast]
      omega
    refine ⟨⟨⟨by omega, by omega⟩, ⟨⟨by omega, by omega⟩, by omega, by omega⟩, trivial⟩, ?_⟩
    simp only [hc]; ring
  · rw [happ]; simp; omega

/-- **Cost of decoding.** -/
theorem decodeFn_cost (m M : ℕ) :
    decodeFn.costAt ((M : ℤ), (m : ℤ)) ≤
      33 * ((m + 1) * (2 * (m + M.size + 2) + 2) ^ 2) ^ 2 := by
  have := costAt_le_weight _ _ decodeFn _ (decodeFn_ok m (m + M.size + 2) m M le_rfl le_rfl)
  rw [weight_decodeFn, depth_decodeFn] at this
  exact this

theorem weight_slackFn : weight slackFn = 154 := by decide
theorem depth_slackFn : depth slackFn = 1 := by decide

/-- **Cost of decoding an LP value.** -/
theorem slackFn_cost {f m : ℕ} (C : Fin m → Walks.Column (Fin f)) (D : CoordinateData m)
    (c : Fin m → ℕ) (Cb : ℕ) (hc : ∀ e, (c e).size ≤ Cb) (v : ℕ) :
    slackFn.costAt ((v : ℤ), edgeInput C D c) ≤
      154 * ((m + 2) * (2 * (3 * m + Cb + v.size + 9) + 2) ^ 2) ^ 2 := by
  have hcs := edgeInput_costs C D c Cb hc
  have hlen := length_edgeInput C D c
  have hT := totalE_bits Cb _ hcs
  have hT' : totalE (edgeInput C D c) = (total c : ℤ) := totalE_edgeInput C D c
  have hv : bits (v : ℤ) = v.size := by simp [bits]
  have hok : OkAt (m + 1) (3 * m + Cb + v.size + 9) slackFn ((v : ℤ), edgeInput C D c) := by
    have h1 := totalFn_ok (m + 1) (3 * m + Cb + v.size + 9) Cb _ hcs (by omega) (by omega)
    simp only [OkAt, slackFn, Ok, ok_call, Expr.denote, Var.get, denote_call, totalFn_apply,
      lengthFn_apply, true_and, IntOp.eval]
    refine ⟨h1, ⟨⟨⟨by omega, by omega⟩, fun _ => ⟨by omega, by omega⟩, fun _ => trivial⟩,
      lengthFn_ok _ _ _ _ (by omega) (by omega)⟩, ?_⟩
    rw [hT', hlen]
    by_cases h : (v : ℤ) ≤ (total c : ℤ)
    · simp only [CmpOp.eval, h, decide_true, ↓reduceIte]
      rw [show (total c : ℤ) - v = ((total c - v : ℕ) : ℤ) by
        have : v ≤ total c := by exact_mod_cast h
        push_cast [this]; ring]
      refine decodeFn_ok _ _ m _ (by omega) ?_
      have : (total c - v).size ≤ 2 * m + Cb + 3 := by
        refine (Nat.size_le_size (Nat.sub_le _ _)).trans ?_
        rw [hT', hlen] at hT; simpa [bits] using hT
      omega
    · simp only [CmpOp.eval, h, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact decodeFn_ok _ _ m 0 (by omega) (by simp; omega)
  have := costAt_le_weight _ _ slackFn _ hok
  rw [weight_slackFn, depth_slackFn] at this
  exact this

end MWIS.FunNetwork


end
