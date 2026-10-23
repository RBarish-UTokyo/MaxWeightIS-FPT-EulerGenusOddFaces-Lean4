module

public import MWIS.TreeCotreeSearch
public import MWIS.TreeCotreeElimination
public import MWIS.CycleQuotient
public import MWIS.ResidueJensen

/-!
# Exact integral quotient coordinates without normal forms

For a connected nonbipartite graph and signed face columns `C` with `BA = 0` and `B1 = 0`,
this file computes free coordinates `freeMap : ℤ^E → ℤ^r` and a parity map
`parityMap : ℤ^E → ℤ/2`, and proves that they induce an isomorphism of the integral cycle
quotient `ker B / Aℤ^V` with `ℤ^r × ℤ/2` sending the class of the all-ones vector to
`(0, 1)`.

The construction is explicit. A spanning tree gives the residual `U(y) = y - A x(y)`, which
vanishes on tree edges. On the non-tree edges, unit-pivot elimination of the face equations
parametrizes the integral cycles by their values on the remaining free edges `X`. The
incidence of the ±1 depth-parity potential is `2g` with `g` a cycle with entries in
`{0, ±1}`; the quotient by `ℤ·2g` is removed by one free pivot edge `j` with `g j = ±1`.
The coordinates are `U(y) e - g_j U(y)_j g_e` on the edges `e ∈ X \ {j}`, and the parity is
`U(y)_j mod 2`. Every coefficient of `freeMap` is at most `4n` in absolute value.
-/

@[expose] public section

namespace MWIS.TreeCotree

open CycleQuotient

variable {f m n : ℕ} (left right : Fin m → Fin n) (C : Fin m → Walks.Column (Fin f))
  (root : Fin n)

/-! ## The spanning tree and the residual -/

/-- The edges of the spanning tree. -/
def treeEdges : List (Fin m) := (tree left right root).map Prod.snd

/-- The edges outside the spanning tree. -/
def nonTree : Finset (Fin m) := Finset.univ.filter fun e => e ∉ treeEdges left right root

/-- The tree potential with root value zero. -/
def treePotential (y : Fin m → ℤ) : Fin n → ℤ :=
  potential left right root (tree left right root) 0 y

/-- The ±1 depth-parity potential. -/
def parityPotential : Fin n → ℤ := potential left right root (tree left right root) 1 0

/-- The residual `y - A x(y)`, which vanishes on the tree edges. -/
def residual : (Fin m → ℤ) →+ (Fin m → ℤ) where
  toFun y := y - IncidenceSplit.incidence left right (treePotential left right root y)
  map_zero' := by
    simp only [treePotential, potential_zero, map_zero, sub_zero]
  map_add' y₁ y₂ := by
    simp only [treePotential, potential_add, map_add]
    abel

theorem residual_apply (y : Fin m → ℤ) :
    residual left right root y =
      y - IncidenceSplit.incidence left right (treePotential left right root y) := rfl

/-- Half the incidence of the depth-parity potential. -/
def half (e : Fin m) : ℤ :=
  IncidenceSplit.incidence left right (parityPotential left right root) e / 2

/-! ## Free edges, pivot edge, coordinates -/

/-- The final elimination state of the face equations on the non-tree edges. -/
def elimination : ElimState f m := (columnState C (nonTree left right root)).run

/-- The free edges: those left active by the elimination. -/
def free : Finset (Fin m) := (elimination left right C root).act

/-- The first free edge where the half-parity cycle is nonzero. -/
def pivotEdge : Option (Fin m) :=
  (List.finRange m).find? fun e =>
    decide (e ∈ free left right C root ∧ half left right root e ≠ 0)

/-- The coordinate edges: the free edges other than the pivot edge. -/
def coordEdges : List (Fin m) :=
  (List.finRange m).filter fun e =>
    decide (e ∈ free left right C root ∧ pivotEdge left right C root ≠ some e)

/-- The free rank. -/
def rank : ℕ := (coordEdges left right C root).length

/-- The coordinate edge of index `i`. -/
def coordEdge (i : Fin (rank left right C root)) : Fin m :=
  (coordEdges left right C root).get i

/-- The integer parity row: the residual at the pivot edge. -/
def parityRow : (Fin m → ℤ) →+ ℤ where
  toFun y := (pivotEdge left right C root).elim 0 fun j => residual left right root y j
  map_zero' := by cases pivotEdge left right C root <;> simp
  map_add' y₁ y₂ := by cases pivotEdge left right C root <;> simp

/-- The multiple of the half-parity cycle in the residual. -/
def lead : (Fin m → ℤ) →+ ℤ where
  toFun y := (pivotEdge left right C root).elim 0 fun j =>
    half left right root j * residual left right root y j
  map_zero' := by cases pivotEdge left right C root <;> simp
  map_add' y₁ y₂ := by cases pivotEdge left right C root <;> simp [mul_add]

/-- The free coordinates. -/
def freeMap : (Fin m → ℤ) →+ (Fin (rank left right C root) → ℤ) where
  toFun y i := residual left right root y (coordEdge left right C root i) -
    lead left right C root y * half left right root (coordEdge left right C root i)
  map_zero' := by funext i; simp
  map_add' y₁ y₂ := by funext i; simp only [map_add, Pi.add_apply]; ring

/-- The parity coordinate. -/
def parityMap : (Fin m → ℤ) →+ ZMod 2 :=
  (Int.castAddHom (ZMod 2)).comp (parityRow left right C root)

/-- The residue labels: parity and free coordinates modulo `GroupSize.modulus r`. -/
def residueLabel : (Fin m → ℤ) →+ ResidueJensen.Residue (rank left right C root) where
  toFun y := (parityMap left right C root y,
    fun i => ((freeMap left right C root y i : ℤ) : ZMod (GroupSize.modulus (rank left right C root))))
  map_zero' := by ext i <;> simp
  map_add' y₁ y₂ := by ext i <;> simp

/-! ## Facts about the tree -/

section Tree

variable {left right root}

theorem mem_nonTree {e : Fin m} : e ∈ nonTree left right root ↔ e ∉ treeEdges left right root := by
  simp [nonTree]

theorem tree_edge_equation (c : ℤ) (y : Fin m → ℤ) {e : Fin m}
    (he : e ∈ treeEdges left right root) :
    potential left right root (tree left right root) c y (left e) +
      potential left right root (tree left right root) c y (right e) = y e := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
  exact potential_edge left right (tree_good left right root) c y p hp

theorem residual_tree (y : Fin m → ℤ) {e : Fin m} (he : e ∉ nonTree left right root) :
    residual left right root y e = 0 := by
  rw [mem_nonTree, not_not] at he
  simp only [residual_apply, Pi.sub_apply, IncidenceSplit.incidence, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk, treePotential]
  rw [tree_edge_equation 0 y he]; ring

variable (hc : Incidence.Connected left right)
include hc

theorem potential_eq (c : ℤ) (y : Fin m → ℤ) (z : Fin n → ℤ) (hz : z root = c)
    (hedge : ∀ e ∈ treeEdges left right root, z (left e) + z (right e) = y e) :
    z = potential left right root (tree left right root) c y := by
  funext w
  apply potential_unique left right (tree_good left right root) c y z hz _ w
    (tree_spanning left right root hc w)
  intro p hp
  exact hedge p.2 (List.mem_map.mpr ⟨p, hp, rfl⟩)

theorem residual_incidence (x : Fin n → ℤ) :
    residual left right root (IncidenceSplit.incidence left right x) =
      x root • IncidenceSplit.incidence left right (parityPotential left right root) := by
  have hroot1 := potential_root left right (tree_good left right root) 1 0
  have hz : x - x root • parityPotential left right root =
      treePotential left right root (IncidenceSplit.incidence left right x) := by
    apply potential_eq hc
    · simp [parityPotential, hroot1]
    · intro e he
      have h1 := tree_edge_equation (left := left) (right := right) (root := root) 1 0 he
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, IncidenceSplit.incidence,
        AddMonoidHom.coe_mk, ZeroHom.coe_mk, parityPotential] at h1 ⊢
      have : x root * potential left right root (tree left right root) 1 0 (left e) +
          x root * potential left right root (tree left right root) 1 0 (right e) = 0 := by
        rw [← mul_add, h1]; simp
      linarith
  rw [residual_apply, ← hz, map_sub, map_zsmul]
  abel

theorem residual_of_tree_zero (y : Fin m → ℤ) (hy : ∀ e ∉ nonTree left right root, y e = 0) :
    residual left right root y = y := by
  have h0 : (0 : Fin n → ℤ) = treePotential left right root y := by
    apply potential_eq hc
    · rfl
    · intro e he
      rw [hy e (by rw [mem_nonTree, not_not]; exact he)]; simp
  rw [residual_apply, ← h0, map_zero, sub_zero]

theorem parityPotential_pm (w : Fin n) :
    parityPotential left right root w = 1 ∨ parityPotential left right root w = -1 := by
  have key : ∀ s, Good left right root s → ∀ v ∈ discovered root s,
      potential left right root s 1 0 v = 1 ∨ potential left right root s 1 0 v = -1 := by
    intro s hs
    induction hs with
    | nil =>
      intro v hv
      simp only [discovered, List.map_nil, List.mem_singleton] at hv
      subst hv; simp [potential]
    | @snoc s v e hs hv he ih =>
      intro w hw
      rcases mem_discovered_snoc.mp hw with hw | hw
      · rw [potential_old left right hv 1 0 hw]; exact ih w hw
      · simp only at hw
        subst hw
        rw [potential_snoc]
        unfold potentialStep other
        simp only [Function.update_self, Pi.zero_apply, zero_sub]
        rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · simp only [h1, if_true]
          rcases ih _ h2 with h | h <;> rw [h] <;> simp
        · have hne : left e ≠ w := by rintro rfl; exact hv h2
          simp only [hne, if_false]
          rcases ih _ h2 with h | h <;> rw [h] <;> simp
  exact key _ (tree_good left right root) w (tree_spanning left right root hc w)

theorem incidence_parity_eq (e : Fin m) :
    IncidenceSplit.incidence left right (parityPotential left right root) e =
      2 * half left right root e := by
  unfold half
  simp only [IncidenceSplit.incidence, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rcases parityPotential_pm hc (left e) with h1 | h1 <;>
    rcases parityPotential_pm hc (right e) with h2 | h2 <;> rw [h1, h2] <;> norm_num

theorem half_cases (e : Fin m) :
    half left right root e = 0 ∨ half left right root e = 1 ∨ half left right root e = -1 := by
  unfold half
  simp only [IncidenceSplit.incidence, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rcases parityPotential_pm hc (left e) with h1 | h1 <;>
    rcases parityPotential_pm hc (right e) with h2 | h2 <;> rw [h1, h2] <;> norm_num

theorem half_tree {e : Fin m} (he : e ∉ nonTree left right root) : half left right root e = 0 := by
  rw [mem_nonTree, not_not] at he
  unfold half
  simp only [IncidenceSplit.incidence, AddMonoidHom.coe_mk, ZeroHom.coe_mk, parityPotential]
  rw [tree_edge_equation 1 0 he]; rfl

theorem incidence_parity_eq_smul :
    IncidenceSplit.incidence left right (parityPotential left right root) =
      (2 : ℤ) • (fun e => half left right root e) := by
  funext e; rw [incidence_parity_eq hc]; simp

theorem residual_one : residual left right root (fun _ => 1) = fun e => half left right root e := by
  have h2 : (fun _ : Fin m => (2 : ℤ)) = IncidenceSplit.incidence left right (fun _ => 1) := by
    funext e; simp [IncidenceSplit.incidence]
  have h := residual_incidence (root := root) hc (fun _ => (1 : ℤ))
  rw [← h2, one_smul, incidence_parity_eq_smul hc] at h
  have h' : (2 : ℤ) • residual left right root (fun _ => 1) =
      (2 : ℤ) • (fun e => half left right root e) := by
    rw [← map_zsmul, ← h]; congr 1
  funext e
  have := congrFun h' e
  simp only [Pi.smul_apply, smul_eq_mul] at this
  omega

variable (hn : ¬ Incidence.Bipartite left right)
include hn

theorem half_ne_zero : ∃ e, half left right root e ≠ 0 := by
  by_contra hall
  push_neg at hall
  apply hn
  refine ⟨fun v => decide (parityPotential left right root v = 1), fun e => ?_⟩
  have h := incidence_parity_eq (root := root) hc e
  rw [hall e] at h
  simp only [IncidenceSplit.incidence, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at h
  show decide (parityPotential left right root (left e) = 1) ≠
    decide (parityPotential left right root (right e) = 1)
  rcases parityPotential_pm (root := root) hc (left e) with h1 | h1 <;>
    rcases parityPotential_pm (root := root) hc (right e) with h2 | h2 <;>
    rw [h1, h2] at h ⊢ <;> simp at h ⊢

end Tree

/-! ## The isomorphism -/

section Iso

variable {left right C root}
variable (B : (Fin m → ℤ) →+ (Fin f → ℤ))
  (hBA : ∀ z, B (IncidenceSplit.incidence left right z) = 0)
  (hB1 : B (fun _ => 1) = 0)
  (hBC : ∀ y row, B y row = ∑ edge, Walks.columnVector (C edge) row * y edge)

include hBC in
theorem kernel_iff (u : Fin m → ℤ) (hu : ∀ e ∉ nonTree left right root, u e = 0) :
    B u = 0 ↔ Holds (elimination left right C root).piv u := by
  have hk := (ElimState.run_kernel (columnState_inv C (nonTree left right root))).2.2 u hu
  change B u = 0 ↔ Holds (columnState C (nonTree left right root)).run.piv u
  rw [← hk, columnState_sys C _ u hu]
  constructor
  · intro h r; rw [← hBC]; exact congrFun h r
  · intro h; funext r; rw [hBC]; exact h r

theorem elimination_tri :
    Triangular (free left right C root) (elimination left right C root).piv :=
  (ElimState.run_kernel (columnState_inv C (nonTree left right root))).1

theorem elimination_part (e : Fin m) :
    e ∈ nonTree left right root ↔
      e ∈ free left right C root ∪ pivots (elimination left right C root).piv :=
  (ElimState.run_kernel (columnState_inv C (nonTree left right root))).2.1 e

theorem zero_off_of_nonTree {u : Fin m → ℤ} (hu : ∀ e ∉ nonTree left right root, u e = 0) :
    ∀ e ∉ free left right C root ∪ pivots (elimination left right C root).piv, u e = 0 := by
  intro e he
  exact hu e (fun h => he ((elimination_part e).mp h))

variable (hc : Incidence.Connected left right) (hn : ¬ Incidence.Bipartite left right)

include hBA hBC in
theorem residual_holds (y : B.ker) :
    Holds (elimination left right C root).piv (residual left right root y.val) := by
  apply (kernel_iff B hBC _ (fun e he => residual_tree _ he)).mp
  rw [residual_apply, map_sub, y.property, hBA, sub_zero]

include hBA hBC hc in
theorem half_holds : Holds (elimination left right C root).piv (fun e => half left right root e) := by
  apply (kernel_iff B hBC _ (fun e he => half_tree hc he)).mp
  have h := hBA (parityPotential left right root)
  rw [incidence_parity_eq_smul hc, map_zsmul] at h
  funext r
  have := congrFun h r
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
  omega

include hBA hBC hc hn in
theorem pivotEdge_spec : ∃ j, pivotEdge left right C root = some j ∧
    j ∈ free left right C root ∧ (half left right root j = 1 ∨ half left right root j = -1) := by
  cases hp : pivotEdge left right C root with
  | some j =>
    have := List.find?_some hp
    simp only [decide_eq_true_eq] at this
    refine ⟨j, rfl, this.1, ?_⟩
    rcases half_cases hc j with h | h | h
    · exact absurd h this.2
    · exact Or.inl h
    · exact Or.inr h
  | none =>
    exfalso
    have hnone := List.find?_eq_none.mp hp
    obtain ⟨e, he⟩ := half_ne_zero hc hn (root := root)
    have hzero := eq_zero_of_free (elimination_tri (left := left) (right := right) (C := C)
      (root := root)) (half_holds B hBA hBC hc)
      (zero_off_of_nonTree (fun e he => half_tree hc he))
      (fun e he' => by
        have := hnone e (List.mem_finRange e)
        simp only [decide_eq_true_eq, not_and, not_not] at this
        exact this he')
    exact he (congrFun hzero e)

theorem mem_coordEdges {j : Fin m} (hj : pivotEdge left right C root = some j) (e : Fin m) :
    e ∈ coordEdges left right C root ↔ e ∈ free left right C root ∧ e ≠ j := by
  simp only [coordEdges, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq, hj,
    ne_eq, Option.some.injEq]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => h2 h.symm⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => h2 h.symm⟩

theorem coordEdges_nodup : (coordEdges left right C root).Nodup :=
  List.Nodup.filter _ (List.nodup_finRange m)

theorem coordEdge_mem (i : Fin (rank left right C root)) :
    coordEdge left right C root i ∈ coordEdges left right C root := List.get_mem _ _

theorem lead_eq {j : Fin m} (hj : pivotEdge left right C root = some j) (y : Fin m → ℤ) :
    lead left right C root y = half left right root j * residual left right root y j := by
  simp [lead, hj]

theorem parityRow_eq {j : Fin m} (hj : pivotEdge left right C root = some j) (y : Fin m → ℤ) :
    parityRow left right C root y = residual left right root y j := by
  simp [parityRow, hj]

/-- The cycle map onto free and parity coordinates. -/
def cycleMap : B.ker →+ (Fin (rank left right C root) → ℤ) × ZMod 2 :=
  ((freeMap left right C root).comp B.ker.subtype).prod
    ((parityMap left right C root).comp B.ker.subtype)

include hBA hBC hc hn in
theorem cycleMap_ker :
    (cycleMap (left := left) (right := right) (C := C) (root := root) B).ker =
      (boundary left right B hBA).range := by
  obtain ⟨j, hj, hjX, hjs⟩ := pivotEdge_spec B hBA hBC hc hn
  have hjj : half left right root j * half left right root j = 1 := by
    rcases hjs with h | h <;> rw [h] <;> norm_num
  ext y
  constructor
  · intro hy
    have hy' : cycleMap (left := left) (right := right) (C := C) (root := root) B y = 0 := hy
    simp only [cycleMap, AddMonoidHom.prod_apply, AddMonoidHom.coe_comp, Function.comp_apply,
      AddSubgroup.coe_subtype, Prod.mk_eq_zero] at hy'
    obtain ⟨hfree, hpar⟩ := hy'
    set u := residual left right root y.val with hu
    set a := lead left right C root y.val with ha
    have hz : u - a • (fun e => half left right root e) = 0 := by
      apply eq_zero_of_free elimination_tri
        (holds_sub (residual_holds B hBA hBC y) (holds_smul a (half_holds B hBA hBC hc)))
      · apply zero_off_of_nonTree
        intro e he
        simp [u, residual_tree _ he, half_tree hc he]
      · intro e he
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        by_cases hej : e = j
        · subst hej
          rw [ha, lead_eq hj]
          calc u e - half left right root e * u e * half left right root e
              = u e * (1 - half left right root e * half left right root e) := by ring
            _ = 0 := by rw [hjj]; ring
        · have hm : e ∈ coordEdges left right C root := (mem_coordEdges hj e).mpr ⟨he, hej⟩
          obtain ⟨i, hi⟩ := List.get_of_mem hm
          have := congrFun hfree i
          simp only [freeMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.zero_apply,
            coordEdge, hi] at this
          rw [← hu, ← ha] at this
          exact this
    have hueq : u = a • (fun e => half left right root e) := sub_eq_zero.mp hz
    have hpar' : ((u j : ℤ) : ZMod 2) = 0 := by
      simpa [parityMap, parityRow_eq hj, u] using hpar
    obtain ⟨b, hb⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hpar'
    have hab : a = 2 * (half left right root j * b) := by
      rw [ha, lead_eq hj, ← hu, hb]; ring
    refine ⟨treePotential left right root y.val + (half left right root j * b) •
      parityPotential left right root, ?_⟩
    apply Subtype.ext
    change IncidenceSplit.incidence left right (treePotential left right root y.val +
      (half left right root j * b) • parityPotential left right root) = y.val
    rw [map_add, map_zsmul, incidence_parity_eq_smul hc, smul_smul]
    have hy2 : y.val = IncidenceSplit.incidence left right (treePotential left right root y.val) + u := by
      rw [hu, residual_apply]; abel
    conv_rhs => rw [hy2]
    rw [hueq, hab, mul_comm (half left right root j * b) 2]
  · rintro ⟨z, rfl⟩
    change cycleMap (left := left) (right := right) (C := C) (root := root) B
      (boundary left right B hBA z) = 0
    have hres : residual left right root (IncidenceSplit.incidence left right z) =
        fun e => 2 * z root * half left right root e := by
      rw [residual_incidence hc, incidence_parity_eq_smul hc]
      funext e; simp; ring
    simp only [cycleMap, AddMonoidHom.prod_apply, AddMonoidHom.coe_comp, Function.comp_apply,
      AddSubgroup.coe_subtype, Prod.mk_eq_zero]
    change freeMap left right C root (IncidenceSplit.incidence left right z) = 0 ∧
      parityMap left right C root (IncidenceSplit.incidence left right z) = 0
    constructor
    · funext i
      simp only [freeMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.zero_apply, lead_eq hj, hres]
      calc 2 * z root * half left right root (coordEdge left right C root i) -
            half left right root j * (2 * z root * half left right root j) *
              half left right root (coordEdge left right C root i)
          = 2 * z root * half left right root (coordEdge left right C root i) *
              (1 - half left right root j * half left right root j) := by ring
        _ = 0 := by rw [hjj]; ring
    · simp only [parityMap, AddMonoidHom.coe_comp, Function.comp_apply, parityRow_eq hj, hres,
        Int.coe_castAddHom, Int.cast_mul, Int.cast_ofNat]
      rw [show (2 : ZMod 2) = 0 from rfl, zero_mul, zero_mul]

include hBA hBC hc hn in
theorem cycleMap_surjective :
    Function.Surjective (cycleMap (left := left) (right := right) (C := C) (root := root) B) := by
  obtain ⟨j, hj, hjX, hjs⟩ := pivotEdge_spec B hBA hBC hc hn
  have hjj : half left right root j * half left right root j = 1 := by
    rcases hjs with h | h <;> rw [h] <;> norm_num
  have hjc : j ∉ coordEdges left right C root := fun h => ((mem_coordEdges hj j).mp h).2 rfl
  rintro ⟨z, t⟩
  set t' : ℤ := (t.val : ℤ)
  let w : Fin m → ℤ := fun e =>
    if h : e ∈ coordEdges left right C root then
      z ⟨(coordEdges left right C root).idxOf e, List.idxOf_lt_length_iff.mpr h⟩ +
        t' * half left right root e
    else half left right root j * t'
  obtain ⟨hu, hfreeval, hzero⟩ := extend_spec (elimination_tri (left := left) (right := right)
    (C := C) (root := root)) w
  set u := extend (elimination left right C root).piv (restrictZero (free left right C root) w)
    with hu_def
  have hun : ∀ e ∉ nonTree left right root, u e = 0 := by
    intro e he
    exact hzero e (fun h => he ((elimination_part e).mpr h))
  have hB : B u = 0 := (kernel_iff B hBC u hun).mpr hu
  refine ⟨⟨u, hB⟩, ?_⟩
  have hres : residual left right root u = u := residual_of_tree_zero hc u hun
  have huj : u j = half left right root j * t' := by
    rw [hfreeval j hjX]; simp [w, hjc]
  have hlead : lead left right C root u = t' := by
    rw [lead_eq hj, hres, huj, ← mul_assoc, hjj, one_mul]
  simp only [cycleMap, AddMonoidHom.prod_apply, AddMonoidHom.coe_comp, Function.comp_apply,
    AddSubgroup.coe_subtype, Prod.mk.injEq]
  constructor
  · funext i
    change freeMap left right C root u i = z i
    simp only [freeMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hlead, hres]
    have hmem := coordEdge_mem (left := left) (right := right) (C := C) (root := root) i
    have hX : coordEdge left right C root i ∈ free left right C root :=
      ((mem_coordEdges hj _).mp hmem).1
    rw [hfreeval _ hX]
    simp only [w, dif_pos hmem]
    have hidx : (coordEdges left right C root).idxOf (coordEdge left right C root i) = i := by
      unfold coordEdge
      exact List.get_idxOf coordEdges_nodup i
    have : (⟨(coordEdges left right C root).idxOf (coordEdge left right C root i),
        List.idxOf_lt_length_iff.mpr hmem⟩ : Fin (rank left right C root)) = i := Fin.ext hidx
    rw [this]; ring
  · change parityMap left right C root u = t
    simp only [parityMap, AddMonoidHom.coe_comp, Function.comp_apply, parityRow_eq hj, hres, huj,
      Int.coe_castAddHom, Int.cast_mul, t']
    rcases hjs with h | h
    · rw [h]; simp
    · rw [h]; simp only [Int.cast_neg, Int.cast_one, neg_one_mul, Int.cast_natCast,
        ZMod.natCast_zmod_val]
      exact ZMod.neg_eq_self_mod_two t

include hBA hB1 hBC hc hn in
/-- **Exact coordinates.** The computed free and parity coordinates induce an isomorphism
of the integral cycle quotient with `ℤ^r × ℤ/2` that sends the all-ones class to `(0, 1)`;
`freeMap` and `residueLabel` are its ambient free coordinates and residue labels. These are
exactly the hypotheses of `CoreNetwork.exists_network_optimum_of_labels`. -/
theorem exists_coordinates :
    ∃ e : Homology left right B hBA ≃+ (Fin (rank left right C root) → ℤ) × ZMod 2,
      e (characteristicClass left right B hBA hB1) = (0, 1) ∧
      (∀ y : B.ker, freeMap left right C root y.val = (e (classMap left right B hBA y)).1) ∧
      (∀ y : B.ker, residueLabel left right C root y.val =
        ResidueJensen.residueMap e (classMap left right B hBA y)) := by
  let φ := cycleMap (left := left) (right := right) (C := C) (root := root) B
  let e : Homology left right B hBA ≃+ (Fin (rank left right C root) → ℤ) × ZMod 2 :=
    (QuotientAddGroup.quotientAddEquivOfEq (cycleMap_ker B hBA hBC hc hn).symm).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective φ (cycleMap_surjective B hBA hBC hc hn))
  have he : ∀ y : B.ker, e (classMap left right B hBA y) = φ y := fun y => rfl
  refine ⟨e, ?_, ?_, ?_⟩
  · unfold characteristicClass
    rw [he]
    obtain ⟨j, hj, -, hjs⟩ := pivotEdge_spec B hBA hBC hc hn
    have hjj : half left right root j * half left right root j = 1 := by
      rcases hjs with h | h <;> rw [h] <;> norm_num
    have h1 := residual_one (left := left) (right := right) (root := root) hc
    simp only [φ, cycleMap, AddMonoidHom.prod_apply, AddMonoidHom.coe_comp, Function.comp_apply,
      AddSubgroup.coe_subtype, Prod.mk.injEq]
    constructor
    · funext i
      change freeMap left right C root (fun _ => 1) i = 0
      simp only [freeMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, lead_eq hj, h1, hjj]
      ring
    · change parityMap left right C root (fun _ => 1) = 1
      simp only [parityMap, AddMonoidHom.coe_comp, Function.comp_apply, parityRow_eq hj, h1,
        Int.coe_castAddHom]
      rcases hjs with h | h <;> rw [h] <;> decide
  · intro y; rw [he]; rfl
  · intro y
    show residueLabel left right C root y.val = ((e (classMap left right B hBA y)).2,
      fun i => (((e (classMap left right B hBA y)).1 i : ℤ) :
        ZMod (GroupSize.modulus (rank left right C root))))
    rw [he]; rfl

end Iso

/-! ## Coefficient bounds -/

section Bounds

variable {left right C root}

theorem residual_single_abs (e e' : Fin m) :
    |residual left right root (Pi.single e 1) e'| ≤ 2 * n := by
  have hlen := (tree_good left right root).length_lt left right
  have hb : ∀ w, |treePotential left right root (Pi.single e 1) w| ≤
      (tree left right root).length := by
    intro w
    have := potential_abs_le left right (root := root) (s := tree left right root) 0
      (Pi.single e 1) 1 (fun d => by by_cases h : d = e <;> simp [Pi.single_apply, h])
      (by norm_num) w
    simp only [abs_zero, zero_add, mul_one] at this
    exact this
  simp only [residual_apply, Pi.sub_apply, IncidenceSplit.incidence, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk]
  have h1 : |(Pi.single e (1 : ℤ) : Fin m → ℤ) e'| ≤ 1 := by
    by_cases h : e' = e <;> simp [Pi.single_apply, h]
  have h2 := hb (left e')
  have h3 := hb (right e')
  have hl : ((tree left right root).length : ℤ) + 1 ≤ n := by exact_mod_cast hlen
  calc _ ≤ |(Pi.single e (1 : ℤ) : Fin m → ℤ) e'| +
        |treePotential left right root (Pi.single e 1) (left e') +
          treePotential left right root (Pi.single e 1) (right e')| := abs_sub _ _
    _ ≤ 1 + (|treePotential left right root (Pi.single e 1) (left e')| +
          |treePotential left right root (Pi.single e 1) (right e')|) :=
        add_le_add h1 (abs_add_le _ _)
    _ ≤ 2 * n := by linarith

theorem half_abs (e : Fin m) : |half left right root e| ≤ 1 := by
  unfold half
  have : ∀ v, |potential left right root (tree left right root) 1 0 v| ≤ 1 := by
    intro v
    have := potential_abs_le left right (root := root) (s := tree left right root) 1 0 0
      (fun _ => by simp) le_rfl v
    simpa using this
  simp only [IncidenceSplit.incidence, AddMonoidHom.coe_mk, ZeroHom.coe_mk, parityPotential]
  have h1 := this (left e)
  have h2 := this (right e)
  rw [abs_le] at h1 h2 ⊢
  constructor <;> omega

/-- Every coefficient of the free coordinates is at most `4n` in absolute value. -/
theorem freeMap_single_abs (e : Fin m) (i : Fin (rank left right C root)) :
    |freeMap left right C root (Pi.single e 1) i| ≤ 4 * n := by
  simp only [freeMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  have hr := residual_single_abs (left := left) (right := right) (root := root) e (coordEdge left right C root i)
  have hh := half_abs (left := left) (right := right) (root := root) (coordEdge left right C root i)
  have hl : |lead left right C root (Pi.single e 1)| ≤ 2 * n := by
    simp only [lead, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    cases pivotEdge left right C root with
    | none => simp
    | some j =>
      simp only [Option.elim_some, abs_mul]
      have := half_abs (left := left) (right := right) (root := root) j
      have := residual_single_abs (left := left) (right := right) (root := root) e j
      have : (0 : ℤ) ≤ |residual left right root (Pi.single e 1) j| := abs_nonneg _
      nlinarith
  calc _ ≤ |residual left right root (Pi.single e 1) (coordEdge left right C root i)| +
        |lead left right C root (Pi.single e 1) * half left right root (coordEdge left right C root i)| :=
        abs_sub _ _
    _ ≤ 2 * n + 2 * n := by
        rw [abs_mul]
        have : (0 : ℤ) ≤ |lead left right C root (Pi.single e 1)| := abs_nonneg _
        nlinarith
    _ = 4 * n := by ring

/-- The parity row has coefficients at most `2n` in absolute value. -/
theorem parityRow_single_abs (e : Fin m) :
    |parityRow left right C root (Pi.single e 1)| ≤ 2 * n := by
  simp only [parityRow, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  cases pivotEdge left right C root with
  | none => simp
  | some j => exact residual_single_abs e j

theorem rank_le : rank left right C root ≤ m := by
  unfold rank coordEdges
  exact (List.length_filter_le _ _).trans (by simp)

end Bounds

end MWIS.TreeCotree

end
