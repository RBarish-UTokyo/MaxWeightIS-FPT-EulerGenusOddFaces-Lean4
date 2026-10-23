module

public import MWIS.IncidenceSplit
public import MWIS.Incidence
public import Mathlib.Tactic

/-!
# A spanning tree and its vertex potentials

A breadth-first growth from a root adds, one at a time, a new vertex together with an
edge joining it to an already discovered vertex. For a connected graph, `n` growth steps
discover every vertex. Along the resulting spanning tree, every edge vector `y` has a unique
vertex potential `x` with prescribed root value whose unsigned incidence agrees with `y` on
the tree edges. The residual `y - Ax` vanishes on the tree, is additive in `y`, equals
`x(root)` times the incidence of the ±1 depth-parity potential on incidence vectors, and is
the identity on vectors vanishing on the tree.
-/

@[expose] public section

namespace MWIS.TreeCotree

variable {m n : ℕ} (left right : Fin m → Fin n)

/-- The discovered vertices: the root, then the discovered vertices in order. -/
def discovered (root : Fin n) (s : List (Fin n × Fin m)) : List (Fin n) :=
  root :: s.map Prod.fst

/-- An edge with exactly one discovered endpoint, with its undiscovered endpoint. -/
def frontierEdge (root : Fin n) (s : List (Fin n × Fin m)) (e : Fin m) :
    Option (Fin n × Fin m) :=
  if left e ∈ discovered root s ∧ right e ∉ discovered root s then some (right e, e)
  else if right e ∈ discovered root s ∧ left e ∉ discovered root s then some (left e, e)
  else none

/-- The first frontier edge. -/
def frontier (root : Fin n) (s : List (Fin n × Fin m)) : Option (Fin n × Fin m) :=
  (List.finRange m).findSome? (frontierEdge left right root s)

/-- Discover one more vertex, if possible. -/
def grow (root : Fin n) (s : List (Fin n × Fin m)) : List (Fin n × Fin m) :=
  match frontier left right root s with
  | some p => s ++ [p]
  | none => s

/-- The discovered vertices with their tree edges after `n` growth steps. -/
def tree (root : Fin n) : List (Fin n × Fin m) := (grow left right root)^[n] []

/-- A growth sequence: every vertex is new and joined to an earlier one by its edge. -/
inductive Good (root : Fin n) : List (Fin n × Fin m) → Prop
  | nil : Good root []
  | snoc {s : List (Fin n × Fin m)} {v : Fin n} {e : Fin m} :
      Good root s → v ∉ discovered root s →
      ((left e = v ∧ right e ∈ discovered root s) ∨ (right e = v ∧ left e ∈ discovered root s)) →
      Good root (s ++ [(v, e)])

theorem discovered_snoc (root : Fin n) (s : List (Fin n × Fin m)) (p : Fin n × Fin m) :
    discovered root (s ++ [p]) = discovered root s ++ [p.1] := by
  simp [discovered]

theorem mem_discovered_snoc {root : Fin n} {s : List (Fin n × Fin m)} {p : Fin n × Fin m}
    {w : Fin n} : w ∈ discovered root (s ++ [p]) ↔ w ∈ discovered root s ∨ w = p.1 := by
  rw [discovered_snoc]; simp

theorem root_mem_discovered (root : Fin n) (s : List (Fin n × Fin m)) :
    root ∈ discovered root s := by simp [discovered]

/-- Both endpoints of every tree edge are discovered. -/
theorem Good.endpoints {root : Fin n} {s : List (Fin n × Fin m)} (h : Good left right root s) :
    ∀ p ∈ s, left p.2 ∈ discovered root s ∧ right p.2 ∈ discovered root s := by
  induction h with
  | nil => simp
  | @snoc s v e hs hv he ih =>
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨h1, h2⟩ := ih p hp
      exact ⟨mem_discovered_snoc.mpr (Or.inl h1), mem_discovered_snoc.mpr (Or.inl h2)⟩
    · simp only [List.mem_singleton] at hp
      subst hp
      rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨mem_discovered_snoc.mpr (Or.inr h1), mem_discovered_snoc.mpr (Or.inl h2)⟩
      · exact ⟨mem_discovered_snoc.mpr (Or.inl h2), mem_discovered_snoc.mpr (Or.inr h1)⟩

theorem Good.nodup {root : Fin n} {s : List (Fin n × Fin m)} (h : Good left right root s) :
    (discovered root s).Nodup := by
  induction h with
  | nil => simp [discovered]
  | @snoc s v e hs hv he ih =>
    rw [discovered_snoc, List.nodup_append]
    refine ⟨ih, by simp, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst hb
    intro hab; subst hab; exact hv ha

theorem Good.length_lt {root : Fin n} {s : List (Fin n × Fin m)} (h : Good left right root s) :
    s.length < n := by
  have hn := (h.nodup left right).length_le_card
  simp only [discovered, List.length_cons, List.length_map, Fintype.card_fin] at hn
  omega

/-! ## Growth -/

theorem frontier_some_good {root : Fin n} {s : List (Fin n × Fin m)} {p : Fin n × Fin m}
    (h : Good left right root s) (hp : frontier left right root s = some p) :
    Good left right root (s ++ [p]) := by
  obtain ⟨e, _, he⟩ := List.exists_of_findSome?_eq_some hp
  unfold frontierEdge at he
  split_ifs at he with h1 h2
  · cases he; exact .snoc h h1.2 (Or.inr ⟨rfl, h1.1⟩)
  · cases he; exact .snoc h h2.2 (Or.inl ⟨rfl, h2.1⟩)

theorem frontier_none_closed {root : Fin n} {s : List (Fin n × Fin m)}
    (hp : frontier left right root s = none) (e : Fin m) :
    left e ∈ discovered root s ↔ right e ∈ discovered root s := by
  have := List.findSome?_eq_none_iff.mp hp e (List.mem_finRange e)
  unfold frontierEdge at this
  by_cases h1 : left e ∈ discovered root s ∧ right e ∉ discovered root s
  · rw [if_pos h1] at this; simp at this
  · rw [if_neg h1] at this
    by_cases h2 : right e ∈ discovered root s ∧ left e ∉ discovered root s
    · rw [if_pos h2] at this; simp at this
    · push_neg at h1 h2
      exact ⟨h1, h2⟩

theorem grow_progress (root : Fin n) (k : ℕ) :
    Good left right root ((grow left right root)^[k] []) ∧
      (((grow left right root)^[k] []).length = k ∨
        frontier left right root ((grow left right root)^[k] []) = none) := by
  induction k with
  | zero => exact ⟨.nil, Or.inl rfl⟩
  | succ k ih =>
    obtain ⟨hg, hl⟩ := ih
    rw [Function.iterate_succ_apply']
    cases hf : frontier left right root ((grow left right root)^[k] []) with
    | none =>
      have hs : grow left right root ((grow left right root)^[k] []) =
          (grow left right root)^[k] [] := by simp [grow, hf]
      rw [hs]; exact ⟨hg, Or.inr hf⟩
    | some p =>
      have hs : grow left right root ((grow left right root)^[k] []) =
          (grow left right root)^[k] [] ++ [p] := by simp [grow, hf]
      rw [hs]
      refine ⟨frontier_some_good left right hg hf, ?_⟩
      rcases hl with hl | hl
      · left; simp [hl]
      · rw [hl] at hf; cases hf

theorem tree_good (root : Fin n) : Good left right root (tree left right root) :=
  (grow_progress left right root n).1

/-- For a connected graph the tree discovers every vertex. -/
theorem tree_spanning (root : Fin n) (hc : Incidence.Connected left right) (w : Fin n) :
    w ∈ discovered root (tree left right root) := by
  obtain ⟨hg, hl⟩ := grow_progress left right root n
  have hclosed : frontier left right root (tree left right root) = none := by
    rcases hl with hl | hl
    · have := hg.length_lt left right
      exact absurd hl (by omega)
    · exact hl
  obtain ⟨k, hw⟩ := hc root w
  induction hw with
  | nil => exact root_mem_discovered _ _
  | forward e hb _ ih =>
    rw [hb] at ih
    exact (frontier_none_closed left right hclosed e).mp ih
  | backward e hb _ ih =>
    rw [hb] at ih
    exact (frontier_none_closed left right hclosed e).mpr ih

/-! ## Potentials -/

/-- The endpoint of `e` other than `v`. -/
def other (e : Fin m) (v : Fin n) : Fin n := if left e = v then right e else left e

/-- Assign the potential of a newly discovered vertex. -/
def potentialStep (y : Fin m → ℤ) (x : Fin n → ℤ) (p : Fin n × Fin m) : Fin n → ℤ :=
  Function.update x p.1 (y p.2 - x (other left right p.2 p.1))

/-- The potential with root value `c` along a growth sequence. -/
def potential (root : Fin n) (s : List (Fin n × Fin m)) (c : ℤ) (y : Fin m → ℤ) :
    Fin n → ℤ :=
  s.foldl (potentialStep left right y) (fun v => if v = root then c else 0)

theorem potential_snoc (root : Fin n) (s : List (Fin n × Fin m)) (p : Fin n × Fin m)
    (c : ℤ) (y : Fin m → ℤ) :
    potential left right root (s ++ [p]) c y =
      potentialStep left right y (potential left right root s c y) p := by
  simp [potential, List.foldl_append]

theorem potential_old {root : Fin n} {s : List (Fin n × Fin m)} {v : Fin n} {e : Fin m}
    (hv : v ∉ discovered root s) (c : ℤ) (y : Fin m → ℤ) {w : Fin n}
    (hw : w ∈ discovered root s) :
    potential left right root (s ++ [(v, e)]) c y w = potential left right root s c y w := by
  rw [potential_snoc]
  unfold potentialStep
  rw [Function.update_of_ne]
  rintro rfl; exact hv hw

theorem potential_root {root : Fin n} {s : List (Fin n × Fin m)} (h : Good left right root s)
    (c : ℤ) (y : Fin m → ℤ) : potential left right root s c y root = c := by
  induction h with
  | nil => simp [potential]
  | @snoc s v e hs hv he ih =>
    rw [potential_old left right hv c y (root_mem_discovered _ _), ih]

/-- The potential satisfies every tree-edge equation. -/
theorem potential_edge {root : Fin n} {s : List (Fin n × Fin m)} (h : Good left right root s)
    (c : ℤ) (y : Fin m → ℤ) :
    ∀ p ∈ s, potential left right root s c y (left p.2) +
      potential left right root s c y (right p.2) = y p.2 := by
  induction h with
  | nil => simp
  | @snoc s v e hs hv he ih =>
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨h1, h2⟩ := hs.endpoints left right p hp
      rw [potential_old left right hv c y h1, potential_old left right hv c y h2]
      exact ih p hp
    · simp only [List.mem_singleton] at hp
      subst hp
      simp only
      rw [potential_snoc]
      unfold potentialStep other
      rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hne : right e ≠ v := by rintro rfl; exact hv h2
        simp only [h1, if_true, Function.update_self, Function.update_of_ne hne]
        ring
      · have hne : left e ≠ v := by rintro rfl; exact hv h2
        simp only [h1, hne, if_false, Function.update_self, Function.update_of_ne hne]
        ring

/-- Any potential with the same root value and tree-edge equations agrees with the
computed potential on discovered vertices. -/
theorem potential_unique {root : Fin n} {s : List (Fin n × Fin m)} (h : Good left right root s)
    (c : ℤ) (y : Fin m → ℤ) (z : Fin n → ℤ) (hz : z root = c)
    (hedge : ∀ p ∈ s, z (left p.2) + z (right p.2) = y p.2) :
    ∀ w ∈ discovered root s, z w = potential left right root s c y w := by
  induction h with
  | nil =>
    intro w hw
    simp only [discovered, List.map_nil, List.mem_singleton] at hw
    subst hw; simp [potential, hz]
  | @snoc s v e hs hv he ih =>
    have ih' := ih (fun p hp => hedge p (List.mem_append_left _ hp))
    intro w hw
    rcases mem_discovered_snoc.mp hw with hw | hw
    · rw [potential_old left right hv c y hw]; exact ih' w hw
    · simp only at hw
      subst hw
      have hnew := hedge (w, e) (by simp)
      rw [potential_snoc]
      unfold potentialStep other
      simp only [Function.update_self]
      rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp only [h1, if_true]
        rw [← ih' _ h2]
        simp only [h1] at hnew
        linarith
      · have hne : left e ≠ w := by rintro rfl; exact hv h2
        simp only [hne, if_false]
        rw [← ih' _ h2]
        simp only [h1] at hnew
        linarith

theorem foldl_step_add (y₁ y₂ : Fin m → ℤ) (s : List (Fin n × Fin m)) (x₁ x₂ : Fin n → ℤ) :
    s.foldl (potentialStep left right (y₁ + y₂)) (x₁ + x₂) =
      s.foldl (potentialStep left right y₁) x₁ + s.foldl (potentialStep left right y₂) x₂ := by
  induction s generalizing x₁ x₂ with
  | nil => rfl
  | cons p s ih =>
    simp only [List.foldl_cons]
    rw [← ih]
    congr 1
    funext v
    unfold potentialStep
    by_cases hv : v = p.1
    · subst hv; simp only [Function.update_self, Pi.add_apply]; ring
    · simp [Function.update_of_ne hv]

/-- Potentials with root value zero are additive in the edge vector. -/
theorem potential_add (root : Fin n) (s : List (Fin n × Fin m)) (y₁ y₂ : Fin m → ℤ) :
    potential left right root s 0 (y₁ + y₂) =
      potential left right root s 0 y₁ + potential left right root s 0 y₂ := by
  unfold potential
  rw [← foldl_step_add]
  congr 1
  funext v; split_ifs <;> simp

theorem potential_zero (root : Fin n) (s : List (Fin n × Fin m)) :
    potential left right root s 0 0 = 0 := by
  have h := potential_add left right root s 0 0
  rw [add_zero] at h
  funext v
  have := congrFun h v
  simp only [Pi.add_apply] at this
  simp only [Pi.zero_apply]
  omega

/-- Potentials grow at most linearly along the growth sequence. -/
theorem potential_abs_le {root : Fin n} {s : List (Fin n × Fin m)} (c : ℤ) (y : Fin m → ℤ)
    (Y : ℤ) (hY : ∀ e, |y e| ≤ Y) (hY0 : 0 ≤ Y) :
    ∀ w, |potential left right root s c y w| ≤ |c| + s.length * Y := by
  induction s using List.reverseRecOn with
  | nil =>
    intro w
    simp only [potential, List.foldl_nil, List.length_nil, Nat.cast_zero, zero_mul, add_zero]
    split_ifs <;> simp
  | append_singleton s p ih =>
    intro w
    rw [potential_snoc]
    unfold potentialStep
    simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
    by_cases hw : w = p.1
    · subst hw
      rw [Function.update_self]
      calc |y p.2 - potential left right root s c y (other left right p.2 p.1)|
          ≤ |y p.2| + |potential left right root s c y (other left right p.2 p.1)| :=
            abs_sub _ _
        _ ≤ Y + (|c| + s.length * Y) := add_le_add (hY _) (ih _)
        _ = |c| + (s.length + 1) * Y := by ring
    · rw [Function.update_of_ne hw]
      have := ih w
      nlinarith

end MWIS.TreeCotree

end
