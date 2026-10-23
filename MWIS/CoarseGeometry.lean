module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Pi.Interval
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Push

/-!
# Midpoint neighbours in a dilated lattice hull

The hull is represented by nonnegative barycentric coefficients whose sum is
the dilation factor.  The geometric proof constructs neighbours explicitly.
-/

@[expose] public section

namespace MWIS.CoarseGeometry

variable {α β : Type*} [Fintype β]

def linearCombination (v : β → α → ℤ) (t : β → ℝ) (a : α) : ℝ :=
  ∑ i, t i * (v i a : ℝ)

def InScaledHull (v : β → α → ℤ) (k : ℕ) (x : α → ℤ) : Prop :=
  ∃ t : β → ℝ, (∀ i, 0 ≤ t i) ∧ (∑ i, t i) = (k : ℝ) ∧
    ∀ a, (x a : ℝ) = linearCombination v t a

private def shift [DecidableEq β] (t : β → ℝ) (i j : β) (δ : ℝ) (a : β) : ℝ :=
  t a + (if a = i then δ else 0) - (if a = j then δ else 0)

private theorem sum_shift [DecidableEq β] (t : β → ℝ) (i j : β) (δ : ℝ) :
    ∑ a, shift t i j δ a = ∑ a, t a := by
  simp [shift, Finset.sum_add_distrib, Finset.sum_sub_distrib]

private theorem combination_shift [DecidableEq β]
    (v : β → α → ℤ) (t : β → ℝ) (i j : β) (δ : ℝ) (a : α) :
    linearCombination v (shift t i j δ) a =
      linearCombination v t a + δ * (v i a : ℝ) - δ * (v j a : ℝ) := by
  simp [linearCombination, shift, add_mul, sub_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ite_mul]

/-- Either two barycentric coefficients are at least one, or one coefficient
is at least half the total dilation. -/
theorem coefficient_dichotomy [Nonempty β] (t : β → ℝ) (k : ℝ)
    (hsum : ∑ i, t i = k) (hcard : (Fintype.card β : ℝ) ≤ k)
    (hscale : 2 * ((Fintype.card β - 1 : ℕ) : ℝ) ≤ k) :
    (∃ i j, i ≠ j ∧ 1 ≤ t i ∧ 1 ≤ t j) ∨ ∃ j, k / 2 ≤ t j := by
  classical
  by_cases htwo : ∃ i j, i ≠ j ∧ 1 ≤ t i ∧ 1 ≤ t j
  · exact Or.inl htwo
  right
  have hlarge : ∃ j, 1 ≤ t j := by
    by_contra h
    push Not at h
    obtain ⟨j⟩ := ‹Nonempty β›
    have hlt : (∑ i, t i) < ∑ _ : β, (1 : ℝ) :=
      Finset.sum_lt_sum (fun i _ => (h i).le) ⟨j, Finset.mem_univ j, h j⟩
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hlt
    linarith
  obtain ⟨j, hj⟩ := hlarge
  have hother : ∀ i, i ≠ j → t i ≤ 1 := by
    intro i hij
    by_contra hi
    exact htwo ⟨i, j, hij, (lt_of_not_ge hi).le, hj⟩
  have hbound : ∑ i ∈ Finset.univ.erase j, t i ≤
      ((Fintype.card β - 1 : ℕ) : ℝ) := by
    calc
      _ ≤ ∑ _ ∈ Finset.univ.erase j, (1 : ℝ) :=
        Finset.sum_le_sum fun i hi => hother i (Finset.mem_erase.mp hi).1
      _ = _ := by simp
  have heq := Finset.sum_erase_add (s := Finset.univ) t (Finset.mem_univ j)
  refine ⟨j, ?_⟩
  rw [hsum] at heq
  linarith

theorem vertex_mem (v : β → α → ℤ) (k : ℕ) (j : β) :
    InScaledHull v k (k • v j) := by
  classical
  refine ⟨(fun i => if i = j then (k : ℝ) else 0), ?_, ?_, ?_⟩
  · intro i
    change 0 ≤ if i = j then (k : ℝ) else 0
    split_ifs <;> positivity
  · simp
  · intro a
    simp [linearCombination, Pi.smul_apply, ite_mul]

/-- Scaling a convex combination of lattice vertices gives membership in the
dilated lattice hull whenever its barycenter is integral. -/
theorem scaled_combination_mem (v : β → α → ℤ) (k : ℕ)
    (weights : β → ℝ) (z : α → ℤ) (hw : ∀ i, 0 ≤ weights i)
    (hsum : ∑ i, weights i = 1)
    (hbarycenter : ∀ a, (z a : ℝ) = linearCombination v weights a) :
    InScaledHull v k (k • z) := by
  refine ⟨(fun i => (k : ℝ) * weights i), ?_, ?_, ?_⟩
  · intro i
    exact mul_nonneg (Nat.cast_nonneg k) (hw i)
  · rw [← Finset.mul_sum, hsum, mul_one]
  · intro a
    simp only [linearCombination, mul_assoc, ← Finset.mul_sum]
    simpa [Pi.smul_apply, linearCombination] using
      congrArg (fun r : ℝ => (k : ℝ) * r) (hbarycenter a)

/-- Applying a real linear map to a coordinatewise barycentric identity. -/
theorem linearMap_barycenter (v : β → α → ℤ) (weights : β → ℝ)
    (z : α → ℤ) (L : (α → ℝ) →ₗ[ℝ] ℝ)
    (hbarycenter : ∀ a, (z a : ℝ) = linearCombination v weights a) :
    L (fun a => (z a : ℝ)) = ∑ i, weights i * L (fun a => (v i a : ℝ)) := by
  have hvector : (fun a => (z a : ℝ)) =
      ∑ i, weights i • (fun a => (v i a : ℝ)) := by
    funext a
    simpa [linearCombination, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
      hbarycenter a
  rw [hvector, map_sum]
  simp only [map_smul, smul_eq_mul]

/-- Affine functions preserve a convex combination of lattice vertices. -/
theorem affine_barycenter (v : β → α → ℤ) (weights : β → ℝ)
    (z : α → ℤ) (L : (α → ℝ) →ₗ[ℝ] ℝ) (c : ℝ)
    (hsum : ∑ i, weights i = 1)
    (hbarycenter : ∀ a, (z a : ℝ) = linearCombination v weights a) :
    c + L (fun a => (z a : ℝ)) =
      ∑ i, weights i * (c + L (fun a => (v i a : ℝ))) := by
  rw [linearMap_barycenter v weights z L hbarycenter]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hsum, one_mul]

/-- Every nonvertex point has two distinct integer midpoint neighbours when
the dilation is at least the number of vertices and twice one less than that
number.  Affine independence is not needed for this geometric assertion. -/
theorem scaled_hull_midpoint_neighbours [Nonempty β]
    (v : β → α → ℤ) (hv : Function.Injective v) (k : ℕ)
    (hcard : (Fintype.card β : ℝ) ≤ (k : ℝ))
    (hscale : 2 * ((Fintype.card β - 1 : ℕ) : ℝ) ≤ (k : ℝ))
    (x : α → ℤ) (hx : InScaledHull v k x)
    (hvertex : ∀ j, x ≠ k • v j) :
    ∃ p : α → ℤ, p ≠ 0 ∧ InScaledHull v k (x - p) ∧
      InScaledHull v k (x + p) := by
  classical
  obtain ⟨t, ht, hsum, hcomb⟩ := hx
  rcases coefficient_dichotomy t (k : ℝ) hsum hcard hscale with
    ⟨i, j, hij, hi, hj⟩ | ⟨j, hj⟩
  · refine ⟨v i - v j, ?_, ?_, ?_⟩
    · intro hzero
      exact hij (hv (sub_eq_zero.mp hzero))
    · refine ⟨shift t i j (-1), ?_, (sum_shift t i j (-1)).trans hsum, ?_⟩
      · intro a
        have ha := ht a
        by_cases hai : a = i
        · subst a
          simp [shift, hij]
          linarith
        · by_cases haj : a = j
          · subst a
            simp [shift, Ne.symm hij]
            linarith
          · simp [shift, hai, haj, ha]
      · intro a
        rw [combination_shift]
        simp only [Pi.sub_apply, Int.cast_sub]
        rw [hcomb a]
        ring
    · refine ⟨shift t i j 1, ?_, (sum_shift t i j 1).trans hsum, ?_⟩
      · intro a
        have ha := ht a
        by_cases hai : a = i
        · subst a
          simp [shift, hij]
          linarith
        · by_cases haj : a = j
          · subst a
            simp [shift, Ne.symm hij]
            linarith
          · simp [shift, hai, haj, ha]
      · intro a
        rw [combination_shift]
        simp only [Pi.add_apply, Pi.sub_apply, Int.cast_add, Int.cast_sub]
        rw [hcomb a]
        ring
  · refine ⟨x - k • v j, ?_, ?_, ?_⟩
    · intro hzero
      exact hvertex j (sub_eq_zero.mp hzero)
    · simpa only [sub_sub_cancel] using vertex_mem v k j
    · refine ⟨(fun i => 2 * t i - if i = j then (k : ℝ) else 0), ?_, ?_, ?_⟩
      · intro i
        change 0 ≤ 2 * t i - (if i = j then (k : ℝ) else 0)
        by_cases hij : i = j
        · subst i
          simp only [ite_true]
          linarith
        · simp only [ite_eq_right hij, sub_zero]
          have := ht i
          positivity
      · simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
        simp [hsum]
        ring
      · intro a
        simp only [linearCombination, sub_mul, Finset.sum_sub_distrib, ite_mul,
          zero_mul]
        simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        rw [show (∑ i, 2 * t i * (v i a : ℝ)) = 2 * linearCombination v t a by
          simp [linearCombination, Finset.mul_sum, mul_assoc]]
        simp only [Pi.add_apply, Pi.sub_apply, nsmul_eq_mul,
          Pi.mul_apply, Pi.natCast_apply, Int.cast_add, Int.cast_sub, Int.cast_mul,
          Int.cast_natCast]
        rw [hcomb a]
        ring

/-- The cardinal assumptions follow from the dimension threshold `k ≥ 2d`
when the vertex family has at most `d + 1` members. -/
theorem scaled_hull_midpoint_neighbours_of_dimension [Nonempty β]
    (v : β → α → ℤ) (hv : Function.Injective v) (d k : ℕ)
    (hd : 1 ≤ d) (hk : 2 * d ≤ k) (hcard : Fintype.card β ≤ d + 1)
    (x : α → ℤ) (hx : InScaledHull v k x)
    (hvertex : ∀ j, x ≠ k • v j) :
    ∃ p : α → ℤ, p ≠ 0 ∧ InScaledHull v k (x - p) ∧
      InScaledHull v k (x + p) := by
  apply scaled_hull_midpoint_neighbours v hv k ?_ ?_ x hx hvertex
  · exact_mod_cast (show Fintype.card β ≤ k by omega)
  · exact_mod_cast (show 2 * (Fintype.card β - 1) ≤ k by omega)

/-- Every coordinate lies between the correspondingly scaled bounds on the
vertices. -/
theorem coordinate_bounds (v : β → α → ℤ) (k : ℕ) (x lo hi : α → ℤ)
    (hlo : ∀ i a, lo a ≤ v i a) (hhi : ∀ i a, v i a ≤ hi a)
    (hx : InScaledHull v k x) :
    ∀ a, (k : ℤ) * lo a ≤ x a ∧ x a ≤ (k : ℤ) * hi a := by
  obtain ⟨t, ht, hsum, hcomb⟩ := hx
  intro a
  have hl : (k : ℝ) * (lo a : ℝ) ≤ (x a : ℝ) := by
    rw [hcomb a]
    calc
      _ = ∑ i, t i * (lo a : ℝ) := by rw [← Finset.sum_mul, hsum]
      _ ≤ linearCombination v t a := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hlo i a) (ht i)
  have hu : (x a : ℝ) ≤ (k : ℝ) * (hi a : ℝ) := by
    rw [hcomb a]
    calc
      _ ≤ ∑ i, t i * (hi a : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hhi i a) (ht i)
      _ = _ := by rw [← Finset.sum_mul, hsum]
  constructor
  · exact_mod_cast hl
  · exact_mod_cast hu

/-- A dilated finite lattice hull contains only finitely many lattice points. -/
theorem finite_scaled_hull [Fintype α] [Nonempty β]
    (v : β → α → ℤ) (k : ℕ) : {x | InScaledHull v k x}.Finite := by
  classical
  let lo : α → ℤ := fun a => Finset.univ.inf' Finset.univ_nonempty (fun i => v i a)
  let hi : α → ℤ := fun a => Finset.univ.sup' Finset.univ_nonempty (fun i => v i a)
  have hlo : ∀ i a, lo a ≤ v i a := by
    intro i a
    exact Finset.inf'_le (fun i : β => v i a) (Finset.mem_univ i)
  have hhi : ∀ i a, v i a ≤ hi a := by
    intro i a
    exact Finset.le_sup' (fun i : β => v i a) (Finset.mem_univ i)
  apply (Set.finite_Icc (k • lo) (k • hi)).subset
  intro x hx
  have hbound := coordinate_bounds v k x lo hi hlo hhi hx
  constructor
  · intro a
    simpa only [Pi.smul_apply, nsmul_eq_mul] using (hbound a).1
  · intro a
    simpa only [Pi.smul_apply, nsmul_eq_mul] using (hbound a).2

end MWIS.CoarseGeometry
