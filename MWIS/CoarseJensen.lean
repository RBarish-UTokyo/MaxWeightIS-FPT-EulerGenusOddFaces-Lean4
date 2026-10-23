module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Max
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Push
public import MWIS.CoarseGeometry

/-!
# Coarse Jensen inequality on the integer lattice

The main theorem `coarse_jensen` proves the coarse Jensen inequality for every
finite convex combination with an integer barycentre, at every integral scale
at least twice the positive lattice dimension.

The proof first reduces support by affine dependences without increasing the
objective, constructs an affine interpolant, and applies a finite midpoint
maximum principle.  The squared norm breaks ties between maximizers.  The
midpoint-neighbour construction and finiteness of the dilated lattice hull are
proved in `MWIS.CoarseGeometry`.
-/

@[expose] public section

namespace MWIS.CoarseJensen

/-- A finite maximum principle with a strictly increasing tie-break potential.
The local hypothesis only concerns points outside the specified boundary. -/
theorem finite_maximum_principle {X : Type*} [DecidableEq X]
    (s boundary : Finset X) (f potential : X → ℝ) (hs : s.Nonempty)
    (hneighbours : ∀ x ∈ s, x ∉ boundary →
      ∃ y ∈ s, ∃ z ∈ s,
        2 * f x ≤ f y + f z ∧
        2 * potential x < potential y + potential z) :
    ∃ v ∈ s, v ∈ boundary ∧ ∀ x ∈ s, f x ≤ f v := by
  classical
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image s f hs
  let top := s.filter fun x => f x = f m
  have hm_top : m ∈ top := by simp [top, hm]
  obtain ⟨v, hv, hvmax⟩ := Finset.exists_max_image top potential ⟨m, hm_top⟩
  have hv_s : v ∈ s := (Finset.mem_filter.mp hv).1
  have hv_value : f v = f m := (Finset.mem_filter.mp hv).2
  have hfv : ∀ x ∈ s, f x ≤ f v := by
    intro x hx
    rw [hv_value]
    exact hmax x hx
  refine ⟨v, hv_s, ?_, hfv⟩
  by_contra hnot
  obtain ⟨y, hy, z, hz, hmid, hstrict⟩ := hneighbours v hv_s hnot
  have hfy := hfv y hy
  have hfz := hfv z hz
  have hy_value : f y = f m := by linarith
  have hz_value : f z = f m := by linarith
  have hy_top : y ∈ top := by simp [top, hy, hy_value]
  have hz_top : z ∈ top := by simp [top, hz, hz_value]
  have hpy := hvmax y hy_top
  have hpz := hvmax z hz_top
  linarith

variable {ι : Type*} [Fintype ι]

/-- Squared Euclidean norm of an integer vector, valued in the reals. -/
def squareNorm (x : ι → ℤ) : ℝ := ∑ i, (x i : ℝ) ^ 2

theorem squareNorm_nonneg (x : ι → ℤ) : 0 ≤ squareNorm x := by
  exact Finset.sum_nonneg fun i _ => sq_nonneg (x i : ℝ)

theorem squareNorm_pos (x : ι → ℤ) (hx : x ≠ 0) : 0 < squareNorm x := by
  classical
  have hcoord : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext h)
  obtain ⟨i, hi⟩ := hcoord
  have hi_real : (x i : ℝ) ≠ 0 := by exact_mod_cast hi
  have hterm : 0 < (x i : ℝ) ^ 2 := sq_pos_of_ne_zero hi_real
  have hle : (x i : ℝ) ^ 2 ≤ squareNorm x :=
    Finset.single_le_sum (fun j _ => sq_nonneg (x j : ℝ)) (Finset.mem_univ i)
  exact lt_of_lt_of_le hterm hle

theorem squareNorm_midpoint_identity (x p : ι → ℤ) :
    squareNorm (x - p) + squareNorm (x + p) =
      2 * squareNorm x + 2 * squareNorm p := by
  simp only [squareNorm, Pi.sub_apply, Pi.add_apply, Int.cast_sub, Int.cast_add]
  rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Midpoint convexity on the full integer lattice. -/
def MidpointConvex (f : (ι → ℤ) → ℝ) : Prop :=
  ∀ x p, 2 * f x ≤ f (x - p) + f (x + p)

/-- Every point outside `boundary` is the midpoint of two distinct points of
the same finite lattice region. -/
def HasMidpointNeighbours [DecidableEq (ι → ℤ)]
    (s boundary : Finset (ι → ℤ)) : Prop :=
  ∀ x ∈ s, x ∉ boundary →
    ∃ p : ι → ℤ, p ≠ 0 ∧ x - p ∈ s ∧ x + p ∈ s

/-- A midpoint-convex function on a finite lattice region attains a maximum
on any boundary satisfying the midpoint-neighbour property. -/
theorem lattice_maximum_principle [DecidableEq (ι → ℤ)]
    (s boundary : Finset (ι → ℤ)) (f : (ι → ℤ) → ℝ)
    (hs : s.Nonempty) (hf : MidpointConvex f)
    (hgeometry : HasMidpointNeighbours s boundary) :
    ∃ v ∈ s, v ∈ boundary ∧ ∀ x ∈ s, f x ≤ f v := by
  apply finite_maximum_principle s boundary f squareNorm hs
  intro x hx hnot
  obtain ⟨p, hp, hminus, hplus⟩ := hgeometry x hx hnot
  refine ⟨x - p, hminus, x + p, hplus, hf x p, ?_⟩
  rw [squareNorm_midpoint_identity]
  have hpositive := squareNorm_pos p hp
  linarith

/-- An affine real-valued function restricted to the integer lattice. -/
def affineValue (slope : ι → ℝ) (intercept : ℝ) (x : ι → ℤ) : ℝ :=
  intercept + ∑ i, slope i * (x i : ℝ)

theorem affineValue_midpoint (slope : ι → ℝ) (intercept : ℝ)
    (x p : ι → ℤ) :
    affineValue slope intercept (x - p) + affineValue slope intercept (x + p) =
      2 * affineValue slope intercept x := by
  simp only [affineValue, Pi.sub_apply, Pi.add_apply, Int.cast_sub, Int.cast_add,
    mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  ring

theorem midpointConvex_sub_affine {f : (ι → ℤ) → ℝ}
    (hf : MidpointConvex f) (slope : ι → ℝ) (intercept : ℝ) :
    MidpointConvex (fun x => f x - affineValue slope intercept x) := by
  intro x p
  have h := hf x p
  have ha := affineValue_midpoint slope intercept x p
  linarith

/-- If an affine comparison dominates a midpoint-convex function on the
boundary, it dominates throughout the finite lattice region. -/
theorem affine_domination [DecidableEq (ι → ℤ)]
    (s boundary : Finset (ι → ℤ)) (f : (ι → ℤ) → ℝ)
    (slope : ι → ℝ) (intercept : ℝ)
    (hf : MidpointConvex f) (hgeometry : HasMidpointNeighbours s boundary)
    (hboundary : ∀ v ∈ s, v ∈ boundary → f v ≤ affineValue slope intercept v) :
    ∀ x ∈ s, f x ≤ affineValue slope intercept x := by
  intro x hx
  obtain ⟨v, hv, hvboundary, hmax⟩ := lattice_maximum_principle s boundary
    (fun y => f y - affineValue slope intercept y) ⟨x, hx⟩
    (midpointConvex_sub_affine hf slope intercept) hgeometry
  have hvbound := hboundary v hv hvboundary
  have hxbound := hmax x hx
  linarith

/-- The same comparison principle for an arbitrary function preserving
midpoints, including restrictions of affine maps. -/
theorem midpoint_comparison_domination [DecidableEq (ι → ℤ)]
    (s boundary : Finset (ι → ℤ)) (f a : (ι → ℤ) → ℝ)
    (hf : MidpointConvex f) (hgeometry : HasMidpointNeighbours s boundary)
    (ha : ∀ x p, a (x - p) + a (x + p) = 2 * a x)
    (hboundary : ∀ v ∈ s, v ∈ boundary → f v ≤ a v) :
    ∀ x ∈ s, f x ≤ a x := by
  intro x hx
  have hdiff : MidpointConvex (fun y => f y - a y) := by
    intro y p
    have hf' := hf y p
    have ha' := ha y p
    linarith
  obtain ⟨v, hv, hvboundary, hmax⟩ := lattice_maximum_principle s boundary
    (fun y => f y - a y) ⟨x, hx⟩ hdiff hgeometry
  have hvbound := hboundary v hv hvboundary
  have hxbound := hmax x hx
  linarith

section SupportReduction

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Arbitrary values on an affine-independent family admit an affine
interpolant on the entire ambient vector space. -/
theorem affine_interpolation {β : Type*} [Nonempty β]
    (v : β → E) (cost : β → ℝ) (hv : AffineIndependent ℝ v) :
    ∃ L : E →ₗ[ℝ] ℝ, ∃ c : ℝ, ∀ i, c + L (v i) = cost i := by
  classical
  let i₀ : β := Classical.choice inferInstance
  let difference := fun i : {i : β // i ≠ i₀} => v i - v i₀
  have hind : LinearIndependent ℝ difference :=
    (affineIndependent_iff_linearIndependent_vsub ℝ v i₀).mp hv
  let values := fun i : {i : β // i ≠ i₀} => cost i - cost i₀
  let restricted := (Finsupp.linearCombination ℝ values).comp hind.repr
  obtain ⟨L, hL⟩ := restricted.exists_extend
  refine ⟨L, cost i₀ - L (v i₀), ?_⟩
  intro i
  by_cases hi : i = i₀
  · subst i
    ring
  · let j : {i : β // i ≠ i₀} := ⟨i, hi⟩
    let x : Submodule.span ℝ (Set.range difference) :=
      ⟨difference j, Submodule.subset_span (Set.mem_range_self j)⟩
    have hrepr : hind.repr x = Finsupp.single j 1 :=
      hind.repr_eq_single j x rfl
    have hvalue := congrArg (fun f => f x) hL
    have hdiff : L (v i - v i₀) = cost i - cost i₀ := by
      simpa [restricted, LinearMap.comp_apply, hrepr, x, difference, values, j] using hvalue
    rw [map_sub] at hdiff
    linarith

variable {β : Type*} [DecidableEq β]

theorem indexed_affine_dependence (s : Finset β) (v : β → E)
    (hdependent : ¬ AffineIndependent ℝ (fun i : s => v i)) :
    ∃ g : β → ℝ,
      (∑ x ∈ s, g x • v x) = 0 ∧ (∑ x ∈ s, g x) = 0 ∧
      ∃ x ∈ s, g x ≠ 0 := by
  classical
  rw [affineIndependent_iff_of_fintype] at hdependent
  simp only [not_forall, exists_prop] at hdependent
  obtain ⟨w, hsum, hvector, i, hi⟩ := hdependent
  simp only [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ w _ hsum (0 : E),
    vsub_eq_sub, Finset.weightedVSubOfPoint_apply, sub_zero] at hvector
  let g : β → ℝ := fun x => if hx : x ∈ s then w ⟨x, hx⟩ else 0
  have hg : ∀ x : s, g x = w x := by intro x; simp [g, x.property]
  refine ⟨g, ?_, ?_, i, i.property, ?_⟩
  · rw [← Finset.sum_coe_sort]
    simpa only [hg] using hvector
  · rw [← Finset.sum_coe_sort]
    simpa only [hg] using hsum
  · simpa only [hg] using hi

/-- An affine dependence may be oriented so that moving against it cannot
increase a prescribed linear cost. -/
theorem oriented_affine_dependence (s : Finset β) (v : β → E) (cost : β → ℝ)
    (hdependent : ¬ AffineIndependent ℝ (fun i : s => v i)) :
    ∃ g : β → ℝ,
      (∑ x ∈ s, g x • v x) = 0 ∧ (∑ x ∈ s, g x) = 0 ∧
      (∃ x ∈ s, g x ≠ 0) ∧ 0 ≤ ∑ x ∈ s, g x * cost x := by
  obtain ⟨g, hvector, hsum, hnonzero⟩ :=
    indexed_affine_dependence s v hdependent
  by_cases hcost : 0 ≤ ∑ x ∈ s, g x * cost x
  · exact ⟨g, hvector, hsum, hnonzero, hcost⟩
  · refine ⟨fun x => -g x, ?_, ?_, ?_, ?_⟩
    · simp only [neg_smul, Finset.sum_neg_distrib, hvector, neg_zero]
    · simp only [Finset.sum_neg_distrib, hsum, neg_zero]
    · obtain ⟨x, hx, hnx⟩ := hnonzero
      exact ⟨x, hx, neg_ne_zero.mpr hnx⟩
    · simp only [neg_mul, Finset.sum_neg_distrib]
      linarith

/-- One support-elimination step preserves total mass and barycentre and
does not increase cost. -/
theorem reduce_dependent_support (s : Finset β) (v : β → E) (w cost : β → ℝ)
    (hw : ∀ x ∈ s, 0 ≤ w x)
    (hdependent : ¬ AffineIndependent ℝ (fun i : s => v i)) :
    ∃ i ∈ s, ∃ u : β → ℝ,
      (∀ x ∈ s.erase i, 0 ≤ u x) ∧
      (∑ x ∈ s.erase i, u x) = ∑ x ∈ s, w x ∧
      (∑ x ∈ s.erase i, u x • v x) = ∑ x ∈ s, w x • v x ∧
      (∑ x ∈ s.erase i, u x * cost x) ≤ ∑ x ∈ s, w x * cost x := by
  classical
  obtain ⟨g, hvector, hsum, hnonzero, hcost⟩ :=
    oriented_affine_dependence s v cost hdependent
  obtain ⟨j, hj, hgj⟩ := Finset.exists_pos_of_sum_zero_of_exists_nonzero g hsum hnonzero
  let positive := s.filter fun x => 0 < g x
  have hpositive : positive.Nonempty := ⟨j, by simp [positive, hj, hgj]⟩
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image positive (fun x => w x / g x) hpositive
  have his : i ∈ s := (Finset.mem_filter.mp hi).1
  have hgi : 0 < g i := (Finset.mem_filter.mp hi).2
  let c := w i / g i
  let u := fun x => w x - c * g x
  have hc : 0 ≤ c := div_nonneg (hw i his) hgi.le
  have hui : u i = 0 := by simp [u, c, ne_of_gt hgi]
  have hunonneg : ∀ x ∈ s, 0 ≤ u x := by
    intro x hx
    by_cases hgx : 0 < g x
    · have hm := hmin x (by simp [positive, hx, hgx])
      have hle : c * g x ≤ w x := (le_div_iff₀ hgx).mp hm
      exact sub_nonneg.mpr hle
    · have hprod : c * g x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc (le_of_not_gt hgx)
      exact sub_nonneg.mpr (hprod.trans (hw x hx))
  have hmass : (∑ x ∈ s, u x) = ∑ x ∈ s, w x := by
    simp only [u, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum, mul_zero, sub_zero]
  have hbary : (∑ x ∈ s, u x • v x) = ∑ x ∈ s, w x • v x := by
    simp only [u, sub_smul, mul_smul, Finset.sum_sub_distrib, ← Finset.smul_sum,
      hvector, smul_zero, sub_zero]
  have hobjective : (∑ x ∈ s, u x * cost x) ≤ ∑ x ∈ s, w x * cost x := by
    simp only [u, sub_mul, mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum]
    exact sub_le_self _ (mul_nonneg hc hcost)
  refine ⟨i, his, u, fun x hx => hunonneg x (Finset.mem_of_mem_erase hx), ?_, ?_, ?_⟩
  · rw [Finset.sum_erase _ hui, hmass]
  · rw [Finset.sum_erase _ (by rw [hui, zero_smul]), hbary]
  · rw [Finset.sum_erase _ (by rw [hui, zero_mul])]
    exact hobjective

/-- Every finite nonnegative weighted combination has a representation on
affine-independent support with the same mass and barycentre and no larger
prescribed cost.  No compactness or optimization oracle is assumed. -/
theorem affineIndependent_support (s : Finset β) (v : β → E) (w cost : β → ℝ)
    (hw : ∀ x ∈ s, 0 ≤ w x) :
    ∃ t : Finset β, t ⊆ s ∧ ∃ u : β → ℝ,
      AffineIndependent ℝ (fun i : t => v i) ∧
      (∀ x ∈ t, 0 ≤ u x) ∧
      (∑ x ∈ t, u x) = ∑ x ∈ s, w x ∧
      (∑ x ∈ t, u x • v x) = ∑ x ∈ s, w x • v x ∧
      (∑ x ∈ t, u x * cost x) ≤ ∑ x ∈ s, w x * cost x := by
  classical
  induction s using Finset.strongInductionOn generalizing w with
  | _ s ih =>
    by_cases hindependent : AffineIndependent ℝ (fun i : s => v i)
    · exact ⟨s, Finset.Subset.refl s, w, hindependent, hw, rfl, rfl, le_rfl⟩
    · obtain ⟨i, hi, u, hu, hmass, hbary, hcost⟩ :=
        reduce_dependent_support s v w cost hw hindependent
      obtain ⟨t, hts, w', hvind, hv, hvmass, hvbary, hvcost⟩ :=
        ih (s.erase i) (Finset.erase_ssubset hi) u hu
      refine ⟨t, hts.trans (Finset.erase_subset i s), w', hvind, hv, ?_, ?_, ?_⟩
      · exact hvmass.trans hmass
      · exact hvbary.trans hbary
      · exact hvcost.trans hcost

end SupportReduction

/-- Coordinatewise inclusion of the integer lattice in its real vector space. -/
def realVector (x : ι → ℤ) : ι → ℝ := fun i => (x i : ℝ)

omit [Fintype ι] in
@[simp] theorem realVector_add (x y : ι → ℤ) :
    realVector (x + y) = realVector x + realVector y := by
  ext i
  simp [realVector]

omit [Fintype ι] in
@[simp] theorem realVector_sub (x y : ι → ℤ) :
    realVector (x - y) = realVector x - realVector y := by
  ext i
  simp [realVector]

omit [Fintype ι] in
@[simp] theorem realVector_nsmul (k : ℕ) (x : ι → ℤ) :
    realVector (k • x) = (k : ℝ) • realVector x := by
  ext i
  simp [realVector]

/-- Coarse Jensen on one simplex with at most `d + 1` vertices. -/
theorem simplex_coarse_jensen {β : Type*} [Fintype β] [Nonempty β]
    (d k : ℕ) (hd : 1 ≤ d) (hk : 2 * d ≤ k)
    (v : β → ι → ℤ) (hcard : Fintype.card β ≤ d + 1)
    (hind : AffineIndependent ℝ (fun j => realVector (v j)))
    (f : (ι → ℤ) → ℝ) (hf : MidpointConvex f)
    (w : β → ℝ) (hw : ∀ j, 0 ≤ w j) (hmass : ∑ j, w j = 1)
    (z : ι → ℤ) (hz : ∀ a, (z a : ℝ) = ∑ j, w j * (v j a : ℝ)) :
    f (k • z) ≤ ∑ j, w j * f (k • v j) := by
  classical
  have hkpos : 0 < k := by omega
  have hkreal : (k : ℝ) ≠ 0 := by exact_mod_cast hkpos.ne'
  obtain ⟨L, c, hvalues⟩ := affine_interpolation (fun j => realVector (v j))
    (fun j => f (k • v j)) hind
  let a : (ι → ℤ) → ℝ := fun x => c + L (realVector x) / k
  have havalue (j : β) : a (k • v j) = f (k • v j) := by
    change c + L (realVector (k • v j)) / k = f (k • v j)
    rw [realVector_nsmul, map_smul, smul_eq_mul, mul_div_cancel_left₀ _ hkreal]
    exact hvalues j
  have hamid (x p : ι → ℤ) : a (x - p) + a (x + p) = 2 * a x := by
    simp only [a, realVector_sub, realVector_add, map_sub, map_add]
    ring
  let region := (CoarseGeometry.finite_scaled_hull v k).toFinset
  let boundary := Finset.univ.image fun j => k • v j
  have hregion (x : ι → ℤ) : x ∈ region ↔ CoarseGeometry.InScaledHull v k x :=
    Set.Finite.mem_toFinset _
  have hinjective : Function.Injective v := by
    intro i j hij
    exact hind.injective (congrArg realVector hij)
  have hgeometry : HasMidpointNeighbours region boundary := by
    intro x hx hnot
    have hnotvertex : ∀ j, x ≠ k • v j := by
      intro j h
      apply hnot
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, h.symm⟩
    obtain ⟨p, hp, hminus, hplus⟩ :=
      CoarseGeometry.scaled_hull_midpoint_neighbours_of_dimension v hinjective
        d k hd hk hcard x ((hregion x).mp hx) hnotvertex
    exact ⟨p, hp, (hregion _).mpr hminus, (hregion _).mpr hplus⟩
  have hboundary : ∀ x ∈ region, x ∈ boundary → f x ≤ a x := by
    intro x _ hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    exact (havalue j).ge
  have hzregion : k • z ∈ region := by
    apply (hregion _).mpr
    exact CoarseGeometry.scaled_combination_mem v k w z hw hmass hz
  have hbound := midpoint_comparison_domination region boundary f a hf hgeometry
    hamid hboundary (k • z) hzregion
  have hzvector : realVector z = ∑ j, w j • realVector (v j) := by
    ext i
    simpa [realVector, Finset.sum_apply] using hz i
  have hinterpolate : a (k • z) = ∑ j, w j * f (k • v j) := by
    simp only [a, realVector_nsmul, map_smul, smul_eq_mul]
    rw [mul_div_cancel_left₀ _ hkreal, hzvector, map_sum]
    simp only [map_smul, smul_eq_mul]
    simp_rw [← hvalues]
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hmass, one_mul]
  exact hinterpolate ▸ hbound

/-- Coarse Jensen inequality for arbitrary finite convex combinations of
integer points.  The scale is at least twice the lattice dimension. -/
theorem coarse_jensen {d : ℕ} (hd : 1 ≤ d)
    (f : (Fin d → ℤ) → ℝ) (hf : MidpointConvex f)
    (k : ℕ) (hk : 2 * d ≤ k)
    {β : Type*} [Fintype β] (v : β → Fin d → ℤ)
    (w : β → ℝ) (hw : ∀ j, 0 ≤ w j) (hmass : ∑ j, w j = 1)
    (z : Fin d → ℤ) (hz : ∀ a, (z a : ℝ) = ∑ j, w j * (v j a : ℝ)) :
    f (k • z) ≤ ∑ j, w j * f (k • v j) := by
  classical
  obtain ⟨s, _, u, hind, hu, humass, hubary, hucost⟩ :=
    affineIndependent_support Finset.univ (fun j => realVector (v j)) w
      (fun j => f (k • v j)) (fun j _ => hw j)
  have hmass' : (∑ j ∈ s, u j) = 1 := humass.trans hmass
  have hsnonempty : s.Nonempty := by
    by_contra h
    have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [hempty] at hmass'
  have : Nonempty s := hsnonempty.to_subtype
  have hcard : Fintype.card s ≤ d + 1 := by
    have hc := hind.card_le_finrank_succ
    have hr := Submodule.finrank_le (vectorSpan ℝ (Set.range (fun j : s => realVector (v j))))
    have hambient : Module.finrank ℝ (Fin d → ℝ) = d := Module.finrank_fin_fun ℝ
    omega
  have hsubmass : (∑ j : s, u j) = 1 := by
    simpa only [Finset.sum_coe_sort] using hmass'
  have hsubbary : ∀ a, (z a : ℝ) = ∑ j : s, u j * (v j a : ℝ) := by
    intro a
    have hb := congrFun hubary a
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, realVector] at hb
    rw [Finset.sum_coe_sort s (fun j => u j * (v j a : ℝ))]
    exact (hz a).trans hb.symm
  have hs := simplex_coarse_jensen d k hd hk (fun j : s => v j) hcard hind f hf
    (fun j : s => u j) (fun j => hu j j.property) hsubmass z hsubbary
  rw [Finset.sum_coe_sort s (fun j => u j * f (k • v j))] at hs
  exact hs.trans hucost

end MWIS.CoarseJensen
