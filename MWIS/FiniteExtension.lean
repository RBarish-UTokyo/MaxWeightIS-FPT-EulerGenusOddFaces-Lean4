module

public import MWIS.SignedCover
public import MWIS.GroupExtension
public import MWIS.RealCoordinates
public import Mathlib.Analysis.Convex.Hull

/-!
# Finite-group extension of signed integer cycle classes

The signed cover and the finite-group hub network are composed through their
actual coordinate-sum projections. Integral lifting identifies the projected
feasible points exactly, and real network integrality gives the corresponding
convex-hull identity.

Prepared 2026-10-23.
-/

@[expose] public section

namespace MWIS.FiniteExtension

open scoped BigOperators
open MWIS.Walks
open MWIS.RealCoordinates

variable {Row Edge G : Type*} [Fintype Edge]
  [DecidableEq Row] [DecidableEq Edge] [AddCommGroup G]

/-- The integral cover projection sums multiplicities over each original edge. -/
def coverProjection (C : Edge → Column Row) : (Arc C → ℤ) →+ (Edge → ℤ) where
  toFun f e := ∑ a, if a.val.1 = e then f a else 0
  map_zero' := by ext e; simp
  map_add' f g := by
    ext e
    simp only [Pi.add_apply]
    simp_rw [ite_add_zero, Finset.sum_add_distrib]

/-- The same cover projection on real edge spaces. -/
def coverProjectionReal (C : Edge → Column Row) : (Arc C → ℝ) →ₗ[ℝ] (Edge → ℝ) where
  toFun f e := ∑ a, if a.val.1 = e then f a else 0
  map_add' f g := by
    ext e
    simp only [Pi.add_apply]
    simp_rw [ite_add_zero, Finset.sum_add_distrib]
  map_smul' a f := by
    ext e
    simp [Finset.mul_sum, mul_ite]

/-- The real projection agrees exactly with scalar inclusion of the integral projection. -/
theorem coverProjectionReal_cast (C : Edge → Column Row) (f : Arc C → ℤ) :
    coverProjectionReal C (castVector f) = castVector (coverProjection C f) := by
  ext e
  simp [coverProjectionReal, coverProjection, castVector]

/-- Natural and integral cover projections agree on nonnegative multiplicities. -/
theorem coverProjection_nat (C : Edge → Column Row) (f : Arc C → ℕ) (e : Edge) :
    coverProjection C (fun a => (f a : ℤ)) e = (SignedCover.projection C f e : ℤ) := by
  simp [coverProjection, SignedCover.projection]

/-- Arbitrary additive group labels commute with the cover projection. -/
theorem label_coverProjection (C : Edge → Column Row)
    (ell : (Edge → ℤ) →+ G) (f : Arc C → ℤ) :
    ell (coverProjection C f) = ∑ a, f a • ell (Pi.single a.val.1 1) := by
  rw [label_expansion]
  simp only [coverProjection, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Finset.sum_smul, ite_smul, zero_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp

/-- The signed nonnegative integer cycle vectors with one prescribed group label. -/
def signedPoints (C : Edge → Column Row) (ell : (Edge → ℤ) →+ G) (η : G) :
    Set (Edge → ℤ) :=
  {y | (∀ e, 0 ≤ y e) ∧
    (∀ r, (∑ e, columnVector (C e) r * y e) = 0) ∧ ell y = η}

/-- Labelled nonnegative integer circulations in the actual signed cover. -/
def coverPoints (C : Edge → Column Row) (ell : (Edge → ℤ) →+ G) (η : G) :
    Set (Arc C → ℤ) :=
  {f | (∀ a, 0 ≤ f a) ∧
    (∀ u, GroupNetwork.boundary (source C) (target C) f u = 0) ∧
    (∑ a, f a • ell (Pi.single a.val.1 1)) = η}

/-- Exact integral projection of the signed cover, with the complete ambient label. -/
theorem cover_projection_exact [Fintype Row] (C : Edge → Column Row)
    (ell : (Edge → ℤ) →+ G) (η : G) :
    coverProjection C '' coverPoints C ell η = signedPoints C ell η := by
  ext y
  constructor
  · rintro ⟨f, ⟨hfn, hfb, hfl⟩, rfl⟩
    have hcast : ∀ a, ((f a).toNat : ℤ) = f a := fun a => Int.toNat_of_nonneg (hfn a)
    have hp (e : Edge) : (SignedCover.projection C (fun a => (f a).toNat) e : ℤ) =
        coverProjection C f e := by
      rw [← coverProjection_nat]
      simp only [hcast]
    refine ⟨?_, ?_, ?_⟩
    · intro e
      rw [← hp]
      exact Int.natCast_nonneg _
    · intro r
      have h := SignedCover.integral_projection_sound C (fun a => (f a).toNat)
        (by simpa only [hcast] using hfb) r
      simpa only [hp] using h
    · rw [label_coverProjection]
      exact hfl
  · rintro ⟨hyn, hyb, hyl⟩
    have hcast : ∀ e, ((y e).toNat : ℤ) = y e := fun e => Int.toNat_of_nonneg (hyn e)
    obtain ⟨f, hfb, hp⟩ := SignedCover.integral_lift C (fun e => (y e).toNat)
      (by simpa only [hcast] using hyb)
    have hproj : coverProjection C (fun a => (f a : ℤ)) = y := by
      ext e
      rw [coverProjection_nat, hp, hcast]
    refine ⟨fun a => (f a : ℤ), ⟨fun _ => Int.natCast_nonneg _, hfb, ?_⟩, hproj⟩
    rw [← label_coverProjection, hproj]
    exact hyl

/-- The real image of the integral cover classes is exactly the real image of
the corresponding signed classes. -/
theorem cover_projection_cast_exact [Fintype Row] (C : Edge → Column Row)
    (ell : (Edge → ℤ) →+ G) (η : G) :
    coverProjectionReal C '' (castVector '' coverPoints C ell η) =
      castVector '' signedPoints C ell η := by
  rw [← cover_projection_exact C ell η, Set.image_image, Set.image_image]
  congr 1
  funext f
  exact coverProjectionReal_cast C f

/-- Convex hull commutes with the explicit cover projection. -/
theorem cover_projection_convexHull [Fintype Row] (C : Edge → Column Row)
    (ell : (Edge → ℤ) →+ G) (η : G) :
    coverProjectionReal C '' convexHull ℝ (castVector '' coverPoints C ell η) =
      convexHull ℝ (castVector '' signedPoints C ell η) := by
  rw [LinearMap.image_convexHull, cover_projection_cast_exact]

/-- Arc labels are the images of the original coordinate unit vectors. -/
def arcLabel (C : Edge → Column Row) (ell : (Edge → ℤ) →+ G) (a : Arc C) : G :=
  ell (Pi.single a.val.1 1)

/-- Actual arcs of the hub extension built over the signed cover. -/
abbrev ExtensionArc (C : Edge → Column Row) (G : Type*) :=
  GroupNetwork.Arc (State Row) (Arc C) G

/-- The total real projection first sums hub copies, then signed-cover orientations. -/
noncomputable def rho [Fintype Row] [Fintype G] (C : Edge → Column Row) :
    (ExtensionArc C G → ℝ) →ₗ[ℝ] (Edge → ℝ) :=
  (coverProjectionReal C).comp GroupExtension.projectionLinear

/-- The explicit finite-dimensional nonnegative unit-flow extension polyhedron. -/
def polyhedron [Fintype Row] [Fintype G] [DecidableEq G]
    (C : Edge → Column Row) (ell : (Edge → ℤ) →+ G) (η : G) :
    Set (ExtensionArc C G → ℝ) :=
  GroupExtension.realHubFlows (source C) (target C) (arcLabel C ell) η

/-- The actual finite-group network projects exactly onto the convex hull of
all nonnegative integral signed cycles of the required residue class. This
statement includes integral lifting and real network integrality. -/
theorem projection_exact [Fintype Row] [Fintype G] [DecidableEq G]
    (C : Edge → Column Row) (ell : (Edge → ℤ) →+ G) (η : G) :
    rho C '' polyhedron C ell η =
      convexHull ℝ (castVector '' signedPoints C ell η) := by
  change (fun z => coverProjectionReal C (GroupExtension.projectionLinear z)) ''
    GroupExtension.realHubFlows (source C) (target C) (arcLabel C ell) η = _
  rw [← Set.image_image, GroupExtension.projection_real_hull]
  exact cover_projection_convexHull C ell η

omit [DecidableEq Edge] [AddCommGroup G] in
/-- The extension has at most one group copy for each signed state and signed arc. -/
theorem extension_arc_card_le [Fintype Row] [Fintype G]
    (C : Edge → Column Row) :
    Fintype.card (ExtensionArc C G) ≤
      (2 * Fintype.card Row + 1) * (2 * Fintype.card Edge) * Fintype.card G := by
  rw [GroupNetwork.arc_card, Walks.state_card]
  exact Nat.mul_le_mul_right (Fintype.card G)
    (Nat.mul_le_mul_left (2 * Fintype.card Row + 1) (Walks.arc_card_le C))

end MWIS.FiniteExtension

end
