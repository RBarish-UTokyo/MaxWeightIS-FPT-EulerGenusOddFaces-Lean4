module

public import MWIS.FiniteExtension
public import MWIS.ResidueHull
public import MWIS.CoreOptimum
public import MWIS.KernelCoordinates

/-!
# Exact network optimization for an integral cycle quotient

Ambient residue and free-coordinate labels are constructed from the actual
integer kernel. The explicit signed-cover hub network then computes the
independent-set optimum through a real linear program with attained value.

Date: 2026-10-23.
-/

@[expose] public section
namespace MWIS.CoreNetwork

open CycleQuotient ResidueJensen RealCoordinates

variable {V E Row : Type*} [Fintype E] [Fintype Row]
  [DecidableEq E] [DecidableEq Row]

omit [Fintype E] [DecidableEq E] [DecidableEq Row] in
/-- Additive class labels on an integer kernel admit ambient additive extensions. -/
theorem exists_label_extension {H : Type*} [AddCommGroup H]
    (B : (E → ℤ) →+ (Row → ℤ)) (Q : B.ker →+ H) :
    ∃ L : (E → ℤ) →+ H, ∀ y : B.ker, L y.val = Q y := by
  exact KernelCoordinates.exists_ambient_extension B.toIntLinearMap Q

omit [Fintype Row] [DecidableEq E] in
/-- The actual residue points of the integer class quotient agree with the
signed-flow residue points used by the finite-network construction. -/
theorem points_eq_signedPoints {H : Type*} [AddCommGroup H] {r : ℕ}
    (B : (E → ℤ) →+ (Row → ℤ)) (C : E → Walks.Column Row)
    (hBC : ∀ y r, B y r = ∑ e, Walks.columnVector (C e) r * y e)
    (Q : B.ker →+ H) (e : H ≃+ (Fin r → ℤ) × ZMod 2) (κ : H)
    (ell : (E → ℤ) →+ Residue r)
    (hell : ∀ y : B.ker, ell y.val = residueMap e (Q y)) :
    ResidueHull.points B Q e κ = castVector ''
      FiniteExtension.signedPoints C ell (residueMap e κ) := by
  ext u
  constructor
  · rintro ⟨y, hn, hr, rfl⟩
    refine ⟨y.val, ⟨hn, ?_, ?_⟩, rfl⟩
    · intro row
      rw [← hBC]
      exact congrFun y.property row
    · exact (hell y).trans hr
  · rintro ⟨y, ⟨hn, hb, hr⟩, rfl⟩
    have hy : B y = 0 := by ext row; rw [hBC, hb]; rfl
    let y' : B.ker := ⟨y, hy⟩
    refine ⟨y', hn, ?_, rfl⟩
    exact (hell y').symm.trans hr

/-- Transport an attained optimum through an exact image equality. -/
theorem isLeast_pullback {X Y : Type*} (Z : Set X) (S : Set Y) (rho : X → Y)
    (W : Y → Prop) (cost : Y → ℝ) (v : ℝ) (himage : rho '' Z = S)
    (hmin : IsLeast (cost '' {y | y ∈ S ∧ W y}) v) :
    IsLeast ((fun x => cost (rho x)) '' {x | x ∈ Z ∧ W (rho x)}) v := by
  constructor
  · obtain ⟨y, ⟨hy, hW⟩, hcost⟩ := hmin.1
    rw [← himage] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, ⟨hx, hW⟩, hcost⟩
  · rintro a ⟨x, ⟨hx, hW⟩, rfl⟩
    apply hmin.2
    exact ⟨rho x, ⟨himage ▸ Set.mem_image_of_mem rho hx, hW⟩, rfl⟩

/-- An explicit finite network LP has the attained value complementary to a
maximum-weight independent set. All ambient labels, class minima, midpoint
inequalities, and network projection identities are constructed internally.
The remaining structural input is the stated integral class-group isomorphism. -/
theorem exists_network_optimum [Fintype V] [DecidableEq V]
    (left right : E → V) (B : (E → ℤ) →+ (Row → ℤ))
    (hBA : ∀ z, B (IncidenceSplit.incidence left right z) = 0)
    (hB1 : B (fun _ => 1) = 0)
    (C : E → Walks.Column Row)
    (hBC : ∀ y r, B y r = ∑ e, Walks.columnVector (C e) r * y e)
    (r : ℕ) (e : Homology left right B hBA ≃+ (Fin r → ℤ) × ZMod 2)
    (hκ : e (characteristicClass left right B hBA hB1) = (0, 1))
    (c : E → ℚ) (hc : ∀ edge, 0 ≤ c edge) :
    ∃ (W : (E → ℤ) →+ (Fin r → ℤ)) (ell : (E → ℤ) →+ Residue r)
      (I : Finset V) (v : ℝ),
      (∀ y : B.ker, W y.val = (e (classMap left right B hBA y)).1) ∧
      (∀ y : B.ker, ell y.val = residueMap e (classMap left right B hBA y)) ∧
      Slack.Independent left right I ∧
      (∀ J : Finset V, Slack.Independent left right J →
        Slack.setWeight left right c J ≤ Slack.setWeight left right c I) ∧
      (Slack.setWeight left right c I : ℝ) = (Slack.totalCost c : ℝ) - v ∧
      IsLeast ((fun z => cost c (FiniteExtension.rho C z)) ''
        {z | z ∈ FiniteExtension.polyhedron C ell
            (residueMap e (characteristicClass left right B hBA hB1)) ∧
          extension W (FiniteExtension.rho C z) = 0}) v := by
  let Q := classMap left right B hBA
  let κ := characteristicClass left right B hBA hB1
  let freeQ : B.ker →+ (Fin r → ℤ) :=
    (AddMonoidHom.fst (Fin r → ℤ) (ZMod 2)).comp (e.toAddMonoidHom.comp Q)
  obtain ⟨W, hW⟩ := exists_label_extension B freeQ
  have hW' : ∀ y : B.ker, W y.val = (e (Q y)).1 := hW
  obtain ⟨ell, hell⟩ := exists_label_extension B ((residueMap e).comp Q)
  have hell' : ∀ y : B.ker, ell y.val = residueMap e (Q y) := hell
  obtain ⟨F, I, hI, hmax, hvalue, hattain, hlower, hmid⟩ :=
    CoreOptimum.exists_midpoint_optimum left right B hBA hB1 c hc
  refine ⟨W, ell, I, F κ, hW', hell', hI, hmax, hvalue, ?_⟩
  have hmin := ResidueHull.exact_minimum B Q e κ hκ W hW' c F hattain hlower hmid
  have hpoints := points_eq_signedPoints B C hBC Q e κ ell hell'
  have hprojection : FiniteExtension.rho C ''
      FiniteExtension.polyhedron C ell (residueMap e κ) =
      convexHull ℝ (ResidueHull.points B Q e κ) := by
    rw [hpoints]
    exact FiniteExtension.projection_exact C ell (residueMap e κ)
  exact isLeast_pullback _ _ (FiniteExtension.rho C)
    (fun y => extension W y = 0) (cost c) (F κ) hprojection hmin

/-- Explicit ambient coordinate labels may be used directly. This version
supports computed bounded integer labels without any choice in the network data. -/
theorem exists_network_optimum_of_labels [Fintype V] [DecidableEq V]
    (left right : E → V) (B : (E → ℤ) →+ (Row → ℤ))
    (hBA : ∀ z, B (IncidenceSplit.incidence left right z) = 0)
    (hB1 : B (fun _ => 1) = 0)
    (C : E → Walks.Column Row)
    (hBC : ∀ y row, B y row = ∑ edge, Walks.columnVector (C edge) row * y edge)
    (r : ℕ) (e : Homology left right B hBA ≃+ (Fin r → ℤ) × ZMod 2)
    (hκ : e (characteristicClass left right B hBA hB1) = (0, 1))
    (W : (E → ℤ) →+ (Fin r → ℤ))
    (hW : ∀ y : B.ker, W y.val = (e (classMap left right B hBA y)).1)
    (ell : (E → ℤ) →+ Residue r)
    (hell : ∀ y : B.ker, ell y.val = residueMap e (classMap left right B hBA y))
    (c : E → ℚ) (hc : ∀ edge, 0 ≤ c edge) :
    ∃ (I : Finset V) (v : ℝ),
      Slack.Independent left right I ∧
      (∀ J : Finset V, Slack.Independent left right J →
        Slack.setWeight left right c J ≤ Slack.setWeight left right c I) ∧
      (Slack.setWeight left right c I : ℝ) = (Slack.totalCost c : ℝ) - v ∧
      IsLeast ((fun z => cost c (FiniteExtension.rho C z)) ''
        {z | z ∈ FiniteExtension.polyhedron C ell
            (residueMap e (characteristicClass left right B hBA hB1)) ∧
          extension W (FiniteExtension.rho C z) = 0}) v := by
  let Q := classMap left right B hBA
  let κ := characteristicClass left right B hBA hB1
  obtain ⟨F, I, hI, hmax, hvalue, hattain, hlower, hmid⟩ :=
    CoreOptimum.exists_midpoint_optimum left right B hBA hB1 c hc
  refine ⟨I, F κ, hI, hmax, hvalue, ?_⟩
  have hmin := ResidueHull.exact_minimum B Q e κ hκ W hW c F hattain hlower hmid
  have hpoints := points_eq_signedPoints B C hBC Q e κ ell hell
  have hprojection : FiniteExtension.rho C ''
      FiniteExtension.polyhedron C ell (residueMap e κ) =
      convexHull ℝ (ResidueHull.points B Q e κ) := by
    rw [hpoints]
    exact FiniteExtension.projection_exact C ell (residueMap e κ)
  exact isLeast_pullback _ _ (FiniteExtension.rho C)
    (fun y => extension W y = 0) (cost c) (F κ) hprojection hmin

end MWIS.CoreNetwork
end
