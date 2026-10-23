module

public import MWIS.HomologyCoordinates
public import MWIS.Incidence
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.Dimension.Torsion.Finite

/-!
# Rank bounds for the integral free coordinates

Integral cycle coordinates embed in rational cycle coordinates. Rank-nullity
then bounds the free homology rank by the rational supplementary dimension.
-/

@[expose] public section

namespace MWIS.HomologyRank

variable {V E K : Type*} [AddCommGroup K]

/-- Walk connectivity implies connectivity in the equivalence closure of
port adjacency used by the integral presentation. -/
theorem connected_of_walk_connected (left right : E → V)
    (hc : Incidence.Connected left right) :
    (HomologyCoordinates.incidenceMatrix left right).Connected := by
  intro u v
  obtain ⟨n, h⟩ := hc u v
  induction h with
  | nil => exact .refl _
  | @forward b n e hb h ih =>
      subst b
      exact .trans _ _ _ ih (.rel _ _ ⟨e, rfl, rfl⟩)
  | @backward b n e hb h ih =>
      subst b
      exact .trans _ _ _ ih (.symm _ _ (.rel _ _ ⟨e, rfl, rfl⟩))

/-- Connected nonbipartite unsigned incidence is injective over the integers. -/
theorem incidence_injective (left right : E → V)
    (hc : Incidence.Connected left right) (hn : ¬ Incidence.Bipartite left right) :
    Function.Injective (IncidenceSplit.incidence left right) := by
  intro x y hxy
  have hq : (fun v => ((x v - y v : ℤ) : ℚ)) = 0 := by
    apply Incidence.kernel_eq_zero_of_nonbipartite left right hc hn
    intro e
    have h := congrFun hxy e
    change x (left e) + x (right e) = y (left e) + y (right e) at h
    push_cast
    exact_mod_cast (show x (left e) - y (left e) + (x (right e) - y (right e)) = 0 by omega)
  funext v
  have h := congrFun hq v
  change ((x v - y v : ℤ) : ℚ) = 0 at h
  have : x v - y v = 0 := by exact_mod_cast h
  omega

/-- The free rank of a product with the two-element torsion group is the
number of integer coordinates. -/
theorem free_product_finrank (r : ℕ) :
    Module.finrank ℤ ((Fin r → ℤ) × ZMod 2) = r := by
  let f : ((Fin r → ℤ) × ZMod 2) →ₗ[ℤ] (Fin r → ℤ) := LinearMap.fst ℤ _ _
  have hf : Function.Surjective f := fun x => ⟨(x, 0), rfl⟩
  have ht : Module.IsTorsion ℤ f.ker := by
    intro z
    refine ⟨⟨2, mem_nonZeroDivisors_of_ne_zero (by norm_num)⟩, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · have hz : z.val.1 = 0 := z.property
      change (2 : ℤ) • z.val.1 = 0
      rw [hz, smul_zero]
    · change (2 : ℤ) • z.val.2 = 0
      simp only [zsmul_eq_mul, Int.cast_ofNat]
      have hz : (2 : ZMod 2) = 0 := by decide
      rw [hz, zero_mul]
  have hd := LinearMap.rank_range_add_rank_ker f
  rw [rank_range_of_surjective f hf, ht.rank_eq_zero, add_zero] at hd
  have hd' := congrArg Cardinal.toNat hd
  change Module.finrank ℤ (Fin r → ℤ) =
    Module.finrank ℤ ((Fin r → ℤ) × ZMod 2) at hd'
  simpa only [Module.finrank_pi, Fintype.card_fin] using hd'.symm

/-- Rank-nullity inside the actual cycle subgroup subtracts exactly one
independent incidence column per vertex. -/
theorem homology_rank_add_vertices [Fintype E] [Fintype V]
    (left right : E → V) (B : (E → ℤ) →+ K)
    (hBA : ∀ z, B (IncidenceSplit.incidence left right z) = 0)
    (hc : Incidence.Connected left right) (hn : ¬ Incidence.Bipartite left right) :
    Module.finrank ℤ (CycleQuotient.Homology left right B hBA) + Fintype.card V =
      Module.finrank ℤ B.ker := by
  have : Module.Finite ℤ B.ker := by
    change Module.Finite ℤ B.toIntLinearMap.ker
    infer_instance
  let D := (CycleQuotient.boundary left right B hBA).toIntLinearMap
  have hD : Function.Injective D := by
    intro x y hxy
    apply incidence_injective left right hc hn
    exact congrArg Subtype.val hxy
  have hdim := D.range.finrank_quotient_add_finrank
  have hrange : Module.finrank ℤ D.range = Fintype.card V := by
    rw [LinearMap.finrank_range_of_inj hD, Module.finrank_pi]
  change Module.finrank ℤ (CycleQuotient.Homology left right B hBA) +
    Module.finrank ℤ D.range = Module.finrank ℤ B.ker at hdim
  rwa [hrange] at hdim

/-- Integral cycles inject into the rational cycles whenever the rational
cycle equation vanishes on every integral cycle. -/
theorem integer_kernel_rank_le_rational [Fintype E] {W : Type*}
    [AddCommGroup W] [Module ℚ W] (B : (E → ℤ) →+ K)
    (BQ : (E → ℚ) →ₗ[ℚ] W)
    (hcompat : ∀ y : E → ℤ, B y = 0 → BQ (fun e => (y e : ℚ)) = 0) :
    Module.finrank ℤ B.ker ≤ Module.finrank ℚ BQ.ker := by
  let f : B.ker →ₗ[ℤ] BQ.ker :=
    { toFun := fun y => ⟨fun e => ((y : E → ℤ) e : ℚ), hcompat y y.property⟩
      map_add' := by intro x y; apply Subtype.ext; ext e; simp
      map_smul' := by intro n y; apply Subtype.ext; ext e; simp }
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    funext e
    have h := congrArg (fun z : BQ.ker => (z : E → ℚ) e) hxy
    change (((x : E → ℤ) e : ℚ)) = (((y : E → ℤ) e : ℚ)) at h
    exact_mod_cast h
  have hi := LinearMap.rank_le_of_injective f hf
  rw [← IsFractionRing.rank_right_eq ℤ ℚ BQ.ker] at hi
  exact Cardinal.toNat_le_toNat hi (Module.rank_lt_aleph0 ℚ BQ.ker)

/-- The number of free integral homology coordinates is at most the
rational kernel dimension minus the number of vertices. -/
theorem free_rank_le_rational_codimension [Fintype E] [Fintype V] {W : Type*}
    [AddCommGroup W] [Module ℚ W]
    (left right : E → V) (B : (E → ℤ) →+ K)
    (hBA : ∀ z, B (IncidenceSplit.incidence left right z) = 0)
    (hc : Incidence.Connected left right) (hn : ¬ Incidence.Bipartite left right)
    (BQ : (E → ℚ) →ₗ[ℚ] W)
    (hcompat : ∀ y : E → ℤ, B y = 0 → BQ (fun e => (y e : ℚ)) = 0)
    {r : ℕ} (e : CycleQuotient.Homology left right B hBA ≃+
      (Fin r → ℤ) × ZMod 2) :
    r + Fintype.card V ≤ Module.finrank ℚ BQ.ker := by
  have he := e.toIntLinearEquiv.finrank_eq
  rw [free_product_finrank] at he
  have hid := homology_rank_add_vertices left right B hBA hc hn
  rw [he] at hid
  rw [hid]
  exact integer_kernel_rank_le_rational B BQ hcompat

end MWIS.HomologyRank

end
