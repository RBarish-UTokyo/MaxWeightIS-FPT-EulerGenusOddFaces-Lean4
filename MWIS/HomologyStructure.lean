module

public import MWIS.IntegerHomology
public import Mathlib.Algebra.Module.PID
public import Mathlib.Data.ZMod.Basic

/-!
# The free part and the distinguished two-torsion class

A finitely generated abelian group with precisely one nonzero torsion element
is a product of a finite-rank free abelian group and `ZMod 2`.
-/

@[expose] public section

namespace MWIS.HomologyStructure

/-- A group consisting of zero and one nonzero element of order two is
additively isomorphic to `ZMod 2`. -/
noncomputable def twoElementEquiv {G : Type*} [AddCommGroup G]
    (κ : G) (hne : κ ≠ 0) (htwo : κ + κ = 0) (hall : ∀ x, x = 0 ∨ x = κ) :
    ZMod 2 ≃+ G := by
  classical
  have hz : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  have hzz : (1 : ZMod 2) + 1 = 0 := by decide
  let f : ZMod 2 →+ G :=
    { toFun := fun z => if z = 0 then 0 else κ
      map_zero' := by simp
      map_add' := by
        intro a b
        rcases hz a with rfl | rfl <;> rcases hz b with rfl | rfl <;> simp [htwo, hzz] }
  apply AddEquiv.ofBijective f
  constructor
  · intro a b hab
    rcases hz a with rfl | rfl <;> rcases hz b with rfl | rfl <;> simp_all [f]
  · intro g
    rcases hall g with rfl | rfl
    · exact ⟨0, by simp [f]⟩
    · exact ⟨1, by simp [f]⟩

/-- A finitely generated abelian group with precisely one nonzero torsion
class has a finite free part and one factor of order two. -/
theorem exists_free_prod_two {H : Type*} [AddCommGroup H] [Module.Finite ℤ H]
    (κ : H) (hne : κ ≠ 0) (htwo : κ + κ = 0)
    (htorsion : ∀ h n, 0 < n → n • h = 0 → h = 0 ∨ h = κ) :
    ∃ r : ℕ, Nonempty (H ≃+ (Fin r → ℤ) × ZMod 2) := by
  let T := Submodule.torsion ℤ H
  have hκT : κ ∈ T := by
    rw [Submodule.mem_torsion_iff]
    refine ⟨⟨2, mem_nonZeroDivisors_of_ne_zero (by norm_num)⟩, ?_⟩
    change (2 : ℤ) • κ = 0
    simpa only [two_smul] using htwo
  let κT : T := ⟨κ, hκT⟩
  have hκTne : κT ≠ 0 := fun h => hne (congrArg Subtype.val h)
  have hκTtwo : κT + κT = 0 := Subtype.ext htwo
  have hT : ∀ x : T, x = 0 ∨ x = κT := by
    intro x
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff (R := ℤ) (M := H) x.val).mp x.property
    have hn : 0 < a.val.natAbs := Int.natAbs_pos.mpr (nonZeroDivisors.coe_ne_zero a)
    have hz : a.val.natAbs • x.val = 0 := natAbs_nsmul_eq_zero.mpr ha
    rcases htorsion x.val a.val.natAbs hn hz with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  let eT : T ≃+ ZMod 2 := (twoElementEquiv κT hκTne hκTtwo hT).symm
  obtain ⟨r, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := H ⧸ T)
  obtain ⟨f, hf⟩ := Module.projective_lifting_property T.mkQ LinearMap.id T.mkQ_surjective
  have he : T.subtype.range = T.mkQ.ker := by
    rw [Submodule.range_subtype, Submodule.ker_mkQ]
  let es : H ≃ₗ[ℤ] T × (H ⧸ T) :=
    (lequivProdOfRightSplitExact T.injective_subtype he hf).symm
  exact ⟨r, ⟨es.toAddEquiv.trans ((eT.prodCongr b.equivFun.toAddEquiv).trans
    AddEquiv.prodComm)⟩⟩

/-- In every such product decomposition the distinguished nonzero torsion
class has zero free coordinates and nonzero parity coordinate. -/
theorem distinguished_class_coordinates {H : Type*} [AddCommGroup H]
    (κ : H) (hne : κ ≠ 0) (htwo : κ + κ = 0)
    {r : ℕ} (e : H ≃+ (Fin r → ℤ) × ZMod 2) : e κ = (0, 1) := by
  have he : e κ + e κ = 0 := by rw [← map_add, htwo, map_zero]
  have hfree : (e κ).1 = 0 := by
    ext i
    have hi := congrArg (fun p : (Fin r → ℤ) × ZMod 2 => p.1 i) he
    change (e κ).1 i + (e κ).1 i = 0 at hi
    change (e κ).1 i = 0
    omega
  have hparity : (e κ).2 = 1 := by
    have hz : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    rcases hz (e κ).2 with hz | hz
    · exfalso
      apply hne
      apply e.injective
      rw [map_zero]
      exact Prod.ext hfree hz
    · exact hz
  exact Prod.ext hfree hparity

/-- The free and order-two decomposition with the distinguished class in
its specified coordinate. -/
theorem exists_free_prod_two_with_class {H : Type*} [AddCommGroup H]
    [Module.Finite ℤ H] (κ : H) (hne : κ ≠ 0) (htwo : κ + κ = 0)
    (htorsion : ∀ h n, 0 < n → n • h = 0 → h = 0 ∨ h = κ) :
    ∃ (r : ℕ) (e : H ≃+ (Fin r → ℤ) × ZMod 2), e κ = (0, 1) := by
  obtain ⟨r, ⟨e⟩⟩ := exists_free_prod_two κ hne htwo htorsion
  exact ⟨r, e, distinguished_class_coordinates κ hne htwo e⟩

/-- The complete integral cokernel description for connected nonbipartite
unsigned incidence, independent of a choice of Smith normal form. -/
theorem unsigned_cokernel_structure {E V H : Type*} [Fintype E] [AddCommGroup H]
    (A : SignedIncidence.Matrix E V) (hA : A.Connected) (hs : A.Unsigned)
    (hn : ¬ A.Bipartite) (root : V) (p : (E → ℤ) →+ H)
    (hp : Function.Surjective p)
    (hexact : ∀ y, p y = 0 ↔ ∃ x, A.map x = y) :
    ∃ (r : ℕ) (e : H ≃+ (Fin r → ℤ) × ZMod 2), e (p (fun _ => 1)) = (0, 1) := by
  let : Module.Finite ℤ H := Module.Finite.of_surjective p.toIntLinearMap hp
  obtain ⟨hne, htwo⟩ :=
    IntegerHomology.unsigned_distinguished_class_order_two A hs hn p hexact
  apply exists_free_prod_two_with_class (p (fun _ => 1)) hne
    (by simpa only [two_smul] using htwo)
  exact IntegerHomology.unsigned_torsion_classification A hA hs root p hp hexact

end MWIS.HomologyStructure

end
