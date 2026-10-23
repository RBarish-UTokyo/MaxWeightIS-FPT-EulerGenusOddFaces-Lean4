module

public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# Ambient integral coordinates on an integer kernel

A kernel of a map between finite free integer modules is a direct summand.
Consequently every additive class map on the kernel extends to the ambient
integer module. This provides existence of ambient labels without adding a
primitive-coordinate hypothesis.

Date: 2026-10-23.
-/

@[expose] public section
namespace MWIS.KernelCoordinates

variable {E F : Type*} [Fintype E] [Fintype F]

omit [Fintype E] in
/-- An integer kernel admits an integral linear retraction from its ambient
module. The proof splits the surjection onto the free image over the PID ℤ. -/
theorem exists_retraction (B : (E → ℤ) →ₗ[ℤ] (F → ℤ)) :
    ∃ C : (E → ℤ) →ₗ[ℤ] LinearMap.ker B,
      C.comp (LinearMap.ker B).subtype = LinearMap.id := by
  classical
  obtain ⟨d, b⟩ := (LinearMap.range B).basisOfPid (Pi.basisFun ℤ F)
  have : Module.Free ℤ (LinearMap.range B) := Module.Free.of_basis b
  obtain ⟨s, hs⟩ := Module.projective_lifting_property B.rangeRestrict
    (LinearMap.id : LinearMap.range B →ₗ[ℤ] LinearMap.range B)
    B.surjective_rangeRestrict
  let P : (E → ℤ) →ₗ[ℤ] (E → ℤ) := LinearMap.id - s.comp B.rangeRestrict
  have hP (x : E → ℤ) : P x ∈ LinearMap.ker B := by
    have h := LinearMap.congr_fun hs (B.rangeRestrict x)
    have h' := congrArg Subtype.val h
    change B (s (B.rangeRestrict x)) = B x at h'
    simp [P, LinearMap.mem_ker, h']
  let C := P.codRestrict (LinearMap.ker B) hP
  refine ⟨C, ?_⟩
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  have hx : B.rangeRestrict x = 0 := by
    apply Subtype.ext
    exact x.property
  simp [C, P, hx]

omit [Fintype E] in
/-- Every additive homology or residue label on an integer kernel extends to
an additive label on all ambient edge vectors. -/
theorem exists_ambient_extension {H : Type*} [AddCommGroup H]
    (B : (E → ℤ) →ₗ[ℤ] (F → ℤ)) (Q : LinearMap.ker B →+ H) :
    ∃ L : (E → ℤ) →+ H, ∀ y : LinearMap.ker B, L y = Q y := by
  obtain ⟨C, hC⟩ := exists_retraction B
  refine ⟨Q.comp C.toAddMonoidHom, ?_⟩
  intro y
  have h := LinearMap.congr_fun hC y
  change C y = y at h
  change Q (C y) = Q y
  rw [h]

/-- Finite integral kernel coordinates and their ambient coordinate map.
The identity `C ∘ K = I` and reconstruction on every integral cycle are
proved over ℤ, with no denominator clearing or saturation assumptions. -/
theorem exists_kernel_coordinates (B : (E → ℤ) →ₗ[ℤ] (F → ℤ)) :
    ∃ (d : ℕ) (K : (Fin d → ℤ) →ₗ[ℤ] (E → ℤ))
      (C : (E → ℤ) →ₗ[ℤ] (Fin d → ℤ)),
      C.comp K = LinearMap.id ∧
      (∀ z, B (K z) = 0) ∧
      (∀ y, B y = 0 → K (C y) = y) := by
  classical
  obtain ⟨d, b⟩ := (LinearMap.ker B).basisOfPid (Pi.basisFun ℤ E)
  obtain ⟨P, hP⟩ := exists_retraction B
  let e : LinearMap.ker B ≃ₗ[ℤ] (Fin d → ℤ) := b.equivFun
  let K := (LinearMap.ker B).subtype.comp e.symm.toLinearMap
  let C := e.toLinearMap.comp P
  have hfix (y : LinearMap.ker B) : P y = y := LinearMap.congr_fun hP y
  refine ⟨d, K, C, ?_, ?_, ?_⟩
  · apply LinearMap.ext
    intro z
    change e (P (e.symm z)) = z
    rw [hfix, e.apply_symm_apply]
  · intro z
    exact (e.symm z).property
  · intro y hy
    let y' : LinearMap.ker B := ⟨y, hy⟩
    have h := hfix y'
    change P y = y' at h
    change (e.symm (e (P y))).val = y
    rw [e.symm_apply_apply, h]


end MWIS.KernelCoordinates
end
