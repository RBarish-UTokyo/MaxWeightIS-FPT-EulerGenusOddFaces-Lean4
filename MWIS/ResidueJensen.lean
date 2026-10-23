module

public import MWIS.CoreBridge
public import MWIS.GroupSize
public import Mathlib.Algebra.Group.Prod

/-!
# Coarse Jensen on finite residue classes

The free and parity coordinates of an actual class-group isomorphism define
the finite residue label. Equality with the distinguished residue is converted
to a multiple of the prescribed modulus, and the coarse Jensen inequality
then applies to the attained class-value function.

Prepared 2026-10-23.
-/

@[expose] public section

namespace MWIS.ResidueJensen

variable {H : Type*} [AddCommGroup H]

/-- The finite group consisting of one parity coordinate and free residues. -/
abbrev Residue (r : ℕ) := ZMod 2 × (Fin r → ZMod (GroupSize.modulus r))

/-- Lift the free summand through an integral class-group decomposition. -/
def freeLift {r : ℕ} (e : H ≃+ (Fin r → ℤ) × ZMod 2) : (Fin r → ℤ) →+ H where
  toFun z := e.symm (z, 0)
  map_zero' := by simp
  map_add' x y := by simpa using e.symm.map_add (x, 0) (y, 0)

/-- The residue label induced by free coordinates and the unique parity factor. -/
def residueMap {r : ℕ} (e : H ≃+ (Fin r → ℤ) × ZMod 2) : H →+ Residue r where
  toFun h := ((e h).2, fun i => ((e h).1 i : ZMod (GroupSize.modulus r)))
  map_zero' := by ext i <;> simp
  map_add' x y := by
    ext i <;> simp

/-- Equality of distinguished residues gives exact integral divisibility of
every free coordinate, including the empty free summand. -/
theorem residue_fiber {r : ℕ} (e : H ≃+ (Fin r → ℤ) × ZMod 2)
    (κ : H) (hκ : e κ = (0, 1)) (h : H) :
    residueMap e h = residueMap e κ ↔
      ∃ z : Fin r → ℤ, h = κ + GroupSize.modulus r • freeLift e z := by
  constructor
  · intro heq
    have hp : (e h).2 = 1 := by
      have := congrArg Prod.fst heq
      simpa [residueMap, hκ] using this
    have hd (i : Fin r) : (GroupSize.modulus r : ℤ) ∣ (e h).1 i := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      have := congrFun (congrArg Prod.snd heq) i
      simpa [residueMap, hκ] using this
    choose z hz using hd
    refine ⟨z, e.injective ?_⟩
    rw [map_add, map_nsmul, hκ]
    ext i
    · simpa [freeLift, nsmul_eq_mul] using hz i
    · simpa [freeLift] using hp
  · rintro ⟨z, rfl⟩
    ext i
    · simp [residueMap, hκ, freeLift]
    · simp [residueMap, hκ, freeLift, nsmul_eq_mul]

/-- Half of the coarse modulus is large enough for the lattice Jensen theorem. -/
theorem half_modulus_bound (r : ℕ) :
    2 * r ≤ GroupSize.modulus r / 2 ∧
      2 * (GroupSize.modulus r / 2) = GroupSize.modulus r := by
  unfold GroupSize.modulus
  split_ifs <;> omega

/-- Midpoint convexity of class minima implies coarse Jensen at the origin
along the free summand with the exact modulus used by the finite residue group. -/
theorem class_coarse_jensen {r : ℕ} (e : H ≃+ (Fin r → ℤ) × ZMod 2)
    (κ : H) (F : H → ℝ)
    (hmid : ∀ h₀ z d, 2 * F (h₀ + 2 • z) ≤
      F (h₀ + 2 • (z - d)) + F (h₀ + 2 • (z + d))) :
    ExactValue.CoarseJensenAtZero (fun z => F (κ + GroupSize.modulus r • freeLift e z)) := by
  let f : (Fin r → ℤ) → ℝ := fun z => F (κ + 2 • freeLift e z)
  have hf : CoarseJensen.MidpointConvex f := by
    intro z d
    simpa only [f, map_sub, map_add] using hmid κ (freeLift e z) (freeLift e d)
  have hj := CoreBridge.coarse_jensen_at_zero r (GroupSize.modulus r / 2)
    (half_modulus_bound r).1 f hf
  have heq (z : Fin r → ℤ) :
      f ((GroupSize.modulus r / 2) • z) =
        F (κ + GroupSize.modulus r • freeLift e z) := by
    simp only [f, map_nsmul, ← mul_nsmul]
    rw [Nat.mul_comm (GroupSize.modulus r / 2) 2, (half_modulus_bound r).2]
  simpa only [heq] using hj

end MWIS.ResidueJensen

end
