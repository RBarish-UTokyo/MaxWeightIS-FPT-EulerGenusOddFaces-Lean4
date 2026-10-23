module

public import MWIS.ClassMinimum
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Data.Rat.BigOperators

/-!
# Real extensions of integral coordinates

Finite integral coordinate maps extend by their integer coefficients to real
linear maps. The extension agrees with the original map on every integral
vector. The same construction supplies the rational cost functional.

Prepared 2026-10-23.
-/

@[expose] public section

namespace MWIS.RealCoordinates

open scoped BigOperators

/-- Coordinatewise inclusion of integral edge vectors into real edge space. -/
def castVector {E : Type*} (y : E → ℤ) : E → ℝ := fun e => y e

/-- An additive map on a finite integral lattice is the weighted sum of its
values at the coordinate unit vectors. This also applies to torsion labels. -/
theorem label_expansion {E H : Type*} [Fintype E] [DecidableEq E] [AddCommGroup H]
    (Q : (E → ℤ) →+ H) (y : E → ℤ) :
    Q y = ∑ e, y e • Q (Pi.single e 1) := by
  have hy : y = ∑ e, y e • Pi.single e (1 : ℤ) := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply, mul_ite]
  calc
    Q y = Q (∑ e, y e • Pi.single e (1 : ℤ)) := congrArg Q hy
    _ = _ := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro e _
      exact map_zsmul Q _ _

/-- The real linear extension of a finite integral coordinate map. -/
def extension {E D : Type*} [Fintype E] [DecidableEq E]
    (W : (E → ℤ) →+ (D → ℤ)) : (E → ℝ) →ₗ[ℝ] (D → ℝ) where
  toFun y d := ∑ e, y e * (W (Pi.single e 1) d : ℝ)
  map_add' x y := by ext d; simp [add_mul, Finset.sum_add_distrib]
  map_smul' a y := by ext d; simp [Finset.mul_sum, mul_assoc]

/-- The extension agrees with the integral coordinate map after scalar inclusion. -/
theorem extension_cast {E D : Type*} [Fintype E] [DecidableEq E]
    (W : (E → ℤ) →+ (D → ℤ)) (y : E → ℤ) :
    extension W (castVector y) = castVector (W y) := by
  have h := label_expansion W y
  ext d
  have hd := congrFun h d
  simp only [Finset.sum_apply, zsmul_eq_mul] at hd
  change (∑ e, (y e : ℝ) * (W (Pi.single e 1) d : ℝ)) = (W y d : ℝ)
  exact_mod_cast hd.symm

/-- The real linear objective with prescribed rational edge costs. -/
def cost {E : Type*} [Fintype E] (c : E → ℚ) : (E → ℝ) →ₗ[ℝ] ℝ where
  toFun y := ∑ e, (c e : ℝ) * y e
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' a y := by simp [Finset.mul_sum, mul_left_comm]

theorem cost_cast {E : Type*} [Fintype E] (c : E → ℚ) (y : E → ℤ) :
    cost c (castVector y) = ClassMinimum.realCost c y := by
  simp only [cost, LinearMap.coe_mk, AddHom.coe_mk, castVector,
    ClassMinimum.realCost, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    ClassMinimum.rationalCost]
  simp

end MWIS.RealCoordinates

end
