module

public import MWIS.AlgorithmEllipsoid
public import MWIS.AlgorithmPrecision
public import MWIS.AlgorithmRational
public import Mathlib.Data.Rat.Floor
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Integer formulas for one rounded ellipsoid update and one separation query

The rounded update of `AlgorithmEllipsoid` stores integer numerators on the grid
`2^{-k}`. Each stored numerator is one Euclidean division of integers computed
from the stored state and the integer cut: with `V = S a`, `Q = aᵀ V` and
`R = ⌊√(Q 2^k)⌋ + 1`, the centre numerator is `c_i + (V_i 2^k) / ((n+1) R)`, and the
shape numerator is the floor of an explicit quotient of two integers, plus the
diagonal padding. The separation test of `AlgorithmSeparation.separate` is the
integer comparison `b_i 2^k < Σ_j A_ij c_j`.
-/

@[expose] public section

namespace MWIS.FunLPMath

open scoped BigOperators
open AlgorithmEllipsoid AlgorithmRounding

/-- Floor division for an arbitrary nonzero divisor. -/
def floorDiv (N D : ℤ) : ℤ := if 0 < D then N / D else (-N) / (-D)

theorem floor_div_eq_floorDiv (N D : ℤ) (hD : D ≠ 0) :
    ⌊((N : ℚ) / (D : ℚ))⌋ = floorDiv N D := by
  unfold floorDiv
  split_ifs with h
  · have hD' : ((D.toNat : ℕ) : ℤ) = D := Int.toNat_of_nonneg h.le
    rw [← hD']
    have := Rat.floor_intCast_div_natCast N D.toNat
    simpa only [Int.cast_natCast] using this
  · have hneg : 0 < -D := by omega
    have hD' : (((-D).toNat : ℕ) : ℤ) = -D := Int.toNat_of_nonneg hneg.le
    have hq : ((N : ℚ) / (D : ℚ)) = ((-N : ℤ) : ℚ) / (((-D).toNat : ℕ) : ℚ) := by
      have : (((-D).toNat : ℕ) : ℚ) = ((-D : ℤ) : ℚ) := by exact_mod_cast hD'
      rw [this]; push_cast; rw [neg_div_neg_eq]
    rw [hq, Rat.floor_intCast_div_natCast, hD']

variable {n : ℕ}

/-- `V = S a`. -/
def vecV (s : State n) (a : Fin n → ℤ) (i : Fin n) : ℤ := ∑ j, s.shapeNumerator i j * a j

/-- `Q = aᵀ S a`. -/
def quadQ (s : State n) (a : Fin n → ℤ) : ℤ := ∑ i, a i * vecV s a i

/-- `R = ⌊√(Q 2^k)⌋ + 1`. -/
def rootR (k : ℕ) (s : State n) (a : Fin n → ℤ) : ℕ :=
  Nat.sqrt (quadQ s a * 2 ^ k).toNat + 1

/-- The constant `E = 32 (n+1)^2` of the inflation `1 / E`. -/
def inflE (n : ℕ) : ℤ := 32 * ((n : ℤ) + 1) ^ 2

/-- The nonzero normal square used in the quotient (`1` when `Q = 0`). -/
def safeQ (s : State n) (a : Fin n → ℤ) : ℤ := if quadQ s a = 0 then 1 else quadQ s a

/-- The indicator `Q ≠ 0`. -/
def flagQ (s : State n) (a : Fin n → ℤ) : ℤ := if quadQ s a = 0 then 0 else 1

/-- Numerator of the scaled enlarged shape entry. -/
def shapeNum (s : State n) (a : Fin n → ℤ) (i j : Fin n) : ℤ :=
  (inflE n + 1) ^ 2 * (n : ℤ) ^ 2 *
    (((n : ℤ) + 1) * safeQ s a * s.shapeNumerator i j - 2 * vecV s a i * vecV s a j * flagQ s a)

/-- Denominator of the scaled enlarged shape entry. -/
def shapeDen (s : State n) (a : Fin n → ℤ) : ℤ :=
  inflE n ^ 2 * ((n : ℤ) ^ 2 - 1) * ((n : ℤ) + 1) * safeQ s a

theorem direction_eq (k : ℕ) (s : State n) (a : Fin n → ℤ) (i : Fin n) :
    direction (shape k s) a i = (vecV s a i : ℚ) / 2 ^ k := by
  simp only [direction, shape, dyadic, vecV, Int.cast_sum, Int.cast_mul, Finset.sum_div]
  refine Finset.sum_congr rfl (fun j _ => by ring)

theorem normalSquare_eq (k : ℕ) (s : State n) (a : Fin n → ℤ) :
    normalSquare (shape k s) a = (quadQ s a : ℚ) / 2 ^ k := by
  simp only [normalSquare, direction_eq, quadQ, Int.cast_sum, Int.cast_mul, Finset.sum_div]
  refine Finset.sum_congr rfl (fun j _ => by ring)

theorem sqrt_numerator_eq (k : ℕ) (s : State n) (a : Fin n → ℤ) :
    AlgorithmSqrt.numerator k (normalSquare (shape k s) a) = Nat.sqrt (quadQ s a * 2 ^ k).toNat := by
  unfold AlgorithmSqrt.numerator
  congr 1
  rw [normalSquare_eq]
  have h : (quadQ s a : ℚ) / 2 ^ k * ((2 : ℚ) ^ k) ^ 2 = ((quadQ s a * 2 ^ k : ℤ) : ℚ) := by
    push_cast; field_simp
  rw [h, ← Int.floor_toNat, Int.floor_intCast]

theorem upper_eq (k : ℕ) (s : State n) (a : Fin n → ℤ) :
    AlgorithmSqrt.upper k (normalSquare (shape k s) a) = (rootR k s a : ℚ) / 2 ^ k := by
  unfold AlgorithmSqrt.upper rootR
  rw [sqrt_numerator_eq]

/-- The stored centre numerator of the rounded update. -/
theorem update_centerNumerator (k : ℕ) (ε : ℚ) (s : State n) (a : Fin n → ℤ) (i : Fin n) :
    (update k ε s a).centerNumerator i =
      s.centerNumerator i + (vecV s a i * 2 ^ k) / (((n : ℤ) + 1) * (rootR k s a : ℤ)) := by
  simp only [update, roundNumerator, approximateCenter, center, dyadic]
  rw [direction_eq, upper_eq]
  have hR : (0 : ℚ) < rootR k s a := by unfold rootR; positivity
  have hx : ((s.centerNumerator i : ℚ) / 2 ^ k + (vecV s a i : ℚ) / 2 ^ k /
      (((n : ℚ) + 1) * ((rootR k s a : ℚ) / 2 ^ k))) * 2 ^ k =
      (s.centerNumerator i : ℚ) + ((vecV s a i * 2 ^ k : ℤ) : ℚ) /
        ((((n + 1) * rootR k s a : ℕ) : ℤ) : ℚ) := by
    push_cast
    field_simp
  rw [hx, Int.floor_intCast_add]
  congr 1
  rw [Int.cast_natCast, Rat.floor_intCast_div_natCast]
  push_cast
  ring_nf

/-- The scaled enlarged shape entry is the quotient `shapeNum / shapeDen`. -/
theorem enlarged_scaled (hn : 2 ≤ n) (k : ℕ) (s : State n) (a : Fin n → ℤ) (i j : Fin n) :
    enlargedShape (AlgorithmPrecision.inflation n) (shape k s) a i j * 2 ^ k =
      (shapeNum s a i j : ℚ) / (shapeDen s a : ℚ) := by
  have hn' : (2 : ℚ) ≤ n := by exact_mod_cast hn
  have hn1 : (n : ℚ) ^ 2 - 1 ≠ 0 := by nlinarith
  have hn2 : (n : ℚ) + 1 ≠ 0 := by positivity
  have hE : (32 * ((n : ℚ) + 1) ^ 2) ≠ 0 := by positivity
  have hk : (2 : ℚ) ^ k ≠ 0 := by positivity
  simp only [enlargedShape, rawShape, AlgorithmPrecision.inflation, shape, dyadic,
    shapeNum, shapeDen, inflE, safeQ, flagQ]
  rw [direction_eq, direction_eq, normalSquare_eq]
  by_cases hq : quadQ s a = 0
  · simp only [hq, Int.cast_zero, zero_div, inv_zero, mul_zero, zero_mul, sub_zero, ite_true]
    push_cast
    field_simp
  · have hq' : (quadQ s a : ℚ) ≠ 0 := by exact_mod_cast hq
    simp only [hq, ite_false]
    push_cast
    field_simp

theorem shapeDen_ne_zero (hn : 2 ≤ n) (s : State n) (a : Fin n → ℤ) : shapeDen s a ≠ 0 := by
  have hn' : (2 : ℤ) ≤ n := by exact_mod_cast hn
  unfold shapeDen inflE safeQ
  have h1 : (n : ℤ) ^ 2 - 1 ≠ 0 := by nlinarith
  have h2 : (n : ℤ) + 1 ≠ 0 := by omega
  have h3 : (32 * ((n : ℤ) + 1) ^ 2) ≠ 0 := by positivity
  split_ifs with hq
  · simp [h1, h2, h3]
  · exact mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ h3) h1) h2) hq

/-- The stored shape numerator of the rounded update. -/
theorem update_shapeNumerator (hn : 2 ≤ n) (k : ℕ) (s : State n) (a : Fin n → ℤ)
    (i j : Fin n) :
    (update k (AlgorithmPrecision.inflation n) s a).shapeNumerator i j =
      FunLPMath.floorDiv (shapeNum s a i j) (shapeDen s a) + if i = j then (n : ℤ) else 0 := by
  simp only [update, AlgorithmMatrixRounding.paddedNumerator, roundNumerator, Fintype.card_fin]
  rw [enlarged_scaled hn, floor_div_eq_floorDiv _ _ (shapeDen_ne_zero hn s a)]

/-! ## Separation -/

/-- The separation test in integers on the stored centre numerators. -/
theorem separate_test_iff {m : ℕ} (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) (k : ℕ)
    (c : Fin n → ℤ) (i : Fin m) :
    b i * (AlgorithmRational.denominatorProduct (fun j => dyadic k (c j)) : ℤ) <
        AlgorithmSeparation.integerDot (A i)
          (AlgorithmRational.integerize (fun j => dyadic k (c j))) ↔
      b i * 2 ^ k < ∑ j, A i j * c j := by
  set x : Fin n → ℚ := fun j => dyadic k (c j)
  have hD : (0 : ℚ) < AlgorithmRational.denominatorProduct x := by
    exact_mod_cast AlgorithmRational.denominatorProduct_pos x
  have hdot : ((AlgorithmSeparation.integerDot (A i) (AlgorithmRational.integerize x) : ℤ) : ℚ) =
      (AlgorithmRational.denominatorProduct x : ℚ) * ((∑ j, A i j * c j : ℤ) : ℚ) / 2 ^ k := by
    simp only [AlgorithmSeparation.integerDot, Int.cast_sum, Int.cast_mul,
      AlgorithmRational.integerize_eq, x, dyadic, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl (fun j _ => by ring)
  rw [← Int.cast_lt (R := ℚ), hdot, ← Int.cast_lt (R := ℚ)]
  push_cast
  rw [mul_div_assoc, mul_comm (b i : ℚ), mul_lt_mul_iff_right₀ hD, lt_div_iff₀ (by positivity)]

end MWIS.FunLPMath

end
