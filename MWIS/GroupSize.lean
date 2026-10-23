module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.SplitIfs

/-!
# Explicit bounds for the finite residue group

For rank `r`, the modulus is `2` when `r = 0` and `4*r` otherwise.
The residue group has size `2 * modulus r ^ r`.  A rank bound `r ≤ p`
gives the explicit estimate `2 ^ (1 + p * (3 + log2 (p+1)))`.
This is the numerical group-size estimate used in the parameter bound.

Prepared 2026-10-23.
-/

public section

namespace MWIS.GroupSize

/-- The modulus used for the free coordinates, including the rank-zero case. -/
@[expose] def modulus (r : ℕ) : ℕ := if r = 0 then 2 else 4 * r

/-- The cardinality formula for one parity coordinate and `r` residue coordinates. -/
@[expose] def residueCount (r : ℕ) : ℕ := 2 * modulus r ^ r

theorem modulus_pos (r : ℕ) : 0 < modulus r := by
  unfold modulus
  split_ifs with hr <;> omega

instance modulus_neZero (r : ℕ) : NeZero (modulus r) :=
  ⟨Nat.ne_of_gt (modulus_pos r)⟩

/-- The parity coordinate and the free-coordinate residues have the stated size. -/
theorem residue_group_card (r : ℕ) :
    Fintype.card (ZMod 2 × (Fin r → ZMod (modulus r))) = residueCount r := by
  simp [residueCount]

theorem modulus_le (r p : ℕ) (hrp : r ≤ p) : modulus r ≤ 4 * (p + 1) := by
  unfold modulus
  split_ifs with hr <;> omega

theorem residueCount_zero : residueCount 0 = 2 := by
  simp [residueCount]

/-- The polynomial-to-the-parameter form of the finite-group bound. -/
theorem residueCount_le_power (r p : ℕ) (hrp : r ≤ p) :
    residueCount r ≤ 2 * (4 * (p + 1)) ^ p := by
  unfold residueCount
  apply Nat.mul_le_mul_left
  exact (Nat.pow_le_pow_left (modulus_le r p hrp) r).trans
    (Nat.pow_le_pow_right (by omega) hrp)

/-- A natural-number bound with an explicit base-two logarithm. -/
theorem residueCount_le_exponential (r p : ℕ) (hrp : r ≤ p) :
    residueCount r ≤ 2 ^ (1 + p * (3 + Nat.log2 (p + 1))) := by
  have hlog : p + 1 ≤ 2 ^ (Nat.log2 (p + 1) + 1) :=
    Nat.le_of_lt Nat.lt_log2_self
  have hbase : 4 * (p + 1) ≤ 2 ^ (3 + Nat.log2 (p + 1)) := by
    calc
      4 * (p + 1) ≤ 4 * 2 ^ (Nat.log2 (p + 1) + 1) :=
        Nat.mul_le_mul_left 4 hlog
      _ = 2 ^ (3 + Nat.log2 (p + 1)) := by
        rw [show 3 + Nat.log2 (p + 1) = 2 + (Nat.log2 (p + 1) + 1) by omega,
          Nat.pow_add 2 2 (Nat.log2 (p + 1) + 1)]
  calc
    residueCount r ≤ 2 * (4 * (p + 1)) ^ p := residueCount_le_power r p hrp
    _ ≤ 2 * (2 ^ (3 + Nat.log2 (p + 1))) ^ p :=
      Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hbase p)
    _ = 2 ^ (1 + p * (3 + Nat.log2 (p + 1))) := by
      rw [← Nat.pow_mul, Nat.mul_comm (3 + Nat.log2 (p + 1)) p, Nat.pow_add]

end MWIS.GroupSize
