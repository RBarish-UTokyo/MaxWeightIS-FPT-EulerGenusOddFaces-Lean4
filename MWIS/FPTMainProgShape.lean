module

public import MWIS.GroupSize
public import Mathlib.Data.Nat.Size
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-!
# Fixed-parameter bound shapes

`PB K D Y = 2^(K·D) · Y^K`. With `D = d · size d + 1` this is the shape of
`GenericAccounting.shape`. The lemmas below close such bounds under sums, products
and powers, and bound the residue-group size `GroupSize.residueCount r` for `r ≤ d`
by `2^(4D)`.
-/

@[expose] public section

namespace MWIS.FPTMainProg

/-- The bound shape `2^(K·D) · Y^K`. -/
def PB (K D Y : ℕ) : ℕ := 2 ^ (K * D) * Y ^ K

variable {D Y : ℕ}

theorem PB_mono (hY : 1 ≤ Y) {K K' : ℕ} (h : K ≤ K') : PB K D Y ≤ PB K' D Y :=
  Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ h))
    (Nat.pow_le_pow_right hY h)

theorem PB_mul (K L : ℕ) : PB K D Y * PB L D Y = PB (K + L) D Y := by
  unfold PB
  rw [add_mul, pow_add, pow_add]
  ring

theorem PB_pow (K a : ℕ) : PB K D Y ^ a = PB (K * a) D Y := by
  unfold PB
  rw [mul_pow, ← pow_mul, ← pow_mul]
  congr 2
  ring

theorem PB_one_le (hY : 1 ≤ Y) (K : ℕ) : 1 ≤ PB K D Y :=
  Nat.mul_le_mul (Nat.one_le_two_pow) (Nat.one_le_pow _ _ hY)

theorem const_le_PB (hD : 1 ≤ D) (hY : 1 ≤ Y) (k : ℕ) : k ≤ PB k D Y := by
  unfold PB
  calc k ≤ 2 ^ k := Nat.lt_two_pow_self.le
    _ ≤ 2 ^ (k * D) := Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_right _ hD)
    _ ≤ 2 ^ (k * D) * Y ^ k := Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ hY)

theorem Y_le_PB : Y ≤ PB 1 D Y := by
  unfold PB
  rw [pow_one]
  exact Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)

theorem twoPow_le_PB (hY : 1 ≤ Y) : 2 ^ D ≤ PB 1 D Y := by
  unfold PB
  rw [one_mul, pow_one]
  exact Nat.le_mul_of_pos_right _ hY

theorem PB_le_mul {x y K L : ℕ} (hx : x ≤ PB K D Y) (hy : y ≤ PB L D Y) :
    x * y ≤ PB (K + L) D Y := by
  rw [← PB_mul]
  exact Nat.mul_le_mul hx hy

theorem PB_le_pow {x K : ℕ} (hx : x ≤ PB K D Y) (a : ℕ) : x ^ a ≤ PB (K * a) D Y := by
  rw [← PB_pow]
  exact Nat.pow_le_pow_left hx a

/-- `k` terms below one shape stay below a shape. -/
theorem PB_le_of_mul (hD : 1 ≤ D) (hY : 1 ≤ Y) {x k K : ℕ} (hx : x ≤ k * PB K D Y) :
    x ≤ PB (k + K) D Y :=
  hx.trans (PB_le_mul (const_le_PB hD hY k) le_rfl)

/-- The residue-group size is at most `2^(4D)` for `r ≤ d` and `D = d · size d + 1`. -/
theorem residueCount_le (r d : ℕ) (hrd : r ≤ d) :
    GroupSize.residueCount r ≤ 2 ^ (4 * (d * Nat.size d + 1)) := by
  refine (GroupSize.residueCount_le_exponential r d hrd).trans
    (Nat.pow_le_pow_right (by norm_num) ?_)
  have hlog : Nat.log2 (d + 1) ≤ Nat.size d := by
    have h1 : d + 1 ≤ 2 ^ Nat.size d := Nat.lt_size_self d
    have h2 : Nat.log2 (d + 1) < Nat.size d + 1 :=
      (Nat.log2_lt (by omega)).mpr (by rw [pow_succ]; omega)
    omega
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · have hs : 1 ≤ Nat.size d := Nat.size_pos.mpr hd
    have h3 : d * (3 + Nat.log2 (d + 1)) ≤ 3 * d + d * Nat.size d := by
      rw [Nat.mul_add]; exact Nat.add_le_add (by omega) (Nat.mul_le_mul_left _ hlog)
    have h4 : 3 * d ≤ 3 * (d * Nat.size d) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hs)
    omega

end MWIS.FPTMainProg

end
