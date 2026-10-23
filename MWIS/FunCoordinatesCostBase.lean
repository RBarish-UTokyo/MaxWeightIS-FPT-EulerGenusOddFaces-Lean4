module

public import MWIS.FunCoordinatesTables

/-!
# Polynomial cost bounds for the coordinate programs: basic forms

All bounds of the coordinate programs are stated as `K * N ^ d` for a size parameter `N`
that bounds every list length, and `4 N` bounds every integer that occurs (so its binary
length is at most `N` once `N ≥ 5`). This file restates the costs of the list primitives
in this form.
-/

@[expose] public section

namespace MWIS.FunCoordinates

open MWIS.Fun MWIS.FunLP

/-! ## Arithmetic -/

theorem four_mul_lt_two_pow {N : ℕ} (hN : 5 ≤ N) : 4 * N < 2 ^ N := by
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ k _ ih => rw [pow_succ]; omega

theorem bits_small {N : ℕ} (hN : 5 ≤ N) {x : ℤ} (hx : |x| ≤ 4 * N) : bits x ≤ N := by
  unfold bits
  apply Nat.size_le.mpr
  have h1 : (x.natAbs : ℤ) ≤ 4 * N := by rw [Int.natCast_natAbs]; exact hx
  have h2 : x.natAbs ≤ 4 * N := by exact_mod_cast h1
  exact lt_of_le_of_lt h2 (four_mul_lt_two_pow hN)

theorem bits_nat_small {N k : ℕ} (hN : 5 ≤ N) (hk : k ≤ 4 * N) : bits (k : ℤ) ≤ N :=
  bits_small hN (by rw [Nat.abs_cast]; exact_mod_cast hk)

theorem bits_mono {x y : ℤ} (h : |x| ≤ |y|) : bits x ≤ bits y := by
  unfold bits
  apply Nat.size_le_size
  have : (x.natAbs : ℤ) ≤ y.natAbs := by
    rw [Int.natCast_natAbs, Int.natCast_natAbs]; exact h
  exact_mod_cast this

@[simp] theorem bits_zero' : bits 0 = 0 := by decide
@[simp] theorem bits_one' : bits 1 = 1 := by decide
@[simp] theorem bits_neg_one' : bits (-1) = 1 := by decide
@[simp] theorem bits_two' : bits 2 = 2 := by decide
@[simp] theorem bits_four' : bits 4 = 3 := by decide

theorem pow_mono {N : ℕ} (hN : 1 ≤ N) {i j : ℕ} (h : i ≤ j) : N ^ i ≤ N ^ j :=
  Nat.pow_le_pow_right hN h

/-- The standard loop bound: at most `N + 1` rounds of a polynomial body. -/
theorem loop_bound {N a b K d c e : ℕ} (hN : 1 ≤ N) (ha : a ≤ N) (hb : b ≤ K * N ^ d)
    (hd : 1 ≤ d) : (a + 1) * (b + c * N + e) ≤ 2 * (K + c + e) * N ^ (d + 1) := by
  have h1 : N ≤ N ^ d := by simpa using Nat.pow_le_pow_right hN hd
  have h0 : 1 ≤ N ^ d := Nat.one_le_pow _ _ hN
  have hA : a + 1 ≤ 2 * N := by omega
  have hB : b + c * N + e ≤ (K + c + e) * N ^ d := by nlinarith
  calc (a + 1) * (b + c * N + e) ≤ (2 * N) * ((K + c + e) * N ^ d) := Nat.mul_le_mul hA hB
    _ = 2 * (K + c + e) * N ^ (d + 1) := by ring

theorem lift_pow {N a K i j : ℕ} (hN : 1 ≤ N) (h : a ≤ K * N ^ i) (hij : i ≤ j) :
    a ≤ K * N ^ j :=
  h.trans (Nat.mul_le_mul_left _ (pow_mono hN hij))

theorem const_le_pow {N : ℕ} (hN : 1 ≤ N) (c d : ℕ) : c ≤ c * N ^ d := by
  have := Nat.one_le_pow d N hN
  nlinarith

/-! ## Primitives -/

variable {N : ℕ}

theorem getIntFn_costN (hN : 1 ≤ N) (l : List ℤ) (i : ℤ) (hl : l.length ≤ N) (hi : bits i ≤ N) :
    getIntFn.costAt (l, i) ≤ 74 * N ^ 2 := by
  have h := getIntFn_cost l i N (lt_of_le_of_lt hl Nat.lt_two_pow_self)
  have h2 := loop_bound (c := 2) (e := 34) (K := 1) (d := 1) hN hl (b := bits i)
    (by simpa using hi) le_rfl
  calc _ ≤ _ := h
    _ = (l.length + 1) * (bits i + 2 * N + 34) := by ring
    _ ≤ _ := h2

theorem getBoolFn_costN (hN : 1 ≤ N) (l : List Bool) (i : ℤ) (hl : l.length ≤ N)
    (hi : bits i ≤ N) : getBoolFn.costAt (l, i) ≤ 74 * N ^ 2 := by
  have h := getBoolFn_cost l i N (lt_of_le_of_lt hl Nat.lt_two_pow_self)
  have h2 := loop_bound (c := 2) (e := 34) (K := 1) (d := 1) hN hl (b := bits i)
    (by simpa using hi) le_rfl
  calc _ ≤ _ := h
    _ = (l.length + 1) * (bits i + 2 * N + 34) := by ring
    _ ≤ _ := h2

theorem getListFn_costN (hN : 1 ≤ N) (a : Ty) (l : List (List a.denote)) (i : ℤ)
    (hl : l.length ≤ N) (hi : bits i ≤ N) : (getListFn a).costAt (l, i) ≤ 74 * N ^ 2 := by
  have h := getListFn_cost a l i N (lt_of_le_of_lt hl Nat.lt_two_pow_self)
  have h2 := loop_bound (c := 2) (e := 34) (K := 1) (d := 1) hN hl (b := bits i)
    (by simpa using hi) le_rfl
  calc _ ≤ _ := h
    _ = (l.length + 1) * (bits i + 2 * N + 34) := by ring
    _ ≤ _ := h2

theorem getPairFn_costN (hN : 1 ≤ N) (l : List (ℤ × ℤ)) (i : ℤ) (hl : l.length ≤ N)
    (hi : bits i ≤ N) : getPairFn.costAt (l, i) ≤ 74 * N ^ 2 := by
  have h := getPairFn_cost l i N (lt_of_le_of_lt hl Nat.lt_two_pow_self)
  have h2 := loop_bound (c := 2) (e := 34) (K := 1) (d := 1) hN hl (b := bits i)
    (by simpa using hi) le_rfl
  calc _ ≤ _ := h
    _ = (l.length + 1) * (bits i + 2 * N + 34) := by ring
    _ ≤ _ := h2

theorem mapIdxFn_costN {p a b : Ty} (f : Fn (.prod p (.prod .int a)) b) (q : p.denote)
    (l : List a.denote) {K d : ℕ} (hN : 1 ≤ N) (hd : 1 ≤ d) (hl : l.length ≤ N)
    (hc : ∀ j (hj : j < l.length), f.costAt (q, (j : ℤ), l[j]) ≤ K * N ^ d) :
    (mapIdxFn f).costAt (q, l) ≤ 2 * (K + 41) * N ^ (d + 1) := by
  have h := mapIdxFn_cost f q l N (K * N ^ d) (lt_of_le_of_lt hl Nat.lt_two_pow_self) hc
  have h2 := loop_bound (c := 1) (e := 40) hN hl (le_refl (K * N ^ d)) hd
  calc _ ≤ _ := h
    _ = (l.length + 1) * (K * N ^ d + 1 * N + 40) := by ring
    _ ≤ _ := h2

theorem findIdxFn_costN {p a : Ty} (pred : Fn (.prod p a) .bool) (q : p.denote)
    (l : List a.denote) {K d : ℕ} (hN : 1 ≤ N) (hd : 1 ≤ d) (hl : l.length ≤ N)
    (hc : ∀ x ∈ l, pred.costAt (q, x) ≤ K * N ^ d) :
    (findIdxFn pred).costAt (q, l) ≤ 2 * (K + 42) * N ^ (d + 1) := by
  have h := findIdxFn_cost pred q l N (K * N ^ d) hN (lt_of_le_of_lt hl Nat.lt_two_pow_self) hc
  have h2 := loop_bound (c := 2) (e := 40) hN hl (le_refl (K * N ^ d)) hd
  calc _ ≤ _ := h
    _ = (l.length + 1) * (K * N ^ d + 2 * N + 40) := by ring
    _ ≤ _ := h2

theorem cmapFn_costN {p a b : Ty} (f : Fn (.prod p a) b) (q : p.denote) (l : (Ty.list a).denote)
    {K d : ℕ} (hN : 1 ≤ N) (hd : 1 ≤ d) (hl : l.length ≤ N)
    (hc : ∀ x ∈ l, f.costAt (q, x) ≤ K * N ^ d) :
    (cmapFn f).costAt (q, l) ≤ 2 * (K + 17) * N ^ (d + 1) := by
  have h := cmapFn_cost f q l (K * N ^ d) hc
  have h2 := loop_bound (c := 0) (e := 17) hN hl (le_refl (K * N ^ d)) hd
  calc _ ≤ _ := h
    _ = (l.length + 1) * (K * N ^ d + 0 * N + 17) := by ring
    _ ≤ _ := h2

theorem crange_costN (hN : 1 ≤ N) (k : ℕ) (hk : k ≤ N) (hb : bits (k : ℤ) ≤ N) :
    crange.costAt (k : ℤ) ≤ 68 * N ^ 2 := by
  have h := crange_cost (k : ℤ) (by omega)
  simp only [Int.toNat_natCast] at h
  have h2 := loop_bound (c := 0) (e := 30) (K := 4) (d := 1) hN hk (b := 4 * bits (k : ℤ))
    (by simpa using Nat.mul_le_mul_left 4 hb) le_rfl
  calc _ ≤ _ := h
    _ = (k + 1) * (4 * bits (k : ℤ) + 0 * N + 30) := by ring
    _ ≤ _ := h2

theorem crevFn_costN (hN : 1 ≤ N) (a : Ty) (l : List a.denote) (hl : l.length ≤ N) :
    (crevFn a).costAt l ≤ 9 * N ^ 1 := by
  have := crevFn_cost a l
  simp only [pow_one]
  omega

/-! ## Structural cost rules -/

theorem cost_letE_le {Γ : List Ty} {σ τ : Ty} (x : Expr Γ σ) (body : Expr (σ :: Γ) τ)
    (env : Env Γ) (P : σ.denote → Prop) {A B : ℕ} (hx : x.cost env ≤ A) (hP : P (x.denote env))
    (hb : ∀ v, P v → body.cost (v, env) ≤ B) : (Expr.letE x body).cost env ≤ A + B + 1 := by
  simp only [Expr.cost]
  have := hb _ hP
  omega

theorem cost_ite_le {Γ : List Ty} {τ : Ty} (c : Expr Γ .bool) (t e : Expr Γ τ) (env : Env Γ)
    {A B : ℕ} (hc : c.cost env ≤ A) (ht : c.denote env = true → t.cost env ≤ B)
    (he : c.denote env = false → e.cost env ≤ B) : (Expr.ite c t e).cost env ≤ A + B + 1 := by
  simp only [Expr.cost]
  cases h : c.denote env
  · have := he h; simp only [Bool.false_eq_true, ite_false]; omega
  · have := ht h; simp only [ite_true]; omega

theorem cost_ltZero {Γ : List Ty} (x : Expr Γ .int) (env : Env Γ) {N a : ℕ} (hx : x.cost env ≤ a)
    (hb : bits (x.denote env) ≤ N) : (Expr.cmp .lt x (.int 0)).cost env ≤ a + N + 3 := by
  simp only [Expr.cost, CmpOp.charge, Expr.denote, bits_zero']
  omega

end MWIS.FunCoordinates


end
