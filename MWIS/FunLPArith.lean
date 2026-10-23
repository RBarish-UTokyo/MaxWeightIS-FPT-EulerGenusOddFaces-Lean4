module

public import MWIS.FunLPList
public import MWIS.FunLPMath
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Data.Nat.Factorial.Basic

/-!
# Closed `Fun` functions for powers, factorials, square roots and floor division

Integer square roots use binary search over the bits below the binary length
of the argument, so their cost is polynomial in that length.
-/

@[expose] public section

namespace MWIS.FunLP

open MWIS.Fun

/-! ## Powers of two -/

/-- `2 ^ e` for `e ≥ 0` (and `1` for negative `e`). -/
def pow2Fn : Fn .int .int := .iter v0 (.int 1) (.arith .mul v0 (.int 2))

theorem iterate_double (N : ℕ) (s : ℤ) : (fun x : ℤ => x * 2)^[N] s = s * 2 ^ N := by
  induction N generalizing s with
  | zero => simp
  | succ N ih => rw [Function.iterate_succ_apply, ih, pow_succ]; ring

@[simp] theorem pow2Fn_apply (e : ℤ) : pow2Fn.apply e = 2 ^ e.toNat := by
  rw [Fn.apply]
  simp [pow2Fn, Expr.denote, Var.get, IntOp.eval, iterate_double]

theorem pow2Fn_cost (e : ℤ) : pow2Fn.costAt e ≤ (e.toNat + 1) * (4 * e.toNat + bits e + 16) := by
  unfold Fn.costAt pow2Fn
  have h := cost_iter_le_prefix (Γ := [.int]) v0 (.int 1) (.arith .mul v0 (.int 2)) (e, ())
    (3 * e.toNat + 12) (by
      intro j hj
      simp only [Expr.cost, Var.index, Expr.denote, Var.get, IntOp.charge]
      have hi : (fun st => IntOp.eval .mul st 2)^[j] (1 : ℤ) = 2 ^ j := by
        simpa [IntOp.eval] using iterate_double j 1
      simp only [Expr.denote, Var.get] at hj
      rw [hi, bits_pow_two]
      have : bits (2 : ℤ) = 2 := by decide
      rw [this]
      omega)
  simp only [Expr.cost, Var.index, Expr.denote, Var.get] at h ⊢
  nlinarith

/-! ## General powers -/

/-- `x ^ e` for `e ≥ 0`. -/
def powFn : Fn (.prod .int .int) .int := .iter (.snd v0) (.int 1) (.arith .mul v0 (.fst v1))

theorem iterate_mul (x : ℤ) (N : ℕ) (s : ℤ) : (fun t : ℤ => t * x)^[N] s = s * x ^ N := by
  induction N generalizing s with
  | zero => simp
  | succ N ih => rw [Function.iterate_succ_apply, ih, pow_succ]; ring

theorem powFn_apply_mk (x e : Ty.int.denote) : powFn.apply (x, e) = x ^ e.toNat := by
  rw [Fn.apply]
  simp [powFn, Expr.denote, Var.get, IntOp.eval, iterate_mul]

@[simp] theorem powFn_apply (p : (Ty.prod .int .int).denote) :
    powFn.apply p = p.1 ^ p.2.toNat :=
  powFn_apply_mk p.1 p.2

theorem powFn_cost (x e : Ty.int.denote) :
    powFn.costAt (x, e) ≤ (e.toNat + 1) * ((e.toNat * bits x + 2) * (bits x + 1) + bits e + 12) := by
  unfold Fn.costAt powFn
  have h := cost_iter_le_prefix (Γ := [.prod .int .int]) (.snd v0) (.int 1) (.arith .mul v0 (.fst v1))
    ((x, e), ()) ((e.toNat * bits x + 2) * (bits x + 1) + 10) (by
      intro j hj
      simp only [Expr.cost, Var.index, Expr.denote, Var.get, IntOp.charge]
      have hi : (fun st => IntOp.eval .mul st x)^[j] (1 : ℤ) = x ^ j := by
        simpa [IntOp.eval] using iterate_mul x j 1
      simp only [Expr.denote, Var.get] at hj
      rw [hi]
      have hb := bits_pow_le x j
      have : j * bits x ≤ e.toNat * bits x := Nat.mul_le_mul_right _ hj.le
      have : (bits (x ^ j) + 1) * (bits x + 1) ≤ (e.toNat * bits x + 2) * (bits x + 1) :=
        Nat.mul_le_mul_right _ (by omega)
      omega)
  simp only [Expr.cost, Var.index, Expr.denote, Var.get] at h ⊢
  have key : (e.toNat + 1) * ((e.toNat * bits x + 2) * (bits x + 1) + bits e + 12) =
      e.toNat * ((e.toNat * bits x + 2) * (bits x + 1) + 10 + bits e + 1) + e.toNat +
        ((e.toNat * bits x + 2) * (bits x + 1) + bits e + 12) := by ring
  omega

/-! ## Factorials -/

/-- The state step of the factorial loop: `(j!, j + 1) ↦ ((j+1)!, j + 2)`. -/
def factStep : Expr [.prod .int .int, .int] (.prod .int .int) :=
  .pair (.arith .mul (.fst v0) (.snd v0)) (.arith .add (.snd v0) (.int 1))

/-- `e !` for `e ≥ 0`. -/
def factFn : Fn .int .int := .fst (.iter v0 (.pair (.int 1) (.int 1)) factStep)

theorem iterate_fact (N : ℕ) :
    (fun s : ℤ × ℤ => (s.1 * s.2, s.2 + 1))^[N] (1, 1) = (((N.factorial : ℕ) : ℤ), (N : ℤ) + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Function.iterate_succ_apply', ih, Nat.factorial_succ]
    push_cast; ext <;> simp <;> ring

@[simp] theorem factFn_apply (e : ℤ) : factFn.apply e = (e.toNat.factorial : ℤ) := by
  rw [Fn.apply]
  have := iterate_fact e.toNat
  simp only [factFn, factStep, Expr.denote, Var.get, IntOp.eval]
  rw [this]

theorem bits_factorial_le (N : ℕ) : bits (N.factorial : ℤ) ≤ N * N + 1 := by
  rw [bits_natCast, Nat.size_le]
  calc N.factorial ≤ N ^ N := Nat.factorial_le_pow N
    _ ≤ (2 ^ N) ^ N := Nat.pow_le_pow_left Nat.lt_two_pow_self.le N
    _ = 2 ^ (N * N) := by rw [← pow_mul]
    _ < 2 ^ (N * N + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)

theorem factFn_cost (e : ℤ) : factFn.costAt e ≤ (e.toNat + 1) ^ 4 * (bits e + 30) := by
  unfold Fn.costAt factFn
  have h := cost_iter_le_prefix (Γ := [.int]) v0 (.pair (.int 1) (.int 1)) factStep (e, ())
    ((e.toNat * e.toNat + 2) * (e.toNat + 2) + 2 * e.toNat + 20) (by
      intro j hj
      simp only [Expr.denote, Var.get] at hj
      have hi : (fun st => factStep.denote (st, e, ()))^[j] (1, 1) =
          ((((j.factorial : ℕ) : ℤ), (j : ℤ) + 1) : ℤ × ℤ) := by
        have := iterate_fact j
        simpa [factStep, Expr.denote, Var.get, IntOp.eval] using this
      simp only [Expr.denote, Var.get]
      rw [hi]
      simp only [factStep, Expr.cost, Var.index, Expr.denote, Var.get, IntOp.charge]
      have hf := bits_factorial_le j
      have hj1 : bits ((j : ℤ) + 1) ≤ j + 1 := by
        have := bits_le_self_natAbs ((j : ℤ) + 1); omega
      have : bits (1 : ℤ) = 1 := by decide
      have h1 : (bits (j.factorial : ℤ) + 1) * (bits ((j : ℤ) + 1) + 1) ≤
          (e.toNat * e.toNat + 2) * (e.toNat + 2) := Nat.mul_le_mul (by nlinarith) (by omega)
      omega)
  simp only [Expr.cost, Var.index, Expr.denote, Var.get] at h ⊢
  have key : (e.toNat + 1) ^ 4 * (bits e + 30) ≥
      e.toNat * ((e.toNat * e.toNat + 2) * (e.toNat + 2) + 2 * e.toNat + 20 + bits e + 1) + 7 := by
    nlinarith [Nat.zero_le (e.toNat * bits e), Nat.zero_le (e.toNat * e.toNat * bits e)]
  omega

/-! ## Integer square roots -/

/-- One round of the binary-search square root: `(r, p) ↦ (r + p or r, p / 2)`. -/
def sqrtStep : Expr [.prod .int .int, .int, .int, .int] (.prod .int .int) :=
  .pair (.ite (.cmp .le (.arith .mul (.arith .add (.fst v0) (.snd v0))
      (.arith .add (.fst v0) (.snd v0))) v2) (.arith .add (.fst v0) (.snd v0)) (.fst v0))
    (.arith .div (.snd v0) (.int 2))

/-- `⌊√(max x 0)⌋`. -/
def sqrtFn : Fn .int .int :=
  .letE (.ite (.cmp .lt v0 (.int 0)) (.int 0) v0)
    (.letE (.arith .div (.size v0) (.int 2))
      (.fst (.iter (.arith .add v0 (.int 1)) (.pair (.int 0) (call pow2Fn v0)) sqrtStep)))

/-- The integer square root used by the solver. -/
def isqrt (x : ℤ) : ℤ := (Nat.sqrt x.toNat : ℤ)

/-- The square-root round on values. -/
def sqrtRound (X : ℤ) (s : ℤ × ℤ) : ℤ × ℤ :=
  (if (s.1 + s.2) * (s.1 + s.2) ≤ X then s.1 + s.2 else s.1, s.2 / 2)

theorem sqrtRound_spec (X : ℤ) (hX : 0 ≤ X) : ∀ (i : ℕ) (r : ℤ), 0 ≤ r → r * r ≤ X →
    X < (r + 2 * 2 ^ i) * (r + 2 * 2 ^ i) → ((sqrtRound X)^[i + 1] (r, 2 ^ i)).1 = isqrt X := by
  intro i
  induction i with
  | zero =>
    intro r hr h1 h2
    simp only [zero_add, Function.iterate_one, sqrtRound, pow_zero, mul_one]
    unfold isqrt
    have hX' : ((X.toNat : ℕ) : ℤ) = X := Int.toNat_of_nonneg hX
    split_ifs with h
    · have e : (r + 1).toNat = Nat.sqrt X.toNat := by
        apply Nat.eq_sqrt.mpr
        constructor <;> zify <;> rw [Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ r + 1), hX'] <;>
          nlinarith
      rw [← e, Int.toNat_of_nonneg (by omega)]
    · have e : r.toNat = Nat.sqrt X.toNat := by
        apply Nat.eq_sqrt.mpr
        constructor <;> zify <;> rw [Int.toNat_of_nonneg hr, hX'] <;> nlinarith
      rw [← e, Int.toNat_of_nonneg hr]
  | succ i ih =>
    intro r hr h1 h2
    rw [Function.iterate_succ_apply]
    have hp : (2 : ℤ) ^ (i + 1) / 2 = 2 ^ i := by rw [pow_succ]; simp
    simp only [sqrtRound, hp]
    have hpos : (0 : ℤ) < 2 ^ i := by positivity
    have ht : (2 : ℤ) ^ (i + 1) = 2 * 2 ^ i := by rw [pow_succ]; ring
    rw [ht] at h2 ⊢
    split_ifs with h
    · apply ih
      · positivity
      · exact h
      · have e : r + 2 * 2 ^ i + 2 * 2 ^ i = r + 2 * (2 * 2 ^ i) := by ring
        rw [e]; exact h2
    · apply ih r hr h1
      exact lt_of_not_ge h

theorem sqrt_initial (X : ℤ) (hX : 0 ≤ X) :
    X < (0 + 2 * 2 ^ (bits X / 2)) * (0 + 2 * 2 ^ (bits X / 2)) := by
  have h := natAbs_lt_of_bits X
  have hX' : (X.natAbs : ℤ) = X := Int.natAbs_of_nonneg hX
  have h2 : (2 : ℤ) ^ bits X ≤ (2 * 2 ^ (bits X / 2)) * (2 * 2 ^ (bits X / 2)) := by
    rw [← pow_succ', ← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have : (X.natAbs : ℤ) < 2 ^ bits X := by exact_mod_cast h
  simp only [zero_add]
  linarith

theorem sqrt_core (X x : ℤ) (hX : 0 ≤ X) :
    ((fun s => sqrtStep.denote (s, (bits X : ℤ) / 2, X, x, ()))^[((bits X : ℤ) / 2 + 1).toNat]
      (0, 2 ^ ((bits X : ℤ) / 2).toNat)).1 = isqrt X := by
  have hh : ((bits X : ℤ) / 2).toNat = bits X / 2 := by omega
  have hc : ((bits X : ℤ) / 2 + 1).toNat = bits X / 2 + 1 := by omega
  rw [hc, hh]
  have hstep : (fun st => sqrtStep.denote (st, (bits X : ℤ) / 2, X, x, ())) = sqrtRound X := by
    funext st
    simp only [sqrtStep, Expr.denote, Var.get, CmpOp.eval, IntOp.eval, sqrtRound]
    by_cases hc : (st.1 + st.2) * (st.1 + st.2) ≤ X <;> simp [hc]
  rw [hstep]
  exact sqrtRound_spec X hX (bits X / 2) 0 le_rfl (by simpa using hX) (sqrt_initial X hX)

@[simp] theorem sqrtFn_apply (x : ℤ) : sqrtFn.apply x = isqrt x := by
  rw [Fn.apply]
  simp only [sqrtFn, Expr.denote, Var.get, denote_call, pow2Fn_apply, CmpOp.eval, IntOp.eval]
  by_cases h : x < 0
  · simp only [h, decide_true, ite_true]
    rw [sqrt_core 0 x le_rfl]
    unfold isqrt; simp [Int.toNat_eq_zero.mpr h.le]
  · simp only [h, decide_false]
    exact sqrt_core x x (by omega)

theorem isqrt_nonneg (x : ℤ) : 0 ≤ isqrt x := by unfold isqrt; positivity

theorem isqrt_le (x : ℤ) (hx : 0 ≤ x) : isqrt x ≤ x := by
  unfold isqrt
  have := Nat.sqrt_le_self x.toNat
  omega

/-- Reachable square-root states: `(r, 2^(h-j))` with `0 ≤ r` and `r² ≤ X`. -/
theorem sqrtRound_reach (X : ℤ) (hX : 0 ≤ X) (h : ℕ) : ∀ j ≤ h, ∃ r : ℤ, 0 ≤ r ∧ r * r ≤ X ∧
    (sqrtRound X)^[j] (0, 2 ^ h) = (r, 2 ^ (h - j)) := by
  intro j
  induction j with
  | zero => intro _; exact ⟨0, le_rfl, by simpa using hX, by simp⟩
  | succ j ih =>
    intro hj
    obtain ⟨r, hr, hrX, he⟩ := ih (by omega)
    rw [Function.iterate_succ_apply', he]
    have hp : (2 : ℤ) ^ (h - j) / 2 = 2 ^ (h - (j + 1)) := by
      have : h - j = (h - (j + 1)) + 1 := by omega
      rw [this, pow_succ]; simp
    simp only [sqrtRound, hp]
    split_ifs with hc
    · exact ⟨r + 2 ^ (h - j), by positivity, hc, rfl⟩
    · exact ⟨r, hr, hrX, rfl⟩

theorem bits_le_of_le {a b : ℤ} (ha : 0 ≤ a) (hab : a ≤ b) : bits a ≤ bits b :=
  bits_mono (by omega)

theorem sqrtStep_denote (a X x : ℤ) :
    (fun st => sqrtStep.denote (st, a, X, x, ())) = sqrtRound X := by
  funext st
  simp only [sqrtStep, Expr.denote, Var.get, CmpOp.eval, IntOp.eval, sqrtRound]
  by_cases hc : (st.1 + st.2) * (st.1 + st.2) ≤ X <;> simp [hc]

theorem sqrtStep_cost (a X x r : ℤ) (h j : ℕ) (hX : 0 ≤ X) (hr : 0 ≤ r) (hrX : r * r ≤ X)
    (hh : h ≤ bits X) :
    sqrtStep.cost ((r, 2 ^ (h - j)), a, X, x, ()) ≤ 3 * (bits X + 6) ^ 2 := by
  have hrX' : r ≤ X := by nlinarith
  have hbr : bits r ≤ bits X := bits_le_of_le hr hrX'
  have hbp : bits ((2 : ℤ) ^ (h - j)) ≤ bits X + 1 := by rw [bits_pow_two]; omega
  have hb2 : bits (2 : ℤ) = 2 := by decide
  have hs := bits_add_le r (2 ^ (h - j))
  have hm := bits_mul_le (r + 2 ^ (h - j)) (r + 2 ^ (h - j))
  have hsum : bits (r + 2 ^ (h - j)) ≤ bits X + 2 := by
    have := max_le (le_trans hbr (Nat.le_succ _)) hbp
    omega
  have hsq : (bits (r + 2 ^ (h - j)) + 1) * (bits (r + 2 ^ (h - j)) + 1) ≤ (bits X + 3) ^ 2 := by
    nlinarith
  have hdv : (bits ((2 : ℤ) ^ (h - j)) + 2 + 1) ^ 2 ≤ (bits X + 4) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  simp only [sqrtStep, Expr.cost, Var.index, Expr.denote, Var.get, IntOp.charge, CmpOp.charge,
    IntOp.eval]
  rw [hb2]
  have e : 3 * (bits X + 6) ^ 2 = (bits X + 3) ^ 2 + (bits X + 4) ^ 2 +
      (bits X * bits X + 22 * bits X + 83) := by ring
  have hsq2 : (bits X + 3) ^ 2 = bits X * bits X + 6 * bits X + 9 := by ring
  have hdv2 : (bits X + 4) ^ 2 = bits X * bits X + 8 * bits X + 16 := by ring
  have e2 : (bits X + 6) ^ 2 = bits X * bits X + 12 * bits X + 36 := by ring
  rw [e2]
  generalize (bits (r + 2 ^ (h - j)) + 1) * (bits (r + 2 ^ (h - j)) + 1) = A at hsq ⊢
  generalize (bits ((2 : ℤ) ^ (h - j)) + 2 + 1) ^ 2 = B at hdv ⊢
  generalize bits X * bits X = Z at *
  rcases Bool.eq_false_or_eq_true
    (CmpOp.le.eval ((r + 2 ^ (h - j)) * (r + 2 ^ (h - j))) X) with hc | hc <;>
    simp only [hc, ite_true, ite_false, Bool.false_eq_true] <;> omega

theorem sqrtFn_cost (x : ℤ) : sqrtFn.costAt x ≤ 16 * (bits x + 6) ^ 3 := by
  have hX : 0 ≤ (Expr.ite (Γ := [.int]) (.cmp .lt v0 (.int 0)) (.int 0) v0).denote (x, ()) ∧
      bits ((Expr.ite (Γ := [.int]) (.cmp .lt v0 (.int 0)) (.int 0) v0).denote (x, ())) ≤ bits x := by
    simp only [Expr.denote, Var.get, CmpOp.eval]
    by_cases h : x < 0
    · simp only [h, decide_true, ite_true]; exact ⟨le_rfl, by simp [bits]⟩
    · simp only [h, decide_false, Bool.false_eq_true, ite_false]
      exact ⟨le_of_not_gt h, le_rfl⟩
  have hcX : (Expr.ite (Γ := [.int]) (.cmp .lt v0 (.int 0)) (.int 0) v0).cost (x, ()) ≤
      bits x + 7 := by
    simp only [Expr.cost, Var.index, Expr.denote, Var.get, CmpOp.charge, CmpOp.eval]
    have : bits (0 : ℤ) = 0 := by decide
    by_cases h : x < 0
    · simp only [h, decide_true, ite_true, this]; omega
    · simp only [h, decide_false, Bool.false_eq_true, ite_false, this]; omega
  have hb2 : bits (2 : ℤ) = 2 := by decide
  have hb1' : bits (1 : ℤ) = 1 := by decide
  have hb0 : bits (0 : ℤ) = 0 := by decide
  unfold Fn.costAt sqrtFn
  simp only [Expr.cost]
  generalize hgx : (Expr.ite (Γ := [.int]) (.cmp .lt v0 (.int 0)) (.int 0) v0).denote (x, ()) = X
    at hX ⊢
  simp only [Expr.cost, cost_call, Var.index, Expr.denote, Var.get, IntOp.charge, CmpOp.charge,
    IntOp.eval, CmpOp.eval, denote_call, pow2Fn_apply]
  have hhv' : ((bits X : ℤ) / 2).toNat = bits X / 2 := by omega
  have hit := cost_iter_le_prefix (Γ := [.int, .int, .int]) (.arith .add v0 (.int 1))
    (.pair (.int 0) (call pow2Fn v0)) sqrtStep ((bits X : ℤ) / 2, X, x, ())
    (3 * (bits X + 6) ^ 2) (by
      intro j hj
      simp only [Expr.denote, Var.get, denote_call, pow2Fn_apply, IntOp.eval] at hj ⊢
      rw [sqrtStep_denote, hhv']
      have hj' : j ≤ bits X / 2 := by omega
      obtain ⟨r, hr, hrX, he⟩ := sqrtRound_reach X hX.1 (bits X / 2) j hj'
      rw [he]
      exact sqrtStep_cost _ X x r (bits X / 2) j hX.1 hr hrX (by omega))
  simp only [Expr.cost, cost_call, Var.index, Expr.denote, Var.get, IntOp.charge, CmpOp.charge,
    IntOp.eval, CmpOp.eval, denote_call, pow2Fn_apply] at hit
  have hp := pow2Fn_cost ((bits X : ℤ) / 2)
  rw [hhv'] at hp
  have hb1 : bits ((bits X : ℤ) / 2 + 1) ≤ bits X + 1 := by
    have := bits_le_self_natAbs ((bits X : ℤ) / 2 + 1)
    omega
  have hbh : bits ((bits X : ℤ) / 2) ≤ bits X := by
    have := bits_le_self_natAbs ((bits X : ℤ) / 2)
    omega
  have hsz : bits (bits X : ℤ) ≤ bits X := by
    have := bits_le_self_natAbs (bits X : ℤ); simpa using this
  simp only [hhv', hb2, hb1', hb0] at hit ⊢
  have hxb := hX.2
  have c1 : (bits X / 2 + 1) * (3 * (bits X + 6) ^ 2 + bits ((bits X : ℤ) / 2 + 1) + 1) ≤
      (bits x + 1) * (4 * (bits x + 6) ^ 2) := by
    apply Nat.mul_le_mul (by omega)
    have : (bits X + 6) ^ 2 ≤ (bits x + 6) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    nlinarith
  have c2 : (bits X / 2 + 1) * (4 * (bits X / 2) + bits ((bits X : ℤ) / 2) + 16) ≤
      (bits x + 1) * (5 * bits x + 16) := by
    apply Nat.mul_le_mul (by omega); omega
  have c3 : (bits x + 1) * (4 * (bits x + 6) ^ 2) + (bits x + 1) * (5 * bits x + 16) +
      (bits x + 3) ^ 2 + 6 * bits x + 60 ≤ 16 * (bits x + 6) ^ 3 := by nlinarith
  have hdiv : (bits (bits X : ℤ) + 2 + 1) ^ 2 ≤ (bits x + 3) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  have hcc : ((bits X : ℤ) / 2 + 1).toNat = bits X / 2 + 1 := by omega
  rw [hcc] at hit ⊢
  have hite : (if decide (x < 0) = true then 1 else 0 + 1) ≤ 1 := by
    by_cases h : x < 0
    · simp [h]
    · simp [h]
  generalize ehp : pow2Fn.costAt ((bits X : ℤ) / 2) = P at hp hit ⊢
  generalize ehs : bits (bits X : ℤ) = Q at hdiv ⊢
  generalize ehc : ((fun s => (sqrtStep.denote (s.1, (bits X : ℤ) / 2, X, x, ()),
      s.2 + sqrtStep.cost (s.1, (bits X : ℤ) / 2, X, x, ()) + bits ((bits X : ℤ) / 2 + 1) + 1))^[bits X / 2 + 1]
      ((0, 2 ^ (bits X / 2)), 0)).2 = K at hit ⊢
  generalize (bits X / 2 + 1) * (3 * (bits X + 6) ^ 2 + bits ((bits X : ℤ) / 2 + 1) + 1) = A1 at hit c1
  generalize (bits X / 2 + 1) * (4 * (bits X / 2) + bits ((bits X : ℤ) / 2) + 16) = A2 at hp c2
  generalize (bits x + 1) * (4 * (bits x + 6) ^ 2) = T1 at c1 c3
  generalize (bits x + 1) * (5 * bits x + 16) = T2 at c2 c3
  generalize (Q + 2 + 1) ^ 2 = R at hdiv ⊢
  generalize (bits x + 3) ^ 2 = T3 at hdiv c3
  generalize 16 * (bits x + 6) ^ 3 = T4 at c3 ⊢
  simp only [Nat.zero_add, ite_self] at hite ⊢
  omega

end MWIS.FunLP

end
