module

public import MWIS.Fun.ArithNat

/-!
# Register procedures on stored integers

A stored integer is a sign cell over the normalized digit chain of its absolute
value (`reprInt`). The fixed procedures below implement every integer operation
and comparison of `Fun` with event bounds proportional to the charges
`IntOp.charge` and `CmpOp.charge`.
-/

@[expose] public section

namespace MWIS.Fun.Arith

open MWIS.PointerMemory MWIS.RegisterMachine MWIS.EfficientSearch

variable {p : ℕ}

/-! ## Signed values -/

/-- The integer with sign flag `s` and absolute value `m`. -/
def signed (s : Bool) (m : ℕ) : ℤ := if s then -(m : ℤ) else m

@[simp] theorem signed_natAbs (s : Bool) (m : ℕ) : (signed s m).natAbs = m := by
  cases s <;> simp [signed]

theorem reprInt_signed (s : Bool) (m : ℕ) :
    reprInt (signed s m) = .bit (s && decide (m ≠ 0)) (Tree.chain m.bits) := by
  unfold reprInt
  rw [signed_natAbs]
  congr 1
  cases s <;> simp [signed, Nat.pos_iff_ne_zero]

theorem eq_signed (z : ℤ) : z = signed (decide (z < 0)) z.natAbs := by
  unfold signed
  by_cases hz : z < 0
  · simp only [hz, decide_true, ↓reduceIte]
    rw [Int.ofNat_natAbs_of_nonpos hz.le]; ring
  · simp only [hz, decide_false, Bool.false_eq_true, ↓reduceIte]
    rw [Int.natAbs_of_nonneg (by omega)]

theorem reprInt_eq (z : ℤ) : reprInt z = .bit (decide (z < 0)) (Tree.chain z.natAbs.bits) := rfl

/-! ## Digit lists of natural numbers -/

theorem addL_bits (a b : ℕ) : addL a.bits b.bits false = (a + b).bits := by
  have h := norm_eq_bits (addL_norm (bits_norm a) (bits_norm b) false)
  rw [h, lval_addL, lval_bits, lval_bits]; simp

theorem addL_bits_one (a : ℕ) : addL a.bits [] true = (a + 1).bits := by
  have h := norm_eq_bits (addL_norm (bits_norm a) Norm.nil true)
  rw [h, lval_addL, lval_bits]; simp [lval]

theorem subL_bits (a b : ℕ) (hab : b ≤ a) : (subL a.bits b.bits false).1 = (a - b).bits := by
  obtain ⟨hv, hn, -⟩ := subL_spec a.bits b.bits false (by rw [lval_bits, lval_bits]; simpa)
  rw [norm_eq_bits hn, hv, lval_bits, lval_bits]; simp

theorem cmpL_bits (a b : ℕ) : cmpL a.bits b.bits = (decide (a < b), decide (a = b)) := by
  rw [cmpL_spec, lval_bits, lval_bits]

theorem mulL_bits (a b : ℕ) : mulL a.bits b.bits = (a * b).bits := by
  rw [norm_eq_bits (mulL_norm a.bits (bits_norm b)), lval_mulL, lval_bits, lval_bits]

theorem mulL_bits_comm (a b : ℕ) : mulL b.bits a.bits = (a * b).bits := by
  rw [mulL_bits, Nat.mul_comm]

theorem divmodL_bits (a b : ℕ) (hb : 0 < b) :
    divmodL a.bits b.bits = ((a / b).bits, (a % b).bits) := by
  obtain ⟨hq, hr, hqn, hrn⟩ := divmodL_spec a.bits (bs := b.bits) (by rw [lval_bits]; exact hb)
  rw [Prod.ext_iff]
  exact ⟨by rw [norm_eq_bits hqn, hq, lval_bits, lval_bits],
    by rw [norm_eq_bits hrn, hr, lval_bits, lval_bits]⟩

theorem bits_eq_nil (a : ℕ) : a.bits = [] ↔ a = 0 := by
  constructor
  · intro h; have := congrArg lval h; rwa [lval_bits] at this
  · rintro rfl; simp

/-! ## Euclidean division on signed values -/

/-- The Euclidean quotient computed from the digits. -/
def quotSigned (sx sy : Bool) (a d : ℕ) : ℤ :=
  if sx then (if a % d = 0 then signed (!sy) (a / d) else signed (!sy) (a / d + 1))
  else signed sy (a / d)

/-- The Euclidean remainder computed from the digits. -/
def remSigned (sx : Bool) (a d : ℕ) : ℕ :=
  if sx then (if a % d = 0 then 0 else d - a % d) else a % d

theorem ediv_emod_signed (sx sy : Bool) (a d : ℕ) (hd : 0 < d) :
    signed sx a / signed sy d = quotSigned sx sy a d ∧
      signed sx a % signed sy d = (remSigned sx a d : ℤ) := by
  have hlt := Nat.mod_lt a hd
  have hdm : ((a % d : ℕ) : ℤ) + (d : ℤ) * ((a / d : ℕ) : ℤ) = a := by
    exact_mod_cast Nat.mod_add_div a d
  have hlt' : ((a % d : ℕ) : ℤ) < d := by exact_mod_cast hlt
  have hd' : (0 : ℤ) < d := by exact_mod_cast hd
  have key : signed sx a / (d : ℤ) = (if sx then (if a % d = 0 then -((a / d : ℕ) : ℤ)
      else -((a / d : ℕ) : ℤ) - 1) else ((a / d : ℕ) : ℤ)) ∧
      signed sx a % (d : ℤ) = (remSigned sx a d : ℤ) := by
    rw [Int.ediv_emod_unique hd']
    unfold remSigned signed
    cases sx
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact ⟨by linarith, by positivity, hlt'⟩
    · simp only [↓reduceIte]
      split_ifs with hr
      · have h0 : ((a % d : ℕ) : ℤ) = 0 := by exact_mod_cast hr
        refine ⟨?_, by simp, by simpa using hd'⟩
        rw [Nat.cast_zero]; linarith
      · have hpos : 0 < a % d := Nat.pos_of_ne_zero hr
        have hc : ((d - a % d : ℕ) : ℤ) = d - ((a % d : ℕ) : ℤ) := by
          rw [Nat.cast_sub hlt.le]
        rw [hc]
        have : (0 : ℤ) < ((a % d : ℕ) : ℤ) := by exact_mod_cast hpos
        exact ⟨by linarith, by linarith, by linarith⟩
  obtain ⟨k1, k2⟩ := key
  unfold quotSigned
  cases sy
  · simp only [signed, Bool.false_eq_true, ↓reduceIte] at k1 k2 ⊢
    refine ⟨?_, k2⟩
    rw [k1]
    cases sx <;> by_cases hr : a % d = 0 <;> simp [hr, signed] <;> ring
  · simp only [signed, ↓reduceIte, Int.ediv_neg, Int.emod_neg] at k1 k2 ⊢
    refine ⟨?_, k2⟩
    rw [k1]
    cases sx <;> by_cases hr : a % d = 0 <;> simp [hr, signed] <;> ring

theorem signed_add (sx sy : Bool) (a b : ℕ) :
    signed sx a + signed sy b =
      if sx = sy then signed sx (a + b)
      else if a < b then signed sy (b - a) else signed sx (a - b) := by
  cases sx <;> cases sy <;> simp [signed] <;> (try split_ifs) <;> omega

theorem signed_mul (sx sy : Bool) (a b : ℕ) :
    signed sx a * signed sy b = signed (xor sx sy) (a * b) := by
  cases sx <;> cases sy <;> simp [signed]

theorem signed_neg (s : Bool) (b : ℕ) : -signed s b = signed (!s) b := by
  cases s <;> simp [signed]

theorem signed_zero (s : Bool) : signed s 0 = 0 := by cases s <;> simp [signed]

/-- Comparisons of integers through signs and absolute values. -/
theorem int_lt_iff (x y : ℤ) :
    decide (x < y) = (if x < 0 then (if y < 0 then decide (y.natAbs < x.natAbs) else true)
      else (if y < 0 then false else decide (x.natAbs < y.natAbs))) := by
  rcases lt_or_ge x 0 with hx | hx <;> rcases lt_or_ge y 0 with hy | hy
  · simp only [hx, hy, ↓reduceIte, decide_eq_decide]; omega
  · simp only [hx, ↓reduceIte, decide_eq_true_eq, show ¬ y < 0 by omega]; omega
  · simp only [hy, ↓reduceIte, show ¬ x < 0 by omega, decide_eq_false_iff_not]; omega
  · simp only [show ¬ x < 0 by omega, show ¬ y < 0 by omega, ↓reduceIte, decide_eq_decide]
    omega

theorem int_le_iff (x y : ℤ) :
    decide (x ≤ y) = (if x < 0 then (if y < 0 then decide (y.natAbs ≤ x.natAbs) else true)
      else (if y < 0 then false else decide (x.natAbs ≤ y.natAbs))) := by
  rcases lt_or_ge x 0 with hx | hx <;> rcases lt_or_ge y 0 with hy | hy
  · simp only [hx, hy, ↓reduceIte, decide_eq_decide]; omega
  · simp only [hx, ↓reduceIte, decide_eq_true_eq, show ¬ y < 0 by omega]; omega
  · simp only [hy, ↓reduceIte, show ¬ x < 0 by omega, decide_eq_false_iff_not]; omega
  · simp only [show ¬ x < 0 by omega, show ¬ y < 0 by omega, ↓reduceIte, decide_eq_decide]
    omega

theorem int_eq_iff (x y : ℤ) :
    decide (x = y) = (if x < 0 then (if y < 0 then decide (x.natAbs = y.natAbs) else false)
      else (if y < 0 then false else decide (x.natAbs = y.natAbs))) := by
  rcases lt_or_ge x 0 with hx | hx <;> rcases lt_or_ge y 0 with hy | hy
  · simp only [hx, hy, ↓reduceIte, decide_eq_decide]; omega
  · simp only [hx, ↓reduceIte, show ¬ y < 0 by omega, decide_eq_false_iff_not]; omega
  · simp only [hy, ↓reduceIte, show ¬ x < 0 by omega, decide_eq_false_iff_not]; omega
  · simp only [show ¬ x < 0 by omega, show ¬ y < 0 by omega, ↓reduceIte, decide_eq_decide]
    omega

/-! ## Building a stored integer -/

/-- Arguments 0 = sign flag, 1 = magnitude chain; result: the stored integer. -/
def mkIntBody : Command p :=
  .load (.register 1) 2 15 3 { CompiledTrie.failCases with
    nil := .allocate 4 (.bit (.flag false) (.register 1)) (.ret [.register 4])
    bit := .allocate 4 (.bit (.register 0) (.register 1)) (.ret [.register 4]) }

theorem mkInt_compiled (code : Code p) (self : Fin p) (hself : code self = mkIntBody)
    (s : Bool) (m : ℕ) {h : Heap} (hh : Valid h) {mp : Ptr}
    (hm : TreeAt h mp (Tree.chain m.bits)) :
    Yields code h (initialRegisters [.flag s, .pointer mp]) (code self) 30
      (Returns h (reprInt (signed s m))) := by
  rw [hself]
  refine Yields.le (B := 10 + (8 + 3)) ?_ (by omega)
  refine Yields.loadChain hh (by rsimp) hm fun _ _ => ?_
  by_cases hz : m.bits = []
  · rw [if_pos hz]
    have hm0 : m = 0 := (bits_eq_nil m).mp hz
    refine Yields.allocBit hh (b := false) (by rsimp) (by rsimp) hm fun e2 v2 t2 => ?_
    refine Yields.ret ⟨e2, v2, h.length, by rsimp, ?_⟩ (by simp)
    rw [reprInt_signed]; simpa [hm0] using t2
  · rw [if_neg hz]
    have hm0 : m ≠ 0 := fun h0 => hz ((bits_eq_nil m).mpr h0)
    refine Yields.allocBit hh (b := s) (by rsimp) (by rsimp) hm fun e2 v2 t2 => ?_
    refine Yields.ret ⟨e2, v2, h.length, by rsimp, ?_⟩ (by simp)
    rw [reprInt_signed]; simpa [hm0] using t2

/-! ## Signed addition of magnitudes -/

/-- Arguments 0 = first sign, 1 = first magnitude, 2 = second sign, 3 = second
magnitude; result: the stored sum. -/
def addSignedBody (add cmp sub mkInt : Fin p) : Command p :=
  let same : Command p :=
    .call add [.register 1, .register 3, .flag false] [5]
      (.call mkInt [.register 0, .register 5] [6] (.ret [.register 6]))
  let diff : Command p :=
    .call cmp [.register 1, .register 3] [5, 6]
      (.branch (.register 5)
        (.call sub [.register 3, .register 1, .flag false] [7, 8]
          (.call mkInt [.register 2, .register 7] [9] (.ret [.register 9])))
        (.call sub [.register 1, .register 3, .flag false] [7, 8]
          (.call mkInt [.register 0, .register 7] [9] (.ret [.register 9]))))
  .branch (.register 0) (.branch (.register 2) same diff) (.branch (.register 2) diff same)

def addSignedBudget (la lb : ℕ) : ℕ := 200 * (la + lb + 1) + 100

/-- The arithmetic procedures and their identifiers. -/
structure Procedures (p : ℕ) where
  add : Fin p
  sub : Fin p
  cmp : Fin p
  lenLe : Fin p
  mul : Fin p
  div : Fin p
  halve : Fin p
  size : Fin p
  mkInt : Fin p
  addSigned : Fin p
  mulAny : Fin p
  iadd : Fin p
  isub : Fin p
  imul : Fin p
  idiv : Fin p
  imod : Fin p
  ilt : Fin p
  ile : Fin p
  ieq : Fin p
  isize : Fin p

theorem addSigned_compiled (code : Code p) (d : Procedures p)
    (hadd : code d.add = addBody d.add) (hcmp : code d.cmp = cmpBody d.cmp)
    (hsub : code d.sub = subBody d.sub) (hmk : code d.mkInt = mkIntBody)
    (hself : code d.addSigned = addSignedBody d.add d.cmp d.sub d.mkInt)
    (sx sy : Bool) (a b : ℕ) {h : Heap} (hh : Valid h) {ap bp : Ptr}
    (ha : TreeAt h ap (Tree.chain a.bits)) (hb : TreeAt h bp (Tree.chain b.bits)) :
    Yields code h (initialRegisters [.flag sx, .pointer ap, .flag sy, .pointer bp])
      (code d.addSigned) (addSignedBudget a.bits.length b.bits.length)
      (Returns h (reprInt (signed sx a + signed sy b))) := by
  rw [hself]
  have hsame : sx = sy → Yields code h (initialRegisters [.flag sx, .pointer ap, .flag sy, .pointer bp])
      (.call d.add [.register 1, .register 3, .flag false] [5]
        (.call d.mkInt [.register 0, .register 5] [6] (.ret [.register 6])))
      (addSignedBudget a.bits.length b.bits.length - 6)
      (Returns h (reprInt (signed sx a + signed sy b))) := by
    intro hs
    have hy := add_compiled code d.add hadd a.bits b.bits false hh ha hb
    rw [addL_bits] at hy
    refine Yields.le (B := 1 + 2 * 3 + addBudget a.bits.length b.bits.length + (1 + 2 * 2 + 30 + 3))
      ?_ (by unfold addSignedBudget addBudget; omega)
    refine Yields.callTree (by rsimp) hy fun mid q hm vm tq => ?_
    have hk := mkInt_compiled code d.mkInt hmk sx (a + b) vm tq
    refine Yields.callTree (by rsimp) hk fun mid2 q2 hm2 vm2 tq2 => ?_
    refine Yields.ret ⟨hm.trans hm2, vm2, q2, by rsimp, ?_⟩ (by simp)
    rw [signed_add, if_pos hs]; exact tq2
  have hdiff : sx ≠ sy → Yields code h (initialRegisters [.flag sx, .pointer ap, .flag sy, .pointer bp])
      (.call d.cmp [.register 1, .register 3] [5, 6]
        (.branch (.register 5)
          (.call d.sub [.register 3, .register 1, .flag false] [7, 8]
            (.call d.mkInt [.register 2, .register 7] [9] (.ret [.register 9])))
          (.call d.sub [.register 1, .register 3, .flag false] [7, 8]
            (.call d.mkInt [.register 0, .register 7] [9] (.ret [.register 9])))))
      (addSignedBudget a.bits.length b.bits.length - 6)
      (Returns h (reprInt (signed sx a + signed sy b))) := by
    intro hs
    have hc := cmp_compiled code d.cmp hcmp a.bits b.bits hh ha hb
    rw [cmpL_bits] at hc
    refine Yields.le (B := 1 + 2 * 2 + cmpBudget a.bits.length b.bits.length +
      (3 + (1 + 2 * 3 + subBudget (a.bits.length + b.bits.length) (a.bits.length + b.bits.length)
        + (1 + 2 * 2 + 30 + 3)))) ?_ (by unfold addSignedBudget cmpBudget subBudget; omega)
    refine Yields.call (by rsimp) hc fun mid vals hv => ?_
    obtain ⟨hmid, rfl⟩ := hv
    rw [hmid]
    by_cases hlt : a < b
    · refine Yields.branch (b := true) (by rsimp [hlt]) ?_
      have hy := sub_compiled code d.sub hsub b.bits a.bits false hh hb ha
      refine Yields.le (B := 1 + 2 * 3 + subBudget b.bits.length a.bits.length +
        (1 + 2 * 2 + 30 + 3)) ?_ (by unfold subBudget; omega)
      refine Yields.call (by rsimp) hy fun mid2 vals2 hv2 => ?_
      obtain ⟨hm2, vm2, q2, rfl, tq2⟩ := hv2
      rw [subL_bits b a hlt.le] at tq2
      have hk := mkInt_compiled code d.mkInt hmk sy (b - a) vm2 tq2
      refine Yields.callTree (by rsimp) hk fun mid3 q3 hm3 vm3 tq3 => ?_
      refine Yields.ret ⟨hm2.trans hm3, vm3, q3, by rsimp, ?_⟩ (by simp)
      rw [signed_add, if_neg hs, if_pos hlt]; exact tq3
    · refine Yields.branch (b := false) (by rsimp [hlt]) ?_
      have hy := sub_compiled code d.sub hsub a.bits b.bits false hh ha hb
      refine Yields.le (B := 1 + 2 * 3 + subBudget a.bits.length b.bits.length +
        (1 + 2 * 2 + 30 + 3)) ?_ (by unfold subBudget; omega)
      refine Yields.call (by rsimp) hy fun mid2 vals2 hv2 => ?_
      obtain ⟨hm2, vm2, q2, rfl, tq2⟩ := hv2
      rw [subL_bits a b (by omega)] at tq2
      have hk := mkInt_compiled code d.mkInt hmk sx (a - b) vm2 tq2
      refine Yields.callTree (by rsimp) hk fun mid3 q3 hm3 vm3 tq3 => ?_
      refine Yields.ret ⟨hm2.trans hm3, vm3, q3, by rsimp, ?_⟩ (by simp)
      rw [signed_add, if_neg hs, if_neg hlt]; exact tq3
  refine Yields.le (B := 3 + (3 + (addSignedBudget a.bits.length b.bits.length - 6))) ?_
    (by unfold addSignedBudget; omega)
  cases sx <;> cases sy
  · exact Yields.branch (b := false) (by rsimp) (Yields.branch (b := false) (by rsimp) (hsame rfl))
  · exact Yields.branch (b := false) (by rsimp)
      (Yields.branch (b := true) (by rsimp) (hdiff (by simp)))
  · exact Yields.branch (b := true) (by rsimp)
      (Yields.branch (b := false) (by rsimp) (hdiff (by simp)))
  · exact Yields.branch (b := true) (by rsimp) (Yields.branch (b := true) (by rsimp) (hsame rfl))

end MWIS.Fun.Arith

end
