module

public import MWIS.Fun.Heap
public import MWIS.EfficientSearchArithmetic

/-!
# Digit-list arithmetic specifications

Least-significant-first digit lists, with the functions computed by the register
arithmetic procedures: ripple-carry addition, comparison, trimmed subtraction,
shift-and-add multiplication and restoring division. Each function is shown to
compute the expected value and to keep normalized lists normalized.
-/

@[expose] public section

namespace MWIS.Fun

open MWIS.EfficientSearch

/-- The value of a digit. -/
def dg (b : Bool) : ℕ := if b then 1 else 0

@[simp] theorem dg_true : dg true = 1 := rfl
@[simp] theorem dg_false : dg false = 0 := rfl

theorem lval_cons (b : Bool) (l : List Bool) : lval (b :: l) = dg b + 2 * lval l := rfl

theorem lval_head_tail (l : List Bool) : lval l = dg (l.headD false) + 2 * lval l.tail := by
  cases l with
  | nil => rfl
  | cons b l => rfl

theorem dg_le (b : Bool) : dg b ≤ 1 := by cases b <;> decide

theorem tail_lt {as bs : List Bool} (h : ¬(as = [] ∧ bs = [])) :
    as.tail.length + bs.tail.length < as.length + bs.length := by
  rcases as with _ | ⟨_, _⟩ <;> rcases bs with _ | ⟨_, _⟩ <;> simp_all <;> omega

theorem Norm.tail' {l : List Bool} (h : Norm l) : Norm l.tail := by
  cases l with
  | nil => exact Norm.nil
  | cons b l => exact h.tail

/-! ## Addition -/

/-- Ripple-carry addition of digit lists. -/
def addL (as bs : List Bool) (c : Bool) : List Bool :=
  if h : as = [] ∧ bs = [] then (if c then [true] else [])
  else (Bits.fullAdd (as.headD false) (bs.headD false) c).1 ::
    addL as.tail bs.tail (Bits.fullAdd (as.headD false) (bs.headD false) c).2
termination_by as.length + bs.length
decreasing_by
  rcases as with _ | ⟨_, _⟩ <;> rcases bs with _ | ⟨_, _⟩ <;> simp_all <;> omega

theorem fullAdd_dg (a b c : Bool) :
    dg (Bits.fullAdd a b c).1 + 2 * dg (Bits.fullAdd a b c).2 = dg a + dg b + dg c := by
  cases a <;> cases b <;> cases c <;> decide

theorem lval_addL (as bs : List Bool) (c : Bool) :
    lval (addL as bs c) = lval as + lval bs + dg c := by
  by_cases h : as = [] ∧ bs = []
  · obtain ⟨rfl, rfl⟩ := h; rw [addL, dif_pos ⟨rfl, rfl⟩]; cases c <;> simp [lval]
  · rw [addL, dif_neg h, lval_cons, lval_addL as.tail bs.tail, lval_head_tail as, lval_head_tail bs]
    have := fullAdd_dg (as.headD false) (bs.headD false) c
    omega
termination_by as.length + bs.length
decreasing_by all_goals exact tail_lt ‹_›

theorem addL_length (as bs : List Bool) (c : Bool) :
    (addL as bs c).length ≤ max as.length bs.length + 1 := by
  by_cases h : as = [] ∧ bs = []
  · obtain ⟨rfl, rfl⟩ := h; rw [addL, dif_pos ⟨rfl, rfl⟩]; cases c <;> simp
  · rw [addL, dif_neg h]
    have := addL_length as.tail bs.tail (Bits.fullAdd (as.headD false) (bs.headD false) c).2
    rw [List.length_cons]
    rcases as with _ | ⟨_, _⟩ <;> rcases bs with _ | ⟨_, _⟩ <;> simp_all <;> omega
termination_by as.length + bs.length
decreasing_by all_goals exact tail_lt ‹_›

theorem addL_ne_nil (as bs : List Bool) (c : Bool) (h : ¬(as = [] ∧ bs = [])) :
    addL as bs c ≠ [] := by rw [addL, dif_neg h]; simp

theorem addL_norm {as bs : List Bool} (ha : Norm as) (hb : Norm bs) (c : Bool) :
    Norm (addL as bs c) := by
  by_cases h : as = [] ∧ bs = []
  · obtain ⟨rfl, rfl⟩ := h; rw [addL, dif_pos ⟨rfl, rfl⟩]; cases c
    · exact Norm.nil
    · exact Norm.nil.cons (fun _ => rfl)
  · rw [addL, dif_neg h]
    refine (addL_norm ha.tail' hb.tail' _).cons fun hr => ?_
    by_cases ht : as.tail = [] ∧ bs.tail = []
    · rw [addL, dif_pos ht] at hr
      have hc : (Bits.fullAdd (as.headD false) (bs.headD false) c).2 = false := by
        revert hr; cases (Bits.fullAdd (as.headD false) (bs.headD false) c).2 <;> simp
      rcases as with _ | ⟨a, as⟩ <;> rcases bs with _ | ⟨b, bs⟩
      · exact absurd ⟨rfl, rfl⟩ h
      · simp at ht; subst ht
        have hb1 := hb (List.cons_ne_nil _ _); simp at hb1; subst hb1
        revert hc; cases c <;> simp [Bits.fullAdd]
      · simp at ht; subst ht
        have ha1 := ha (List.cons_ne_nil _ _); simp at ha1; subst ha1
        revert hc; cases c <;> simp [Bits.fullAdd]
      · simp at ht; obtain ⟨rfl, rfl⟩ := ht
        have ha1 := ha (List.cons_ne_nil _ _); simp at ha1; subst ha1
        have hb1 := hb (List.cons_ne_nil _ _); simp at hb1; subst hb1
        revert hc; cases c <;> simp [Bits.fullAdd]
    · exact absurd hr (addL_ne_nil _ _ _ ht)
termination_by as.length + bs.length
decreasing_by all_goals exact tail_lt ‹_›

theorem addL_nil_left (bs : List Bool) : addL [] bs false = bs := by
  induction bs with
  | nil => rw [addL]; simp
  | cons b bs ih =>
    rw [addL, dif_neg (by simp)]
    simp only [List.headD_nil, List.headD_cons, List.tail_nil, List.tail_cons]
    have h1 : (Bits.fullAdd false b false).1 = b := by cases b <;> rfl
    have h2 : (Bits.fullAdd false b false).2 = false := by cases b <;> rfl
    rw [h1, h2, ih]

/-! ## Comparison -/

/-- Comparison of digit lists, least significant digit first: strictly-less and
equality flags. -/
def cmpL (as bs : List Bool) : Bool × Bool :=
  if h : as = [] ∧ bs = [] then (false, true)
  else
    if (cmpL as.tail bs.tail).2 then
      (!(as.headD false) && bs.headD false, as.headD false == bs.headD false)
    else ((cmpL as.tail bs.tail).1, false)
termination_by as.length + bs.length
decreasing_by all_goals exact tail_lt ‹_›

theorem cmp_digit (a b : Bool) (x y : ℕ) :
    (if decide (x = y) = true then (!a && b, a == b) else (decide (x < y), false)) =
      (decide (dg a + 2 * x < dg b + 2 * y), decide (dg a + 2 * x = dg b + 2 * y)) := by
  by_cases hxy : x = y
  · subst hxy; cases a <;> cases b <;> simp
  · simp only [hxy, decide_false, Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq]
    constructor
    · cases a <;> cases b <;> simp <;> omega
    · cases a <;> cases b <;> simp <;> omega

theorem cmpL_spec (as bs : List Bool) :
    cmpL as bs = (decide (lval as < lval bs), decide (lval as = lval bs)) := by
  by_cases h : as = [] ∧ bs = []
  · obtain ⟨rfl, rfl⟩ := h; rw [cmpL, dif_pos ⟨rfl, rfl⟩]; simp [lval]
  · rw [cmpL, dif_neg h, cmpL_spec as.tail bs.tail, lval_head_tail as, lval_head_tail bs]
    exact cmp_digit _ _ _ _
termination_by as.length + bs.length
decreasing_by exact tail_lt h

/-! ## Subtraction -/

/-- Digit of `a - b - br` and its borrow. -/
def subDigit (a b br : Bool) : Bool × Bool :=
  (xor (xor a b) br, (!a && (b || br)) || (b && br))

theorem subDigit_dg (a b br : Bool) :
    dg a + 2 * dg (subDigit a b br).2 = dg (subDigit a b br).1 + dg b + dg br := by
  cases a <;> cases b <;> cases br <;> decide

/-- Trimmed subtraction with borrow; the flag reports a zero result. -/
def subL (as bs : List Bool) (br : Bool) : List Bool × Bool :=
  if h : as = [] ∧ bs = [] then ([], true)
  else
    if (subL as.tail bs.tail (subDigit (as.headD false) (bs.headD false) br).2).2 &&
        !(subDigit (as.headD false) (bs.headD false) br).1 then ([], true)
    else ((subDigit (as.headD false) (bs.headD false) br).1 ::
      (subL as.tail bs.tail (subDigit (as.headD false) (bs.headD false) br).2).1, false)
termination_by as.length + bs.length
decreasing_by all_goals exact tail_lt ‹_›

theorem subL_spec (as bs : List Bool) (br : Bool) (hle : lval bs + dg br ≤ lval as) :
    lval (subL as bs br).1 = lval as - lval bs - dg br ∧ Norm (subL as bs br).1 ∧
      (subL as bs br).2 = decide ((subL as bs br).1 = []) := by
  by_cases h : as = [] ∧ bs = []
  · obtain ⟨rfl, rfl⟩ := h; rw [subL, dif_pos ⟨rfl, rfl⟩]; simp [lval] at hle ⊢; exact Norm.nil
  · have e1 := lval_head_tail as
    have e2 := lval_head_tail bs
    have hle' : lval bs.tail + dg (subDigit (as.headD false) (bs.headD false) br).2 ≤
        lval as.tail := by
      rw [e1, e2] at hle
      generalize as.headD false = a at *
      generalize bs.headD false = b at *
      cases a <;> cases b <;> cases br <;> simp [subDigit, dg] at hle ⊢ <;> omega
    obtain ⟨hv, hn, hzero⟩ := subL_spec as.tail bs.tail _ hle'
    rw [subL, dif_neg h]
    have hvd : lval as - lval bs - dg br =
        dg (subDigit (as.headD false) (bs.headD false) br).1 +
          2 * (lval as.tail - lval bs.tail - dg (subDigit (as.headD false) (bs.headD false) br).2) := by
      rw [e1, e2] at hle ⊢
      generalize as.headD false = a at *
      generalize bs.headD false = b at *
      cases a <;> cases b <;> cases br <;> simp [subDigit, dg] at hle hle' ⊢ <;> omega
    split_ifs with hz
    · simp only [Bool.and_eq_true, Bool.not_eq_true'] at hz
      refine ⟨?_, Norm.nil, by simp⟩
      rw [hz.1] at hzero
      have he := (decide_eq_true_iff.mp hzero.symm)
      rw [he] at hv
      rw [hvd, hz.2, ← hv]
      simp [lval]
    · refine ⟨?_, hn.cons fun he => ?_, by simp⟩
      · rw [lval_cons, hv, hvd]
      · rw [he] at hzero
        simp only [decide_true] at hzero
        simp only [hzero, Bool.true_and, Bool.not_eq_true', not_not] at hz
        simpa using hz
termination_by as.length + bs.length
decreasing_by exact tail_lt h

/-! ## Shifts and multiplication -/

/-- Prepend a digit, keeping lists normalized. -/
def shiftL (b : Bool) (l : List Bool) : List Bool := if l = [] ∧ b = false then [] else b :: l

theorem lval_shiftL (b : Bool) (l : List Bool) : lval (shiftL b l) = dg b + 2 * lval l := by
  unfold shiftL; split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h; simp [lval]
  · rfl

theorem shiftL_norm {l : List Bool} (h : Norm l) (b : Bool) : Norm (shiftL b l) := by
  unfold shiftL; split_ifs with hc
  · exact Norm.nil
  · refine h.cons fun hl => ?_
    cases b
    · exact absurd ⟨hl, rfl⟩ hc
    · rfl

theorem shiftL_length (b : Bool) (l : List Bool) : (shiftL b l).length ≤ l.length + 1 := by
  unfold shiftL; split_ifs <;> simp

/-- Shift-and-add multiplication, recursing on the first factor. -/
def mulL : List Bool → List Bool → List Bool
  | [], _ => []
  | a :: as, bs => if a then addL (shiftL false (mulL as bs)) bs false
      else shiftL false (mulL as bs)

theorem lval_mulL (as bs : List Bool) : lval (mulL as bs) = lval as * lval bs := by
  induction as with
  | nil => simp [mulL, lval]
  | cons a as ih =>
    cases a
    · simp only [mulL, Bool.false_eq_true, ↓reduceIte, lval_shiftL, ih, lval_cons]; simp; ring
    · simp only [mulL, ↓reduceIte, lval_addL, lval_shiftL, ih, lval_cons]; simp; ring

theorem mulL_norm (as : List Bool) {bs : List Bool} (hb : Norm bs) : Norm (mulL as bs) := by
  induction as with
  | nil => exact Norm.nil
  | cons a as ih =>
    cases a
    · exact shiftL_norm ih false
    · exact addL_norm (shiftL_norm ih false) hb false

theorem mulL_length (as bs : List Bool) :
    (mulL as bs).length ≤ 2 * as.length + bs.length := by
  induction as with
  | nil => simp [mulL]
  | cons a as ih =>
    have h2 := shiftL_length false (mulL as bs)
    have h1 := addL_length (shiftL false (mulL as bs)) bs false
    rw [List.length_cons]
    cases a
    · show (shiftL false (mulL as bs)).length ≤ _
      omega
    · show (addL (shiftL false (mulL as bs)) bs false).length ≤ _
      have : max (shiftL false (mulL as bs)).length bs.length ≤ 2 * as.length + bs.length + 1 := by
        omega
      omega

/-! ## Division -/

/-- Restoring division, recursing on the dividend digits. -/
def divmodL : List Bool → List Bool → List Bool × List Bool
  | [], _ => ([], [])
  | x :: as, bs =>
    if (cmpL (shiftL x (divmodL as bs).2) bs).1 then
      (shiftL false (divmodL as bs).1, shiftL x (divmodL as bs).2)
    else (shiftL true (divmodL as bs).1, (subL (shiftL x (divmodL as bs).2) bs false).1)

theorem divmodL_spec (as : List Bool) {bs : List Bool} (hb : 0 < lval bs) :
    lval (divmodL as bs).1 = lval as / lval bs ∧ lval (divmodL as bs).2 = lval as % lval bs ∧
      Norm (divmodL as bs).1 ∧ Norm (divmodL as bs).2 := by
  induction as with
  | nil => exact ⟨by simp [divmodL, lval], by simp [divmodL, lval], Norm.nil, Norm.nil⟩
  | cons x as ih =>
    obtain ⟨hq, hr, hqn, hrn⟩ := ih
    have hmod := Nat.mod_lt (lval as) hb
    have hdm := Nat.div_add_mod (lval as) (lval bs)
    have hx := dg_le x
    rw [divmodL, cmpL_spec]
    split_ifs with hc
    · simp only [decide_eq_true_eq] at hc
      rw [lval_shiftL, hr] at hc
      have hu := (Nat.div_mod_unique (a := lval (x :: as)) (d := 2 * (lval as / lval bs))
        (c := dg x + 2 * (lval as % lval bs)) hb).mpr ⟨by rw [lval_cons]; linarith [hdm], hc⟩
      refine ⟨?_, ?_, shiftL_norm hqn _, shiftL_norm hrn _⟩
      · rw [lval_shiftL, hq, hu.1]; simp
      · rw [lval_shiftL, hr, hu.2]
    · simp only [decide_eq_true_eq, not_lt] at hc
      rw [lval_shiftL, hr] at hc
      have hs := subL_spec (shiftL x (divmodL as bs).2) bs false
        (by rw [lval_shiftL, hr]; simpa using hc)
      have hu := (Nat.div_mod_unique (a := lval (x :: as)) (d := 2 * (lval as / lval bs) + 1)
        (c := dg x + 2 * (lval as % lval bs) - lval bs) hb).mpr
          ⟨by rw [lval_cons, Nat.mul_add, Nat.mul_one]; zify [hc] at hdm ⊢; linarith [hdm], by omega⟩
      refine ⟨?_, ?_, shiftL_norm hqn _, hs.2.1⟩
      · rw [lval_shiftL, hq, hu.1]; simp; ring
      · rw [hs.1, lval_shiftL, hr, hu.2]; simp

/-! ## Lengths of normalized lists -/

theorem norm_length {l : List Bool} (h : Norm l) : l.length = (lval l).size := by
  conv_lhs => rw [norm_eq_bits h]
  exact bits_length _

theorem lval_lt_pow (l : List Bool) : lval l < 2 ^ l.length := by
  induction l with
  | nil => simp [lval]
  | cons b l ih => have := dg_le b; simp only [lval_cons, List.length_cons, pow_succ]; omega

theorem size_le_of_lt {a b : ℕ} (h : a < b) : a.size ≤ b.size := Nat.size_le_size h.le

theorem divmodL_rem_length (as : List Bool) {bs : List Bool} (hn : Norm bs) (hb : 0 < lval bs) :
    (divmodL as bs).2.length ≤ bs.length := by
  obtain ⟨-, hr, -, hrn⟩ := divmodL_spec as hb
  rw [norm_length hrn, norm_length hn, hr]
  exact Nat.size_le_size (Nat.mod_lt _ hb).le

theorem divmodL_quot_length (as : List Bool) (bs : List Bool) :
    (divmodL as bs).1.length ≤ as.length := by
  induction as with
  | nil => simp [divmodL]
  | cons x as ih =>
    rw [divmodL]
    split_ifs
    · have := shiftL_length false (divmodL as bs).1; simp; omega
    · have := shiftL_length true (divmodL as bs).1; simp; omega

theorem length_bits_lt_pow (n : ℕ) : n < 2 ^ n.bits.length := by
  rw [bits_length]; exact Nat.lt_size_self n

end MWIS.Fun

end
