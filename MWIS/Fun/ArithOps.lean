module

public import MWIS.Fun.ArithInt

/-!
# The integer operations of `Fun`

Fixed procedures for every `IntOp` and `CmpOp`, and for the binary length,
operating on stored integers. Each runs within `1000` times the charge of the
operation on its actual arguments.
-/

@[expose] public section

namespace MWIS.Fun.Arith

open MWIS.PointerMemory MWIS.RegisterMachine MWIS.EfficientSearch

variable {p : ℕ}

/-! ## Loading two stored integers -/

/-- Load the integers in registers 0 and 1: magnitudes to 2 and 4, signs to 3 and 5. -/
def loadTwo (k : Command p) : Command p :=
  .load (.register 0) 2 15 3 { CompiledTrie.failCases with
    bit := .load (.register 1) 4 15 5 { CompiledTrie.failCases with bit := k } }

theorem Yields.loadTwo {code : Code p} {h : Heap} {regs : Registers} {k : Command p}
    {px py : Ptr} {x y : ℤ} (h0 : regs 0 = .pointer px) (h1 : regs 1 = .pointer py)
    (hx : TreeAt h px (reprInt x)) (hy : TreeAt h py (reprInt y)) {B : ℕ}
    {P : Heap → List Value → Prop}
    (rest : ∀ mx my, TreeAt h mx (Tree.chain x.natAbs.bits) →
      TreeAt h my (Tree.chain y.natAbs.bits) →
      Yields code h (loaded (loaded regs 2 15 3 mx 0 (decide (x < 0))) 4 15 5 my 0
        (decide (y < 0))) k B P) :
    Yields code h regs (loadTwo k) (20 + B) P := by
  refine Yields.le (B := 10 + (10 + B)) ?_ (by omega)
  refine Yields.loadBit (by rsimp [h0]) hx fun mx tmx => ?_
  exact Yields.loadBit (by rsimp [h1]) hy fun my tmy => rest mx my tmx tmy

/-- Allocate a stored boolean whose bit is the value of `a`. -/
def boolRet (a : Atom) : Command p := .allocate 8 (.bit a .null) (.ret [.register 8])

theorem Yields.boolRet {code : Code p} {h : Heap} (hh : Valid h) {regs : Registers}
    {a : Atom} {b : Bool} (ha : a.eval regs = .flag b) :
    Yields code h regs (boolRet a) 11 (Returns h (.bit b .nil)) := by
  refine Yields.le (B := 8 + 3) ?_ (by omega)
  refine Yields.allocBit hh (b := b) ha (by rsimp) (TreeAt.zero hh) fun e2 v2 t2 => ?_
  exact Yields.ret ⟨e2, v2, h.length, by rsimp, t2⟩ (by simp)

/-! ## Procedure bodies -/

def iaddBody (addSigned : Fin p) : Command p :=
  loadTwo (.call addSigned [.register 3, .register 2, .register 5, .register 4] [6]
    (.ret [.register 6]))

def isubBody (addSigned : Fin p) : Command p :=
  loadTwo (.load (.register 4) 6 15 7 { CompiledTrie.failCases with
    nil := .ret [.register 0]
    bit := .branch (.register 5)
      (.call addSigned [.register 3, .register 2, .flag false, .register 4] [8] (.ret [.register 8]))
      (.call addSigned [.register 3, .register 2, .flag true, .register 4] [8]
        (.ret [.register 8])) })

def mulAnyBody (lenLe mul : Fin p) : Command p :=
  .call lenLe [.register 0, .register 1] [2]
    (.branch (.register 2) (.call mul [.register 0, .register 1] [3] (.ret [.register 3]))
      (.call mul [.register 1, .register 0] [3] (.ret [.register 3])))

def mulSign (mkInt : Fin p) (s : Bool) : Command p :=
  .call mkInt [.flag s, .register 6] [7] (.ret [.register 7])

def imulBody (mulAny mkInt : Fin p) : Command p :=
  loadTwo (.call mulAny [.register 2, .register 4] [6]
    (.branch (.register 3)
      (.branch (.register 5) (mulSign mkInt false) (mulSign mkInt true))
      (.branch (.register 5) (mulSign mkInt true) (mulSign mkInt false))))

def negSign (mkInt : Fin p) (r : Register) : Command p :=
  .branch (.register 5) (.call mkInt [.flag false, .register r] [13] (.ret [.register 13]))
    (.call mkInt [.flag true, .register r] [13] (.ret [.register 13]))

def idivBody (div add mkInt : Fin p) : Command p :=
  loadTwo (.load (.register 4) 6 15 7 { CompiledTrie.failCases with
    nil := .allocate 8 (.bit (.flag false) .null) (.ret [.register 8])
    bit := .call div [.register 2, .register 4] [8, 9]
      (.branch (.register 3)
        (.load (.register 9) 10 15 11 { CompiledTrie.failCases with
          nil := negSign mkInt 8
          bit := .call add [.register 8, .null, .flag true] [12] (negSign mkInt 12) })
        (.call mkInt [.register 5, .register 8] [13] (.ret [.register 13]))) })

def imodBody (div sub mkInt : Fin p) : Command p :=
  loadTwo (.load (.register 4) 6 15 7 { CompiledTrie.failCases with
    nil := .ret [.register 0]
    bit := .call div [.register 2, .register 4] [8, 9]
      (.branch (.register 3)
        (.load (.register 9) 10 15 11 { CompiledTrie.failCases with
          nil := .call mkInt [.flag false, .register 9] [13] (.ret [.register 13])
          bit := .call sub [.register 4, .register 9, .flag false] [12, 14]
            (.call mkInt [.flag false, .register 12] [13] (.ret [.register 13])) })
        (.call mkInt [.flag false, .register 9] [13] (.ret [.register 13]))) })

def iltBody (cmp : Fin p) : Command p :=
  loadTwo (.branch (.register 3)
    (.branch (.register 5) (.call cmp [.register 4, .register 2] [6, 7] (boolRet (.register 6)))
      (boolRet (.flag true)))
    (.branch (.register 5) (boolRet (.flag false))
      (.call cmp [.register 2, .register 4] [6, 7] (boolRet (.register 6)))))

def ileBody (cmp : Fin p) : Command p :=
  loadTwo (.branch (.register 3)
    (.branch (.register 5)
      (.call cmp [.register 4, .register 2] [6, 7]
        (.branch (.register 6) (boolRet (.flag true)) (boolRet (.register 7))))
      (boolRet (.flag true)))
    (.branch (.register 5) (boolRet (.flag false))
      (.call cmp [.register 2, .register 4] [6, 7]
        (.branch (.register 6) (boolRet (.flag true)) (boolRet (.register 7))))))

def ieqBody (cmp : Fin p) : Command p :=
  loadTwo (.branch (.register 3)
    (.branch (.register 5) (.call cmp [.register 2, .register 4] [6, 7] (boolRet (.register 7)))
      (boolRet (.flag false)))
    (.branch (.register 5) (boolRet (.flag false))
      (.call cmp [.register 2, .register 4] [6, 7] (boolRet (.register 7)))))

def isizeBody (size : Fin p) : Command p :=
  .load (.register 0) 2 15 3 { CompiledTrie.failCases with
    bit := .call size [.register 2] [4]
      (.allocate 5 (.bit (.flag false) (.register 4)) (.ret [.register 5])) }

/-- The bodies of all arithmetic procedures. -/
structure Procedures.Matches (d : Procedures p) (code : Code p) : Prop where
  add : code d.add = addBody d.add
  sub : code d.sub = subBody d.sub
  cmp : code d.cmp = cmpBody d.cmp
  lenLe : code d.lenLe = lenLeBody d.lenLe
  mul : code d.mul = mulBody d.mul d.add
  div : code d.div = divBody d.div d.cmp d.sub
  halve : code d.halve = halveBody d.halve
  size : code d.size = sizeBody d.size d.halve
  mkInt : code d.mkInt = mkIntBody
  addSigned : code d.addSigned = addSignedBody d.add d.cmp d.sub d.mkInt
  mulAny : code d.mulAny = mulAnyBody d.lenLe d.mul
  iadd : code d.iadd = iaddBody d.addSigned
  isub : code d.isub = isubBody d.addSigned
  imul : code d.imul = imulBody d.mulAny d.mkInt
  idiv : code d.idiv = idivBody d.div d.add d.mkInt
  imod : code d.imod = imodBody d.div d.sub d.mkInt
  ilt : code d.ilt = iltBody d.cmp
  ile : code d.ile = ileBody d.cmp
  ieq : code d.ieq = ieqBody d.cmp
  isize : code d.isize = isizeBody d.size

/-- The procedure implementing an integer operation. -/
def Procedures.intOp (d : Procedures p) : IntOp → Fin p
  | .add => d.iadd | .sub => d.isub | .mul => d.imul | .div => d.idiv | .mod => d.imod

/-- The procedure implementing a comparison. -/
def Procedures.cmpOp (d : Procedures p) : CmpOp → Fin p
  | .lt => d.ilt | .le => d.ile | .eq => d.ieq

/-! ## Correctness -/

variable {code : Code p} {d : Procedures p}

theorem len_eq (x : ℤ) : x.natAbs.bits.length = bits x := bits_length _

theorem iadd_compiled (hm : d.Matches code) (x y : ℤ) {h : Heap} (hh : Valid h) {px py : Ptr}
    (hx : TreeAt h px (reprInt x)) (hy : TreeAt h py (reprInt y)) :
    Yields code h (initialRegisters [.pointer px, .pointer py]) (code d.iadd)
      (1000 * IntOp.charge .add x y) (Returns h (reprInt (x + y))) := by
  rw [hm.iadd]
  refine Yields.le (B := 20 + (1 + 2 * 4 + addSignedBudget (bits x) (bits y) + 3)) ?_
    (by unfold addSignedBudget; simp only [IntOp.charge]; omega)
  refine Yields.loadTwo (by rsimp) (by rsimp) hx hy fun mx my tmx tmy => ?_
  have ha := addSigned_compiled code d hm.add hm.cmp hm.sub hm.mkInt hm.addSigned
    (decide (x < 0)) (decide (y < 0)) x.natAbs y.natAbs hh tmx tmy
  rw [len_eq, len_eq, ← eq_signed, ← eq_signed] at ha
  refine Yields.callTree (by rsimp) ha fun mid q hm' vm tq => ?_
  exact Yields.ret ⟨hm', vm, q, by rsimp, tq⟩ (by simp)

theorem isub_compiled (hm : d.Matches code) (x y : ℤ) {h : Heap} (hh : Valid h) {px py : Ptr}
    (hx : TreeAt h px (reprInt x)) (hy : TreeAt h py (reprInt y)) :
    Yields code h (initialRegisters [.pointer px, .pointer py]) (code d.isub)
      (1000 * IntOp.charge .sub x y) (Returns h (reprInt (x - y))) := by
  rw [hm.isub]
  refine Yields.le (B := 20 + (10 + (3 + (1 + 2 * 4 + addSignedBudget (bits x) (bits y) + 3))))
    ?_ (by unfold addSignedBudget; simp only [IntOp.charge]; omega)
  refine Yields.loadTwo (by rsimp) (by rsimp) hx hy fun mx my tmx tmy => ?_
  refine Yields.loadChain hh (by rsimp) tmy fun _ _ => ?_
  by_cases hy0 : y.natAbs.bits = []
  · rw [if_pos hy0]
    have : y = 0 := by have := (bits_eq_nil _).mp hy0; omega
    subst this
    exact Yields.ret ⟨Extends.refl h, hh, px, by rsimp, by simpa using hx⟩ (by simp)
  · rw [if_neg hy0]
    have hsub : x - y = signed (decide (x < 0)) x.natAbs + signed (!decide (y < 0)) y.natAbs := by
      rw [← signed_neg, ← eq_signed, ← eq_signed]; ring
    cases hs : decide (y < 0)
    · refine Yields.branch (b := false) (by rsimp [hs]) ?_
      have ha := addSigned_compiled code d hm.add hm.cmp hm.sub hm.mkInt hm.addSigned
        (decide (x < 0)) true x.natAbs y.natAbs hh tmx tmy
      rw [len_eq, len_eq] at ha
      refine Yields.callTree (by rsimp) ha fun mid q hm' vm tq => ?_
      refine Yields.ret ⟨hm', vm, q, by rsimp, ?_⟩ (by simp)
      rw [hsub, hs]; exact tq
    · refine Yields.branch (b := true) (by rsimp [hs]) ?_
      have ha := addSigned_compiled code d hm.add hm.cmp hm.sub hm.mkInt hm.addSigned
        (decide (x < 0)) false x.natAbs y.natAbs hh tmx tmy
      rw [len_eq, len_eq] at ha
      refine Yields.callTree (by rsimp) ha fun mid q hm' vm tq => ?_
      refine Yields.ret ⟨hm', vm, q, by rsimp, ?_⟩ (by simp)
      rw [hsub, hs]; exact tq

theorem mulAny_compiled (hm : d.Matches code) (a b : ℕ) {h : Heap} (hh : Valid h)
    {pa pb : Ptr} (ha : TreeAt h pa (Tree.chain a.bits)) (hb : TreeAt h pb (Tree.chain b.bits)) :
    Yields code h (initialRegisters [.pointer pa, .pointer pb]) (code d.mulAny)
      (500 * (a.bits.length + 1) * (b.bits.length + 1)) (Returns h (Tree.chain (a * b).bits)) := by
  rw [hm.mulAny]
  have hl := lenLe_compiled code d.lenLe hm.lenLe a.bits b.bits hh ha hb
  refine Yields.le (B := 1 + 2 * 2 + lenLeBudget a.bits.length +
    (3 + (1 + 2 * 2 + 400 * (a.bits.length + 1) * (b.bits.length + 1) + 3))) ?_
    (by unfold lenLeBudget; nlinarith)
  refine Yields.call (by rsimp) hl fun mid vals hv => ?_
  obtain ⟨hmid, rfl⟩ := hv
  rw [hmid]
  by_cases hle : a.bits.length ≤ b.bits.length
  · refine Yields.branch (b := true) (by rsimp [hle]) ?_
    have hy := mul_compiled code d.mul d.add hm.mul hm.add a.bits b.bits hh ha hb
    rw [mulL_bits] at hy
    refine Yields.callTree (by rsimp) (hy.le (B' := 400 * (a.bits.length + 1) *
      (b.bits.length + 1)) (by unfold mulBudget; nlinarith)) fun mid q hm' vm tq => ?_
    exact Yields.ret ⟨hm', vm, q, by rsimp, tq⟩ (by simp)
  · refine Yields.branch (b := false) (by rsimp [hle]) ?_
    have hy := mul_compiled code d.mul d.add hm.mul hm.add b.bits a.bits hh hb ha
    rw [mulL_bits_comm] at hy
    refine Yields.callTree (by rsimp) (hy.le (B' := 400 * (a.bits.length + 1) *
      (b.bits.length + 1)) (by unfold mulBudget; nlinarith)) fun mid q hm' vm tq => ?_
    exact Yields.ret ⟨hm', vm, q, by rsimp, tq⟩ (by simp)

theorem imul_compiled (hm : d.Matches code) (x y : ℤ) {h : Heap} (hh : Valid h) {px py : Ptr}
    (hx : TreeAt h px (reprInt x)) (hy : TreeAt h py (reprInt y)) :
    Yields code h (initialRegisters [.pointer px, .pointer py]) (code d.imul)
      (1000 * IntOp.charge .mul x y) (Returns h (reprInt (x * y))) := by
  rw [hm.imul]
  refine Yields.le (B := 20 + (1 + 2 * 2 + 500 * (bits x + 1) * (bits y + 1) +
    (3 + (3 + (1 + 2 * 2 + 30 + 3))))) ?_ (by simp only [IntOp.charge]; nlinarith)
  refine Yields.loadTwo (by rsimp) (by rsimp) hx hy fun mx my tmx tmy => ?_
  have ha := mulAny_compiled hm x.natAbs y.natAbs hh tmx tmy
  rw [len_eq, len_eq] at ha
  refine Yields.callTree (by rsimp) ha fun mid q hm' vm tq => ?_
  have hk := fun s => mkInt_compiled code d.mkInt hm.mkInt s (x.natAbs * y.natAbs) vm tq
  have hxy : x * y = signed (xor (decide (x < 0)) (decide (y < 0))) (x.natAbs * y.natAbs) := by
    rw [← signed_mul, ← eq_signed, ← eq_signed]
  have fin : ∀ (regs : Registers) s, regs 6 = .pointer q →
      xor (decide (x < 0)) (decide (y < 0)) = s →
      Yields code mid regs (mulSign d.mkInt s) (1 + 2 * 2 + 30 + 3) (Returns h (reprInt (x * y))) := by
    intro regs s h6 hs
    refine Yields.callTree (by rsimp [h6]) (hk s) fun mid2 q2 hm2 vm2 tq2 => ?_
    refine Yields.ret ⟨hm'.trans hm2, vm2, q2, by rsimp, ?_⟩ (by simp)
    rw [hxy, hs]; exact tq2
  cases hsx : decide (x < 0) <;> cases hsy : decide (y < 0)
  · exact Yields.branch (b := false) (by rsimp [hsx])
      (Yields.branch (b := false) (by rsimp [hsy]) (fin _ false (by rsimp) (by simp [hsx, hsy])))
  · exact Yields.branch (b := false) (by rsimp [hsx])
      (Yields.branch (b := true) (by rsimp [hsy]) (fin _ true (by rsimp) (by simp [hsx, hsy])))
  · exact Yields.branch (b := true) (by rsimp [hsx])
      (Yields.branch (b := false) (by rsimp [hsy]) (fin _ true (by rsimp) (by simp [hsx, hsy])))
  · exact Yields.branch (b := true) (by rsimp [hsx])
      (Yields.branch (b := true) (by rsimp [hsy]) (fin _ false (by rsimp) (by simp [hsx, hsy])))

theorem reprInt_natCast (n : ℕ) : reprInt (n : ℤ) = .bit false (Tree.chain n.bits) := by
  simp [reprInt]

theorem bits_mod_length {a b : ℕ} (hb : 0 < b) : (a % b).bits.length ≤ b.bits.length := by
  rw [bits_length, bits_length]; exact Nat.size_le_size (Nat.mod_lt _ hb).le

theorem bits_div_length (a b : ℕ) : (a / b).bits.length ≤ a.bits.length := by
  rw [bits_length, bits_length]; exact Nat.size_le_size (Nat.div_le_self _ _)

theorem idiv_compiled (hm : d.Matches code) (x y : ℤ) {h : Heap} (hh : Valid h) {px py : Ptr}
    (hx : TreeAt h px (reprInt x)) (hy : TreeAt h py (reprInt y)) :
    Yields code h (initialRegisters [.pointer px, .pointer py]) (code d.idiv)
      (1000 * IntOp.charge .div x y) (Returns h (reprInt (x / y))) := by
  rw [hm.idiv]
  have hdiv : divBudget (bits x) (bits y) ≤ 800 * (bits x + bits y + 1) ^ 2 := by
    unfold divBudget; nlinarith
  have hS1 : bits x + bits y + 1 ≤ (bits x + bits y + 1) ^ 2 := by nlinarith
  refine Yields.le (B := 20 + (10 + (1 + 2 * 2 + divBudget (bits x) (bits y) +
    (3 + (10 + (1 + 2 * 3 + addBudget (bits x) 0 + 41)))))) ?_
    (by unfold addBudget; simp only [IntOp.charge]; omega)
  refine Yields.loadTwo (by rsimp) (by rsimp) hx hy fun mx my tmx tmy => ?_
  refine Yields.loadChain hh (by rsimp) tmy fun _ _ => ?_
  by_cases hy0 : y.natAbs.bits = []
  · rw [if_pos hy0]
    have : y = 0 := by have := (bits_eq_nil _).mp hy0; omega
    subst this
    refine Yields.le (B := 8 + 3) ?_ (by omega)
    refine Yields.allocBit hh (b := false) (by rsimp) (by rsimp) (TreeAt.zero hh) fun e2 v2 t2 => ?_
    exact Yields.ret ⟨e2, v2, h.length, by rsimp, by simpa [reprInt] using t2⟩ (by simp)
  · rw [if_neg hy0]
    have hd : 0 < y.natAbs := by
      rcases Nat.eq_zero_or_pos y.natAbs with h0 | h0
      · exact absurd ((bits_eq_nil _).mpr h0) hy0
      · exact h0
    have hq := div_compiled code d.div d.cmp d.sub hm.div hm.cmp hm.sub x.natAbs.bits
      y.natAbs.bits (bits_norm _) (by rw [lval_bits]; exact hd) hh tmx tmy
    rw [divmodL_bits _ _ hd, len_eq, len_eq] at hq
    refine Yields.call (by rsimp) hq fun mid vals hv => ?_
    obtain ⟨hm1, vm1, q, r, rfl, tq, tr⟩ := hv
    have hres := (ediv_emod_signed (decide (x < 0)) (decide (y < 0)) x.natAbs y.natAbs hd).1
    rw [← eq_signed, ← eq_signed] at hres
    rw [hres]
    have hneg : ∀ (regs : Registers) (rp : Ptr) (m : ℕ), regs 5 = .flag (decide (y < 0)) →
        (∀ r', r' ≠ 13 → True) → regs (if True then 0 else 0) = regs 0 →
        Extends mid mid → True := fun _ _ _ _ _ _ _ => trivial
    clear hneg
    have negSign_ok : ∀ {h2 : Heap} (regs : Registers) (r : Register) (rp : Ptr) (m : ℕ),
        Valid h2 → Extends h h2 → regs 5 = .flag (decide (y < 0)) → regs r = .pointer rp →
        TreeAt h2 rp (Tree.chain m.bits) →
        Yields code h2 regs (negSign d.mkInt r) 41 (Returns h (reprInt (signed (!decide (y < 0)) m))) := by
      intro h2 regs r rp m v2 e2 h5 hr t2
      refine Yields.le (B := 3 + (1 + 2 * 2 + 30 + 3)) ?_ (by omega)
      cases hs : decide (y < 0)
      · refine Yields.branch (b := false) (by rsimp [h5, hs]) ?_
        have hk := mkInt_compiled code d.mkInt hm.mkInt true m v2 t2
        refine Yields.callTree (by rsimp [hr]) hk fun mid2 q2 hm2 vm2 tq2 => ?_
        exact Yields.ret ⟨e2.trans hm2, vm2, q2, by rsimp, by simpa using tq2⟩ (by simp)
      · refine Yields.branch (b := true) (by rsimp [h5, hs]) ?_
        have hk := mkInt_compiled code d.mkInt hm.mkInt false m v2 t2
        refine Yields.callTree (by rsimp [hr]) hk fun mid2 q2 hm2 vm2 tq2 => ?_
        exact Yields.ret ⟨e2.trans hm2, vm2, q2, by rsimp, by simpa using tq2⟩ (by simp)
    unfold quotSigned
    cases hsx : decide (x < 0)
    · refine Yields.le (B := 3 + (1 + 2 * 2 + 30 + 3)) ?_ (by omega)
      refine Yields.branch (b := false) (by rsimp [hsx]) ?_
      have hk := mkInt_compiled code d.mkInt hm.mkInt (decide (y < 0)) (x.natAbs / y.natAbs) vm1 tq
      refine Yields.callTree (by rsimp) hk fun mid2 q2 hm2 vm2 tq2 => ?_
      exact Yields.ret ⟨hm1.trans hm2, vm2, q2, by rsimp, by simpa using tq2⟩ (by simp)
    · refine Yields.branch (b := true) (by rsimp [hsx]) ?_
      simp only [↓reduceIte]
      refine Yields.loadChain vm1 (by rsimp) tr fun _ _ => ?_
      by_cases hr0 : (x.natAbs % y.natAbs).bits = []
      · rw [if_pos hr0]
        rw [if_pos ((bits_eq_nil _).mp hr0)]
        exact (negSign_ok _ 8 q _ vm1 hm1 (by rsimp) (by rsimp) tq).le (by omega)
      · rw [if_neg hr0]
        rw [if_neg (fun h0 => hr0 ((bits_eq_nil _).mpr h0))]
        have ha := add_compiled code d.add hm.add (x.natAbs / y.natAbs).bits [] true vm1 tq
          (TreeAt.zero vm1)
        rw [addL_bits_one] at ha
        refine Yields.callTree (by rsimp) (ha.le (B' := addBudget (bits x) 0)
          (by have := bits_div_length x.natAbs y.natAbs; rw [len_eq] at this
              unfold addBudget; simp; omega)) fun mid2 q2 hm2 vm2 tq2 => ?_
        exact negSign_ok _ 12 q2 _ vm2 (hm1.trans hm2) (by rsimp) (by rsimp) tq2

theorem imod_compiled (hm : d.Matches code) (x y : ℤ) {h : Heap} (hh : Valid h) {px py : Ptr}
    (hx : TreeAt h px (reprInt x)) (hy : TreeAt h py (reprInt y)) :
    Yields code h (initialRegisters [.pointer px, .pointer py]) (code d.imod)
      (1000 * IntOp.charge .mod x y) (Returns h (reprInt (x % y))) := by
  rw [hm.imod]
  have hdiv : divBudget (bits x) (bits y) ≤ 800 * (bits x + bits y + 1) ^ 2 := by
    unfold divBudget; nlinarith
  have hS1 : bits x + bits y + 1 ≤ (bits x + bits y + 1) ^ 2 := by nlinarith
  refine Yields.le (B := 20 + (10 + (1 + 2 * 2 + divBudget (bits x) (bits y) +
    (3 + (10 + (1 + 2 * 3 + subBudget (bits y) (bits y) + (1 + 2 * 2 + 30 + 3))))))) ?_
    (by unfold subBudget; simp only [IntOp.charge]; omega)
  refine Yields.loadTwo (by rsimp) (by rsimp) hx hy fun mx my tmx tmy => ?_
  refine Yields.loadChain hh (by rsimp) tmy fun _ _ => ?_
  by_cases hy0 : y.natAbs.bits = []
  · rw [if_pos hy0]
    have : y = 0 := by have := (bits_eq_nil _).mp hy0; omega
    subst this
    exact Yields.ret ⟨Extends.refl h, hh, px, by rsimp, by simpa using hx⟩ (by simp; omega)
  · rw [if_neg hy0]
    have hd : 0 < y.natAbs := by
      rcases Nat.eq_zero_or_pos y.natAbs with h0 | h0
      · exact absurd ((bits_eq_nil _).mpr h0) hy0
      · exact h0
    have hq := div_compiled code d.div d.cmp d.sub hm.div hm.cmp hm.sub x.natAbs.bits
      y.natAbs.bits (bits_norm _) (by rw [lval_bits]; exact hd) hh tmx tmy
    rw [divmodL_bits _ _ hd, len_eq, len_eq] at hq
    refine Yields.call (by rsimp) hq fun mid vals hv => ?_
    obtain ⟨hm1, vm1, q, r, rfl, tq, tr⟩ := hv
    have hres := (ediv_emod_signed (decide (x < 0)) (decide (y < 0)) x.natAbs y.natAbs hd).2
    rw [← eq_signed, ← eq_signed] at hres
    rw [hres, reprInt_natCast]
    have mk0 : ∀ (regs : Registers) (rp : Ptr) (m : ℕ) {h2 : Heap}, Valid h2 → Extends h h2 →
        regs 9 = .pointer rp ∨ True → TreeAt h2 rp (Tree.chain m.bits) →
        (∀ a, values regs [.flag false, a] = [.flag false, (a.eval regs)]) → True :=
      fun _ _ _ _ _ _ _ _ _ => trivial
    clear mk0
    unfold remSigned
    cases hsx : decide (x < 0)
    · refine Yields.le (B := 3 + (1 + 2 * 2 + 30 + 3)) ?_ (by omega)
      refine Yields.branch (b := false) (by rsimp [hsx]) ?_
      have hk := mkInt_compiled code d.mkInt hm.mkInt false (x.natAbs % y.natAbs) vm1 tr
      refine Yields.callTree (by rsimp) hk fun mid2 q2 hm2 vm2 tq2 => ?_
      refine Yields.ret ⟨hm1.trans hm2, vm2, q2, by rsimp, ?_⟩ (by simp)
      simpa [reprInt_signed] using tq2
    · refine Yields.branch (b := true) (by rsimp [hsx]) ?_
      simp only [↓reduceIte]
      refine Yields.loadChain vm1 (by rsimp) tr fun _ _ => ?_
      by_cases hr0 : (x.natAbs % y.natAbs).bits = []
      · rw [if_pos hr0, if_pos ((bits_eq_nil _).mp hr0)]
        refine Yields.le (B := 1 + 2 * 2 + 30 + 3) ?_ (by omega)
        have hk := mkInt_compiled code d.mkInt hm.mkInt false (x.natAbs % y.natAbs) vm1 tr
        refine Yields.callTree (by rsimp) hk fun mid2 q2 hm2 vm2 tq2 => ?_
        refine Yields.ret ⟨hm1.trans hm2, vm2, q2, by rsimp, ?_⟩ (by simp)
        have := (bits_eq_nil _).mp hr0
        simpa [reprInt_signed, this] using tq2
      · rw [if_neg hr0, if_neg (fun h0 => hr0 ((bits_eq_nil _).mpr h0))]
        have hs := sub_compiled code d.sub hm.sub y.natAbs.bits (x.natAbs % y.natAbs).bits false
          vm1 (tmy.mono hm1) tr
        refine Yields.call (by rsimp) (hs.le (B' := subBudget (bits y) (bits y))
          (by have := bits_mod_length (a := x.natAbs) hd; rw [len_eq] at this ⊢
              unfold subBudget; omega)) fun mid2 vals2 hv2 => ?_
        obtain ⟨hm2, vm2, q2, rfl, tq2⟩ := hv2
        rw [subL_bits _ _ (Nat.mod_lt _ hd).le] at tq2
        have hk := mkInt_compiled code d.mkInt hm.mkInt false (y.natAbs - x.natAbs % y.natAbs) vm2 tq2
        refine Yields.callTree (by rsimp) hk fun mid3 q3 hm3 vm3 tq3 => ?_
        refine Yields.ret ⟨hm1.trans (hm2.trans hm3), vm3, q3, by rsimp, ?_⟩ (by simp)
        simpa [reprInt_signed] using tq3

/-- The stored result of a comparison: a bit cell over the empty cell. -/
theorem cmp_compiled' (hm : d.Matches code) {h : Heap} (hh : Valid h) (a b : ℕ) {pa pb : Ptr}
    (ha : TreeAt h pa (Tree.chain a.bits)) (hb : TreeAt h pb (Tree.chain b.bits)) :
    Yields code h (initialRegisters [.pointer pa, .pointer pb]) (code d.cmp)
      (cmpBudget a.bits.length b.bits.length)
      (CmpOut h (decide (a < b), decide (a = b))) := by
  have := cmp_compiled code d.cmp hm.cmp a.bits b.bits hh ha hb
  rwa [cmpL_bits] at this

theorem icmp_compiled (hm : d.Matches code) (op : CmpOp) (x y : ℤ) {h : Heap} (hh : Valid h)
    {px py : Ptr} (hx : TreeAt h px (reprInt x)) (hy : TreeAt h py (reprInt y)) :
    Yields code h (initialRegisters [.pointer px, .pointer py]) (code (d.cmpOp op))
      (1000 * op.charge x y) (Returns h (.bit (op.eval x y) .nil)) := by
  have hcb : cmpBudget (bits x) (bits y) + 40 ≤ 100 * (bits x + bits y + 1) := by
    unfold cmpBudget; omega
  have ex := Int.natAbs_eq x
  have ey := Int.natAbs_eq y
  refine Yields.le (B := 20 + (3 + (3 + (1 + 2 * 2 + cmpBudget (bits x) (bits y) + (3 + 11)))))
    ?_ (by unfold CmpOp.charge; omega)
  have hcxy := fun {pa pb : Ptr} => cmp_compiled' hm hh x.natAbs y.natAbs (pa := pa) (pb := pb)
  have hcyx := fun {pa pb : Ptr} => cmp_compiled' hm hh y.natAbs x.natAbs (pa := pa) (pb := pb)
  cases op
  · rw [show d.cmpOp .lt = d.ilt from rfl, hm.ilt]
    refine Yields.loadTwo (by rsimp) (by rsimp) hx hy fun mx my tmx tmy => ?_
    simp only [CmpOp.eval]
    by_cases hx0 : x < 0 <;> by_cases hy0 : y < 0
    · refine Yields.branch (b := true) (by rsimp [hx0]) (Yields.branch (b := true) (by rsimp [hy0]) ?_)
      have hc := hcyx tmy tmx
      rw [len_eq, len_eq] at hc
      refine Yields.call (by rsimp) (hc.le (B' := cmpBudget (bits x) (bits y))
        (by unfold cmpBudget; omega)) fun mid vals hv => ?_
      obtain ⟨rfl, rfl⟩ := hv
      rw [show decide (x < y) = decide (y.natAbs < x.natAbs) by rw [decide_eq_decide]; omega]
      exact (Yields.boolRet hh (by rsimp)).le (by omega)
    · refine Yields.branch (b := true) (by rsimp [hx0]) (Yields.branch (b := false) (by rsimp [hy0]) ?_)
      rw [show decide (x < y) = true by simp; omega]
      exact (Yields.boolRet hh (by rsimp)).le (by omega)
    · refine Yields.branch (b := false) (by rsimp [hx0]) (Yields.branch (b := true) (by rsimp [hy0]) ?_)
      rw [show decide (x < y) = false by simp; omega]
      exact (Yields.boolRet hh (by rsimp)).le (by omega)
    · refine Yields.branch (b := false) (by rsimp [hx0]) (Yields.branch (b := false) (by rsimp [hy0]) ?_)
      have hc := hcxy tmx tmy
      rw [len_eq, len_eq] at hc
      refine Yields.call (by rsimp) hc fun mid vals hv => ?_
      obtain ⟨rfl, rfl⟩ := hv
      rw [show decide (x < y) = decide (x.natAbs < y.natAbs) by rw [decide_eq_decide]; omega]
      exact (Yields.boolRet hh (by rsimp)).le (by omega)
  · rw [show d.cmpOp .le = d.ile from rfl, hm.ile]
    refine Yields.loadTwo (by rsimp) (by rsimp) hx hy fun mx my tmx tmy => ?_
    simp only [CmpOp.eval]
    by_cases hx0 : x < 0 <;> by_cases hy0 : y < 0
    · refine Yields.branch (b := true) (by rsimp [hx0]) (Yields.branch (b := true) (by rsimp [hy0]) ?_)
      have hc := hcyx tmy tmx
      rw [len_eq, len_eq] at hc
      refine Yields.call (by rsimp) (hc.le (B' := cmpBudget (bits x) (bits y))
        (by unfold cmpBudget; omega)) fun mid vals hv => ?_
      obtain ⟨rfl, rfl⟩ := hv
      by_cases hl : y.natAbs < x.natAbs
      · refine Yields.branch (b := true) (by rsimp [hl]) ?_
        rw [show decide (x ≤ y) = true by simp; omega]
        exact (Yields.boolRet hh (by rsimp)).le (by omega)
      · refine Yields.branch (b := false) (by rsimp [hl]) ?_
        rw [show decide (x ≤ y) = decide (y.natAbs = x.natAbs) by rw [decide_eq_decide]; omega]
        exact (Yields.boolRet hh (by rsimp)).le (by omega)
    · refine Yields.branch (b := true) (by rsimp [hx0]) (Yields.branch (b := false) (by rsimp [hy0]) ?_)
      rw [show decide (x ≤ y) = true by simp; omega]
      exact (Yields.boolRet hh (by rsimp)).le (by omega)
    · refine Yields.branch (b := false) (by rsimp [hx0]) (Yields.branch (b := true) (by rsimp [hy0]) ?_)
      rw [show decide (x ≤ y) = false by simp; omega]
      exact (Yields.boolRet hh (by rsimp)).le (by omega)
    · refine Yields.branch (b := false) (by rsimp [hx0]) (Yields.branch (b := false) (by rsimp [hy0]) ?_)
      have hc := hcxy tmx tmy
      rw [len_eq, len_eq] at hc
      refine Yields.call (by rsimp) hc fun mid vals hv => ?_
      obtain ⟨rfl, rfl⟩ := hv
      by_cases hl : x.natAbs < y.natAbs
      · refine Yields.branch (b := true) (by rsimp [hl]) ?_
        rw [show decide (x ≤ y) = true by simp; omega]
        exact (Yields.boolRet hh (by rsimp)).le (by omega)
      · refine Yields.branch (b := false) (by rsimp [hl]) ?_
        rw [show decide (x ≤ y) = decide (x.natAbs = y.natAbs) by rw [decide_eq_decide]; omega]
        exact (Yields.boolRet hh (by rsimp)).le (by omega)
  · rw [show d.cmpOp .eq = d.ieq from rfl, hm.ieq]
    refine Yields.loadTwo (by rsimp) (by rsimp) hx hy fun mx my tmx tmy => ?_
    simp only [CmpOp.eval]
    by_cases hx0 : x < 0 <;> by_cases hy0 : y < 0
    · refine Yields.branch (b := true) (by rsimp [hx0]) (Yields.branch (b := true) (by rsimp [hy0]) ?_)
      have hc := hcxy tmx tmy
      rw [len_eq, len_eq] at hc
      refine Yields.call (by rsimp) hc fun mid vals hv => ?_
      obtain ⟨rfl, rfl⟩ := hv
      rw [show decide (x = y) = decide (x.natAbs = y.natAbs) by rw [decide_eq_decide]; omega]
      exact (Yields.boolRet hh (by rsimp)).le (by omega)
    · refine Yields.branch (b := true) (by rsimp [hx0]) (Yields.branch (b := false) (by rsimp [hy0]) ?_)
      rw [show decide (x = y) = false by simp; omega]
      exact (Yields.boolRet hh (by rsimp)).le (by omega)
    · refine Yields.branch (b := false) (by rsimp [hx0]) (Yields.branch (b := true) (by rsimp [hy0]) ?_)
      rw [show decide (x = y) = false by simp; omega]
      exact (Yields.boolRet hh (by rsimp)).le (by omega)
    · refine Yields.branch (b := false) (by rsimp [hx0]) (Yields.branch (b := false) (by rsimp [hy0]) ?_)
      have hc := hcxy tmx tmy
      rw [len_eq, len_eq] at hc
      refine Yields.call (by rsimp) hc fun mid vals hv => ?_
      obtain ⟨rfl, rfl⟩ := hv
      rw [show decide (x = y) = decide (x.natAbs = y.natAbs) by rw [decide_eq_decide]; omega]
      exact (Yields.boolRet hh (by rsimp)).le (by omega)

theorem isize_compiled (hm : d.Matches code) (x : ℤ) {h : Heap} (hh : Valid h) {px : Ptr}
    (hx : TreeAt h px (reprInt x)) :
    Yields code h (initialRegisters [.pointer px]) (code d.isize)
      (1000 * (bits x + 1)) (Returns h (reprInt (bits x : ℤ))) := by
  rw [hm.isize]
  refine Yields.le (B := 10 + (1 + 2 * 1 + sizeBudget (bits x) + (8 + 3))) ?_
    (by unfold sizeBudget; omega)
  refine Yields.loadBit (by rsimp) hx fun mx tmx => ?_
  have hs := size_compiled code d.size d.halve hm.size hm.halve x.natAbs.bits hh tmx
  rw [len_eq] at hs
  refine Yields.callTree (by rsimp) hs fun mid q hm1 vm tq => ?_
  refine Yields.allocBit vm (b := false) (by rsimp) (by rsimp) tq fun e2 v2 t2 => ?_
  refine Yields.ret ⟨hm1.trans e2, v2, mid.length, by rsimp, ?_⟩ (by simp)
  rw [reprInt_natCast]; exact t2

/-- Every integer operation, dispatched by its identifier. -/
theorem intOp_compiled (hm : d.Matches code) (op : IntOp) (x y : ℤ) {h : Heap} (hh : Valid h)
    {px py : Ptr} (hx : TreeAt h px (reprInt x)) (hy : TreeAt h py (reprInt y)) :
    Yields code h (initialRegisters [.pointer px, .pointer py]) (code (d.intOp op))
      (1000 * op.charge x y) (Returns h (reprInt (op.eval x y))) := by
  cases op
  · exact iadd_compiled hm x y hh hx hy
  · exact isub_compiled hm x y hh hx hy
  · exact imul_compiled hm x y hh hx hy
  · exact idiv_compiled hm x y hh hx hy
  · exact imod_compiled hm x y hh hx hy

end MWIS.Fun.Arith

end
