module

public import MWIS.FPTRegisterClaim
public import MWIS.FPTTreeParse
public import MWIS.RegisterFlagKeys

/-!
# Running fixed `Fun` programs from register code

A wrapper procedure runs one fixed closed `Fun` program on tree inputs held in
its argument registers: it calls a procedure that builds the stored program
`prog.encode`, allocates the environment (a cons spine of the input pointers),
and calls the interpreter. Its correctness follows from two contracts:

* `EvalSpec code eval K`: the interpreter procedure `eval`, called with a pointer
  to `e.encode` and a pointer to a stored environment, returns the stored value
  `e.denote env` within `K * e.cost env` events;
* `BuildsTree code build t B`: the procedure `build`, called without arguments,
  returns a pointer to the tree `t` within `B` events.

`wrap2_compiled` and `wrap5_compiled` give the wrappers for two and five tree
inputs. `constsSpec` instantiates the constants stage (`FPTRegister.ConstsSpec`)
with the program `constsProg` and proves its polynomial budget
(`constsBudgetBound`). `funStageSpec` turns a denotation equation and a cost bound
of a five-input program (`ProgFunStage`) into the numerical stage contract
`FPTRegister.FunStageSpec`.
-/

@[expose] public section

namespace MWIS.FPTRunFun

open MWIS.PointerMemory MWIS.RegisterMachine MWIS.Fun MWIS.FunLP
open MWIS.FPTTrees MWIS.FPTRegister MWIS.FPTTreeParse MWIS.RegisterFlagKeys
open MWIS.RegisterComponentSolve (HardBudget)

variable {p : ℕ}

/-! ## The interpreter and builder contracts -/

/-- The interpreter contract: on a stored expression and a stored environment, the
procedure `eval` returns the stored value of the expression within `K` times its
cost. -/
def EvalSpec (code : Code p) (eval : Fin p) (K : ℕ) : Prop :=
  ∀ {Γ : List Ty} {τ : Ty} (e : Expr Γ τ) (env : Env Γ) {h : Heap}, Valid h →
    ∀ {ep envp : Ptr}, TreeAt h ep e.encode → EnvAt Γ h envp env →
      ∃ out vp, Extends h out ∧ Valid out ∧ ValAt τ out vp (e.denote env) ∧
        Within code h (initialRegisters [.pointer ep, .pointer envp]) (code eval)
          [.pointer vp] out (K * e.cost env)

/-- The builder contract: called without arguments, the procedure `build` returns a
pointer to the constant tree `t` within `B` events. -/
def BuildsTree (code : Code p) (build : Fin p) (t : Tree) (B : ℕ) : Prop :=
  ∀ {h : Heap}, Valid h → ∃ out q, Extends h out ∧ Valid out ∧ TreeAt out q t ∧
    Within code h (initialRegisters []) (code build) [.pointer q] out B

/-! ## Two tree inputs -/

/-- Arguments 0, 1 = the two input trees. -/
def wrap2Body (build eval : Fin p) : Command p :=
  .call build [] [2]
  (.allocate 3 (.cons (.register 1) .null)
  (.allocate 4 (.cons (.register 0) (.register 3))
  (.call eval [.register 2, .register 4] [5]
  (.ret [.register 5]))))

/-- The two-input wrapper runs `prog` on its two input trees. -/
theorem wrap2_compiled (code : Code p) (self build eval : Fin p)
    (hself : code self = wrap2Body build eval) {K B : ℕ} (heval : EvalSpec code eval K)
    (prog : Expr [.tree, .tree] .tree) (hbuild : BuildsTree code build prog.encode B)
    {h : Heap} (hh : Valid h) {p0 p1 : Ptr} {t0 t1 : Tree}
    (h0 : TreeAt h p0 t0) (h1 : TreeAt h p1 t1) :
    ∃ out q, Extends h out ∧ Valid out ∧ TreeAt out q (prog.denote (t0, t1, ())) ∧
      Within code h (initialRegisters [.pointer p0, .pointer p1]) (code self) [.pointer q] out
        (B + K * prog.cost (t0, t1, ()) + 40) := by
  obtain ⟨o1, ep, e1, v1, hep, w1⟩ := hbuild hh
  obtain ⟨e2, v2, c2⟩ := alloc_consT v1 (h1.mono e1) (TreeAt.zero v1)
  obtain ⟨e3, v3, c3⟩ := alloc_consT v2 ((h0.mono e1).mono e2) c2
  have henv : EnvAt [.tree, .tree] (o1 ++ [Cell.cons p1 0] ++ [Cell.cons p0 o1.length])
      (o1 ++ [Cell.cons p1 0]).length (t0, t1, ()) := c3
  obtain ⟨o4, vp, e4, v4, hv, w4⟩ := heval prog (t0, t1, ()) v3 ((hep.mono e2).mono e3) henv
  refine ⟨o4, vp, (e1.trans (e2.trans e3)).trans e4, v4, hv, ?_⟩
  rw [hself]
  refine (call_of (by reg_simp) w1
    (Within.allocate (c := Cell.cons p1 0) (by reg_simp)
    (Within.allocate (c := Cell.cons p0 o1.length) (by reg_simp)
    (call_of (by reg_simp) w4 (ret_values (by reg_simp) le_rfl))))).mono ?_
  simp only [CellExpr.args, List.length_cons, List.length_nil]
  omega

/-! ## Five tree inputs -/

/-- Arguments 0, …, 4 = the five input trees. -/
def wrap5Body (build eval : Fin p) : Command p :=
  .call build [] [5]
  (.allocate 6 (.cons (.register 4) .null)
  (.allocate 7 (.cons (.register 3) (.register 6))
  (.allocate 8 (.cons (.register 2) (.register 7))
  (.allocate 9 (.cons (.register 1) (.register 8))
  (.allocate 10 (.cons (.register 0) (.register 9))
  (.call eval [.register 5, .register 10] [11]
  (.ret [.register 11])))))))

/-- The five-input wrapper runs `prog` on its five input trees. -/
theorem wrap5_compiled (code : Code p) (self build eval : Fin p)
    (hself : code self = wrap5Body build eval) {K B : ℕ} (heval : EvalSpec code eval K)
    (prog : Expr [.tree, .tree, .tree, .tree, .tree] .tree)
    (hbuild : BuildsTree code build prog.encode B)
    {h : Heap} (hh : Valid h) {p0 p1 p2 p3 p4 : Ptr} {t0 t1 t2 t3 t4 : Tree}
    (h0 : TreeAt h p0 t0) (h1 : TreeAt h p1 t1) (h2 : TreeAt h p2 t2) (h3 : TreeAt h p3 t3)
    (h4 : TreeAt h p4 t4) :
    ∃ out q, Extends h out ∧ Valid out ∧
      TreeAt out q (prog.denote (t0, t1, t2, t3, t4, ())) ∧
      Within code h (initialRegisters [.pointer p0, .pointer p1, .pointer p2, .pointer p3,
          .pointer p4]) (code self) [.pointer q] out
        (B + K * prog.cost (t0, t1, t2, t3, t4, ()) + 80) := by
  obtain ⟨o1, ep, e1, v1, hep, w1⟩ := hbuild hh
  obtain ⟨e2, v2, c2⟩ := alloc_consT v1 (h4.mono e1) (TreeAt.zero v1)
  set o2 := o1 ++ [Cell.cons p4 0]
  obtain ⟨e3, v3, c3⟩ := alloc_consT v2 ((h3.mono e1).mono e2) c2
  set o3 := o2 ++ [Cell.cons p3 o1.length]
  obtain ⟨e4, v4, c4⟩ := alloc_consT v3 (((h2.mono e1).mono e2).mono e3) c3
  set o4 := o3 ++ [Cell.cons p2 o2.length]
  obtain ⟨e5, v5, c5⟩ := alloc_consT v4 ((((h1.mono e1).mono e2).mono e3).mono e4) c4
  set o5 := o4 ++ [Cell.cons p1 o3.length]
  obtain ⟨e6, v6, c6⟩ := alloc_consT v5 (((((h0.mono e1).mono e2).mono e3).mono e4).mono e5) c5
  set o6 := o5 ++ [Cell.cons p0 o4.length]
  have e26 := e2.trans (e3.trans (e4.trans (e5.trans e6)))
  have henv : EnvAt [.tree, .tree, .tree, .tree, .tree] o6 o5.length (t0, t1, t2, t3, t4, ()) := c6
  obtain ⟨o7, vp, e7, v7, hv, w7⟩ := heval prog (t0, t1, t2, t3, t4, ()) v6 (hep.mono e26) henv
  refine ⟨o7, vp, (e1.trans e26).trans e7, v7, hv, ?_⟩
  rw [hself]
  refine (call_of (by reg_simp) w1
    (Within.allocate (c := Cell.cons p4 0) (by reg_simp)
    (Within.allocate (c := Cell.cons p3 o1.length) (by reg_simp)
    (Within.allocate (c := Cell.cons p2 o2.length) (by (reg_simp; simp [o2]))
    (Within.allocate (c := Cell.cons p1 o3.length) (by (reg_simp; simp [o2, o3]))
    (Within.allocate (c := Cell.cons p0 o4.length) (by (reg_simp; simp [o2, o3, o4]))
    (call_of (by (reg_simp; simp [o2, o3, o4, o5])) w7 (ret_values (by reg_simp) le_rfl)))))))).mono ?_
  simp only [CellExpr.args, List.length_cons, List.length_nil]
  omega

/-! ## The constants stage -/

theorem bits_le_natAbs (z : ℤ) : bits z ≤ z.natAbs := Nat.size_le.mpr Nat.lt_two_pow_self

theorem items_length (t : Tree) : t.items.length = t.spine := by
  induction t <;> simp_all [Tree.items, Tree.spine]

theorem lengthF_cost (a : Ty) (l : List a.denote) :
    Expr.cost (lengthF a) (l, ()) ≤ (l.length + 1) * (l.length + 8) := by
  have h := cost_foldl_le_prefix (Γ := [.list a]) v0 (.int 0) (.arith .add v1 (.int 1)) (l, ())
    (l.length + 6) (by
      intro j hj
      change j < l.length at hj
      simp only [Expr.cost, Var.index, IntOp.charge, Expr.denote, Var.get, IntOp.eval]
      have hf : (l.take j).foldl (fun acc (_ : a.denote) => acc + 1) (0 : ℤ) = j := by
        rw [lengthF_fold]; simp [List.length_take]; omega
      rw [hf]
      have : bits (j : ℤ) ≤ j := by have := bits_le_natAbs (j : ℤ); simpa using this
      have h1 : bits (1 : ℤ) = 1 := rfl
      omega)
  simp only [Expr.cost, Var.index, Expr.denote, Var.get] at h
  calc Expr.cost (lengthF a) (l, ()) ≤ 0 + 1 + 1 + l.length * (l.length + 6 + 1) + 1 := h
    _ ≤ _ := by nlinarith

/-- The cost of the constants program, quadratic in the two spine lengths. -/
theorem consts_cost (a b : Tree) : consts.costAt (a, b) ≤ 64 * (a.spine + b.spine + 2) ^ 2 := by
  have ha := lengthF_cost .tree a.items
  have hb := lengthF_cost .tree b.items
  have hla : Expr.denote (lengthF Ty.tree) (a.items, ()) = (a.items.length : ℤ) :=
    lengthF_apply .tree _
  have hlb : Expr.denote (lengthF Ty.tree) (b.items, ()) = (b.items.length : ℤ) :=
    lengthF_apply .tree _
  simp only [consts, Fn.costAt, Expr.cost, cost_call, Expr.denote, Var.get, denote_call, Var.index,
    IntOp.charge, IntOp.eval, Fn.apply]
  rw [hla, hlb]
  simp only [items_length] at ha hb ⊢
  generalize a.spine = n at ha ⊢
  generalize b.spine = m at hb ⊢
  have e1 : bits (3 * (n : ℤ)) ≤ 3 * n := by have := bits_le_natAbs (3 * (n : ℤ)); omega
  have e2 : bits (m : ℤ) ≤ m := by have := bits_le_natAbs (m : ℤ); omega
  have e3 : bits (n : ℤ) ≤ n := by have := bits_le_natAbs (n : ℤ); omega
  have e4 : bits (3 * (n : ℤ) + m) ≤ 3 * n + m := by
    have := bits_le_natAbs (3 * (n : ℤ) + m); omega
  have e5 : (3 * (n : ℤ) + m + 4).toNat = 3 * n + m + 4 := by omega
  have b3 : bits (3 : ℤ) = 2 := rfl
  have b4 : bits (4 : ℤ) = 3 := rfl
  have b1 : bits (1 : ℤ) = 1 := rfl
  have b0 : bits (0 : ℤ) = 0 := rfl
  rw [e5, b3, b4, b1, b0]
  nlinarith

/-- The constants stage as a two-input program. -/
def constsProg : Expr [.tree, .tree] .tree := call consts (.pair v0 v1)

theorem constsProg_denote (a b : Tree) : constsProg.denote (a, b, ()) = consts.apply (a, b) := by
  simp [constsProg, Expr.denote, Var.get]

theorem constsProg_cost (a b : Tree) :
    constsProg.cost (a, b, ()) ≤ 64 * (a.spine + b.spine + 2) ^ 2 + 5 := by
  have h := consts_cost a b
  simp only [constsProg, cost_call, Expr.cost, Var.index, Expr.denote, Var.get]
  omega

theorem spine_wordsTree {n : ℕ} (ws : List (EfficientSearch.Bits n)) :
    (wordsTree ws).spine = ws.length := by
  rw [wordsTree, listTree, spine_ofList, List.length_map]

/-- The budget of the constants stage. -/
def constsBudget (K B : ℕ) : ℕ → ℕ → ℕ → ℕ :=
  fun _W n m => B + K * (64 * (n + m + 2) ^ 2 + 5) + 40

/-- **The constants stage.** The two-input wrapper running `constsProg` meets the
constants contract. -/
theorem constsSpec (code : Code p) (self build eval : Fin p)
    (hself : code self = wrap2Body build eval) {K B : ℕ} (heval : EvalSpec code eval K)
    (hbuild : BuildsTree code build constsProg.encode B) :
    ConstsSpec code self (constsBudget K B) := by
  intro W n m h hh rp ip hr hi
  obtain ⟨out, q, he, hv, hq, hw⟩ := wrap2_compiled code self build eval hself heval constsProg
    hbuild hh hr hi
  rw [constsProg_denote, consts_apply] at hq
  refine ⟨out, q, he, hv, hq, hw.mono ?_⟩
  have hc := constsProg_cost (wordsTree (RibbonTable.rangeWords W n))
    (wordsTree (GraphReachEncoded.rangeWords W m))
  rw [spine_wordsTree, spine_wordsTree, RibbonTable.rangeWords_length] at hc
  have hlm : (GraphReachEncoded.rangeWords W m).length = m := by simp [GraphReachEncoded.rangeWords]
  rw [hlm] at hc
  unfold constsBudget
  have := Nat.mul_le_mul_left K hc
  omega

/-- The constants budget is polynomial. -/
theorem constsBudgetBound (K B : ℕ) : ConstsBudgetBound (B + 69 * K + 40) (constsBudget K B) := by
  intro W n m
  unfold constsBudget
  have hY : 1 ≤ (n + m + 2) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hX2 : (n + m + 2) ^ 2 ≤ (n + m + W + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hXc : (n + m + W + 2) ^ 2 ≤ (n + m + W + 2) ^ (B + 69 * K + 40) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have h2c : B + 69 * K + 40 < 2 ^ (B + 69 * K + 40) := Nat.lt_two_pow_self
  have hK : K * (64 * (n + m + 2) ^ 2 + 5) ≤ 69 * K * (n + m + W + 2) ^ 2 := by
    have h1 : 64 * (n + m + 2) ^ 2 + 5 ≤ 69 * (n + m + W + 2) ^ 2 := by omega
    calc K * (64 * (n + m + 2) ^ 2 + 5) ≤ K * (69 * (n + m + W + 2) ^ 2) :=
          Nat.mul_le_mul_left K h1
      _ = 69 * K * (n + m + W + 2) ^ 2 := by ring
  have hB : B + 40 ≤ (B + 40) * (n + m + W + 2) ^ 2 :=
    Nat.le_mul_of_pos_right _ (hY.trans hX2)
  calc B + K * (64 * (n + m + 2) ^ 2 + 5) + 40
      ≤ (B + 69 * K + 40) * (n + m + W + 2) ^ 2 := by
        have e : (B + 69 * K + 40) * (n + m + W + 2) ^ 2 =
            (B + 40) * (n + m + W + 2) ^ 2 + 69 * K * (n + m + W + 2) ^ 2 := by ring
        rw [e]
        generalize (B + 40) * (n + m + W + 2) ^ 2 = U at hB
        generalize 69 * K * (n + m + W + 2) ^ 2 = V at hK
        generalize K * (64 * (n + m + 2) ^ 2 + 5) = T at hK
        omega
    _ ≤ 2 ^ (B + 69 * K + 40) * (n + m + W + 2) ^ (B + 69 * K + 40) :=
        Nat.mul_le_mul h2c.le hXc

/-! ## The numerical stage -/

/-- The input environment of the numerical stage. -/
abbrev stageEnv (W c : ℕ) {n m : ℕ} {left right : Fin m → Fin n}
    (R : EmbeddingFaces.Ribbon left right) (w : Fin n → ℚ) :
    Env [.tree, .tree, .tree, .tree, .tree] :=
  (columnsTree R, edgesTree W left right, wordsTree (RibbonTable.rangeWords W n),
    costsTree c (FPTHard.integerCosts left right w),
    bitsTree (GraphReachEncoded.word (fptWidth n m) (2 * rowCount R + 1)), ())

/-- A five-input program computes the numerical stage within the budget `pb`: on
every instance of `FPTRegister.FunStageSpec` its denotation is the output tree of
the decoded slack, and its cost is at most `pb W c R w`. -/
def ProgFunStage (prog : Expr [.tree, .tree, .tree, .tree, .tree] .tree) (coords : CoordFn)
    (pb : ℕ → ℕ → HardBudget) : Prop :=
  ∀ (W c : ℕ) {n m : ℕ} {left right : Fin m → Fin n} (R : EmbeddingFaces.Ribbon left right)
    (w : Fin n → ℚ) (hn0 : 0 < n), n < 2 ^ W → m < 2 ^ W →
    Incidence.Connected left right → ¬ Incidence.Bipartite left right → (∀ v, 0 ≤ w v) →
    Persistence.Optimal (EdgeTransport.Adj left right) w (fun _ => 1 / 2) →
    (∀ e, FPTHard.integerCosts left right w e < 2 ^ c) →
    prog.denote (stageEnv W c R w) = outputTree n m (slackValue coords R w ⟨0, hn0⟩) ∧
      prog.cost (stageEnv W c R w) ≤ pb W c R w

/-- The budget of the numerical stage run by the wrapper. -/
def stageBudget (K B : ℕ) (pb : ℕ → ℕ → HardBudget) : ℕ → ℕ → HardBudget :=
  fun W c {_n _m} {_left _right} R w => B + K * pb W c R w + 80

/-- **The numerical stage.** The five-input wrapper running a program that computes
the numerical stage meets the numerical stage contract. -/
theorem funStageSpec (code : Code p) (self build eval : Fin p)
    (hself : code self = wrap5Body build eval) {K B : ℕ} (heval : EvalSpec code eval K)
    (prog : Expr [.tree, .tree, .tree, .tree, .tree] .tree)
    (hbuild : BuildsTree code build prog.encode B) {coords : CoordFn}
    {pb : ℕ → ℕ → HardBudget} (hprog : ProgFunStage prog coords pb) :
    FunStageSpec code self coords (stageBudget K B pb) := by
  intro W c n m left right R w hn0 hn hmW hc hnb hw ho hcost h hh kp ep rp cp np hk he hr hcs hcn
  obtain ⟨hden, hpc⟩ := hprog W c R w hn0 hn hmW hc hnb hw ho hcost
  obtain ⟨out, q, hx, hv, hq, hwi⟩ := wrap5_compiled code self build eval hself heval prog hbuild
    hh hk he hr hcs hcn
  change TreeAt out q (prog.denote (stageEnv W c R w)) at hq
  rw [hden] at hq
  refine ⟨out, q, hx, hv, hq, hwi.mono ?_⟩
  change B + K * prog.cost (stageEnv W c R w) + 80 ≤ B + K * pb W c R w + 80
  have := Nat.mul_le_mul_left K hpc
  omega

/-- Multiplying a shape by `a` costs `a` in the exponent. -/
theorem shape_scale (a c d X : ℕ) (hX : 1 ≤ X) :
    a * GenericAccounting.shape c d X ≤ GenericAccounting.shape (c + a) d X := by
  unfold GenericAccounting.shape
  have e1 : 2 ^ ((c + a) * (d * d.size + 1)) =
      2 ^ (c * (d * d.size + 1)) * 2 ^ (a * (d * d.size + 1)) := by
    rw [← pow_add, add_mul]
  have e2 : X ^ (c + a) = X ^ c * X ^ a := pow_add _ _ _
  rw [e1, e2]
  have a1 : a ≤ 2 ^ (a * (d * d.size + 1)) :=
    (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_right (by norm_num)
      (Nat.le_mul_of_pos_right _ (by omega)))
  have a2 : 1 ≤ X ^ a := Nat.one_le_pow _ _ hX
  calc a * (2 ^ (c * (d * d.size + 1)) * X ^ c)
      ≤ 2 ^ (a * (d * d.size + 1)) * (2 ^ (c * (d * d.size + 1)) * X ^ c) :=
        Nat.mul_le_mul_right _ a1
    _ ≤ 2 ^ (a * (d * d.size + 1)) * (2 ^ (c * (d * d.size + 1)) * X ^ c) * X ^ a :=
        Nat.le_mul_of_pos_right _ a2
    _ = 2 ^ (c * (d * d.size + 1)) * 2 ^ (a * (d * d.size + 1)) * (X ^ c * X ^ a) := by ring

/-- A fixed-parameter cost bound for the program gives one for the wrapper budget. -/
theorem stageBudget_bound {c K B : ℕ} {pb : ℕ → ℕ → HardBudget} (hpb : FunBudgetBound c pb) :
    FunBudgetBound (c + (B + K + 80)) (stageBudget K B pb) := by
  intro W w0 n m left right R w hc hnb hw ho
  have h := hpb W w0 R w hc hnb hw ho
  have hs1 : 1 ≤ GenericAccounting.shape c (ComputedEmbeddedMatrices.globalRows R).length
      (n + m + W + w0 + 2) := by
    unfold GenericAccounting.shape
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hsc := shape_scale (B + K + 80) c (ComputedEmbeddedMatrices.globalRows R).length
    (n + m + W + w0 + 2) (by omega)
  have hK := Nat.mul_le_mul_left K h
  show B + K * pb W (NetworkWeights.width w0 n) R w + 80 ≤ _
  refine le_trans ?_ hsc
  generalize GenericAccounting.shape c (ComputedEmbeddedMatrices.globalRows R).length
    (n + m + W + w0 + 2) = S at hs1 hK
  nlinarith

end MWIS.FPTRunFun

end
