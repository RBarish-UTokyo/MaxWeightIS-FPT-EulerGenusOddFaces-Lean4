module

public import MWIS.FunNetworkDense

/-!
# `Fun` programs for the encoded network program

Closed `Fun` functions computing every piece of `encodedProgram`, assembled into
`networkFn`, together with their meanings. `networkFn_apply` states that
`networkFn` computes `encodedProgram` exactly; with `encodedProgram_eq` this is
the dense network program `FPTHard.program C D c rowsEquiv colsEquiv`.

Prepared 2026-10-23.
-/

@[expose] public section

namespace MWIS.FunNetwork

open MWIS.Fun MWIS.FunLP

/-! ## More variables -/

/-- The sixth variable. -/
abbrev v5 {Γ : List Ty} {a b c d e g : Ty} : Expr (a :: b :: c :: d :: e :: g :: Γ) g :=
  .var (.there (.there (.there (.there (.there .here)))))
/-- The seventh variable. -/
abbrev v6 {Γ : List Ty} {a b c d e g h : Ty} : Expr (a :: b :: c :: d :: e :: g :: h :: Γ) h :=
  .var (.there (.there (.there (.there (.there (.there .here))))))
/-- The eighth variable. -/
abbrev v7 {Γ : List Ty} {a b c d e g h i : Ty} :
    Expr (a :: b :: c :: d :: e :: g :: h :: i :: Γ) i :=
  .var (.there (.there (.there (.there (.there (.there (.there .here)))))))
/-- The ninth variable. -/
abbrev v8 {Γ : List Ty} {a b c d e g h i j : Ty} :
    Expr (a :: b :: c :: d :: e :: g :: h :: i :: j :: Γ) j :=
  .var (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))
/-- The tenth variable. -/
abbrev v9 {Γ : List Ty} {a b c d e g h i j k : Ty} :
    Expr (a :: b :: c :: d :: e :: g :: h :: i :: j :: k :: Γ) k :=
  .var (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))

/-! ## Types -/

/-- Integer lists. -/
abbrev tL : Ty := .list .int
/-- Per-edge input records. -/
abbrev tE : Ty := .prod tL (.prod tL (.prod tL .int))
/-- Arc records. -/
abbrev tArc : Ty := .prod .int (.prod .bool (.prod .int (.prod .int (.prod tL (.prod tL .int)))))
/-- Column records. -/
abbrev tCol : Ty := .prod .int (.prod tArc (.prod tL tL))
/-- Numbered column records. -/
abbrev tColI : Ty := .prod .int tCol
/-- Node records. -/
abbrev tNode : Ty := .prod .int (.prod .int tL)
/-- Row records. -/
abbrev tRow : Ty := .prod .int (.prod .int (.prod .int tNode))
/-- Equality-row templates. -/
abbrev tEq : Ty := .prod .int (.prod .int tNode)
/-- The network input: rows `f`, rank `r`, modulus `μ`, and edge records. -/
abbrev tIn : Ty := .prod .int (.prod .int (.prod .int (.list tE)))
/-- The dense program output. -/
abbrev tOut : Ty := .prod (.list tL) (.prod tL tL)

/-! ## Basic list functions -/

/-- `(x, l) ↦ x :: l`. -/
def consFn (a : Ty) : Fn (.prod a (.list a)) (.list a) := .cons (.fst v0) (.snd v0)

@[simp] theorem consFn_apply (a : Ty) (x : a.denote × List a.denote) :
    (consFn a).apply x = x.1 :: x.2 := rfl

/-- `(l, x) ↦ l.map (x :: ·)`. -/
def extendFn : Fn (.prod (.list tL) .int) (.list tL) :=
  call (mapWith (consFn .int)) (.pair (.snd v0) (.fst v0))

@[simp] theorem extendFn_apply (x : List (List ℤ) × ℤ) :
    extendFn.apply x = x.1.map (x.2 :: ·) := by
  rw [Fn.apply]; unfold extendFn
  simp only [denote_call, Expr.denote, Var.get, mapWith_apply, consFn_apply]

/-- Append two lists. -/
def appendFn (a : Ty) : Fn (.prod (.list a) (.list a)) (.list a) :=
  .foldl (call (rev a) (.fst v0)) (.snd v0) (.cons v0 v1)

@[simp] theorem appendFn_apply (a : Ty) (x : List a.denote × List a.denote) :
    (appendFn a).apply x = x.1 ++ x.2 := by
  rw [Fn.apply]; unfold appendFn
  simp only [Expr.denote, denote_call, Var.get, rev_apply]
  rw [foldl_cons_eq, List.reverse_reverse]

/-- Length of a list, as an integer. -/
def lengthFn (a : Ty) : Fn (.list a) .int := .foldl v0 (.int 0) (.arith .add v1 (.int 1))

theorem foldl_succ_int {α : Type*} (l : List α) (k : ℤ) :
    l.foldl (fun acc _ => acc + 1) k = k + l.length := by
  induction l generalizing k with
  | nil => simp
  | cons _ l ih => simp only [List.foldl_cons, ih, List.length_cons]; push_cast; ring

@[simp] theorem lengthFn_apply (a : Ty) (l : List a.denote) :
    (lengthFn a).apply l = (l.length : ℤ) := by
  simp only [lengthFn, Fn.apply, Expr.denote, Var.get, IntOp.eval]
  rw [foldl_succ_int]; simp

/-- `n ↦ 2 ^ n` for `n ≥ 0`. -/
def powFn : Fn .int .int := .iter v0 (.int 1) (.arith .mul (.int 2) v0)

@[simp] theorem powFn_apply (n : ℤ) : powFn.apply n = 2 ^ n.toNat := by
  simp only [powFn, Fn.apply, Expr.denote, Var.get, IntOp.eval]
  generalize n.toNat = k
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, pow_succ]; ring

/-- `n ↦ [0, …, 0]` of length `n`. -/
def replFn : Fn .int tL := .iter v0 .nil (.cons (.int 0) v0)

@[simp] theorem replFn_apply (n : ℤ) : replFn.apply n = List.replicate n.toNat 0 := by
  simp only [replFn, Fn.apply, Expr.denote, Var.get]
  generalize n.toNat = k
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, List.replicate_succ]

/-- Number the elements of a list from zero. -/
def indexFromFn (a : Ty) : Fn (.list a) (.list (.prod .int a)) :=
  call (rev (.prod .int a)) (.snd (.foldl v0 (.pair (.int 0) .nil)
    (.pair (.arith .add (.fst v1) (.int 1)) (.cons (.pair (.fst v1) v0) (.snd v1)))))

theorem indexFrom_foldl {α : Type*} (l : List α) (k : ℤ) (acc : List (ℤ × α)) :
    l.foldl (fun (s : ℤ × List (ℤ × α)) y => (s.1 + 1, (s.1, y) :: s.2)) (k, acc) =
      (k + l.length, (indexFrom k l).reverse ++ acc) := by
  induction l generalizing k acc with
  | nil => simp [indexFrom]
  | cons y l ih =>
    rw [List.foldl_cons, ih]
    simp only [indexFrom, List.length_cons, List.reverse_cons, List.append_assoc,
      List.singleton_append, Prod.mk.injEq, and_true]
    push_cast; ring

@[simp] theorem indexFromFn_apply (a : Ty) (l : List a.denote) :
    (indexFromFn a).apply l = indexFrom 0 l := by
  rw [Fn.apply]; unfold indexFromFn
  simp only [denote_call, Expr.denote, Var.get, IntOp.eval]
  rw [indexFrom_foldl, List.append_nil, rev_apply, List.reverse_reverse]

/-- Number the elements of a list from zero, with the powers `2^i`. -/
def indexPowFn : Fn (.list tE) (.list (.prod .int (.prod .int tE))) :=
  call (rev (.prod .int (.prod .int tE))) (.snd (.snd (.foldl v0 (.pair (.int 0) (.pair (.int 1) .nil))
    (.pair (.arith .add (.fst v1) (.int 1))
      (.pair (.arith .mul (.int 2) (.fst (.snd v1)))
        (.cons (.pair (.fst v1) (.pair (.fst (.snd v1)) v0)) (.snd (.snd v1))))))))

theorem indexPow_foldl {α : Type*} (l : List α) (k p : ℤ) (acc : List (ℤ × ℤ × α)) :
    l.foldl (fun (s : ℤ × ℤ × List (ℤ × ℤ × α)) y =>
        (s.1 + 1, 2 * s.2.1, (s.1, s.2.1, y) :: s.2.2)) (k, p, acc) =
      (k + l.length, p * 2 ^ l.length, (indexPow k p l).reverse ++ acc) := by
  induction l generalizing k p acc with
  | nil => simp [indexPow]
  | cons y l ih =>
    rw [List.foldl_cons, ih]
    simp only [indexPow, List.length_cons, List.reverse_cons, List.append_assoc,
      List.singleton_append, Prod.mk.injEq, and_true, pow_succ]
    constructor
    · push_cast; ring
    · ring

@[simp] theorem indexPowFn_apply (l : List (List ℤ × List ℤ × List ℤ × ℤ)) :
    indexPowFn.apply l = indexPow 0 1 l := by
  rw [Fn.apply]; unfold indexPowFn
  simp only [denote_call, Expr.denote, Var.get, IntOp.eval]
  rw [indexPow_foldl, List.append_nil, rev_apply, List.reverse_reverse]

/-! ## States, residues and residue addition -/

/-- `(_, k) ↦ [2k + 1, 2k + 2]`. -/
def stubPairFn : Fn (.prod .unit .int) tL :=
  .cons (.arith .add (.arith .mul (.int 2) (.snd v0)) (.int 1))
    (.cons (.arith .add (.arith .mul (.int 2) (.snd v0)) (.int 2)) .nil)

/-- The encoded states for `f` rows. -/
def statesFn : Fn .int tL :=
  .cons (.int 0) (call (flatMapWith stubPairFn) (.pair .unit (call range v0)))

@[simp] theorem statesFn_apply (f : ℤ) : statesFn.apply f = statesE f := by
  rw [Fn.apply]; unfold statesFn
  simp only [Expr.denote, denote_call, Var.get, flatMapWith_apply, range_apply]
  rfl

/-- `(μ, k) ↦ vecsE μ k`. -/
def vecsFn : Fn (.prod .int .int) (.list tL) :=
  .iter (.snd v0) (.cons .nil .nil)
    (call (flatMapWith extendFn) (.pair v0 (call range (.fst v1))))

theorem vecsE_succ' (μ : ℤ) (k : ℕ) :
    vecsE μ (k + 1) = (zrange μ).flatMap (fun x => (vecsE μ k).map (x :: ·)) := rfl

@[simp] theorem vecsFn_apply (x : ℤ × ℤ) : vecsFn.apply x = vecsE x.1 x.2.toNat := by
  rw [Fn.apply]; unfold vecsFn
  simp only [Expr.denote, denote_call, Var.get, flatMapWith_apply, range_apply, extendFn_apply]
  generalize x.2.toNat = k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, vecsE_succ']
    rfl

/-- `(r, μ) ↦ groupE r μ`. -/
def groupFn : Fn (.prod .int .int) (.list tL) :=
  call (flatMapWith extendFn) (.pair (call vecsFn (.pair (.snd v0) (.fst v0))) (call range (.int 2)))

@[simp] theorem groupFn_apply (x : ℤ × ℤ) : groupFn.apply x = groupE x.1 x.2 := by
  rw [Fn.apply]; unfold groupFn
  simp only [Expr.denote, denote_call, Var.get, flatMapWith_apply, range_apply, extendFn_apply,
    vecsFn_apply]
  rfl

/-- `(μ, g, h) ↦ zipWith (fun a b => (a + b) % μ) g h`. -/
def zipModFn : Fn (.prod .int (.prod tL tL)) tL :=
  call (rev .int) (.snd (.foldl (.fst (.snd v0)) (.pair (.snd (.snd v0)) .nil)
    (.listCase (.fst v1) v1
      (.pair v1 (.cons (.arith .mod (.arith .add v2 v0) (.fst v4)) (.snd v3))))))

/-- The step of `zipModFn`. -/
def zipStep (μ : ℤ) (s : List ℤ × List ℤ) (x : ℤ) : List ℤ × List ℤ :=
  match s.1 with
  | [] => s
  | y :: ys => (ys, ((x + y) % μ) :: s.2)

theorem zipStep_fold (μ : ℤ) (g h acc : List ℤ) :
    (g.foldl (zipStep μ) (h, acc)).2 = (List.zipWith (fun a b => (a + b) % μ) g h).reverse ++ acc := by
  induction g generalizing h acc with
  | nil => simp
  | cons x g ih =>
    cases h with
    | nil =>
      simp only [List.foldl_cons, zipStep, List.zipWith_nil_right, List.reverse_nil, List.nil_append]
      have hf : ∀ l : List ℤ, (l.foldl (zipStep μ) ([], acc)).2 = acc := by
        intro l; induction l with
        | nil => rfl
        | cons _ l ih2 => simpa [zipStep] using ih2
      exact hf g
    | cons y ys =>
      rw [List.foldl_cons]
      simp only [zipStep]
      rw [ih]
      simp

@[simp] theorem zipModFn_apply (x : ℤ × List ℤ × List ℤ) :
    zipModFn.apply x = List.zipWith (fun a b => (a + b) % x.1) x.2.1 x.2.2 := by
  rw [Fn.apply]; unfold zipModFn
  simp only [denote_call, Expr.denote, Var.get, IntOp.eval]
  rw [List.foldl_ext _ (zipStep x.1)]
  · rw [zipStep_fold, List.append_nil, rev_apply, List.reverse_reverse]
  · intro acc y _
    rcases acc with ⟨l, a⟩
    cases l <;> rfl

/-- `(μ, g, h) ↦ addE μ g h`. -/
def addFn : Fn (.prod .int (.prod tL tL)) tL :=
  .listCase (.fst (.snd v0)) .nil
    (.listCase (.snd (.snd v2)) .nil
      (.cons (.arith .mod (.arith .add v2 v0) (.int 2))
        (call zipModFn (.pair (.fst v4) (.pair v3 v1)))))

@[simp] theorem addFn_apply (x : ℤ × List ℤ × List ℤ) : addFn.apply x = addE x.1 x.2.1 x.2.2 := by
  rcases x with ⟨μ, g, h⟩
  cases g with
  | nil => rfl
  | cons a g =>
    cases h with
    | nil => rfl
    | cons b h =>
      rw [Fn.apply]; unfold addFn
      simp only [Expr.denote, Var.get, IntOp.eval, denote_call, addE, zipModFn_apply]

/-! ## Arcs -/

/-- The opposite stub code. -/
def oppFn : Fn .int .int :=
  .ite (.cmp .eq (.arith .mod v0 (.int 2)) (.int 1)) (.arith .add v0 (.int 1))
    (.arith .sub v0 (.int 1))

@[simp] theorem oppFn_apply (c : ℤ) : oppFn.apply c = oppE c := by
  rw [Fn.apply]; unfold oppFn
  simp only [Expr.denote, Var.get, IntOp.eval, CmpOp.eval, oppE]
  by_cases h : c % 2 = 1 <;> simp [h]

/-- `(col, b) ↦ srcE col b`. -/
def srcFn : Fn (.prod tL .bool) .int :=
  .listCase (.fst v0) (.int 0)
    (.listCase v1 (.ite (.snd v2) (call oppFn v0) (.int 0))
      (.ite (.snd v4) (call oppFn v0) (call oppFn v2)))

@[simp] theorem srcFn_apply (x : List ℤ × Bool) : srcFn.apply x = srcE x.1 x.2 := by
  rcases x with ⟨col, b⟩
  rw [Fn.apply]; unfold srcFn
  rcases col with _ | ⟨s, _ | ⟨t, rest⟩⟩ <;> cases b <;>
    simp [Expr.denote, Var.get, denote_call, srcE, oppFn_apply]

/-- `(col, b) ↦ tgtE col b`. -/
def tgtFn : Fn (.prod tL .bool) .int :=
  .listCase (.fst v0) (.int 0)
    (.listCase v1 (.ite (.snd v2) (.int 0) v0) (.ite (.snd v4) v2 v0))

@[simp] theorem tgtFn_apply (x : List ℤ × Bool) : tgtFn.apply x = tgtE x.1 x.2 := by
  rcases x with ⟨col, b⟩
  rw [Fn.apply]; unfold tgtFn
  rcases col with _ | ⟨s, _ | ⟨t, rest⟩⟩ <;> cases b <;>
    simp [Expr.denote, Var.get, tgtE]

/-- `col ↦ dirsE col`. -/
def dirsFn : Fn tL (.list .bool) :=
  .listCase v0 (.cons (.bool false) .nil) (.cons (.bool false) (.cons (.bool true) .nil))

@[simp] theorem dirsFn_apply (col : List ℤ) : dirsFn.apply col = dirsE col := by
  rw [Fn.apply]; unfold dirsFn
  cases col <;> simp [Expr.denote, Var.get, dirsE]

/-- The arc record of a direction, for the context `(P, e, p, edge)`. -/
def arcOfDirFn : Fn (.prod (.prod .int (.prod .int (.prod .int tE))) .bool) tArc :=
  .pair (.fst (.snd (.fst v0)))
    (.pair (.snd v0)
      (.pair (call srcFn (.pair (.fst (.snd (.snd (.snd (.fst v0))))) (.snd v0)))
        (.pair (call tgtFn (.pair (.fst (.snd (.snd (.snd (.fst v0))))) (.snd v0)))
          (.pair (.fst (.snd (.snd (.snd (.snd (.snd (.fst v0)))))))
            (.pair (.fst (.snd (.snd (.snd (.snd (.fst v0))))))
              (.arith .mul (.int 2)
                (.arith .add (.arith .mul (.fst (.fst v0))
                    (.snd (.snd (.snd (.snd (.snd (.snd (.fst v0))))))))
                  (.fst (.snd (.snd (.fst v0)))))))))))

/-- `(P, e, p, edge) ↦ edgeArcs P (e, p, edge)`. -/
def edgeArcsFn : Fn (.prod .int (.prod .int (.prod .int tE))) (.list tArc) :=
  call (mapWith arcOfDirFn) (.pair v0 (call dirsFn (.fst (.snd (.snd (.snd v0))))))

@[simp] theorem edgeArcsFn_apply (x : ℤ × ℤ × ℤ × (List ℤ × List ℤ × List ℤ × ℤ)) :
    edgeArcsFn.apply x = edgeArcs x.1 x.2 := by
  rw [Fn.apply]; unfold edgeArcsFn
  simp only [denote_call, Expr.denote, Var.get, mapWith_apply, dirsFn_apply]
  rw [edgeArcs]
  apply List.map_congr_left
  intro b _
  rw [Fn.apply]; unfold arcOfDirFn
  simp only [Expr.denote, Var.get, denote_call, IntOp.eval, srcFn_apply, tgtFn_apply]

/-- `(P, edges) ↦ arcsE P edges`. -/
def arcsFn : Fn (.prod .int (.list tE)) (.list tArc) :=
  call (flatMapWith edgeArcsFn) (.pair (.fst v0) (call indexPowFn (.snd v0)))

@[simp] theorem arcsFn_apply (x : ℤ × List (List ℤ × List ℤ × List ℤ × ℤ)) :
    arcsFn.apply x = arcsE x.1 x.2 := by
  rw [Fn.apply]; unfold arcsFn
  simp only [denote_call, Expr.denote, Var.get, flatMapWith_apply, indexPowFn_apply,
    edgeArcsFn_apply]
  rfl

end MWIS.FunNetwork

end
