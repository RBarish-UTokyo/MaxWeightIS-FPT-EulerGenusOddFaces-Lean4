module

public import MWIS.FunLPUpdate
public import MWIS.AlgorithmTrajectory
public import MWIS.AlgorithmStateBounds

/-!
# The separation query and the rounded ellipsoid loop as `Fun` programs

`sepFn` returns the first violated row (as a list of length at most one), and
`stepFn` performs one round of `AlgorithmEllipsoid.run` on encoded states with an
explicit status code: `0` running, `1` feasible, `2` zero row, `3` exhausted.
Iterating `stepFn` `fuel + 1` times from status `0` yields the status of
`run A b k ε fuel s` (`loop_status`).
-/

@[expose] public section

namespace MWIS.FunLP

open MWIS.Fun

/-! ## Separation -/

/-- The separation test `b_i k2 < row · c`. Argument `((k2, c), (row, b_i))`. -/
def sepTestFn : Fn (.prod (.prod .int (.list .int)) (.prod (.list .int) .int)) .bool :=
  .cmp .lt (.arith .mul (.snd (.snd v0)) (.fst (.fst v0))) (call dotFn (.pair (.fst (.snd v0)) (.snd (.fst v0))))

@[simp] theorem sepTestFn_apply
    (p : (Ty.prod (.prod .int (.list .int)) (.prod (.list .int) .int)).denote) :
    sepTestFn.apply p = decide (p.2.2 * p.1.1 < dotL p.2.1 p.1.2) := by
  rw [Fn.apply]; simp [sepTestFn, Expr.denote, Var.get, IntOp.eval, CmpOp.eval]

/-- The step of the separation fold. -/
def sepStepE : Expr [.prod (.list .int) .int, .list (.list .int),
    .prod .int (.prod (.list (.list .int)) (.prod (.list .int) (.list .int)))] (.list (.list .int)) :=
  .listCase v1
    (.ite (call sepTestFn (.pair (.pair (.fst v2) (.snd (.snd (.snd v2)))) v0))
      (.cons (.fst v0) .nil) .nil)
    v3

/-- The first violated row. Argument `(k2, (A, (b, c)))`. -/
def sepFn : Fn (.prod .int (.prod (.list (.list .int)) (.prod (.list .int) (.list .int))))
    (.list (.list .int)) :=
  .foldl (call (zipFn (.list .int) .int) (.pair (.fst (.snd v0)) (.fst (.snd (.snd v0))))) .nil sepStepE

/-- The first violated row on lists. -/
def sepL (k2 : ℤ) (A : List (List ℤ)) (b c : List ℤ) : Option (List ℤ) :=
  ((A.zip b).find? (fun rb => decide (rb.2 * k2 < dotL rb.1 c))).map Prod.fst

theorem sep_fold (p : List ℤ × ℤ → Bool) (F : List (List ℤ) → List ℤ × ℤ → List (List ℤ))
    (hnil : ∀ x, F [] x = if p x then [x.1] else [])
    (hcons : ∀ y ys x, F (y :: ys) x = y :: ys) :
    ∀ (l : List (List ℤ × ℤ)), l.foldl F [] = ((l.find? p).map Prod.fst).toList := by
  have hkeep : ∀ (l : List (List ℤ × ℤ)) y ys, l.foldl F (y :: ys) = y :: ys := by
    intro l; induction l with
    | nil => intro y ys; rfl
    | cons x l ih => intro y ys; rw [List.foldl_cons, hcons, ih]
  intro l
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.foldl_cons, hnil, List.find?_cons]
    by_cases hp : p x
    · simp only [hp, ite_true]; rw [hkeep]; rfl
    · simp only [hp, Bool.false_eq_true, ite_false]; exact ih

@[simp] theorem sepFn_apply
    (p : (Ty.prod .int (.prod (.list (.list .int)) (.prod (.list .int) (.list .int)))).denote) :
    sepFn.apply p = (sepL p.1 p.2.1 p.2.2.1 p.2.2.2).toList := by
  rw [Fn.apply]
  simp only [sepFn, Expr.denote, Var.get, denote_call, zipFn_apply]
  rw [sep_fold (fun rb => decide (rb.2 * p.1 < dotL rb.1 p.2.2.2)) _
    (fun x => by
      simp only [sepStepE, Expr.denote, Var.get, denote_call, sepTestFn_apply])
    (fun y ys x => by simp [sepStepE, Expr.denote, Var.get])]
  rfl

open AlgorithmEllipsoid in
/-- The list separation query finds the row of the actual separation query. -/
theorem sepL_encode {m n : ℕ} (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) (k : ℕ) (c : Fin n → ℤ) :
    sepL (2 ^ k) (matE A) (vecE b) (vecE c) =
      (AlgorithmSeparation.separate A b (fun j => AlgorithmRounding.dyadic k (c j))).map
        (fun i => vecE (A i)) := by
  unfold sepL AlgorithmSeparation.separate
  have hz : (matE A).zip (vecE b) = (List.finRange m).map (fun i => (vecE (A i), b i)) := by
    rw [matE, vecE, zip_ofFn, List.ofFn_eq_map]; rfl
  rw [hz, List.find?_map, Option.map_map]
  congr 1
  congr 1
  funext i
  simp only [Function.comp, vecE, dotL_ofFn]
  exact decide_eq_decide.mpr (FunLPMath.separate_test_iff A b k c i).symm

/-! ## One round of the loop -/

/-- Stored loop state `(status, (fuel, (c, S)))`. -/
abbrev StTy : Ty := .prod .int (.prod .int (.prod (.list .int) (.list (.list .int))))

/-- Loop parameters `(n, (k2, (A, b)))`. -/
abbrev ParTy : Ty := .prod .int (.prod .int (.prod (.list (.list .int)) (.list .int)))

/-- A list is the zero vector exactly when its dot square vanishes. -/
def zeroFn : Fn (.list .int) .bool := .cmp .eq (call dotFn (.pair v0 v0)) (.int 0)

@[simp] theorem zeroFn_apply (l : (Ty.list .int).denote) : zeroFn.apply l = decide (dotL l l = 0) := by
  rw [Fn.apply]; simp [zeroFn, Expr.denote, Var.get, CmpOp.eval]

/-- The branch after a violated row has been found. Context `[row, rest, (P, st)]`. -/
def foundE : Expr [.list .int, .list (.list .int), .prod ParTy StTy] StTy :=
  .ite (call zeroFn v0) (.pair (.int 2) (.snd (.snd v2)))
    (.ite (.cmp .eq (.fst (.snd (.snd v2))) (.int 0)) (.pair (.int 3) (.snd (.snd v2)))
      (.pair (.int 0) (.pair (.arith .sub (.fst (.snd (.snd v2))) (.int 1))
        (call updFn (.pair (.fst (.fst v2)) (.pair (.fst (.snd (.fst v2)))
          (.pair (.fst (.snd (.snd (.snd v2)))) (.pair (.snd (.snd (.snd (.snd v2))))
            (call negFn v0)))))))))

/-- One round. Argument `(P, st)`. -/
def stepFn : Fn (.prod ParTy StTy) StTy :=
  .ite (.cmp .eq (.fst (.snd v0)) (.int 0))
    (.listCase (call sepFn (.pair (.fst (.snd (.fst v0))) (.pair (.fst (.snd (.snd (.fst v0))))
        (.pair (.snd (.snd (.snd (.fst v0)))) (.fst (.snd (.snd (.snd v0))))))))
      (.pair (.int 1) (.snd (.snd v0)))
      foundE)
    (.snd v0)

/-- One round on values. -/
def stepL (n k2 : ℤ) (A : List (List ℤ)) (b : List ℤ) (st : ℤ × ℤ × List ℤ × List (List ℤ)) :
    ℤ × ℤ × List ℤ × List (List ℤ) :=
  if st.1 = 0 then
    match sepL k2 A b st.2.2.1 with
    | none => (1, st.2)
    | some row =>
      if dotL row row = 0 then (2, st.2)
      else if st.2.1 = 0 then (3, st.2)
      else (0, st.2.1 - 1, updL n k2 st.2.2.1 st.2.2.2 (row.map (fun x => -x)))
  else st

@[simp] theorem stepFn_apply (p : (Ty.prod ParTy StTy).denote) :
    stepFn.apply p = stepL p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2 p.2 := by
  rw [Fn.apply]
  simp only [stepFn, Expr.denote, Var.get, denote_call, sepFn_apply, CmpOp.eval, stepL]
  by_cases h0 : p.2.1 = 0
  · simp only [h0, decide_true, ite_true]
    cases hs : sepL p.1.2.1 p.1.2.2.1 p.1.2.2.2 p.2.2.2.1 with
    | none => rfl
    | some row =>
      simp only [Option.toList_some, foundE, Expr.denote, Var.get, denote_call, zeroFn_apply,
        CmpOp.eval, IntOp.eval, updFn_apply, negFn_apply]
      by_cases hz : dotL row row = 0
      · simp [hz]
      · by_cases hf : p.2.2.1 = 0 <;> simp [hz, hf]
  · simp [h0]

/-! ## The loop -/

/-- Iterate `fuel + 1` rounds. Argument `(P, st)`. -/
def loopFn : Fn (.prod ParTy StTy) StTy :=
  .iter (.arith .add (.fst (.snd (.snd v0))) (.int 1)) (.snd v0) (call stepFn (.pair (.fst v1) v0))

@[simp] theorem loopFn_apply (p : (Ty.prod ParTy StTy).denote) :
    loopFn.apply p = (stepL p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2)^[(p.2.2.1 + 1).toNat] p.2 := by
  rw [Fn.apply]
  simp only [loopFn, Expr.denote, Var.get, denote_call, stepFn_apply, IntOp.eval]

open AlgorithmEllipsoid

/-- The encoded centre and shape of a state. -/
def encSt {n : ℕ} (s : State n) : List ℤ × List (List ℤ) :=
  (vecE s.centerNumerator, matE s.shapeNumerator)

/-- The status code of an outcome. -/
def outcomeCode {n : ℕ} : Outcome n → ℤ
  | .feasible _ => 1
  | .zeroRow => 2
  | .exhausted => 3

theorem stepL_fixed (n k2 : ℤ) (A : List (List ℤ)) (b : List ℤ)
    (st : ℤ × ℤ × List ℤ × List (List ℤ)) (h : st.1 ≠ 0) : stepL n k2 A b st = st := by
  simp [stepL, h]

theorem iterate_fixed (n k2 : ℤ) (A : List (List ℤ)) (b : List ℤ)
    (st : ℤ × ℤ × List ℤ × List (List ℤ)) (h : st.1 ≠ 0) (j : ℕ) :
    (stepL n k2 A b)^[j] st = st :=
  Function.iterate_fixed (stepL_fixed n k2 A b st h) j

theorem dotL_vecE_self {n : ℕ} (v : Fin n → ℤ) : dotL (vecE v) (vecE v) = 0 ↔ v = 0 := by
  rw [vecE, dotL_ofFn]
  constructor
  · intro h
    have h' := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_self_nonneg (v i))).mp h
    funext i
    exact mul_self_eq_zero.mp (h' i (Finset.mem_univ i))
  · intro h; simp [h]

theorem neg_vecE {n : ℕ} (v : Fin n → ℤ) : (vecE v).map (fun x => -x) = vecE (fun j => -v j) := by
  simp only [vecE, List.map_ofFn]; rfl

section Round

variable {m n : ℕ} (hn : 2 ≤ n) (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) (k : ℕ)
include hn

/-- One round on an encoded running state. -/
theorem stepL_running (fuel : ℤ) (s : State n) :
    stepL n (2 ^ k) (matE A) (vecE b) (0, fuel, encSt s) =
      match AlgorithmSeparation.separate A b (center k s) with
      | none => (1, fuel, encSt s)
      | some i => if A i = 0 then (2, fuel, encSt s) else if fuel = 0 then (3, fuel, encSt s)
          else (0, fuel - 1, encSt (update k (AlgorithmPrecision.inflation n) s (fun j => -A i j))) := by
  have hsep := sepL_encode A b k s.centerNumerator
  simp only [stepL, encSt, ite_true] at hsep ⊢
  rw [hsep]
  change _ = match AlgorithmSeparation.separate A b (fun j => AlgorithmRounding.dyadic k
    (s.centerNumerator j)) with
      | none => _ | some i => _
  cases AlgorithmSeparation.separate A b (fun j => AlgorithmRounding.dyadic k (s.centerNumerator j)) with
  | none => rfl
  | some i =>
    simp only [Option.map_some, dotL_vecE_self, neg_vecE]
    by_cases hA : A i = 0
    · simp [hA]
    · by_cases hf : fuel = 0
      · simp [hA, hf]
      · simp only [hA, hf, ite_false]
        rw [update_encode hn]

omit hn in
/-- Iterating `fuel + 1` rounds from a running state computes the status of `run`. -/
theorem loop_status (hn : 2 ≤ n) : ∀ (fuel : ℕ) (s : State n),
    ((stepL n (2 ^ k) (matE A) (vecE b))^[fuel + 1] (0, (fuel : ℤ), encSt s)).1 =
      outcomeCode (run A b k (AlgorithmPrecision.inflation n) fuel s) := by
  intro fuel
  induction fuel with
  | zero =>
    intro s
    rw [Function.iterate_one, stepL_running hn, run]
    cases AlgorithmSeparation.separate A b (center k s) with
    | none => rfl
    | some i => by_cases hA : A i = 0 <;> simp [hA, outcomeCode]
  | succ t ih =>
    intro s
    rw [Function.iterate_succ_apply, stepL_running hn, run]
    cases hs : AlgorithmSeparation.separate A b (center k s) with
    | none =>
      simp only
      rw [iterate_fixed _ _ _ _ _ (by simp)]; rfl
    | some i =>
      simp only
      by_cases hA : A i = 0
      · simp only [hA, ite_true]
        rw [iterate_fixed _ _ _ _ _ (by simp)]; rfl
      · have hf : ((t + 1 : ℕ) : ℤ) ≠ 0 := by omega
        simp only [hA, hf, ite_false]
        have : ((t + 1 : ℕ) : ℤ) - 1 = (t : ℤ) := by omega
        rw [this, ih]

omit hn in
/-- Every reachable loop state stores a trajectory state with index at most `T`. -/
theorem loop_reach (hn : 2 ≤ n) (T : ℕ) (s0 : State n) : ∀ j : ℕ, ∃ t ≤ T, ∃ code fuel : ℤ,
    0 ≤ code ∧ code ≤ 3 ∧ 0 ≤ fuel ∧ fuel ≤ T ∧ (code = 0 → fuel + t = T) ∧
    (stepL n (2 ^ k) (matE A) (vecE b))^[j] (0, (T : ℤ), encSt s0) =
      (code, fuel, encSt (AlgorithmTrajectory.trajectory A b k (AlgorithmPrecision.inflation n) s0 t)) := by
  intro j
  induction j with
  | zero => exact ⟨0, Nat.zero_le _, 0, T, le_rfl, by omega, by omega, le_rfl, by simp, rfl⟩
  | succ j ih =>
    obtain ⟨t, ht, code, fuel, hc0, hc3, hf0, hfT, hft, he⟩ := ih
    rw [Function.iterate_succ_apply', he]
    by_cases hc : code = 0
    · subst hc
      have hft := hft rfl
      rw [stepL_running hn]
      cases hs : AlgorithmSeparation.separate A b
          (center k (AlgorithmTrajectory.trajectory A b k (AlgorithmPrecision.inflation n) s0 t)) with
      | none => exact ⟨t, ht, 1, fuel, by omega, by omega, hf0, hfT, by simp, rfl⟩
      | some i =>
        simp only
        by_cases hA : A i = 0
        · simp only [hA, ite_true]; exact ⟨t, ht, 2, fuel, by omega, by omega, hf0, hfT, by simp, rfl⟩
        · simp only [hA, ite_false]
          by_cases hf : fuel = 0
          · simp only [hf, ite_true]
            exact ⟨t, ht, 3, 0, by omega, by omega, le_rfl, by omega, by simp, rfl⟩
          · simp only [hf, ite_false]
            refine ⟨t + 1, by omega, 0, fuel - 1, le_rfl, by omega, by omega, by omega,
              fun _ => by omega, ?_⟩
            simp only [AlgorithmTrajectory.trajectory, AlgorithmTrajectory.advance, hs, hA, ite_false]
    · rw [stepL_fixed _ _ _ _ _ hc]
      exact ⟨t, ht, code, fuel, hc0, hc3, hf0, hfT, hft, rfl⟩

end Round

end MWIS.FunLP

end
