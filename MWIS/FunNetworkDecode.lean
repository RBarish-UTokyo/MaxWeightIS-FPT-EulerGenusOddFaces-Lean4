module

public import MWIS.FunNetworkProgram

/-!
# Offset, search width and slack decoding in `Fun`

`offsetFn` and `bitsFn` compute `2 · total c` and `searchBits c` from the encoded
edge records; `decodeFn` computes the decoded slack `decode m (total c - value)`.

Prepared 2026-10-23.
-/

@[expose] public section

namespace MWIS.FunNetwork

open MWIS.Fun MWIS.FunLP FPTHard

/-! ## The total perturbed cost -/

/-- The total perturbed cost of encoded edge records. -/
def totalE (edges : List EdgeIn) : ℤ :=
  (indexPow 0 1 edges).foldl
    (fun s x => s + ((2 : ℤ) ^ (edges.length + 1) * x.2.2.2.2.2 + x.2.1)) 0

theorem foldl_add_eq {α : Type*} (F : α → ℤ) (l : List α) (a : ℤ) :
    l.foldl (fun s x => s + F x) a = a + (l.map F).sum := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih]; simp; ring

theorem totalE_edgeInput {f m : ℕ} (C : Fin m → Walks.Column (Fin f)) (D : CoordinateData m)
    (c : Fin m → ℕ) : totalE (edgeInput C D c) = (total c : ℤ) := by
  have hlen : (edgeInput C D c).length = m := by simp [edgeInput]
  unfold totalE
  rw [hlen, foldl_add_eq, edgeInput, indexPow_ofFn, List.map_ofFn, List.sum_ofFn]
  simp [total, perturbed]

/-- The total perturbed cost. -/
def totalFn : Fn (.list tE) .int :=
  .letE (call powFn (.arith .add (call (lengthFn tE) v0) (.int 1)))
    (.foldl (call indexPowFn v1) (.int 0)
      (.arith .add v1 (.arith .add (.arith .mul v2 (.snd (.snd (.snd (.snd (.snd v0))))))
        (.fst (.snd v0)))))

@[simp] theorem totalFn_apply (edges : List EdgeIn) : totalFn.apply edges = totalE edges := by
  rw [Fn.apply]; unfold totalFn totalE
  simp only [denote_call, Expr.denote, Var.get, IntOp.eval, powFn_apply, lengthFn_apply,
    indexPowFn_apply]
  have h : ((edges.length : ℤ) + 1).toNat = edges.length + 1 := by omega
  rw [h]

/-- Twice the total perturbed cost: the threshold-search offset. -/
def offsetFn : Fn (.list tE) .int := .arith .mul (.int 2) (call totalFn v0)

/-- The threshold-search width `(2 · total).size`. -/
def bitsFn : Fn (.list tE) .int := .size (.arith .mul (.int 2) (call totalFn v0))

theorem offsetFn_correct {f m : ℕ} (C : Fin m → Walks.Column (Fin f)) (D : CoordinateData m)
    (c : Fin m → ℕ) : offsetFn.apply (edgeInput C D c) = 2 * (total c : ℤ) := by
  rw [Fn.apply]; unfold offsetFn
  simp only [denote_call, Expr.denote, Var.get, IntOp.eval, totalFn_apply, totalE_edgeInput]

theorem bitsFn_correct {f m : ℕ} (C : Fin m → Walks.Column (Fin f)) (D : CoordinateData m)
    (c : Fin m → ℕ) : bitsFn.apply (edgeInput C D c) = (searchBits c : ℤ) := by
  rw [Fn.apply]; unfold bitsFn
  simp only [denote_call, Expr.denote, Var.get, IntOp.eval, totalFn_apply, totalE_edgeInput,
    bits, searchBits]
  congr 2

/-! ## Decoding -/

/-- `(M, m) ↦ [M / 2^0 % 2, …, M / 2^(m-1) % 2]`. -/
def decodeFn : Fn (.prod .int .int) tL :=
  call (rev .int) (.snd (.iter (.snd v0) (.pair (.int 1) .nil)
    (.pair (.arith .mul (.int 2) (.fst v0))
      (.cons (.arith .mod (.arith .div (.fst v1) (.fst v0)) (.int 2)) (.snd v0)))))

theorem decode_iterate (M : ℤ) : ∀ (k : ℕ) (p : ℤ) (acc : List ℤ),
    (fun s : ℤ × List ℤ => (2 * s.1, (M / s.1 % 2) :: s.2))^[k] (p, acc) =
      (p * 2 ^ k, (List.ofFn (fun i : Fin k => M / (p * 2 ^ (i : ℕ)) % 2)).reverse ++ acc)
  | 0, p, acc => by simp
  | k + 1, p, acc => by
    rw [Function.iterate_succ_apply', decode_iterate M k p acc]
    simp only [Prod.mk.injEq]
    refine ⟨by ring, ?_⟩
    rw [List.ofFn_succ_last, List.reverse_append]
    simp

@[simp] theorem decodeFn_apply (x : ℤ × ℤ) :
    decodeFn.apply x = List.ofFn (fun i : Fin x.2.toNat => x.1 / 2 ^ (i : ℕ) % 2) := by
  rw [Fn.apply]; unfold decodeFn
  simp only [denote_call, Expr.denote, Var.get, IntOp.eval]
  rw [decode_iterate, rev_apply, List.append_nil, List.reverse_reverse]
  simp

/-- **Decoding.** The decoded slack of the minimum perturbed slack cost. -/
theorem decodeFn_correct (m M : ℕ) :
    decodeFn.apply ((M : ℤ), (m : ℤ)) = List.ofFn (decode m M) := by
  rw [decodeFn_apply]
  simp only [Int.toNat_natCast]
  congr 1

/-! ## Slack from an LP value -/

/-- `(v, edges) ↦` the decoded slack of `max (total - v) 0`, as a list over the edges. -/
def slackFn : Fn (.prod .int (.list tE)) tL :=
  .letE (call totalFn (.snd v0)) <|
    call decodeFn (.pair (.ite (.cmp .le (.fst v1) v0) (.arith .sub v0 (.fst v1)) (.int 0))
      (call (lengthFn tE) (.snd v1)))

theorem slackFn_apply (x : ℤ × List EdgeIn) :
    slackFn.apply x = decodeFn.apply
      (if x.1 ≤ totalE x.2 then totalE x.2 - x.1 else 0, (x.2.length : ℤ)) := by
  rw [Fn.apply]; unfold slackFn
  simp only [denote_call, Expr.denote, Var.get, IntOp.eval, CmpOp.eval, totalFn_apply,
    lengthFn_apply]
  by_cases h : x.1 ≤ totalE x.2 <;> simp [h]

/-- **Decoding an LP value.** For a natural value `v`, `slackFn` returns the decoded
slack `decode m (total c - v)` of `FPTHard.recoveredSet`. -/
theorem slackFn_correct {f m : ℕ} (C : Fin m → Walks.Column (Fin f)) (D : CoordinateData m)
    (c : Fin m → ℕ) (v : ℕ) :
    slackFn.apply ((v : ℤ), edgeInput C D c) = List.ofFn (decode m (total c - v)) := by
  have hlen : (edgeInput C D c).length = m := by simp [edgeInput]
  rw [slackFn_apply]
  simp only [totalE_edgeInput, hlen]
  by_cases h : v ≤ total c
  · have h' : (v : ℤ) ≤ (total c : ℤ) := by exact_mod_cast h
    simp only [h', ↓reduceIte]
    rw [show (total c : ℤ) - v = ((total c - v : ℕ) : ℤ) by push_cast [h]; ring,
      decodeFn_correct]
  · have h' : ¬ (v : ℤ) ≤ (total c : ℤ) := by exact_mod_cast h
    simp only [h', ↓reduceIte]
    rw [show (total c - v : ℕ) = 0 by omega, show ((0 : ℤ)) = ((0 : ℕ) : ℤ) from rfl,
      decodeFn_correct]

end MWIS.FunNetwork

end
