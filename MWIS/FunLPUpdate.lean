module

public import MWIS.FunLPArith
public import MWIS.FunLPBound

/-!
# The rounded ellipsoid update as a `Fun` program

`updFn` computes, from the stored centre and shape numerators and an integer
cut, the stored numerators of `AlgorithmEllipsoid.update` with the inflation
`AlgorithmPrecision.inflation n`. Its meaning is the list function `updL`, which
agrees with the update on the canonical list encodings (`update_encode`).
-/

@[expose] public section

namespace MWIS.FunLP

open MWIS.Fun

/-! ## The list-level update -/

/-- The list encoding of an integer vector. -/
def vecE {n : ℕ} (v : Fin n → ℤ) : List ℤ := List.ofFn v

/-- The list encoding of an integer matrix, by rows. -/
def matE {m n : ℕ} (M : Fin m → Fin n → ℤ) : List (List ℤ) := List.ofFn fun i => List.ofFn (M i)

/-- The rounded update on list encodings. `k2 = 2^k`. -/
def updL (n k2 : ℤ) (c : List ℤ) (S : List (List ℤ)) (a : List ℤ) : List ℤ × List (List ℤ) :=
  let V := S.map (fun row => dotL row a)
  let Q := dotL a V
  let R := isqrt (Q * k2) + 1
  let Qs := if Q = 0 then 1 else Q
  let fl : ℤ := if Q = 0 then 0 else 1
  let E := 32 * ((n + 1) * (n + 1))
  let M := (E + 1) * (E + 1) * (n * n)
  let Dn := E * E * (n * n - 1) * (n + 1) * Qs
  (List.zipWith (fun ci Vi => ci + Vi * k2 / ((n + 1) * R)) c V,
   (S.zip V).mapIdx (fun i rv => (rv.1.zip V).mapIdx (fun j sv =>
      FunLPMath.floorDiv (M * ((n + 1) * Qs * sv.1 - 2 * rv.2 * sv.2 * fl)) Dn +
        (if (i : ℤ) = (j : ℤ) then n else 0))))

/-! ## Agreement with the rounded update -/

theorem zipWith_ofFn {α β γ : Type*} {n : ℕ} (f : α → β → γ) (u : Fin n → α) (v : Fin n → β) :
    List.zipWith f (List.ofFn u) (List.ofFn v) = List.ofFn fun i => f (u i) (v i) := by
  apply List.ext_getElem <;> simp

theorem dotL_ofFn {n : ℕ} (u v : Fin n → ℤ) : dotL (List.ofFn u) (List.ofFn v) = ∑ i, u i * v i := by
  unfold dotL
  rw [zipWith_ofFn, List.sum_ofFn]

theorem zip_ofFn {α β : Type*} {n : ℕ} (u : Fin n → α) (v : Fin n → β) :
    (List.ofFn u).zip (List.ofFn v) = List.ofFn fun i => (u i, v i) := by
  apply List.ext_getElem <;> simp

theorem mapIdx_ofFn {α β : Type*} {n : ℕ} (f : ℕ → α → β) (u : Fin n → α) :
    (List.ofFn u).mapIdx f = List.ofFn fun i => f i (u i) := by
  apply List.ext_getElem <;> simp

open AlgorithmEllipsoid FunLPMath in
/-- The list update computes the rounded update on the canonical encodings. -/
theorem update_encode {n : ℕ} (hn : 2 ≤ n) (k : ℕ) (s : State n) (a : Fin n → ℤ) :
    updL n (2 ^ k) (vecE s.centerNumerator) (matE s.shapeNumerator) (vecE a) =
      (vecE (update k (AlgorithmPrecision.inflation n) s a).centerNumerator,
       matE (update k (AlgorithmPrecision.inflation n) s a).shapeNumerator) := by
  have hV : (matE s.shapeNumerator).map (fun row => dotL row (vecE a)) = vecE (vecV s a) := by
    simp only [matE, vecE, List.map_ofFn]
    congr 1
    funext i
    simp [dotL_ofFn, vecV]
  have hQ : dotL (vecE a) (vecE (vecV s a)) = quadQ s a := by
    simp [vecE, dotL_ofFn, quadQ]
  have hR : isqrt (quadQ s a * 2 ^ k) + 1 = (rootR k s a : ℤ) := by
    simp [isqrt, rootR]
  unfold updL
  simp only [hV, hQ, hR]
  refine Prod.ext ?_ ?_
  · simp only [vecE, zipWith_ofFn]
    congr 1
    funext i
    rw [update_centerNumerator]
  · simp only [matE, vecE, zip_ofFn, mapIdx_ofFn]
    congr 1
    funext i
    congr 1
    funext j
    rw [update_shapeNumerator hn]
    have hij : ((i : ℕ) : ℤ) = ((j : ℕ) : ℤ) ↔ i = j := by
      rw [Nat.cast_inj, Fin.val_inj]
    simp only [hij]
    congr 1
    unfold shapeNum shapeDen inflE safeQ flagQ
    split_ifs <;> ring_nf

/-! ## The `Fun` program -/

/-- Floor division for a nonzero divisor of either sign. -/
def floorDivFn : Fn (.prod .int .int) .int :=
  .ite (.cmp .lt (.int 0) (.snd v0)) (.arith .div (.fst v0) (.snd v0))
    (.arith .div (.arith .sub (.int 0) (.fst v0)) (.arith .sub (.int 0) (.snd v0)))

@[simp] theorem floorDivFn_apply (p : (Ty.prod .int .int).denote) :
    floorDivFn.apply p = FunLPMath.floorDiv p.1 p.2 := by
  rw [Fn.apply]
  simp only [floorDivFn, Expr.denote, Var.get, CmpOp.eval, IntOp.eval, FunLPMath.floorDiv]
  by_cases h : 0 < p.2 <;> simp [h]

/-- `dot(row, a)` with the parameter first. -/
def dotRevFn : Fn (.prod (.list .int) (.list .int)) .int := call dotFn (.pair (.snd v0) (.fst v0))

@[simp] theorem dotRevFn_apply (p : (Ty.prod (.list .int) (.list .int)).denote) :
    dotRevFn.apply p = dotL p.2 p.1 := by
  rw [Fn.apply]; simp [dotRevFn, Expr.denote, Var.get]

/-- Matrix-vector product `S a`, by rows. -/
def matVecFn : Fn (.prod (.list .int) (.list (.list .int))) (.list .int) := mapFn dotRevFn

@[simp] theorem matVecFn_apply (p : (Ty.prod (.list .int) (.list (.list .int))).denote) :
    matVecFn.apply p = p.2.map (fun row => dotL row p.1) := by
  simp [matVecFn]

/-- One centre entry: `c_i + V_i k2 / D1`, with parameter `(k2, D1)`. -/
def centerEntryFn : Fn (.prod (.prod .int .int) (.prod .int .int)) .int :=
  .arith .add (.fst (.snd v0)) (.arith .div (.arith .mul (.snd (.snd v0)) (.fst (.fst v0)))
    (.snd (.fst v0)))

@[simp] theorem centerEntryFn_apply (p : (Ty.prod (.prod .int .int) (.prod .int .int)).denote) :
    centerEntryFn.apply p = p.2.1 + p.2.2 * p.1.1 / p.1.2 := rfl

/-- The constants `(n, Qs, fl, M, Dn)` of a shape update. -/
abbrev CstTy : Ty := .prod .int (.prod .int (.prod .int (.prod .int .int)))

/-- One shape entry. Argument `((cst, (i, V_i)), (j, (S_ij, V_j)))`. -/
def entryFn : Fn (.prod (.prod CstTy (.prod .int .int)) (.prod .int (.prod .int .int))) .int :=
  .arith .add
    (call floorDivFn (.pair
      (.arith .mul (.fst (.snd (.snd (.snd (.fst (.fst v0))))))
        (.arith .sub
          (.arith .mul (.arith .mul (.arith .add (.fst (.fst (.fst v0))) (.int 1))
            (.fst (.snd (.fst (.fst v0))))) (.fst (.snd (.snd v0))))
          (.arith .mul (.arith .mul (.arith .mul (.int 2) (.snd (.snd (.fst v0))))
            (.snd (.snd (.snd v0)))) (.fst (.snd (.snd (.fst (.fst v0))))))))
      (.snd (.snd (.snd (.snd (.fst (.fst v0))))))))
    (.ite (.cmp .eq (.fst (.snd (.fst v0))) (.fst (.snd v0))) (.fst (.fst (.fst v0))) (.int 0))

/-- The meaning of one shape entry. -/
def entryL (cst : CstTy.denote) (i Vi j Sij Vj : ℤ) : ℤ :=
  FunLPMath.floorDiv (cst.2.2.2.1 * ((cst.1 + 1) * cst.2.1 * Sij - 2 * Vi * Vj * cst.2.2.1))
    cst.2.2.2.2 + (if i = j then cst.1 else 0)

@[simp] theorem entryFn_apply
    (p : (Ty.prod (.prod CstTy (.prod .int .int)) (.prod .int (.prod .int .int))).denote) :
    entryFn.apply p = entryL p.1.1 p.1.2.1 p.1.2.2 p.2.1 p.2.2.1 p.2.2.2 := by
  rw [Fn.apply]
  simp only [entryFn, Expr.denote, Var.get, denote_call, floorDivFn_apply, IntOp.eval, CmpOp.eval,
    entryL]
  by_cases h : p.1.2.1 = p.2.1 <;> simp [h]

/-- One shape row. Argument `((cst, V), (i, (S_i, V_i)))`. -/
def rowFn : Fn (.prod (.prod CstTy (.list .int)) (.prod .int (.prod (.list .int) .int))) (.list .int) :=
  call (mapIdxFn entryFn)
    (.pair (.pair (.fst (.fst v0)) (.pair (.fst (.snd v0)) (.snd (.snd (.snd v0)))))
      (call (zipFn .int .int) (.pair (.fst (.snd (.snd v0))) (.snd (.fst v0)))))

@[simp] theorem rowFn_apply
    (p : (Ty.prod (.prod CstTy (.list .int)) (.prod .int (.prod (.list .int) .int))).denote) :
    rowFn.apply p = (p.2.2.1.zip p.1.2).mapIdx
      (fun j sv => entryL p.1.1 p.2.1 p.2.2.2 (j : ℤ) sv.1 sv.2) := by
  rw [Fn.apply]
  simp [rowFn, Expr.denote, Var.get]

/-- The square-root denominator `R = ⌊√(Q k2)⌋ + 1`. Argument `(Q, k2)`. -/
def rootFn : Fn (.prod .int .int) .int :=
  .arith .add (call sqrtFn (.arith .mul (.fst v0) (.snd v0))) (.int 1)

@[simp] theorem rootFn_apply (p : (Ty.prod .int .int).denote) :
    rootFn.apply p = isqrt (p.1 * p.2) + 1 := by
  rw [Fn.apply]; simp [rootFn, Expr.denote, Var.get, IntOp.eval]

/-- The shape constants `(n, Qs, fl, M, Dn)` from `(n, Q)`. -/
def scalarsFn : Fn (.prod .int .int) CstTy :=
  .letE (.ite (.cmp .eq (.snd v0) (.int 0)) (.int 1) (.snd v0))
  (.letE (.ite (.cmp .eq (.snd v1) (.int 0)) (.int 0) (.int 1))
  (.letE (.arith .mul (.int 32) (.arith .mul (.arith .add (.fst v2) (.int 1))
      (.arith .add (.fst v2) (.int 1))))
  -- context [E, fl, Qs, (n, Q)]
  (.pair (.fst v3) (.pair v2 (.pair v1 (.pair
    (.arith .mul (.arith .mul (.arith .add v0 (.int 1)) (.arith .add v0 (.int 1)))
      (.arith .mul (.fst v3) (.fst v3)))
    (.arith .mul (.arith .mul (.arith .mul (.arith .mul v0 v0)
      (.arith .sub (.arith .mul (.fst v3) (.fst v3)) (.int 1))) (.arith .add (.fst v3) (.int 1))) v2)))))))

/-- The meaning of `scalarsFn`. -/
def scalarsL (n Q : ℤ) : ℤ × ℤ × ℤ × ℤ × ℤ :=
  let Qs := if Q = 0 then 1 else Q
  let fl : ℤ := if Q = 0 then 0 else 1
  let E := 32 * ((n + 1) * (n + 1))
  (n, Qs, fl, (E + 1) * (E + 1) * (n * n), E * E * (n * n - 1) * (n + 1) * Qs)

@[simp] theorem scalarsFn_apply (p : (Ty.prod .int .int).denote) :
    scalarsFn.apply p = scalarsL p.1 p.2 := by
  rw [Fn.apply]
  simp only [scalarsFn, Expr.denote, Var.get, IntOp.eval, CmpOp.eval, scalarsL]
  by_cases h : p.2 = 0 <;> simp [h]

/-- The centre denominator `(n + 1) R`. Argument `(n, R)`. -/
def d1Fn : Fn (.prod .int .int) .int := .arith .mul (.arith .add (.fst v0) (.int 1)) (.snd v0)

@[simp] theorem d1Fn_apply (p : (Ty.prod .int .int).denote) : d1Fn.apply p = (p.1 + 1) * p.2 := rfl

/-- The update program. Argument `(n, (k2, (c, (S, a))))`. -/
def updFn : Fn (.prod .int (.prod .int (.prod (.list .int) (.prod (.list (.list .int)) (.list .int)))))
    (.prod (.list .int) (.list (.list .int))) :=
  -- V, context [inp]
  .letE (call matVecFn (.pair (.snd (.snd (.snd (.snd v0)))) (.fst (.snd (.snd (.snd v0))))))
  -- Q, context [V, inp]
  (.letE (call dotFn (.pair (.snd (.snd (.snd (.snd v1)))) v0))
  -- R, context [Q, V, inp]
  (.letE (call rootFn (.pair v0 (.fst (.snd v2))))
  -- cst, context [R, Q, V, inp]
  (.letE (call scalarsFn (.pair (.fst v3) v1))
  -- D1, context [cst, R, Q, V, inp]
  (.letE (call d1Fn (.pair (.fst v4) v1))
  -- body, context [D1, cst, R, Q, V, inp]
  (.pair
    (call (zipWithFn centerEntryFn) (.pair (.pair (.fst (.snd v5)) v0) (.pair (.fst (.snd (.snd v5))) v4)))
    (call (mapIdxFn rowFn)
      (.pair (.pair v1 v4) (call (zipFn (.list .int) .int) (.pair (.fst (.snd (.snd (.snd v5)))) v4)))))))))

@[simp] theorem updFn_apply
    (p : (Ty.prod .int (.prod .int (.prod (.list .int) (.prod (.list (.list .int)) (.list .int))))).denote) :
    updFn.apply p = updL p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 := by
  rw [Fn.apply]
  simp only [updFn, Expr.denote, Var.get, denote_call, matVecFn_apply, dotFn_apply, rootFn_apply,
    scalarsFn_apply, d1Fn_apply, zipFn_apply, zipWithFn_apply, mapIdxFn_apply, centerEntryFn_apply,
    rowFn_apply, updL, entryL, scalarsL]


/-! ## Cost -/

theorem scalarsFn_loopFree : scalarsFn.loopFree = true := by decide
theorem d1Fn_loopFree : d1Fn.loopFree = true := by decide
theorem centerEntryFn_loopFree : centerEntryFn.loopFree = true := by decide
theorem entryFn_loopFree : entryFn.loopFree = true := by decide
theorem scalarsFn_sbc : scalarsFn.sbc = 1638 := by decide
theorem scalarsFn_kbc : scalarsFn.kbc = 1140950 := by decide
theorem d1Fn_sbc : d1Fn.sbc = 4 := by decide
theorem d1Fn_kbc : d1Fn.kbc = 18 := by decide
theorem centerEntryFn_kbc : centerEntryFn.kbc = 39 := by decide
theorem entryFn_kbc : entryFn.kbc = 11759 := by decide

theorem dotRevFn_cost (a row : (Ty.list .int).denote) (β L : ℕ) (hL : row.length ≤ L)
    (hr : ∀ y ∈ row, bits y ≤ β) (ha : ∀ y ∈ a, bits y ≤ β) :
    dotRevFn.costAt (a, row) ≤ 4 * (L + 1) * (β + L + 10) ^ 2 + 10 := by
  unfold Fn.costAt dotRevFn
  rw [cost_call]
  have := dotFn_cost row a β L hL hr ha
  simp only [Expr.cost, Var.index, Expr.denote, Var.get] at this ⊢
  omega

theorem rootFn_cost (Q k2 : Ty.int.denote) :
    rootFn.costAt (Q, k2) ≤ 16 * (bits (Q * k2) + 6) ^ 3 + (bits Q + 1) * (bits k2 + 1) +
      bits (Q * k2) + 20 := by
  unfold Fn.costAt rootFn
  simp only [Expr.cost, cost_call, Var.index, Expr.denote, Var.get, IntOp.charge, IntOp.eval,
    denote_call, sqrtFn_apply]
  have hs := sqrtFn_cost (Q * k2)
  have hi : bits (isqrt (Q * k2)) ≤ bits (Q * k2) := by
    apply bits_mono
    unfold isqrt
    have := Nat.sqrt_le_self (Q * k2).toNat
    omega
  have h1 : bits (1 : ℤ) = 1 := by decide
  rw [h1]
  dsimp only [Ty.denote] at hs hi ⊢
  omega

theorem rowFn_cost (cst : CstTy.denote) (V : (Ty.list .int).denote) (i : Ty.int.denote)
    (Si : (Ty.list .int).denote) (Vi : Ty.int.denote) (Z : ℕ)
    (hcst : CstTy.Bnd Z cst) (hi : bits i ≤ Z) (hVi : bits Vi ≤ Z)
    (hSi : ∀ x ∈ Si, bits x ≤ Z) (hV : ∀ x ∈ V, bits x ≤ Z) (hlen : Si.length ≤ Z) :
    rowFn.costAt ((cst, V), (i, (Si, Vi))) ≤
      (Si.length + 1) * (11759 * (Z + 1) ^ 2 + 3 * Si.length + 40) + 62 * (Si.length + 1) + 30 := by
  unfold Fn.costAt rowFn
  rw [cost_call]
  have hz := zipFn_cost .int .int Si V
  have hzl : (Si.zip V).length ≤ Si.length := by simp
  have hm := mapIdxFn_cost entryFn (cst, i, Vi) (Si.zip V) (11759 * (Z + 1) ^ 2) (by
    intro j hj x hx
    have hb := (Fn.loopFree_bound entryFn entryFn_loopFree ((cst, i, Vi), (j : ℤ), x) Z ?_).2
    · rw [entryFn_kbc] at hb; exact hb
    · obtain ⟨hx1, hx2⟩ : x.1 ∈ Si ∧ x.2 ∈ V := ⟨List.of_mem_zip hx |>.1, List.of_mem_zip hx |>.2⟩
      have hj' : bits (j : ℤ) ≤ Z := by
        have := bits_le_self_natAbs (j : ℤ); simp at this; omega
      exact ⟨⟨hcst, hi, hVi⟩, hj', hSi _ hx1, hV _ hx2⟩)
  simp only [Expr.cost, cost_call, Var.index, Expr.denote, Var.get, denote_call, zipFn_apply] at hz hm ⊢
  have : (Si.zip V).length + 1 ≤ Si.length + 1 := by omega
  have h2 : ((Si.zip V).length + 1) * (11759 * (Z + 1) ^ 2 + 3 * (Si.zip V).length + 40) ≤
      (Si.length + 1) * (11759 * (Z + 1) ^ 2 + 3 * Si.length + 40) :=
    Nat.mul_le_mul this (by omega)
  dsimp only [Ty.denote] at hz hm h2 ⊢
  omega

theorem pow_mono_one {w : ℕ} (hw : 1 ≤ w) (a b : ℕ) (hab : a ≤ b) : w ^ a ≤ w ^ b :=
  Nat.pow_le_pow_right hw hab

theorem sq_le_of {x c w : ℕ} (h : x ≤ c * w) : x ^ 2 ≤ (c * c) * w ^ 2 := by
  calc x ^ 2 ≤ (c * w) ^ 2 := Nat.pow_le_pow_left h 2
    _ = (c * c) * w ^ 2 := by ring

theorem cube_le_of {x c w : ℕ} (h : x ≤ c * w) : x ^ 3 ≤ (c * c * c) * w ^ 3 := by
  calc x ^ 3 ≤ (c * w) ^ 3 := Nat.pow_le_pow_left h 3
    _ = (c * c * c) * w ^ 3 := by ring

theorem bits_isqrt_le (x : ℤ) : bits (isqrt x) ≤ bits x := by
  apply bits_mono; unfold isqrt; have := Nat.sqrt_le_self x.toNat; omega

/-- The update costs at most `2^60 (W + 1)^4` when all stored integers, the dimension and the
grid exponent have binary length (resp. value) at most `W`. -/
theorem updFn_cost (N k W : ℕ) (c a : (Ty.list .int).denote) (S : (Ty.list (.list .int)).denote)
    (hNW : N ≤ W) (hkW : k + 1 ≤ W) (hc : c.length ≤ N) (hS : S.length ≤ N)
    (hrows : ∀ row ∈ S, row.length ≤ N) (ha : a.length ≤ N)
    (bc : ∀ x ∈ c, bits x ≤ W) (bS : ∀ row ∈ S, ∀ x ∈ row, bits x ≤ W) (ba : ∀ x ∈ a, bits x ≤ W) :
    updFn.costAt ((N : ℤ), (2 : ℤ) ^ k, c, S, a) ≤ 2 ^ 60 * (W + 1) ^ 4 := by
  -- values
  set V := S.map (fun row => dotL row a) with hVdef
  set Q := dotL a V with hQdef
  have hV : ∀ x ∈ V, bits x ≤ 3 * W := by
    intro x hx
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hx
    have := bits_dotL_le row a W N (hrows row hrow) (bS row hrow) ba
    omega
  have hVl : V.length ≤ N := by simp [hVdef]; omega
  have hQ : bits Q ≤ 7 * W := by
    have h := bits_dotL_le a V (3 * W) N ha (fun y hy => by have := ba y hy; omega) hV
    rw [← hQdef] at h
    omega
  have hk2 : bits ((2 : ℤ) ^ k) ≤ W := by rw [bits_pow_two]; omega
  have hQk : bits (Q * 2 ^ k) ≤ 8 * W := by
    have := bits_mul_le Q (2 ^ k); omega
  have hNb : bits (N : ℤ) ≤ W := by
    have := bits_le_self_natAbs (N : ℤ); simp at this; omega
  set R := isqrt (Q * 2 ^ k) + 1 with hRdef
  have hR : bits R ≤ 8 * W + 1 := by
    have ha1 := bits_add_le (isqrt (Q * 2 ^ k)) 1
    have ha2 := bits_isqrt_le (Q * 2 ^ k)
    have h1 : bits (1 : ℤ) = 1 := by decide
    rw [h1, ← hRdef] at ha1
    omega
  -- loop-free pieces
  have hsc := Fn.loopFree_bound scalarsFn scalarsFn_loopFree ((N : ℤ), Q) (7 * W)
    ⟨le_trans hNb (by omega), hQ⟩
  rw [scalarsFn_sbc, scalarsFn_kbc] at hsc
  have hd1 := Fn.loopFree_bound d1Fn d1Fn_loopFree ((N : ℤ), R) (8 * W + 1)
    ⟨le_trans hNb (by omega), hR⟩
  rw [d1Fn_sbc, d1Fn_kbc] at hd1
  have hD1 : bits ((N + 1 : ℤ) * R) ≤ 4 * (8 * W + 2) := hd1.1
  -- costs of the calls
  have cmv := mapFn_cost dotRevFn a S (4 * (N + 1) * (W + N + 10) ^ 2 + 10) (fun row hrow =>
    dotRevFn_cost a row W N (hrows row hrow) (bS row hrow) ba)
  have cdot := dotFn_cost a V (3 * W) N ha (fun y hy => by have := ba y hy; omega) hV
  have croot := rootFn_cost Q ((2 : ℤ) ^ k)
  have Zc := 4 * (8 * W + 2) + 3 * W
  have ccen := zipWithFn_cost centerEntryFn ((2 : ℤ) ^ k, (N + 1 : ℤ) * R) c V
    (39 * (4 * (8 * W + 2) + 3 * W + 1) ^ 2) (fun x hx y hy => by
      have hb := (Fn.loopFree_bound centerEntryFn centerEntryFn_loopFree
        (((2 : ℤ) ^ k, (N + 1 : ℤ) * R), x, y) (4 * (8 * W + 2) + 3 * W)
        ⟨⟨le_trans hk2 (by omega), le_trans hD1 (by omega)⟩,
          le_trans (bc x hx) (by omega),
          le_trans (hV y hy) (by omega)⟩).2
      rw [centerEntryFn_kbc] at hb
      exact hb)
  have czip := zipFn_cost (.list .int) .int S V
  set Ze := 1638 * (7 * W + 1) + 3 * W with hZe
  have crows := mapIdxFn_cost rowFn (scalarsL N Q, V) (S.zip V)
    ((N + 1) * (11759 * (Ze + 1) ^ 2 + 3 * N + 40) + 62 * (N + 1) + 30) (by
      rintro i hi ⟨x1, x2⟩ hx
      obtain ⟨hx1, hx2⟩ : x1 ∈ S ∧ x2 ∈ V := ⟨List.of_mem_zip hx |>.1, List.of_mem_zip hx |>.2⟩
      have hb := rowFn_cost (scalarsL N Q) V (i : ℤ) x1 x2 Ze
        (Ty.Bnd.mono _ (show 1638 * (7 * W + 1) ≤ Ze by rw [hZe]; omega)
          (by have h := hsc.1; rwa [scalarsFn_apply] at h))
        (by
          have h1 := bits_le_self_natAbs (i : ℤ)
          have h2 : i < (S.zip V).length := hi
          have h3 : (S.zip V).length ≤ S.length := by simp
          simp only [Int.natAbs_natCast] at h1
          rw [hZe]; omega)
        (by have := hV _ hx2; rw [hZe]; omega)
        (fun y hy => by have := bS _ hx1 y hy; rw [hZe]; omega)
        (fun y hy => by have := hV y hy; rw [hZe]; omega)
        (by have := hrows _ hx1; rw [hZe]; omega)
      have hl := hrows _ hx1
      have e1 : (x1.length + 1) * (11759 * (Ze + 1) ^ 2 + 3 * x1.length + 40) ≤
          (N + 1) * (11759 * (Ze + 1) ^ 2 + 3 * N + 40) := Nat.mul_le_mul (by omega) (by omega)
      omega)
  -- assemble
  unfold Fn.costAt updFn
  simp only [Expr.cost, cost_call, Var.index, Expr.denote, Var.get, denote_call, matVecFn_apply,
    dotFn_apply, rootFn_apply, scalarsFn_apply, d1Fn_apply, zipFn_apply]
  simp only [← hVdef, ← hQdef, ← hRdef]
  have cmv' : matVecFn.costAt (a, S) ≤ (S.length + 1) * (4 * (N + 1) * (W + N + 10) ^ 2 + 10 + 17) :=
    cmv
  have hzl : (S.zip V).length ≤ N := by simp; omega
  -- normalise every bound to a multiple of a power of `w = W + 1`
  have hw1 : 1 ≤ W + 1 := by omega
  have p12 : W + 1 ≤ (W + 1) ^ 2 := by simpa using pow_mono_one hw1 1 2 (by norm_num)
  have p23 : (W + 1) ^ 2 ≤ (W + 1) ^ 3 := pow_mono_one hw1 2 3 (by norm_num)
  have p34 : (W + 1) ^ 3 ≤ (W + 1) ^ 4 := pow_mono_one hw1 3 4 (by norm_num)
  have hN1 : N + 1 ≤ W + 1 := by omega
  have b1 : matVecFn.costAt (a, S) ≤ 427 * (W + 1) ^ 4 := by
    have h1 : (W + N + 10) ^ 2 ≤ (10 * 10) * (W + 1) ^ 2 := sq_le_of (by omega)
    have h2 : 4 * (N + 1) * (W + N + 10) ^ 2 ≤ 400 * (W + 1) ^ 3 := by
      calc 4 * (N + 1) * (W + N + 10) ^ 2 ≤ 4 * (W + 1) * ((10 * 10) * (W + 1) ^ 2) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ hN1) h1
        _ = 400 * (W + 1) ^ 3 := by ring
    calc matVecFn.costAt (a, S) ≤ (S.length + 1) * (4 * (N + 1) * (W + N + 10) ^ 2 + 10 + 17) := cmv'
      _ ≤ (W + 1) * (400 * (W + 1) ^ 3 + 27 * (W + 1) ^ 3) := Nat.mul_le_mul (by omega) (by
          have : 1 ≤ (W + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
          omega)
      _ = 427 * (W + 1) ^ 4 := by ring
  have b2 : dotFn.costAt (a, V) ≤ 400 * (W + 1) ^ 4 := by
    have h1 : (3 * W + N + 10) ^ 2 ≤ (10 * 10) * (W + 1) ^ 2 := sq_le_of (by omega)
    calc dotFn.costAt (a, V) ≤ 4 * (N + 1) * (3 * W + N + 10) ^ 2 := cdot
      _ ≤ 4 * (W + 1) * ((10 * 10) * (W + 1) ^ 2) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hN1) h1
      _ = 400 * (W + 1) ^ 3 := by ring
      _ ≤ 400 * (W + 1) ^ 4 := Nat.mul_le_mul_left _ p34
  have b3 : rootFn.costAt (Q, 2 ^ k) ≤ 8300 * (W + 1) ^ 4 := by
    have h1 : (bits (Q * 2 ^ k) + 6) ^ 3 ≤ (8 * 8 * 8) * (W + 1) ^ 3 := cube_le_of (by omega)
    have h2 : (bits Q + 1) * (bits ((2 : ℤ) ^ k) + 1) ≤ 8 * (W + 1) ^ 2 := by
      calc (bits Q + 1) * (bits ((2 : ℤ) ^ k) + 1) ≤ (8 * (W + 1)) * (W + 1) :=
            Nat.mul_le_mul (by omega) (by omega)
        _ = 8 * (W + 1) ^ 2 := by ring
    have := croot
    omega
  have b4 : scalarsFn.costAt ((N : ℤ), Q) ≤ 1140950 * (8 * 8) * (W + 1) ^ 4 := by
    have h := hsc.2
    have h1 : (7 * W + 1) ^ 2 ≤ (8 * 8) * (W + 1) ^ 2 := sq_le_of (by omega)
    have h2 := Nat.mul_le_mul_left 1140950 h1
    have h3 : (W + 1) ^ 2 ≤ (W + 1) ^ 4 := le_trans p23 p34
    have h4 := Nat.mul_le_mul_left (1140950 * (8 * 8)) h3
    rw [show 1140950 * ((8 * 8) * (W + 1) ^ 2) = 1140950 * (8 * 8) * (W + 1) ^ 2 by ring] at h2
    norm_num at h2 h4 ⊢
    omega
  have b5 : d1Fn.costAt ((N : ℤ), R) ≤ 18 * (10 * 10) * (W + 1) ^ 4 := by
    have h := hd1.2
    have h1 : (8 * W + 1 + 1) ^ 2 ≤ (10 * 10) * (W + 1) ^ 2 := sq_le_of (by omega)
    have h2 := Nat.mul_le_mul_left 18 h1
    have h3 : (W + 1) ^ 2 ≤ (W + 1) ^ 4 := le_trans p23 p34
    have h4 := Nat.mul_le_mul_left (18 * (10 * 10)) h3
    rw [show 18 * ((10 * 10) * (W + 1) ^ 2) = 18 * (10 * 10) * (W + 1) ^ 2 by ring] at h2
    norm_num at h2 h4 ⊢
    omega
  have b6 : (zipWithFn centerEntryFn).costAt (((2 : ℤ) ^ k, ((N : ℤ) + 1) * R), c, V) ≤
      65000 * (W + 1) ^ 4 := by
    have h1 : (4 * (8 * W + 2) + 3 * W + 1) ^ 2 ≤ (40 * 40) * (W + 1) ^ 2 := sq_le_of (by omega)
    calc _ ≤ (c.length + 1) * (39 * (4 * (8 * W + 2) + 3 * W + 1) ^ 2 + 60) := ccen
      _ ≤ (W + 1) * (39 * ((40 * 40) * (W + 1) ^ 2) + 60 * (W + 1) ^ 2) := Nat.mul_le_mul (by omega) (by
          have : 1 ≤ (W + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
          omega)
      _ = 62460 * (W + 1) ^ 3 := by ring
      _ ≤ 65000 * (W + 1) ^ 4 := by have := Nat.mul_le_mul_left 62460 p34; omega
  have b7 : (zipFn (.list .int) .int).costAt (S, V) ≤ 66 * (W + 1) ^ 4 := by
    have := czip
    have : W + 1 ≤ (W + 1) ^ 4 := le_trans p12 (le_trans p23 p34)
    omega
  have b8 : (mapIdxFn rowFn).costAt ((scalarsL N Q, V), S.zip V) ≤ 2 ^ 44 * (W + 1) ^ 4 := by
    have h1 : (Ze + 1) ^ 2 ≤ (11470 * 11470) * (W + 1) ^ 2 := sq_le_of (by rw [hZe]; omega)
    have h2 : 11759 * (Ze + 1) ^ 2 + 3 * N + 40 ≤ 2 ^ 41 * (W + 1) ^ 2 := by
      have := Nat.mul_le_mul_left 11759 h1
      have : 1 ≤ (W + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
      omega
    have h3 : (N + 1) * (11759 * (Ze + 1) ^ 2 + 3 * N + 40) + 62 * (N + 1) + 30 + 3 * N + 40 ≤
        2 ^ 42 * (W + 1) ^ 3 := by
      have h4 : (N + 1) * (11759 * (Ze + 1) ^ 2 + 3 * N + 40) ≤ (W + 1) * (2 ^ 41 * (W + 1) ^ 2) :=
        Nat.mul_le_mul hN1 h2
      have e : (W + 1) * (2 ^ 41 * (W + 1) ^ 2) = 2 ^ 41 * (W + 1) ^ 3 := by ring
      have : 1 ≤ (W + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
      omega
    calc _ ≤ ((S.zip V).length + 1) * ((N + 1) * (11759 * (Ze + 1) ^ 2 + 3 * N + 40) + 62 * (N + 1) + 30
          + 3 * (S.zip V).length + 40) := crows
      _ ≤ (W + 1) * (2 ^ 42 * (W + 1) ^ 3) := Nat.mul_le_mul (by omega) (by omega)
      _ = 2 ^ 42 * (W + 1) ^ 4 := by ring
      _ ≤ 2 ^ 44 * (W + 1) ^ 4 := Nat.mul_le_mul_right _ (by norm_num)
  have : 1 ≤ (W + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
  dsimp only [Ty.denote] at b1 b2 b3 b4 b5 b6 b7 b8 ⊢
  omega

end MWIS.FunLP

end
