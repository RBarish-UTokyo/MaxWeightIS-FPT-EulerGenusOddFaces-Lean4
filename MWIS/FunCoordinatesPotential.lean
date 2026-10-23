module

public import MWIS.FunCoordinatesTree

/-!
# Tree potentials in `Fun`

`potFn` computes, along an encoded growth sequence, the tree potential with a given root
value of the unit edge vector at position `u` (the zero vector when `u` is not an edge).
Its value is the list of the values of `TreeCotree.potential`.
-/

@[expose] public section

namespace MWIS.FunCoordinates

open MWIS.Fun MWIS.FunLP MWIS.TreeCotree

/-- The argument: the encoded tree, the edge list, the vertex count, the root, the unit
position and the root value. -/
abbrev PotArg : Ty :=
  .prod (.list (.prod .int .int)) (.prod (.list (.prod .int .int)) (.prod .int (.prod .int (.prod .int .int))))

/-- `((root, c), k) ↦ if k = root then c else 0`. -/
def rootItem : Fn (.prod (.prod .int .int) .int) .int :=
  .ite (.cmp .eq (.snd v0) (.fst (.fst v0))) (.snd (.fst v0)) (.int 0)

/-- `((pos, val), (k, x)) ↦ if k = pos then val else x`. -/
def setItem : Fn (.prod (.prod .int .int) (.prod .int .int)) .int :=
  .ite (.cmp .eq (.fst (.snd v0)) (.fst (.fst v0))) (.snd (.fst v0)) (.snd (.snd v0))

/-- Replace the entry at a position. -/
def setIntFn : Fn (.prod (.prod .int .int) (.list .int)) (.list .int) := mapIdxFn setItem

/-- The initial potential: `c` at the root, `0` elsewhere. -/
def potInit : Expr [PotArg] (.list .int) :=
  call (cmapFn rootItem)
    (.pair (.pair (.fst (.snd (.snd (.snd v0)))) (.snd (.snd (.snd (.snd (.snd v0))))))
      (call crange (.fst (.snd (.snd v0)))))

/-- One potential step along the tree pair `(v, e)`. -/
def potStep : Expr [.prod .int .int, .list .int, PotArg] (.list .int) :=
  .letE (call getPairFn (.pair (.fst (.snd v2)) (.snd v0)))
    (.letE (.ite (.cmp .eq (.fst v0) (.fst v1)) (.snd v0) (.fst v0))
      (.letE (.arith .sub
          (.ite (.cmp .eq (.snd v2) (.fst (.snd (.snd (.snd (.snd v4)))))) (.int 1) (.int 0))
          (call getIntFn (.pair v3 v0)))
        (call setIntFn (.pair (.pair (.fst v3) v0) v4))))

/-- The tree potential. -/
def potFn : Fn PotArg (.list .int) := .foldl (.fst v0) potInit potStep

/-! ## Denotation -/

/-- The unit edge vector at an integer position. -/
def unitAt (u : ℤ) (e : ℤ) : ℤ := if e = u then 1 else 0

/-- One potential step on lists. -/
def potStepSpec (edges : List (ℤ × ℤ)) (u : ℤ) (x : List ℤ) (p : ℤ × ℤ) : List ℤ :=
  let lr := getI edges (0, 0) p.2
  let o := if lr.1 = p.1 then lr.2 else lr.1
  let val := unitAt u p.2 - getI x 0 o
  x.mapIdx fun k xk => if (k : ℤ) = p.1 then val else xk

@[simp] theorem setIntFn_apply (x : (Ty.prod (.prod .int .int) (.list .int)).denote) :
    setIntFn.apply x = x.2.mapIdx fun k xk => if (k : ℤ) = x.1.1 then x.1.2 else xk := by
  rw [setIntFn, mapIdxFn_apply']
  congr 1
  funext k xk
  by_cases h : (k : ℤ) = x.1.1 <;> simp [Fn.apply, setItem, Expr.denote, Var.get, CmpOp.eval, h]

theorem potStep_denote (arg : PotArg.denote) :
    (fun x p => potStep.denote (p, x, (arg, ()))) = potStepSpec arg.2.1 arg.2.2.2.2.1 := by
  funext x p
  simp only [potStep, potStepSpec, unitAt, Expr.denote, Var.get, denote_call, getPairFn_apply',
    getIntFn_apply', setIntFn_apply, CmpOp.eval, IntOp.eval]
  by_cases h1 : (getI arg.2.1 (0, 0) p.2).1 = p.1 <;> by_cases h2 : p.2 = arg.2.2.2.2.1 <;>
    simp [h1, h2]

theorem potInit_denote (arg : PotArg.denote) :
    potInit.denote (arg, ()) = (List.range arg.2.2.1.toNat).map
      (fun i : ℕ => if (i : ℤ) = arg.2.2.2.1 then arg.2.2.2.2.2 else 0) := by
  simp only [potInit, Expr.denote, Var.get, denote_call, cmapFn_apply', crange_apply, List.map_map]
  apply List.map_congr_left
  intro i _
  by_cases h : (i : ℤ) = arg.2.2.2.1 <;> simp [Fn.apply, rootItem, Expr.denote, Var.get, CmpOp.eval, h]

theorem potFn_apply (arg : PotArg.denote) :
    potFn.apply arg = arg.1.foldl (potStepSpec arg.2.1 arg.2.2.2.2.1)
      ((List.range arg.2.2.1.toNat).map
        (fun i : ℕ => if (i : ℤ) = arg.2.2.2.1 then arg.2.2.2.2.2 else 0)) := by
  rw [Fn.apply]
  simp only [potFn, Expr.denote, Var.get]
  rw [potStep_denote, potInit_denote]

/-! ## Agreement with the tree potentials -/

variable {m n : ℕ} (left right : Fin m → Fin n)

/-- The list of the values of a vertex function. -/
def vertexList (x : Fin n → ℤ) : List ℤ := List.ofFn x

theorem potStepSpec_step (u : ℤ) (x : Fin n → ℤ) (v : Fin n) (e : Fin m) :
    potStepSpec (edgeList left right) u (vertexList x) ((v : ℤ), (e : ℤ)) =
      vertexList (potentialStep left right (fun d : Fin m => unitAt u d) x (v, e)) := by
  unfold potStepSpec potentialStep vertexList other
  simp only [edgeList, getI_ofFn]
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp only [List.getElem_mapIdx, List.getElem_ofFn, Nat.cast_inj]
  try simp only [List.length_mapIdx, List.length_ofFn] at h1
  by_cases hk : k = (v : ℕ)
  · have hkv : (⟨k, h1⟩ : Fin n) = v := Fin.ext hk
    rw [if_pos hk, hkv, Function.update_self]
    by_cases hl : left e = v
    · have : ((left e : Fin n) : ℕ) = (v : ℕ) := by rw [hl]
      simp only [this, ite_true, hl, getI_ofFn]
    · have : ¬ ((left e : Fin n) : ℕ) = (v : ℕ) := fun h => hl (Fin.ext h)
      simp only [this, ite_false, hl, getI_ofFn]
  · have hkv : (⟨k, h1⟩ : Fin n) ≠ v := fun h => hk (by rw [← h])
    rw [if_neg hk, Function.update_of_ne hkv]

theorem potSpec_eq (root : Fin n) (u c : ℤ) (s : List (Fin n × Fin m)) :
    (treeCode s).foldl (potStepSpec (edgeList left right) u)
        ((List.range n).map (fun i : ℕ => if (i : ℤ) = ((root : ℕ) : ℤ) then c else 0)) =
      vertexList (potential left right root s c (fun d : Fin m => unitAt u d)) := by
  induction s using List.reverseRecOn with
  | nil =>
    simp only [treeCode, List.map_nil, List.foldl_nil]
    apply List.ext_getElem (by simp [vertexList])
    intro k h1 h2
    simp [vertexList, potential, Fin.ext_iff]
  | append_singleton s p ih =>
    simp only [treeCode, List.map_append, List.map_singleton, List.foldl_append,
      List.foldl_cons, List.foldl_nil] at ih ⊢
    rw [ih, potStepSpec_step, potential_snoc]

/-- **The potential program computes the tree potential of the unit vector at `u`.** -/
theorem potFn_potential (root : Fin n) (u c : ℤ) :
    potFn.apply (treeCode (tree left right root),
      (edgeList left right, ((n : ℤ), (((root : ℕ) : ℤ), (u, c))))) =
      vertexList (potential left right root (tree left right root) c
        (fun d : Fin m => unitAt u d)) := by
  rw [potFn_apply]
  simp only [Int.toNat_natCast]
  exact potSpec_eq left right root u c _

end MWIS.FunCoordinates

end
