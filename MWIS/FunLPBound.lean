module

public import MWIS.FunLPList

/-!
# Uniform cost bounds for loop-free expressions

For an expression without folds, iterations and tree conversions, if every
integer stored in the environment has binary length at most `W`, then every
integer in its value has binary length at most `sbc e * (W + 1)` and its cost is
at most `kbc e * (W + 1) ^ 2`. Both coefficients are numerals computed from the
syntax.
-/

@[expose] public section

namespace MWIS.Fun

/-- Every integer stored in a value has binary length at most `W`. -/
def Ty.Bnd : (τ : Ty) → ℕ → τ.denote → Prop
  | .int, W, v => bits v ≤ W
  | .bool, _, _ => True
  | .unit, _, _ => True
  | .tree, _, _ => True
  | .prod a b, W, v => Ty.Bnd a W v.1 ∧ Ty.Bnd b W v.2
  | .list a, W, v => ∀ x ∈ v, Ty.Bnd a W x

theorem Ty.Bnd.mono : (τ : Ty) → {W W' : ℕ} → W ≤ W' → {v : τ.denote} → τ.Bnd W v → τ.Bnd W' v
  | .int, _, _, h, _, hv => le_trans hv h
  | .bool, _, _, _, _, _ => trivial
  | .unit, _, _, _, _, _ => trivial
  | .tree, _, _, _, _, _ => trivial
  | .prod a b, _, _, h, _, hv => ⟨Ty.Bnd.mono a h hv.1, Ty.Bnd.mono b h hv.2⟩
  | .list a, _, _, h, _, hv => fun x hx => Ty.Bnd.mono a h (hv x hx)

/-- Every integer stored in an environment has binary length at most `W`. -/
def Env.Bnd : {Γ : List Ty} → Env Γ → ℕ → Prop
  | [], _, _ => True
  | τ :: _, env, W => τ.Bnd W env.1 ∧ Env.Bnd env.2 W

theorem Env.Bnd.mono : {Γ : List Ty} → {env : Env Γ} → {W W' : ℕ} → W ≤ W' →
    Env.Bnd env W → Env.Bnd env W'
  | [], _, _, _, _, _ => trivial
  | τ :: _, _, _, _, h, hv => ⟨Ty.Bnd.mono τ h hv.1, Env.Bnd.mono h hv.2⟩

theorem Var.get_bnd {Γ : List Ty} {τ : Ty} (v : Var Γ τ) {env : Env Γ} {W : ℕ}
    (h : Env.Bnd env W) : τ.Bnd W (v.get env) := by
  induction v with
  | here => exact h.1
  | there v ih => exact ih h.2

namespace Expr

/-- The loop-free fragment: no folds, no iterations and no tree conversions. -/
def loopFree {Γ : List Ty} {τ : Ty} : Expr Γ τ → Bool
  | .var _ => true
  | .int _ => true
  | .bool _ => true
  | .unit => true
  | .arith _ x y => x.loopFree && y.loopFree
  | .cmp _ x y => x.loopFree && y.loopFree
  | .ite c t e => c.loopFree && t.loopFree && e.loopFree
  | .pair x y => x.loopFree && y.loopFree
  | .fst p => p.loopFree
  | .snd p => p.loopFree
  | .nil => true
  | .cons x xs => x.loopFree && xs.loopFree
  | .listCase xs n c => xs.loopFree && n.loopFree && c.loopFree
  | .foldl _ _ _ => false
  | .iter _ _ _ => false
  | .letE x b => x.loopFree && b.loopFree
  | .treeCase t a b c d e f =>
      t.loopFree && a.loopFree && b.loopFree && c.loopFree && d.loopFree && e.loopFree && f.loopFree
  | .treeNil => true
  | .treeBit b t => b.loopFree && t.loopFree
  | .treeCons x t => x.loopFree && t.loopFree
  | .treePair x y => x.loopFree && y.loopFree
  | .items _ => false
  | .ofItems _ => false
  | .wordValue _ => false
  | .word _ _ => false
  | .size x => x.loopFree

/-- Linear coefficient for the binary lengths of the integers in the value. -/
def sbc {Γ : List Ty} {τ : Ty} : Expr Γ τ → ℕ
  | .var _ => 1
  | .int z => bits z
  | .bool _ => 0
  | .unit => 0
  | .arith .add x y => x.sbc + y.sbc + 1
  | .arith .sub x y => x.sbc + y.sbc + 1
  | .arith .mul x y => x.sbc + y.sbc
  | .arith .div x _ => x.sbc
  | .arith .mod x y => x.sbc + y.sbc
  | .cmp _ _ _ => 0
  | .ite _ t e => t.sbc + e.sbc
  | .pair x y => x.sbc + y.sbc
  | .fst p => p.sbc
  | .snd p => p.sbc
  | .nil => 0
  | .cons x xs => x.sbc + xs.sbc
  | .listCase xs n c => n.sbc + c.sbc * (xs.sbc + 1)
  | .foldl _ _ _ => 0
  | .iter _ _ _ => 0
  | .letE x b => b.sbc * (x.sbc + 1)
  | .treeCase _ a b c d e f => a.sbc + b.sbc + c.sbc + d.sbc + e.sbc + f.sbc
  | .treeNil => 0
  | .treeBit _ _ => 0
  | .treeCons _ _ => 0
  | .treePair _ _ => 0
  | .items _ => 0
  | .ofItems _ => 0
  | .wordValue _ => 0
  | .word _ _ => 0
  | .size x => x.sbc

/-- Quadratic coefficient for the cost. -/
def kbc {Γ : List Ty} {τ : Ty} : Expr Γ τ → ℕ
  | .var v => v.index + 1
  | .int _ => 1
  | .bool _ => 1
  | .unit => 1
  | .arith .add x y => x.kbc + y.kbc + (x.sbc + y.sbc + 1) + 1
  | .arith .sub x y => x.kbc + y.kbc + (x.sbc + y.sbc + 1) + 1
  | .arith .mul x y => x.kbc + y.kbc + (x.sbc + 1) * (y.sbc + 1) + 1
  | .arith .div x y => x.kbc + y.kbc + (x.sbc + y.sbc + 1) ^ 2 + 1
  | .arith .mod x y => x.kbc + y.kbc + (x.sbc + y.sbc + 1) ^ 2 + 1
  | .cmp _ x y => x.kbc + y.kbc + (x.sbc + y.sbc + 1) + 1
  | .ite c t e => c.kbc + t.kbc + e.kbc + 1
  | .pair x y => x.kbc + y.kbc + 1
  | .fst p => p.kbc + 1
  | .snd p => p.kbc + 1
  | .nil => 1
  | .cons x xs => x.kbc + xs.kbc + 1
  | .listCase xs n c => xs.kbc + n.kbc + c.kbc * (xs.sbc + 1) ^ 2 + 1
  | .foldl _ _ _ => 0
  | .iter _ _ _ => 0
  | .letE x b => x.kbc + b.kbc * (x.sbc + 1) ^ 2 + 1
  | .treeCase t a b c d e f => t.kbc + a.kbc + b.kbc + c.kbc + d.kbc + e.kbc + f.kbc + 1
  | .treeNil => 1
  | .treeBit b t => b.kbc + t.kbc + 1
  | .treeCons x t => x.kbc + t.kbc + 1
  | .treePair x y => x.kbc + y.kbc + 1
  | .items _ => 0
  | .ofItems _ => 0
  | .wordValue _ => 0
  | .word _ _ => 0
  | .size x => x.kbc + x.sbc + 1

end Expr

/-! ## Soundness -/

theorem bits_ediv_le (x y : ℤ) : bits (x / y) ≤ bits x := by
  apply FunLP.bits_mono
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · exact Int.natAbs_ediv_le_natAbs x y

theorem bits_emod_le (x y : ℤ) : bits (x % y) ≤ bits x + bits y := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · have h1 : 0 ≤ x % y := Int.emod_nonneg x hy
    have h2 : x % y < (y.natAbs : ℤ) := Int.emod_lt x hy
    have : (x % y).natAbs ≤ y.natAbs := by omega
    have := FunLP.bits_mono (x := x % y) (y := y) this
    omega

private theorem w_pos (W : ℕ) : 1 ≤ (W + 1) := by omega

private theorem w_le_sq (W : ℕ) : W + 1 ≤ (W + 1) ^ 2 := by nlinarith

set_option maxHeartbeats 2000000 in
theorem bound_sound {Γ : List Ty} {τ : Ty} (e : Expr Γ τ) : e.loopFree = true →
    ∀ (env : Env Γ) (W : ℕ), Env.Bnd env W →
      τ.Bnd (e.sbc * (W + 1)) (e.denote env) ∧ e.cost env ≤ e.kbc * (W + 1) ^ 2 := by
  induction e with
  | var v =>
    intro _ env W h
    refine ⟨Ty.Bnd.mono _ (by simp [Expr.sbc]) (Var.get_bnd v h), ?_⟩
    simp only [Expr.cost, Expr.kbc]
    nlinarith [w_le_sq W, w_pos W]
  | int z =>
    intro _ env W _
    refine ⟨?_, ?_⟩
    · show bits z ≤ bits z * (W + 1)
      nlinarith
    · simp only [Expr.cost, Expr.kbc]; nlinarith [w_le_sq W]
  | bool b => intro _ env W _; exact ⟨trivial, by simp only [Expr.cost, Expr.kbc]; nlinarith [w_le_sq W]⟩
  | unit => intro _ env W _; exact ⟨trivial, by simp only [Expr.cost, Expr.kbc]; nlinarith [w_le_sq W]⟩
  | arith op x y ihx ihy =>
    intro hlf env W h
    simp only [Expr.loopFree, Bool.and_eq_true] at hlf
    obtain ⟨bx, cx⟩ := ihx hlf.1 env W h
    obtain ⟨by_, cy⟩ := ihy hlf.2 env W h
    change bits _ ≤ _ at bx by_
    have hw := w_le_sq W
    have hw1 := w_pos W
    cases op with
    | add =>
      refine ⟨?_, ?_⟩
      · show bits (x.denote env + y.denote env) ≤ _
        have := FunLP.bits_add_le (x.denote env) (y.denote env)
        simp only [Expr.sbc]
        have := max_le_iff.mpr ⟨le_trans bx (Nat.le_add_right _ (y.sbc * (W+1))),
          le_trans by_ (Nat.le_add_left _ (x.sbc * (W+1)))⟩
        nlinarith
      · simp only [Expr.cost, Expr.kbc, IntOp.charge]
        nlinarith
    | sub =>
      refine ⟨?_, ?_⟩
      · show bits (x.denote env - y.denote env) ≤ _
        have := FunLP.bits_sub_le (x.denote env) (y.denote env)
        simp only [Expr.sbc]
        have := max_le_iff.mpr ⟨le_trans bx (Nat.le_add_right _ (y.sbc * (W+1))),
          le_trans by_ (Nat.le_add_left _ (x.sbc * (W+1)))⟩
        nlinarith
      · simp only [Expr.cost, Expr.kbc, IntOp.charge]
        nlinarith
    | mul =>
      refine ⟨?_, ?_⟩
      · show bits (x.denote env * y.denote env) ≤ _
        have := FunLP.bits_mul_le (x.denote env) (y.denote env)
        simp only [Expr.sbc]
        nlinarith
      · simp only [Expr.cost, Expr.kbc, IntOp.charge]
        have h1 : (bits (x.denote env) + 1) * (bits (y.denote env) + 1) ≤
            (x.sbc * (W + 1) + 1) * (y.sbc * (W + 1) + 1) := Nat.mul_le_mul (by omega) (by omega)
        have h2 : (x.sbc * (W + 1) + 1) * (y.sbc * (W + 1) + 1) ≤
            (x.sbc + 1) * (y.sbc + 1) * (W + 1) ^ 2 := by nlinarith
        nlinarith
    | div =>
      refine ⟨?_, ?_⟩
      · show bits (x.denote env / y.denote env) ≤ _
        have := bits_ediv_le (x.denote env) (y.denote env)
        simp only [Expr.sbc]
        omega
      · simp only [Expr.cost, Expr.kbc, IntOp.charge]
        have h1 : (bits (x.denote env) + bits (y.denote env) + 1) ^ 2 ≤
            ((x.sbc + y.sbc + 1) * (W + 1)) ^ 2 := Nat.pow_le_pow_left (by nlinarith) 2
        rw [mul_pow] at h1
        nlinarith
    | mod =>
      refine ⟨?_, ?_⟩
      · show bits (x.denote env % y.denote env) ≤ _
        have := bits_emod_le (x.denote env) (y.denote env)
        simp only [Expr.sbc]
        nlinarith
      · simp only [Expr.cost, Expr.kbc, IntOp.charge]
        have h1 : (bits (x.denote env) + bits (y.denote env) + 1) ^ 2 ≤
            ((x.sbc + y.sbc + 1) * (W + 1)) ^ 2 := Nat.pow_le_pow_left (by nlinarith) 2
        rw [mul_pow] at h1
        nlinarith
  | cmp op x y ihx ihy =>
    intro hlf env W h
    simp only [Expr.loopFree, Bool.and_eq_true] at hlf
    obtain ⟨bx, cx⟩ := ihx hlf.1 env W h
    obtain ⟨by_, cy⟩ := ihy hlf.2 env W h
    change bits _ ≤ _ at bx by_
    refine ⟨trivial, ?_⟩
    simp only [Expr.cost, Expr.kbc, CmpOp.charge]
    nlinarith [w_le_sq W, w_pos W]
  | ite c t f ihc iht ihf =>
    intro hlf env W h
    simp only [Expr.loopFree, Bool.and_eq_true] at hlf
    obtain ⟨_, cc⟩ := ihc hlf.1.1 env W h
    obtain ⟨bt, ct⟩ := iht hlf.1.2 env W h
    obtain ⟨bf, cf⟩ := ihf hlf.2 env W h
    refine ⟨?_, ?_⟩
    · simp only [Expr.denote, Expr.sbc]
      split
      · exact Ty.Bnd.mono _ (by nlinarith) bt
      · exact Ty.Bnd.mono _ (by nlinarith) bf
    · simp only [Expr.cost, Expr.kbc]
      have hw := w_le_sq W
      split <;> nlinarith
  | pair x y ihx ihy =>
    intro hlf env W h
    simp only [Expr.loopFree, Bool.and_eq_true] at hlf
    obtain ⟨bx, cx⟩ := ihx hlf.1 env W h
    obtain ⟨by_, cy⟩ := ihy hlf.2 env W h
    refine ⟨⟨Ty.Bnd.mono _ (by simp only [Expr.sbc]; nlinarith) bx,
      Ty.Bnd.mono _ (by simp only [Expr.sbc]; nlinarith) by_⟩, ?_⟩
    simp only [Expr.cost, Expr.kbc]
    nlinarith [w_le_sq W]
  | fst p ih =>
    intro hlf env W h
    obtain ⟨b, c⟩ := ih hlf env W h
    exact ⟨b.1, by simp only [Expr.cost, Expr.kbc]; nlinarith [w_le_sq W]⟩
  | snd p ih =>
    intro hlf env W h
    obtain ⟨b, c⟩ := ih hlf env W h
    exact ⟨b.2, by simp only [Expr.cost, Expr.kbc]; nlinarith [w_le_sq W]⟩
  | nil =>
    intro _ env W _
    exact ⟨fun x hx => by simp [Expr.denote] at hx, by simp only [Expr.cost, Expr.kbc]; nlinarith [w_le_sq W]⟩
  | cons x xs ihx ihxs =>
    intro hlf env W h
    simp only [Expr.loopFree, Bool.and_eq_true] at hlf
    obtain ⟨bx, cx⟩ := ihx hlf.1 env W h
    obtain ⟨bxs, cxs⟩ := ihxs hlf.2 env W h
    refine ⟨?_, ?_⟩
    · intro z hz
      simp only [Expr.denote, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact Ty.Bnd.mono _ (by simp only [Expr.sbc]; nlinarith) bx
      · exact Ty.Bnd.mono _ (by simp only [Expr.sbc]; nlinarith) (bxs z hz)
    · simp only [Expr.cost, Expr.kbc]
      nlinarith [w_le_sq W]
  | @listCase Γ' a b xs n c ihxs ihn ihc =>
    intro hlf env W h
    simp only [Expr.loopFree, Bool.and_eq_true] at hlf
    obtain ⟨bxs, cxs⟩ := ihxs hlf.1.1 env W h
    obtain ⟨bn, cn⟩ := ihn hlf.1.2 env W h
    have hw := w_le_sq W
    simp only [Expr.denote, Expr.cost, Expr.sbc, Expr.kbc]
    split
    · refine ⟨Ty.Bnd.mono _ (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)) bn, ?_⟩
      have e : (xs.kbc + n.kbc + c.kbc * (xs.sbc + 1) ^ 2 + 1) * (W + 1) ^ 2 =
          xs.kbc * (W + 1) ^ 2 + n.kbc * (W + 1) ^ 2 + c.kbc * (xs.sbc + 1) ^ 2 * (W + 1) ^ 2 +
            (W + 1) ^ 2 := by ring
      have : 1 ≤ (W + 1) ^ 2 := by nlinarith
      omega
    · rename_i y ys hys
      rw [hys] at bxs
      have henv : Env.Bnd (Γ := a :: .list a :: Γ') (y, ys, env) (xs.sbc * (W + 1) + W) := by
        simp only [Env.Bnd]
        exact ⟨Ty.Bnd.mono _ (by omega) (bxs y (by simp)),
          fun z hz => Ty.Bnd.mono _ (by omega) (bxs z (by simp [hz])),
            Env.Bnd.mono (by omega) h⟩
      obtain ⟨bc, cc⟩ := ihc hlf.2 _ _ henv
      have e : xs.sbc * (W + 1) + W + 1 = (xs.sbc + 1) * (W + 1) := by ring
      rw [e] at bc cc
      refine ⟨Ty.Bnd.mono _ (by nlinarith) bc, ?_⟩
      rw [mul_pow] at cc
      nlinarith
  | foldl xs i s => intro hlf; simp [Expr.loopFree] at hlf
  | iter c i s => intro hlf; simp [Expr.loopFree] at hlf
  | @letE Γ' a b x body ihx ihb =>
    intro hlf env W h
    simp only [Expr.loopFree, Bool.and_eq_true] at hlf
    obtain ⟨bx, cx⟩ := ihx hlf.1 env W h
    have henv : Env.Bnd (Γ := a :: Γ') (x.denote env, env) (x.sbc * (W + 1) + W) := by
      simp only [Env.Bnd]
      exact ⟨Ty.Bnd.mono _ (by omega) bx, Env.Bnd.mono (by omega) h⟩
    obtain ⟨bb, cb⟩ := ihb hlf.2 _ _ henv
    have e : x.sbc * (W + 1) + W + 1 = (x.sbc + 1) * (W + 1) := by ring
    rw [e] at bb cb
    refine ⟨Ty.Bnd.mono _ (by simp only [Expr.sbc]; nlinarith) bb, ?_⟩
    simp only [Expr.cost, Expr.kbc]
    rw [mul_pow] at cb
    nlinarith [w_le_sq W]
  | treeCase t a b c d f g iht iha ihb ihc ihd ihf ihg =>
    intro hlf env W h
    simp only [Expr.loopFree, Bool.and_eq_true] at hlf
    obtain ⟨_, ct⟩ := iht hlf.1.1.1.1.1.1 env W h
    have hw := w_le_sq W
    simp only [Expr.denote, Expr.cost, Expr.sbc, Expr.kbc]
    split
    · obtain ⟨bb, cb⟩ := iha hlf.1.1.1.1.1.2 env W h
      exact ⟨Ty.Bnd.mono _ (by nlinarith) bb, by nlinarith⟩
    · rename_i bit u _
      obtain ⟨bb, cb⟩ := ihb hlf.1.1.1.1.2 (bit, u, env) W ⟨trivial, trivial, h⟩
      exact ⟨Ty.Bnd.mono _ (by nlinarith) bb, by nlinarith⟩
    · rename_i u v _
      obtain ⟨bb, cb⟩ := ihc hlf.1.1.1.2 (u, v, env) W ⟨trivial, trivial, h⟩
      exact ⟨Ty.Bnd.mono _ (by nlinarith) bb, by nlinarith⟩
    · rename_i u v _
      obtain ⟨bb, cb⟩ := ihd hlf.1.1.2 (u, v, env) W ⟨trivial, trivial, h⟩
      exact ⟨Ty.Bnd.mono _ (by nlinarith) bb, by nlinarith⟩
    · rename_i u _
      obtain ⟨bb, cb⟩ := ihf hlf.1.2 (u, env) W ⟨trivial, h⟩
      exact ⟨Ty.Bnd.mono _ (by nlinarith) bb, by nlinarith⟩
    · rename_i u v _
      obtain ⟨bb, cb⟩ := ihg hlf.2 (u, v, env) W ⟨trivial, trivial, h⟩
      exact ⟨Ty.Bnd.mono _ (by nlinarith) bb, by nlinarith⟩
  | treeNil => intro _ env W _; exact ⟨trivial, by simp only [Expr.cost, Expr.kbc]; nlinarith [w_le_sq W]⟩
  | treeBit b t ihb iht =>
    intro hlf env W h
    simp only [Expr.loopFree, Bool.and_eq_true] at hlf
    obtain ⟨_, cb⟩ := ihb hlf.1 env W h
    obtain ⟨_, ct⟩ := iht hlf.2 env W h
    exact ⟨trivial, by simp only [Expr.cost, Expr.kbc]; nlinarith [w_le_sq W]⟩
  | treeCons x t ihx iht =>
    intro hlf env W h
    simp only [Expr.loopFree, Bool.and_eq_true] at hlf
    obtain ⟨_, cx⟩ := ihx hlf.1 env W h
    obtain ⟨_, ct⟩ := iht hlf.2 env W h
    exact ⟨trivial, by simp only [Expr.cost, Expr.kbc]; nlinarith [w_le_sq W]⟩
  | treePair x y ihx ihy =>
    intro hlf env W h
    simp only [Expr.loopFree, Bool.and_eq_true] at hlf
    obtain ⟨_, cx⟩ := ihx hlf.1 env W h
    obtain ⟨_, cy⟩ := ihy hlf.2 env W h
    exact ⟨trivial, by simp only [Expr.cost, Expr.kbc]; nlinarith [w_le_sq W]⟩
  | items t => intro hlf; simp [Expr.loopFree] at hlf
  | ofItems t => intro hlf; simp [Expr.loopFree] at hlf
  | wordValue t => intro hlf; simp [Expr.loopFree] at hlf
  | word w k => intro hlf; simp [Expr.loopFree] at hlf
  | size x ih =>
    intro hlf env W h
    obtain ⟨bx, cx⟩ := ih hlf env W h
    change bits _ ≤ _ at bx
    refine ⟨?_, ?_⟩
    · show bits ((bits (x.denote env) : ℕ) : ℤ) ≤ _
      have := FunLP.bits_le_self_natAbs ((bits (x.denote env) : ℕ) : ℤ)
      simp only [Int.natAbs_natCast] at this
      simp only [Expr.sbc]
      omega
    · simp only [Expr.cost, Expr.kbc]
      nlinarith [w_le_sq W]

end MWIS.Fun

namespace MWIS.FunLP

open MWIS.Fun

/-- The uniform bound for a closed loop-free function. -/
theorem Fn.loopFree_bound {σ τ : Ty} (f : Fn σ τ) (hf : f.loopFree = true) (x : σ.denote) (W : ℕ)
    (hx : σ.Bnd W x) : τ.Bnd (f.sbc * (W + 1)) (f.apply x) ∧ f.costAt x ≤ f.kbc * (W + 1) ^ 2 :=
  bound_sound f hf (x, ()) W ⟨hx, trivial⟩

end MWIS.FunLP

end
