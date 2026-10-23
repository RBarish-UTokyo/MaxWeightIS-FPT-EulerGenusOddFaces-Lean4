module

public import MWIS.FPTRegister
public import MWIS.GenericAccounting

/-!
# From the numerical stage to the fixed-parameter claim

If the numerical stage meets `FPTRegister.FunStageSpec` with a budget of
fixed-parameter shape in the number `d` of XP global kernel rows of the
component (`FunBudgetBound`), and the constants stage meets
`FPTRegister.ConstsSpec` with a polynomial budget (`ConstsBudgetBound`), then the
whole hard procedure has a budget of fixed-parameter shape (`fptHardBound`): its
other stages cost at most `2 ^ 26 · (n + m + W + w0 + 2) ^ 13` events
(`FPTRegister.fixedBudget_le`).
Together with valid coordinates, `Spec.FPTClaim` follows for every code table
carrying XP's entry procedure with the fixed-parameter hard procedure as its
hard procedure (`fptClaim_of_funStage`).
-/

@[expose] public section

namespace MWIS.FPTRegister

open MWIS.RegisterMachine MWIS.GenericAccounting
open MWIS.RegisterComponentSolve (HardBudget)

/-- A budget of fixed-parameter shape for the numerical stage, at XP's cost width
`NetworkWeights.width w0 n`, on every connected nonbipartite all-half instance with
nonnegative weights. Here `d` is the number of XP global kernel rows. -/
def FunBudgetBound (c : ℕ) (fb : ℕ → ℕ → HardBudget) : Prop :=
  ∀ (W w0 : ℕ) {n m : ℕ} {left right : Fin m → Fin n} (R : EmbeddingFaces.Ribbon left right)
    (w : Fin n → ℚ),
    Incidence.Connected left right → ¬ Incidence.Bipartite left right → (∀ v, 0 ≤ w v) →
    Persistence.Optimal (EdgeTransport.Adj left right) w (fun _ => 1 / 2) →
    fb W (NetworkWeights.width w0 n) R w ≤
      shape c (ComputedEmbeddedMatrices.globalRows R).length (n + m + W + w0 + 2)

/-- A polynomial budget for the constants stage. -/
def ConstsBudgetBound (c : ℕ) (cb : ℕ → ℕ → ℕ → ℕ) : Prop :=
  ∀ W n m, cb W n m ≤ 2 ^ c * (n + m + W + 2) ^ c

theorem shape_mono_c {c c' d X : ℕ} (hc : c ≤ c') (hX : 1 ≤ X) : shape c d X ≤ shape c' d X := by
  unfold shape
  exact Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ hc))
    (Nat.pow_le_pow_right hX hc)

theorem shape_double {c d X : ℕ} (hX : 1 ≤ X) : 2 * shape c d X ≤ shape (c + 1) d X := by
  unfold shape
  have h1 : 2 ^ (c * (d * d.size + 1)) * 2 ≤ 2 ^ ((c + 1) * (d * d.size + 1)) := by
    rw [← pow_succ]
    exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  calc 2 * (2 ^ (c * (d * d.size + 1)) * X ^ c)
      = (2 ^ (c * (d * d.size + 1)) * 2) * X ^ c := by ring
    _ ≤ 2 ^ ((c + 1) * (d * d.size + 1)) * X ^ c := Nat.mul_le_mul_right _ h1
    _ ≤ 2 ^ ((c + 1) * (d * d.size + 1)) * X ^ (c + 1) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX (by omega))

theorem fixed_le_shape (d X : ℕ) (hX : 1 ≤ X) : 2 ^ 26 * X ^ 13 ≤ shape 26 d X := by
  unfold shape
  exact Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (by nlinarith))
    (Nat.pow_le_pow_right hX (by norm_num))

theorem poly_le_shape {c d X Y : ℕ} (hXY : X ≤ Y) : 2 ^ c * X ^ c ≤ shape c d Y := by
  unfold shape
  exact Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num)
    (Nat.le_mul_of_pos_right c (by omega))) (Nat.pow_le_pow_left hXY c)

/-- The whole hard procedure has a budget of fixed-parameter shape. -/
theorem fptHardBound {c : ℕ} {cb : ℕ → ℕ → ℕ → ℕ} (hcb : ConstsBudgetBound c cb)
    {fb : ℕ → ℕ → HardBudget} (hfb : FunBudgetBound c fb) :
    FPTHardBound (c + 28) (fptBudget cb fb) := by
  intro W w0 n m left right R w hc hnb hw ho
  set d := (ComputedEmbeddedMatrices.globalRows R).length
  set X := n + m + W + w0 + 2
  have hX : 1 ≤ X := by omega
  have h1 : fixedBudget W w0 n m ≤ shape (c + 26) d X :=
    (fixedBudget_le W w0 n m).trans ((fixed_le_shape d X hX).trans (shape_mono_c (by omega) hX))
  have h2 : fb W (NetworkWeights.width w0 n) R w ≤ shape (c + 26) d X :=
    (hfb W w0 R w hc hnb hw ho).trans (shape_mono_c (by omega) hX)
  have h0 : cb W n m ≤ shape (c + 26) d X :=
    (hcb W n m).trans ((poly_le_shape (d := d) (by omega)).trans (shape_mono_c (by omega) hX))
  have h3 := shape_double (c := c + 26) (d := d) hX
  have h4 := shape_double (c := c + 26 + 1) (d := d) hX
  have h5 := shape_mono_c (c := c + 26) (c' := c + 26 + 1) (d := d) (by omega) hX
  change fixedBudget W w0 n m + cb W n m + fb W (NetworkWeights.width w0 n) R w ≤
    shape (c + 26 + 1 + 1) d X
  omega

/-- **The fixed-parameter claim from the two `Fun` stages.** For a code table
carrying XP's entry procedure whose hard procedure is the fixed-parameter hard
procedure, with valid coordinates, a constants stage meeting its contract with a
polynomial budget, and a numerical stage meeting its contract with a budget of
fixed-parameter shape, `Spec.FPTClaim` holds. -/
theorem fptClaim_of_funStage {P : ℕ} (code : Code P) (top : RegisterTopLevel.Procedures P)
    (htop : top.Matches code) (ids : Procedures P) (hm : ids.Matches code)
    (hhard : top.hard = ids.hard) {coords : CoordFn} (hco : CoordsValid coords)
    {cb : ℕ → ℕ → ℕ → ℕ} (hconsts : ConstsSpec code ids.consts cb)
    {fb : ℕ → ℕ → HardBudget} (hfun : FunStageSpec code ids.funStage coords fb)
    {c : ℕ} (hcb : ConstsBudgetBound c cb) (hfb : FunBudgetBound c fb) : Spec.FPTClaim := by
  refine fptClaim_of_hard code top htop (solverOf coords) (solverOf_correct hco) (c + 28)
    (fptBudget cb fb) (fun W w0 => ?_) (fptHardBound hcb hfb)
  rw [hhard]
  exact hard_spec ids code hm hco hconsts hfun W w0

end MWIS.FPTRegister

end
