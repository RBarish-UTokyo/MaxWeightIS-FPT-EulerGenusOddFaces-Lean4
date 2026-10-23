module

public import MWIS.GenericTopLevel
public import MWIS.FinalAccounting
public import MWIS.FPTStatement

/-!
# Accounting for a parametric hard solver, and the fixed-parameter claim

The entry procedure of `RegisterTopLevel` calls its hard procedure only on
connected nonbipartite all-half components. If the hard procedure meets the
generic contract `GenericHardSpec` for a correct hard function, with budgets of
fixed-parameter shape in the number `d` of global kernel rows of the component,

  `hb R w ≤ 2 ^ (c · (d · size d + 1)) · (n + m + W + w0 + 2) ^ c`,

then `Spec.FPTClaim` holds (`fptClaim_of_hard`). The number of rows is
`d = (ComputedEmbeddedMatrices.globalRows R).length`; on a connected
nonbipartite ribbon it equals `m - n - rank` of the face rows
(`ComputedEmbeddedMatrices.globalRows_spec`), and on every hard component of the
input it is at most `γ + k` (`component_rows_le`, from `Spec.Drawing.solve_spec`).

The proof charges the hard budget only on nonbipartite components (`sharp`),
sums it over the at most `N` computed components, adds the polynomial entry
budget `RegisterTopLevel.inputBudget_le`, and converts events to the bit-stack
cost with `GenericTopLevel.top_correct`. Integer weights enter through
`Spec.intWeights`; their encoding widths are bounded by `size M`.
-/

@[expose] public section

namespace MWIS.GenericAccounting

open MWIS.Spec MWIS.SpecEncoding MWIS.EmbeddingFaces MWIS.RegisterMachine MWIS.PointerMemory
open MWIS.RegisterComponentSolve (HardBudget componentHardBudget)
open MWIS.GenericComponentSolve (GenericHardSpec)
open MWIS.RegisterWeightMask (CanonAt)

/-! ## Charging only nonbipartite components -/

open Classical in
/-- A hard budget restricted to nonbipartite instances (zero on bipartite ones). -/
noncomputable def sharp (hb : HardBudget) : HardBudget :=
  fun {_n _m} {left right} R w => if Incidence.Bipartite left right then 0 else hb R w

/-- The generic contract only constrains nonbipartite instances. -/
theorem genericHardSpec_sharp {p : ℕ} {code : Code p} {hard : Fin p} {W : ℕ}
    {WeightAt : Heap → Ptr → ℚ → Prop} {solver : Generic.HardFn} {hb : HardBudget}
    (h : GenericHardSpec code hard W WeightAt solver hb) :
    GenericHardSpec code hard W WeightAt solver (sharp hb) := by
  intro n m left right R w hn0 hn hmW hc hnb hw ho h' hh tp rp wp hT hr hwp
  unfold sharp
  beta_reduce
  simp only [hnb, ↓reduceIte]
  exact h R w hn0 hn hmW hc hnb hw ho hh hT hr hwp

/-! ## The fixed-parameter shape -/

/-- The fixed-parameter shape `2 ^ (c · (d · size d + 1)) · s ^ c`. -/
def shape (c d s : ℕ) : ℕ := 2 ^ (c * (d * Nat.size d + 1)) * s ^ c

theorem shape_mono {c d d' s s' : ℕ} (hd : d ≤ d') (hs : s ≤ s') : shape c d s ≤ shape c d' s' := by
  unfold shape
  apply Nat.mul_le_mul
  · apply Nat.pow_le_pow_right (by norm_num)
    apply Nat.mul_le_mul_left
    have := Nat.mul_le_mul hd (Nat.size_le_size hd)
    omega
  · exact Nat.pow_le_pow_left hs c

/-- Budgets of fixed-parameter shape in the number of global kernel rows, on every
connected nonbipartite all-half instance with nonnegative weights. The budget
may depend on the index width `W` and the weight width `w0`. -/
def FPTHardBound (c : ℕ) (hb : ℕ → ℕ → HardBudget) : Prop :=
  ∀ (W w0 : ℕ) {n m : ℕ} {left right : Fin m → Fin n} (R : Ribbon left right) (w : Fin n → ℚ),
    Incidence.Connected left right → ¬ Incidence.Bipartite left right → (∀ v, 0 ≤ w v) →
    Persistence.Optimal (EdgeTransport.Adj left right) w (fun _ => 1 / 2) →
    hb W w0 R w ≤ shape c (ComputedEmbeddedMatrices.globalRows R).length (n + m + W + w0 + 2)

/-! ## Per-component and summed bounds -/

/-- The charged budget of one component, when every nonbipartite component has at
most `Dx` global rows. -/
theorem componentHardBudget_le {c W w0 : ℕ} {hb : ℕ → ℕ → HardBudget} (hbound : FPTHardBound c hb)
    {n m : ℕ} {left right : Fin m → Fin n} (H : Ribbon left right) (w : Fin n → ℚ)
    (hw : ∀ v, 0 ≤ w v) (ho : Persistence.Optimal (EdgeTransport.Adj left right) w (fun _ => 1 / 2))
    {Dx : ℕ} (root : Fin n)
    (hd : ¬ Incidence.Bipartite (ComputedComponents.localLeft left right root)
        (ComputedComponents.localRight left right root) →
      (ComputedEmbeddedMatrices.globalRows
        (ComputedComponents.componentRibbon left right root H)).length ≤ Dx) :
    componentHardBudget (sharp (hb W w0)) H w root ≤ shape c Dx (n + m + W + w0 + 2) := by
  unfold componentHardBudget sharp
  beta_reduce
  split_ifs with hbip
  · exact Nat.zero_le _
  · refine (hbound W w0 _ _ (ComputedComponents.local_connected left right root) hbip
      (fun v => hw _) (ComputedComponents.local_half_optimal left right root w ho)).trans ?_
    apply shape_mono (hd hbip)
    have hv := ComputedComponents.vertices_length_le left right root
    have he := ComputedComponents.edges_length_le left right root
    omega

/-- The summed charged budget over all computed components. -/
theorem hardSum_le {c W w0 : ℕ} {hb : ℕ → ℕ → HardBudget} (hbound : FPTHardBound c hb)
    {n m : ℕ} {left right : Fin m → Fin n} (H : Ribbon left right) (w : Fin n → ℚ)
    (hw : ∀ v, 0 ≤ w v) (ho : Persistence.Optimal (EdgeTransport.Adj left right) w (fun _ => 1 / 2))
    {Dx : ℕ}
    (hd : ∀ root : Fin n, ¬ Incidence.Bipartite (ComputedComponents.localLeft left right root)
        (ComputedComponents.localRight left right root) →
      (ComputedEmbeddedMatrices.globalRows
        (ComputedComponents.componentRibbon left right root H)).length ≤ Dx) :
    RegisterAllHalf.hardSum (sharp (hb W w0)) H w ≤ n * shape c Dx (n + m + W + w0 + 2) := by
  unfold RegisterAllHalf.hardSum
  refine FinalBudget.list_sum_le _ ?_ ?_
  · rw [List.length_map]; exact ComputedComponents.roots_length_le left right
  · intro x hx
    obtain ⟨root, -, rfl⟩ := List.mem_map.mp hx
    exact componentHardBudget_le hbound H w hw ho root (hd root)

/-! ## The parameter bound on every hard component -/

/-- Every nonbipartite residual component of the solver on a drawing in a
closed-surface map has at most `γ + k` global kernel rows. -/
theorem component_rows_le (A : Map) (hA : A.IsClosedSurface) (D : Drawing) (W : D.In A)
    (w : Fin D.vertices → ℚ)
    (root : Fin (ComputedInduced.vertices
      (ExecutableMIS.residualVertices (left := D.left) (right := D.right) w)).length)
    (hnb : ¬ Incidence.Bipartite
      (ComputedComponents.localLeft (ComputedInduced.localLeft D.left D.right
          (ExecutableMIS.residualVertices (left := D.left) (right := D.right) w))
        (ComputedInduced.localRight D.left D.right
          (ExecutableMIS.residualVertices (left := D.left) (right := D.right) w)) root)
      (ComputedComponents.localRight (ComputedInduced.localLeft D.left D.right
          (ExecutableMIS.residualVertices (left := D.left) (right := D.right) w))
        (ComputedInduced.localRight D.left D.right
          (ExecutableMIS.residualVertices (left := D.left) (right := D.right) w)) root)) :
    (ComputedEmbeddedMatrices.globalRows (ComputedComponents.componentRibbon
      (ComputedInduced.localLeft D.left D.right
        (ExecutableMIS.residualVertices (left := D.left) (right := D.right) w))
      (ComputedInduced.localRight D.left D.right
        (ExecutableMIS.residualVertices (left := D.left) (right := D.right) w)) root
      (ComputedInduced.ribbon D.left D.right
        (ExecutableMIS.residualVertices (left := D.left) (right := D.right) w)
        (Drawing.ribbon hA W)))).length ≤ A.eulerGenus + A.oddRegionCount W.drawn :=
  ((Drawing.solve_spec A hA D W w).2 root hnb).1.trans (FinalBudget.exponentD_le _ _)

/-- The event budget of the entry procedure with a fixed-parameter hard budget. -/
theorem events_le {c : ℕ} {hb : ℕ → ℕ → HardBudget} (hbound : FPTHardBound c hb)
    (A : Map) (hA : A.IsClosedSurface) (D : Drawing) (W : D.In A) (w : Fin D.vertices → ℚ) :
    RegisterTopLevel.inputBudget D w +
        RegisterFinalAssembly.residualHardSum (sharp (hb (indexWidth D) (weightWidth w)))
          (Drawing.ribbon hA W) w ≤
      2 ^ 36 * D.size ^ 11 * (weightLength w + 1) ^ 2 +
        D.size * shape c (A.eulerGenus + A.oddRegionCount W.drawn)
          (D.size + indexWidth D + weightWidth w + 2) := by
  have hi := RegisterTopLevel.inputBudget_le D w
  -- the induced all-half instance
  let z := RegisterFinalAssembly.zPoint D.left D.right w
  have hz := OriginalReduction.preprocessingPoint_correct (left := D.left) (right := D.right)
    w (List.finRange D.vertices) (fun v => List.mem_finRange v)
  have hzr := InducedReduction.residual_optimal (EdgeTransport.Adj D.left D.right)
    (NegativeWeights.nonnegative w) z hz.2 hz.1
  have hopt := ComputedInduced.half_optimal D.left D.right
    (RegisterFinalAssembly.halfKeep D.left D.right w) (NegativeWeights.nonnegative w) hzr
  have hs := hardSum_le (W := indexWidth D) (w0 := weightWidth w) hbound
    (ComputedInduced.ribbon D.left D.right
      (RegisterFinalAssembly.halfKeep D.left D.right w) (Drawing.ribbon hA W))
    (RegisterFinalAssembly.halfWeights D.left D.right w)
    (fun v => NegativeWeights.nonnegative_nonnegative w _) hopt
    (Dx := A.eulerGenus + A.oddRegionCount W.drawn)
    (fun root hnb => component_rows_le A hA D W w root hnb)
  have hvl : (ComputedInduced.vertices (RegisterFinalAssembly.halfKeep D.left D.right w)).length ≤
      D.vertices := by
    simpa [ComputedInduced.vertices] using List.length_filter_le _ (List.finRange D.vertices)
  have hel : (ComputedInduced.edges D.left D.right
      (RegisterFinalAssembly.halfKeep D.left D.right w)).length ≤ D.edges := by
    simpa [ComputedInduced.edges] using List.length_filter_le _ (List.finRange D.edges)
  have hr : RegisterFinalAssembly.residualHardSum (sharp (hb (indexWidth D) (weightWidth w)))
      (Drawing.ribbon hA W) w ≤
      D.size * shape c (A.eulerGenus + A.oddRegionCount W.drawn)
        (D.size + indexWidth D + weightWidth w + 2) := by
    refine hs.trans (Nat.mul_le_mul (by simp only [Drawing.size]; omega) (shape_mono le_rfl ?_))
    simp only [Drawing.size]
    omega
  omega

/-! ## Integer weights -/

theorem one_le_weightBound {n : ℕ} (w : Fin n → ℤ) : 1 ≤ weightBound w := le_max_left _ _

theorem one_le_size_weightBound {n : ℕ} (w : Fin n → ℤ) : 1 ≤ Nat.size (weightBound w) := by
  have h := Nat.size_le_size (one_le_weightBound w)
  simpa using h

theorem natAbs_le_weightBound {n : ℕ} (w : Fin n → ℤ) (v : Fin n) :
    (w v).natAbs ≤ weightBound w :=
  (Finset.le_sup (f := fun v => (w v).natAbs) (Finset.mem_univ v)).trans (le_max_right _ _)

theorem weightWidth_intWeights_le {n : ℕ} (w : Fin n → ℤ) :
    weightWidth (intWeights w) ≤ Nat.size (weightBound w) := by
  unfold weightWidth
  apply Finset.sup_le
  intro v _
  simp only [intWeights, Rat.num_intCast, Rat.den_intCast]
  refine max_le (Nat.size_le_size (natAbs_le_weightBound w v)) ?_
  simpa using one_le_size_weightBound w

theorem weightLength_intWeights_le {n : ℕ} (w : Fin n → ℤ) :
    weightLength (intWeights w) ≤ n * (2 * Nat.size (weightBound w)) := by
  unfold weightLength
  calc ∑ v : Fin n, ((intWeights w v).num.natAbs.size + (intWeights w v).den.size)
      ≤ ∑ _v : Fin n, 2 * Nat.size (weightBound w) := by
        apply Finset.sum_le_sum
        intro v _
        simp only [intWeights, Rat.num_intCast, Rat.den_intCast]
        have h1 := Nat.size_le_size (natAbs_le_weightBound w v)
        have h2 := one_le_size_weightBound w
        simp only [Nat.size_one]
        omega
    _ = n * (2 * Nat.size (weightBound w)) := by simp

/-! ## Arithmetic normal form -/

/-- The final arithmetic: an event bound in the shape of `events_le` gives the
fixed-parameter bound after the logarithmic-overhead conversion. -/
theorem final_arith {E N L S F c : ℕ} (hN : 1 ≤ N) (hS : 1 ≤ S) (hF : 2 ≤ F)
    (hL : L + 1 ≤ 3 * (N * S))
    (hE : E ≤ 2 ^ 36 * N ^ 11 * (L + 1) ^ 2 + N * (F ^ c * (5 * (N * S)) ^ c)) :
    E * (102 + 35 * (100 * N ^ 2 * (L + 1) + E)) ≤
      F ^ (7 * c + 96) * (N * S) ^ (7 * c + 96) := by
  set X := N * S with hX
  have hX1 : 1 ≤ X := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hNX : N ≤ X := Nat.le_mul_of_pos_right _ hS
  have hF1 : 1 ≤ F := by omega
  have hFc : 1 ≤ F ^ c := Nat.one_le_pow _ _ hF1
  -- the event bound in one monomial
  set G := 2 ^ 41 * 5 ^ c * F ^ c * X ^ (c + 13) with hG
  have hG1 : 1 ≤ G := by
    have : 0 < G := by rw [hG]; positivity
    omega
  have hEG : E ≤ G := by
    refine hE.trans ?_
    have t1 : 2 ^ 36 * N ^ 11 * (L + 1) ^ 2 ≤ 2 ^ 40 * X ^ 13 := by
      calc 2 ^ 36 * N ^ 11 * (L + 1) ^ 2 ≤ 2 ^ 36 * X ^ 11 * (3 * X) ^ 2 := by gcongr
        _ = 9 * 2 ^ 36 * X ^ 13 := by ring
        _ ≤ 2 ^ 40 * X ^ 13 := by gcongr; norm_num
    have t2 : N * (F ^ c * (5 * X) ^ c) ≤ 5 ^ c * F ^ c * X ^ (c + 13) := by
      calc N * (F ^ c * (5 * X) ^ c) ≤ X * (F ^ c * (5 * X) ^ c) := by gcongr
        _ = 5 ^ c * F ^ c * X ^ (c + 1) := by ring
        _ ≤ 5 ^ c * F ^ c * X ^ (c + 13) := by gcongr; omega
    have t3 : 2 ^ 40 * X ^ 13 ≤ 2 ^ 40 * (5 ^ c * F ^ c * X ^ (c + 13)) := by
      apply Nat.mul_le_mul_left
      have : X ^ 13 ≤ X ^ (c + 13) := Nat.pow_le_pow_right hX1 (by omega)
      have : 1 ≤ 5 ^ c * F ^ c := Nat.one_le_iff_ne_zero.mpr (by positivity)
      calc X ^ 13 = 1 * X ^ 13 := by ring
        _ ≤ (5 ^ c * F ^ c) * X ^ (c + 13) := by gcongr
        _ = 5 ^ c * F ^ c * X ^ (c + 13) := by ring
    have : 2 ^ 41 * 5 ^ c * F ^ c * X ^ (c + 13) =
        2 ^ 40 * (5 ^ c * F ^ c * X ^ (c + 13)) + 2 ^ 40 * (5 ^ c * F ^ c * X ^ (c + 13)) := by
      ring
    have t4 : 5 ^ c * F ^ c * X ^ (c + 13) ≤ 2 ^ 40 * (5 ^ c * F ^ c * X ^ (c + 13)) :=
      Nat.le_mul_of_pos_left _ (by positivity)
    omega
  -- the overhead factor
  have hX3 : 1 ≤ X ^ 3 := Nat.one_le_pow _ _ hX1
  have hover : 102 + 35 * (100 * N ^ 2 * (L + 1) + E) ≤ 10637 * X ^ 3 * G := by
    have a : 100 * N ^ 2 * (L + 1) ≤ 300 * X ^ 3 := by
      calc 100 * N ^ 2 * (L + 1) ≤ 100 * X ^ 2 * (3 * X) := by gcongr
        _ = 300 * X ^ 3 := by ring
    have b : X ^ 3 ≤ X ^ 3 * G := Nat.le_mul_of_pos_right _ hG1
    have c' : G ≤ X ^ 3 * G := Nat.le_mul_of_pos_left _ (by omega)
    have d : 1 ≤ X ^ 3 * G := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have e : 10637 * X ^ 3 * G = 10637 * (X ^ 3 * G) := by ring
    omega
  have hmain : E * (102 + 35 * (100 * N ^ 2 * (L + 1) + E)) ≤ 10637 * X ^ 3 * G ^ 2 := by
    calc E * (102 + 35 * (100 * N ^ 2 * (L + 1) + E)) ≤ G * (10637 * X ^ 3 * G) :=
          Nat.mul_le_mul hEG hover
      _ = 10637 * X ^ 3 * G ^ 2 := by ring
  refine hmain.trans ?_
  -- normal form
  have hpow : (2 : ℕ) ^ (96 + 5 * c) ≤ F ^ (96 + 5 * c) := Nat.pow_le_pow_left hF _
  have h25 : (5 : ℕ) ^ (2 * c) ≤ 2 ^ (5 * c) := by
    rw [pow_mul, pow_mul]; exact Nat.pow_le_pow_left (by norm_num) c
  calc 10637 * X ^ 3 * G ^ 2
      = 10637 * 2 ^ 82 * 5 ^ (2 * c) * F ^ (2 * c) * X ^ (2 * c + 29) := by
        rw [hG]; ring
    _ ≤ 2 ^ 14 * 2 ^ 82 * 2 ^ (5 * c) * F ^ (2 * c) * X ^ (2 * c + 29) := by gcongr; norm_num
    _ = 2 ^ (96 + 5 * c) * F ^ (2 * c) * X ^ (2 * c + 29) := by ring
    _ ≤ F ^ (96 + 5 * c) * F ^ (2 * c) * X ^ (7 * c + 96) :=
        Nat.mul_le_mul (Nat.mul_le_mul_right _ hpow) (Nat.pow_le_pow_right hX1 (by omega))
    _ = F ^ (7 * c + 96) * X ^ (7 * c + 96) := by ring

/-! ## The fixed-parameter claim -/

/-- **The fixed-parameter claim from a hard procedure.** Let a finite code table
carry the entry procedure of `RegisterTopLevel` and, as its hard procedure, a
procedure meeting the generic contract for a correct hard function, at every
index and weight width, with budgets of fixed-parameter shape. Then
`Spec.FPTClaim` holds with the constant `7 c + 96`. -/
theorem fptClaim_of_hard {P : ℕ} (code : Code P) (top : RegisterTopLevel.Procedures P)
    (htop : top.Matches code) (solver : Generic.HardFn) (hcor : Generic.HardCorrect solver)
    (c : ℕ) (hb : ℕ → ℕ → HardBudget)
    (hspec : ∀ W w0, GenericHardSpec code top.hard W (CanonAt w0) solver (hb W w0))
    (hbound : FPTHardBound c hb) : FPTClaim := by
  refine ⟨P, code, top.top, 7 * c + 96, ?_⟩
  intro A hA D W w
  have hspec' : GenericHardSpec code top.hard (indexWidth D) (CanonAt (weightWidth (intWeights w)))
      solver (sharp (hb (indexWidth D) (weightWidth (intWeights w)))) :=
    @genericHardSpec_sharp P code top.hard (indexWidth D) (CanonAt (weightWidth (intWeights w)))
      solver (hb (indexWidth D) (weightWidth (intWeights w)))
      (@hspec (indexWidth D) (weightWidth (intWeights w)))
  obtain ⟨hex, hall⟩ := @GenericTopLevel.top_correct P solver hcor top code htop
    (sharp (hb (indexWidth D) (weightWidth (intWeights w)))) A hA D W (intWeights w) hspec'
  refine ⟨hex, fun r t hr => ?_⟩
  obtain ⟨hmax, hcost⟩ := hall r t hr
  refine ⟨hmax, hcost.trans ?_⟩
  -- the event bound
  have hE := events_le hbound A hA D W (intWeights w)
  set p := A.eulerGenus + A.oddRegionCount W.drawn
  set S := Nat.size (weightBound w)
  have hN : 1 ≤ D.size := by simp [Drawing.size]
  have hS : 1 ≤ S := one_le_size_weightBound w
  have hNX : D.size ≤ D.size * S := Nat.le_mul_of_pos_right _ hS
  have hSX : S ≤ D.size * S := Nat.le_mul_of_pos_left _ hN
  have hW := indexWidth_le D
  have hw0 : weightWidth (intWeights w) ≤ S := weightWidth_intWeights_le w
  have hL : weightLength (intWeights w) ≤ D.vertices * (2 * S) := weightLength_intWeights_le w
  have hL' : weightLength (intWeights w) + 1 ≤ 3 * (D.size * S) := by
    have : D.vertices * (2 * S) ≤ 2 * (D.size * S) := by
      have : D.vertices ≤ D.size := by simp [Drawing.size]; omega
      calc D.vertices * (2 * S) ≤ D.size * (2 * S) := Nat.mul_le_mul_right _ this
        _ = 2 * (D.size * S) := by ring
    have h1 : 1 ≤ D.size * S := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  have hsz : D.size + indexWidth D + weightWidth (intWeights w) + 2 ≤ 5 * (D.size * S) := by
    have : indexWidth D ≤ D.size := by simp only [Drawing.size]; omega
    have h1 : 1 ≤ D.size * S := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  have hshape : shape c p (D.size + indexWidth D + weightWidth (intWeights w) + 2) ≤
      (2 ^ (p * Nat.size p + 1)) ^ c * (5 * (D.size * S)) ^ c := by
    unfold shape
    rw [← pow_mul, Nat.mul_comm (p * Nat.size p + 1) c]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsz c)
  have hE' : RegisterTopLevel.inputBudget D (intWeights w) +
      RegisterFinalAssembly.residualHardSum (sharp (hb (indexWidth D) (weightWidth (intWeights w))))
        (Drawing.ribbon hA W) (intWeights w) ≤
      2 ^ 36 * D.size ^ 11 * (weightLength (intWeights w) + 1) ^ 2 +
        D.size * ((2 ^ (p * Nat.size p + 1)) ^ c * (5 * (D.size * S)) ^ c) :=
    hE.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ hshape) _)
  have hF : 2 ≤ 2 ^ (p * Nat.size p + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (p * Nat.size p + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine (final_arith hN hS hF hL' hE').trans_eq ?_
  unfold fptBound
  rw [← pow_mul, Nat.mul_comm (p * Nat.size p + 1) (7 * c + 96)]

end MWIS.GenericAccounting

end
