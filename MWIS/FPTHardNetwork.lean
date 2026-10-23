module

public import MWIS.NetworkTarget
public import MWIS.AlgorithmNetworkOptimize
public import MWIS.CoreNetwork
public import MWIS.AlgorithmNetworkEnumeration
public import MWIS.ComputedRecovery

/-!
# The fixed-parameter hard-component computation, for abstract coordinates

The facial equations are given by signed columns. Integral quotient
coordinates are supplied as data (`CoordinateData`): a rank `r`, a free-coordinate
homomorphism and a residue homomorphism. `CoordinateData.Valid` states that they
come from an isomorphism of the integral quotient with `ℤ^r × ℤ/2` sending the
distinguished class to `(0, 1)`, exactly as required by
`CoreNetwork.exists_network_optimum_of_labels`.

Natural edge costs `c` are perturbed to `c'_e = 2^(m+1)·c_e + 2^e`. The finite-group
network LP with costs `c'` is solved by the dense threshold optimizer. Its value
is the maximum `c'`-induced vertex weight of an independent set. Subtracting it from
the total perturbed cost gives the minimum perturbed slack cost, whose low `m` bits
are exactly the binary slack of a maximizer. Integer-potential recovery and
threshold rounding return that maximizer, which also maximizes the unperturbed
`c`-induced weight.

Prepared 2026-10-23.
-/

@[expose] public section

namespace MWIS.FPTHard

open scoped BigOperators
open CycleQuotient ResidueJensen Walks AlgorithmNetworkEncoding AlgorithmThresholdLP

/-! ## Facial equations from signed columns -/

section Columns

variable {Row : Type*} [Fintype Row] [DecidableEq Row] {m : ℕ}

/-- The integer facial homomorphism whose columns are the given signed columns. -/
def columnHom (C : Fin m → Column Row) : (Fin m → ℤ) →+ (Row → ℤ) where
  toFun y row := ∑ e, columnVector (C e) row * y e
  map_zero' := by funext row; simp
  map_add' x y := by funext row; simp [mul_add, Finset.sum_add_distrib]

theorem columnHom_apply (C : Fin m → Column Row) (y : Fin m → ℤ) (row : Row) :
    columnHom C y row = ∑ e, columnVector (C e) row * y e := rfl

end Columns

/-! ## Coordinate data -/

/-- Computed coordinate data: a free rank, free coordinates and residue labels. -/
structure CoordinateData (m : ℕ) where
  rank : ℕ
  free : (Fin m → ℤ) →+ (Fin rank → ℤ)
  residue : (Fin m → ℤ) →+ Residue rank

/-- The coordinate data are the ambient maps of an integral quotient isomorphism
sending the class of the all-ones vector to `(0, 1)`. -/
def CoordinateData.Valid {Row : Type*} [Fintype Row] [DecidableEq Row] {m n : ℕ}
    (left right : Fin m → Fin n) (C : Fin m → Column Row)
    (hBA : ∀ z, columnHom C (IncidenceSplit.incidence left right z) = 0)
    (hB1 : columnHom C (fun _ => 1) = 0) (D : CoordinateData m) : Prop :=
  ∃ e : Homology left right (columnHom C) hBA ≃+ (Fin D.rank → ℤ) × ZMod 2,
    e (characteristicClass left right (columnHom C) hBA hB1) = (0, 1) ∧
    (∀ y : (columnHom C).ker,
      D.free y.val = (e (classMap left right (columnHom C) hBA y)).1) ∧
    (∀ y : (columnHom C).ker,
      D.residue y.val = residueMap e (classMap left right (columnHom C) hBA y))

/-! ## Perturbed costs and the network program -/

/-- The perturbed natural cost `2^(m+1)·c_e + 2^e` of edge `e`. -/
def perturbed {m : ℕ} (c : Fin m → ℕ) (e : Fin m) : ℕ := 2 ^ (m + 1) * c e + 2 ^ (e : ℕ)

/-- The total perturbed cost. -/
def total {m : ℕ} (c : Fin m → ℕ) : ℕ := ∑ e, perturbed c e

/-- Bits used by the threshold search: enough for twice the total perturbed cost. -/
def searchBits {m : ℕ} (c : Fin m → ℕ) : ℕ := (2 * total c).size

section Program

variable {f m : ℕ}

/-- The dense integer network program for the perturbed costs, with an
arbitrary numbering of its rows and columns. The objective numerators are twice
the perturbed costs (the dense encoding uses the denominator two). -/
def program (C : Fin m → Column (Fin f)) (D : CoordinateData m) (c : Fin m → ℕ) {M N : ℕ}
    (rows : InequalityRow C (G := Residue D.rank) D.rank ≃ Fin M)
    (cols : FiniteExtension.ExtensionArc C (Residue D.rank) ≃ Fin N) : DenseProgram M N :=
  toDense C D.free D.residue (AlgorithmComputedNetwork.target D.rank)
    (fun e => 2 * (perturbed c e : ℤ)) rows cols

/-- The optimum value returned by the threshold optimizer. -/
def lpValue (C : Fin m → Column (Fin f)) (D : CoordinateData m) (c : Fin m → ℕ) {M N : ℕ}
    (rows : InequalityRow C (G := Residue D.rank) D.rank ≃ Fin M)
    (cols : FiniteExtension.ExtensionArc C (Residue D.rank) ≃ Fin N) : ℕ :=
  optimize (program C D c rows cols) (2 * (total c : ℤ)) (searchBits c)

/-- The program with the executable enumeration of rows and columns. -/
def enumeratedProgram (C : Fin m → Column (Fin f)) (D : CoordinateData m) (c : Fin m → ℕ) :
    DenseProgram (AlgorithmNetworkEnumeration.rowCount C D.rank)
      (AlgorithmNetworkEnumeration.columnCount C D.rank) :=
  program C D c (AlgorithmNetworkEnumeration.rows C D.rank)
    (AlgorithmNetworkEnumeration.columns C D.rank)

/-- The optimum value for the executable enumeration. -/
def enumeratedValue (C : Fin m → Column (Fin f)) (D : CoordinateData m) (c : Fin m → ℕ) : ℕ :=
  lpValue C D c (AlgorithmNetworkEnumeration.rows C D.rank)
    (AlgorithmNetworkEnumeration.columns C D.rank)

end Program

/-! ## Natural set weights and slack bits -/

section Weights

variable {n m : ℕ} (left right : Fin m → Fin n)

/-- How many endpoints of edge `e` lie in `I` (two for a loop at a vertex of `I`). -/
def incidenceCount (I : Finset (Fin n)) (e : Fin m) : ℕ :=
  (if left e ∈ I then 1 else 0) + (if right e ∈ I then 1 else 0)

/-- The natural weight of `I` induced by natural edge costs. -/
def natSetWeight (c : Fin m → ℕ) (I : Finset (Fin n)) : ℕ :=
  ∑ e, c e * incidenceCount left right I e

/-- The binary edge slack of an independent set. -/
def slackBit (I : Finset (Fin n)) (e : Fin m) : ℕ :=
  if left e ∈ I ∨ right e ∈ I then 0 else 1

theorem incidenceCount_le (I : Finset (Fin n)) (e : Fin m) :
    incidenceCount left right I e ≤ 2 := by
  unfold incidenceCount; split_ifs <;> omega

theorem slackBit_le (I : Finset (Fin n)) (e : Fin m) : slackBit left right I e ≤ 1 := by
  unfold slackBit; split_ifs <;> omega

theorem incidence_add_slack {I : Finset (Fin n)} (hI : Slack.Independent left right I)
    (e : Fin m) : incidenceCount left right I e + slackBit left right I e = 1 := by
  have h := hI e
  unfold incidenceCount slackBit
  split_ifs <;> simp_all

/-- Rational set weights of natural costs are the natural set weights. -/
theorem setWeight_natCast (c : Fin m → ℕ) (I : Finset (Fin n)) :
    Slack.setWeight left right (fun e => (c e : ℚ)) I = (natSetWeight left right c I : ℚ) := by
  rw [Slack.set_weight_incidence]
  unfold Slack.edgeObjective natSetWeight incidenceCount Slack.indicator
  push_cast
  apply Finset.sum_congr rfl
  intro e _
  split_ifs <;> simp

theorem natSetWeight_le_two_total (c : Fin m → ℕ) (I : Finset (Fin n)) :
    natSetWeight left right c I ≤ 2 * ∑ e, c e := by
  unfold natSetWeight
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e _
  have := incidenceCount_le left right I e
  calc c e * incidenceCount left right I e ≤ c e * 2 := Nat.mul_le_mul_left _ this
    _ = 2 * c e := by ring

/-- For an independent set, its weight and its slack cost add to the total cost. -/
theorem natSetWeight_add_slack (c : Fin m → ℕ) {I : Finset (Fin n)}
    (hI : Slack.Independent left right I) :
    natSetWeight left right c I + ∑ e, c e * slackBit left right I e = ∑ e, c e := by
  unfold natSetWeight
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  rw [← Nat.mul_add, incidence_add_slack left right hI e, Nat.mul_one]

theorem natSetWeight_add (c d : Fin m → ℕ) (I : Finset (Fin n)) :
    natSetWeight left right (fun e => c e + d e) I =
      natSetWeight left right c I + natSetWeight left right d I := by
  unfold natSetWeight
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem natSetWeight_mul (k : ℕ) (c : Fin m → ℕ) (I : Finset (Fin n)) :
    natSetWeight left right (fun e => k * c e) I = k * natSetWeight left right c I := by
  unfold natSetWeight
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  ring

end Weights

/-! ## Binary masks -/

/-- Adding a multiple of a higher power of two does not change a lower bit. -/
theorem div_pow_mod_two_add (x A j k : ℕ) (hjk : j < k) :
    (x + 2 ^ k * A) / 2 ^ j % 2 = x / 2 ^ j % 2 := by
  have hk : 2 ^ k * A = 2 ^ j * (2 * (2 ^ (k - j - 1) * A)) := by
    rw [← mul_assoc, ← mul_assoc, ← pow_succ, ← pow_add]
    congr 2
    omega
  rw [hk, Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left]

/-- A binary mask indexed by `Fin m` is smaller than `2^m`. -/
theorem mask_lt : ∀ {m : ℕ} (s : Fin m → ℕ), (∀ e, s e ≤ 1) →
    ∑ e : Fin m, 2 ^ e.val * s e < 2 ^ m
  | 0, _, _ => by simp
  | m + 1, s, hs => by
    rw [Fin.sum_univ_castSucc]
    have ih := mask_lt (fun e : Fin m => s e.castSucc) (fun e => hs _)
    have hl := hs (Fin.last m)
    simp only [Fin.val_castSucc, Fin.val_last] at ih ⊢
    rw [pow_succ]
    nlinarith [Nat.zero_le (2 ^ m)]

/-- Every bit of a binary mask reads back its coefficient. -/
theorem mask_bit : ∀ {m : ℕ} (s : Fin m → ℕ), (∀ e, s e ≤ 1) → ∀ j : Fin m,
    (∑ e : Fin m, 2 ^ e.val * s e) / 2 ^ (j : ℕ) % 2 = s j
  | 0, _, _, j => j.elim0
  | m + 1, s, hs, j => by
    rw [Fin.sum_univ_castSucc]
    have hlt := mask_lt (fun e : Fin m => s e.castSucc) (fun e => hs _)
    simp only [Fin.val_castSucc, Fin.val_last] at hlt ⊢
    by_cases hj : (j : ℕ) < m
    · have ih := mask_bit (fun e : Fin m => s e.castSucc) (fun e => hs _) ⟨j, hj⟩
      simp only [Fin.val_castSucc] at ih
      rw [div_pow_mod_two_add _ _ _ _ hj, ih]
      rfl
    · have hjm : (j : ℕ) = m := by omega
      have hjl : j = Fin.last m := Fin.ext hjm
      rw [hjm, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hlt, zero_add,
        hjl, Nat.mod_eq_of_lt (by have := hs (Fin.last m); omega)]

/-- Decode the low `m` bits of a natural number as an integer edge vector. -/
def decode (m M : ℕ) (e : Fin m) : ℤ := ((M / 2 ^ (e : ℕ) % 2 : ℕ) : ℤ)

/-- The perturbed slack cost of a binary slack decodes to that slack. -/
theorem decode_perturbed {m : ℕ} (c : Fin m → ℕ) (s : Fin m → ℕ) (hs : ∀ e, s e ≤ 1) :
    decode m (∑ e, perturbed c e * s e) = fun e => (s e : ℤ) := by
  funext j
  have hsplit : (∑ e, perturbed c e * s e) =
      (∑ e : Fin m, 2 ^ e.val * s e) + 2 ^ (m + 1) * ∑ e, c e * s e := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    unfold perturbed
    ring
  unfold decode
  rw [hsplit, div_pow_mod_two_add _ _ _ _ (by have := j.isLt; omega), mask_bit s hs j]

/-! ## The network value -/

section Value

variable {f n m : ℕ} (left right : Fin m → Fin n) (C : Fin m → Column (Fin f))

/-- **The network value.** For valid coordinates and any numbering of rows and
columns, the threshold optimizer returns the maximum perturbed-cost weight of an
independent set, attained by an actual independent set. -/
theorem lpValue_spec
    (hBA : ∀ z, columnHom C (IncidenceSplit.incidence left right z) = 0)
    (hB1 : columnHom C (fun _ => 1) = 0) (D : CoordinateData m)
    (hD : D.Valid left right C hBA hB1) (c : Fin m → ℕ) {M N : ℕ}
    (rows : InequalityRow C (G := Residue D.rank) D.rank ≃ Fin M)
    (cols : FiniteExtension.ExtensionArc C (Residue D.rank) ≃ Fin N) :
    ∃ I : Finset (Fin n), Slack.Independent left right I ∧
      (∀ J, Slack.Independent left right J →
        natSetWeight left right (perturbed c) J ≤ natSetWeight left right (perturbed c) I) ∧
      lpValue C D c rows cols = natSetWeight left right (perturbed c) I := by
  obtain ⟨e, hκ, hW, hell⟩ := hD
  obtain ⟨I, v, hI, hmax, hval, hmin⟩ := CoreNetwork.exists_network_optimum_of_labels
    left right (columnHom C) hBA hB1 C (fun _ _ => rfl) D.rank e hκ D.free hW D.residue hell
    (fun e => (perturbed c e : ℚ)) (fun _ => by positivity)
  have hη : residueMap e (characteristicClass left right (columnHom C) hBA hB1) =
      AlgorithmComputedNetwork.target D.rank := by
    ext d <;> simp [residueMap, hκ, AlgorithmComputedNetwork.target]
  rw [hη] at hmin
  have hsw := setWeight_natCast left right (perturbed c) I
  refine ⟨I, hI, ?_, ?_⟩
  · intro J hJ
    have h := hmax J hJ
    rw [setWeight_natCast, hsw] at h
    exact_mod_cast h
  · have htot : Slack.totalCost (fun e => (perturbed c e : ℚ)) = (total c : ℚ) := by
      simp [Slack.totalCost, total]
    apply AlgorithmNetworkOptimize.optimize_network_correct C D.free D.residue _
      (fun e => 2 * (perturbed c e : ℤ)) (fun e => (perturbed c e : ℚ)) _ rows cols v hmin
    · rw [htot]; push_cast; ring
    · rw [hsw] at hval
      rw [htot] at hval ⊢
      have hval' : ((natSetWeight left right (perturbed c) I : ℚ) : ℝ) =
          ((total c : ℚ) : ℝ) - v := by exact_mod_cast hval
      push_cast at hval' ⊢
      linarith
    · calc natSetWeight left right (perturbed c) I ≤ 2 * total c :=
            natSetWeight_le_two_total left right _ I
        _ < 2 ^ (2 * total c).size := Nat.lt_size_self _
    · intro e; push_cast; ring

/-- The value does not depend on the numbering of rows and columns. -/
theorem lpValue_eq_of_valid
    (hBA : ∀ z, columnHom C (IncidenceSplit.incidence left right z) = 0)
    (hB1 : columnHom C (fun _ => 1) = 0) (D : CoordinateData m)
    (hD : D.Valid left right C hBA hB1) (c : Fin m → ℕ) {M N M' N' : ℕ}
    (rows : InequalityRow C (G := Residue D.rank) D.rank ≃ Fin M)
    (cols : FiniteExtension.ExtensionArc C (Residue D.rank) ≃ Fin N)
    (rows' : InequalityRow C (G := Residue D.rank) D.rank ≃ Fin M')
    (cols' : FiniteExtension.ExtensionArc C (Residue D.rank) ≃ Fin N') :
    lpValue C D c rows cols = lpValue C D c rows' cols' := by
  obtain ⟨I, hI, hm, hv⟩ := lpValue_spec left right C hBA hB1 D hD c rows cols
  obtain ⟨I', hI', hm', hv'⟩ := lpValue_spec left right C hBA hB1 D hD c rows' cols'
  rw [hv, hv']
  exact le_antisymm (hm' I hI) (hm I' hI')

end Value

/-! ## Recovery -/

section Recovery

variable {n m : ℕ} (left right : Fin m → Fin n)

theorem threshold_indicator (I : Finset (Fin n)) : Slack.threshold (Slack.indicator I) = I := by
  ext v
  rw [Slack.threshold_mem]
  unfold Slack.indicator
  split_ifs <;> simp_all

/-- Integer-potential recovery from the binary slack of an independent set
returns that set. -/
theorem recover_slackBit (root : Fin n) (hc : Incidence.Connected left right)
    (π : Fin m → ℤ) (hπ : IntegerSlacks.OddRow left right root π)
    {I : Finset (Fin n)} (hI : Slack.Independent left right I) :
    Slack.threshold (ComputedRecovery.recover left right (List.finRange m) (List.finRange n)
      root π (fun e => (slackBit left right I e : ℤ))) = I := by
  rw [ComputedRecovery.recover_eq left right (List.finRange m) (fun e => List.mem_finRange e)
    (List.finRange n) (fun v => List.mem_finRange v) root hc π _ hπ (Slack.indicator I) ?_]
  · exact threshold_indicator I
  · intro e
    have h := hI e
    unfold Slack.indicator slackBit
    split_ifs <;> simp_all

/-- A maximizer of the perturbed weight maximizes the unperturbed weight. -/
theorem maximum_of_perturbed (c : Fin m → ℕ) {I : Finset (Fin n)}
    (hmax : ∀ J, Slack.Independent left right J →
      natSetWeight left right (perturbed c) J ≤ natSetWeight left right (perturbed c) I) :
    ∀ J, Slack.Independent left right J →
      natSetWeight left right c J ≤ natSetWeight left right c I := by
  intro J hJ
  have hsplit (K : Finset (Fin n)) : natSetWeight left right (perturbed c) K =
      2 ^ (m + 1) * natSetWeight left right c K +
        natSetWeight left right (fun e : Fin m => 2 ^ e.val) K := by
    unfold perturbed
    rw [natSetWeight_add, natSetWeight_mul]
  have hpow (K : Finset (Fin n)) :
      natSetWeight left right (fun e : Fin m => 2 ^ e.val) K < 2 ^ (m + 1) := by
    have h1 := natSetWeight_le_two_total left right (fun e : Fin m => 2 ^ (e : ℕ)) K
    have h2 := mask_lt (fun _ : Fin m => 1) (fun _ => le_rfl)
    simp only [mul_one] at h2
    rw [pow_succ]
    omega
  have h := hmax J hJ
  rw [hsplit, hsplit] at h
  have hI := hpow I
  by_contra hlt
  push Not at hlt
  have : 2 ^ (m + 1) * (natSetWeight left right c I + 1) ≤
      2 ^ (m + 1) * natSetWeight left right c J := Nat.mul_le_mul_left _ hlt
  nlinarith

end Recovery

/-! ## The abstract hard-component output -/

section Abstract

variable {f n m : ℕ} (left right : Fin m → Fin n) (C : Fin m → Column (Fin f))

/-- The output for given coordinate data, natural costs, root, parity row and
numbering: decode the minimum perturbed slack cost and recover its set. -/
def recoveredSet (D : CoordinateData m) (c : Fin m → ℕ) (root : Fin n) (π : Fin m → ℤ)
    {M N : ℕ} (rows : InequalityRow C (G := Residue D.rank) D.rank ≃ Fin M)
    (cols : FiniteExtension.ExtensionArc C (Residue D.rank) ≃ Fin N) : Finset (Fin n) :=
  Slack.threshold (ComputedRecovery.recover left right (List.finRange m) (List.finRange n)
    root π (decode m (total c - lpValue C D c rows cols)))

/-- **Abstract correctness.** With valid coordinates, a connected graph and an
odd row, the recovered set is independent and maximizes the weight induced by the
natural edge costs. -/
theorem recoveredSet_correct
    (hBA : ∀ z, columnHom C (IncidenceSplit.incidence left right z) = 0)
    (hB1 : columnHom C (fun _ => 1) = 0) (D : CoordinateData m)
    (hD : D.Valid left right C hBA hB1) (c : Fin m → ℕ) (root : Fin n)
    (hc : Incidence.Connected left right) (π : Fin m → ℤ)
    (hπ : IntegerSlacks.OddRow left right root π) {M N : ℕ}
    (rows : InequalityRow C (G := Residue D.rank) D.rank ≃ Fin M)
    (cols : FiniteExtension.ExtensionArc C (Residue D.rank) ≃ Fin N) :
    Slack.Independent left right (recoveredSet left right C D c root π rows cols) ∧
      ∀ J, Slack.Independent left right J →
        natSetWeight left right c J ≤
          natSetWeight left right c (recoveredSet left right C D c root π rows cols) := by
  obtain ⟨I, hI, hmax, hv⟩ := lpValue_spec left right C hBA hB1 D hD c rows cols
  have hslack := natSetWeight_add_slack left right (perturbed c) hI
  have hdiff : total c - lpValue C D c rows cols =
      ∑ e, perturbed c e * slackBit left right I e := by
    unfold total
    omega
  have hdec : decode m (total c - lpValue C D c rows cols) =
      fun e => (slackBit left right I e : ℤ) := by
    rw [hdiff]
    exact decode_perturbed c _ (slackBit_le left right I)
  have hset : recoveredSet left right C D c root π rows cols = I := by
    unfold recoveredSet
    rw [hdec]
    exact recover_slackBit left right root hc π hπ hI
  rw [hset]
  exact ⟨hI, maximum_of_perturbed left right c hmax⟩

/-- The recovered set does not depend on the numbering of rows and columns. -/
theorem recoveredSet_enumeration_invariant
    (hBA : ∀ z, columnHom C (IncidenceSplit.incidence left right z) = 0)
    (hB1 : columnHom C (fun _ => 1) = 0) (D : CoordinateData m)
    (hD : D.Valid left right C hBA hB1) (c : Fin m → ℕ) (root : Fin n) (π : Fin m → ℤ)
    {M N M' N' : ℕ}
    (rows : InequalityRow C (G := Residue D.rank) D.rank ≃ Fin M)
    (cols : FiniteExtension.ExtensionArc C (Residue D.rank) ≃ Fin N)
    (rows' : InequalityRow C (G := Residue D.rank) D.rank ≃ Fin M')
    (cols' : FiniteExtension.ExtensionArc C (Residue D.rank) ≃ Fin N') :
    recoveredSet left right C D c root π rows cols =
      recoveredSet left right C D c root π rows' cols' := by
  unfold recoveredSet
  rw [lpValue_eq_of_valid left right C hBA hB1 D hD c rows cols rows' cols']

end Abstract

end MWIS.FPTHard

end
