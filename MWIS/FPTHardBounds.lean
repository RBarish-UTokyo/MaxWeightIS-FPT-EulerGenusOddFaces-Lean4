module

public import MWIS.FPTHardNetwork

/-!
# Size bounds for the fixed-parameter hard-component program

Explicit bounds, used for the operational cost, on the dense network program of
`MWIS.FPTHard`:

* rows plus columns are at most `6 · |Γ| · (2f + 2m + r + 2)^2`, where `|Γ|` is
  the residue-group size `GroupSize.residueCount r`;
* constraint coefficients are at most `K + 1` in absolute value when every
  free-coordinate entry is at most `K`; right-hand sides are at most one; the
  objective numerators are at most `2^(m+2) · (c_max + 1)`;
* the coefficient magnitude of every thresholded query program, the total
  perturbed cost, and the number of threshold-search bits.

Prepared 2026-10-23.
-/

@[expose] public section

namespace MWIS.FPTHard

open scoped BigOperators
open Walks ResidueJensen AlgorithmNetworkEncoding AlgorithmThresholdLP

/-! ## Generic magnitude bounds -/

/-- Entrywise bounds give a bound on the dense magnitude. -/
theorem magnitude_le_of_bounds {M N : ℕ} (P : DenseProgram M N) (a b d : ℕ)
    (ha : ∀ i j, (P.coefficient i j).natAbs ≤ a) (hb : ∀ i, (P.rhs i).natAbs ≤ b)
    (hd : ∀ j, (P.objective j).natAbs ≤ d) :
    magnitude P ≤ 1 + M * N * a + M * b + N * d := by
  unfold magnitude
  have h1 : (∑ i, ∑ j, (P.coefficient i j).natAbs) ≤ M * N * a := by
    calc _ ≤ ∑ _i : Fin M, ∑ _j : Fin N, a :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ha i j
      _ = _ := by simp [Nat.mul_assoc]
  have h2 : (∑ i, (P.rhs i).natAbs) ≤ M * b := by
    calc _ ≤ ∑ _i : Fin M, b := Finset.sum_le_sum fun i _ => hb i
      _ = _ := by simp
  have h3 : (∑ j, (P.objective j).natAbs) ≤ N * d := by
    calc _ ≤ ∑ _j : Fin N, d := Finset.sum_le_sum fun j _ => hd j
      _ = _ := by simp
  omega

/-- A threshold row adds exactly the objective magnitudes and the threshold. -/
theorem magnitude_withThreshold {M N : ℕ} (P : DenseProgram M N) (t : ℤ) :
    magnitude (P.withThreshold t) =
      magnitude P + (∑ j, (P.objective j).natAbs) + t.natAbs := by
  unfold magnitude DenseProgram.withThreshold
  simp only [Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ]
  ring

section Program

variable {f m : ℕ} (C : Fin m → Column (Fin f)) (D : CoordinateData m) (c : Fin m → ℕ)

/-! ## Dimensions -/

/-- Rows plus columns of the network program. -/
theorem rows_add_columns_le {M N : ℕ}
    (rows : InequalityRow C (G := Residue D.rank) D.rank ≃ Fin M)
    (cols : FiniteExtension.ExtensionArc C (Residue D.rank) ≃ Fin N) :
    M + N ≤ 6 * GroupSize.residueCount D.rank * (2 * f + 2 * m + D.rank + 2) ^ 2 := by
  have hm : Fintype.card (InequalityRow C (G := Residue D.rank) D.rank) = M := by
    simpa using Fintype.card_congr rows
  have hn : Fintype.card (FiniteExtension.ExtensionArc C (Residue D.rank)) = N := by
    simpa using Fintype.card_congr cols
  have hs := Walks.state_card (Fin f)
  have ha := Walks.arc_card_le C
  simp only [Fintype.card_fin] at hs ha
  have h := dimensions_bound (G := Residue D.rank) C D.rank (2 * f + 2 * m + D.rank + 1)
    (by omega) (by omega) (by omega)
  rw [hm, hn, GroupSize.residue_group_card] at h
  simpa [Nat.add_assoc] using h

/-! ## Coefficients -/

/-- Constraint coefficients are signed units or free-coordinate entries. -/
theorem program_coefficient_natAbs_le (K : ℕ)
    (hK : ∀ e d, (D.free (Pi.single e 1) d).natAbs ≤ K) {M N : ℕ}
    (rows : InequalityRow C (G := Residue D.rank) D.rank ≃ Fin M)
    (cols : FiniteExtension.ExtensionArc C (Residue D.rank) ≃ Fin N) (i : Fin M) (j : Fin N) :
    ((program C D c rows cols).coefficient i j).natAbs ≤ K + 1 := by
  change (matrix C D.free D.residue (rows.symm i) (cols.symm j)).natAbs ≤ K + 1
  rcases rows.symm i with a | ⟨u, s⟩
  · simp only [matrix]
    split_ifs <;> simp
  · have hu : (equalityCoefficient C D.free D.residue u (cols.symm j)).natAbs ≤ K + 1 := by
      cases u with
      | inl u =>
        have := incidenceCoefficient_natAbs_le C D.residue u (cols.symm j)
        exact this.trans (by omega)
      | inr d => exact (hK _ d).trans (by omega)
    cases s <;> simpa [matrix, rowSign] using hu

/-- Right-hand sides are signed units or zero. -/
theorem program_rhs_natAbs_le {M N : ℕ}
    (rows : InequalityRow C (G := Residue D.rank) D.rank ≃ Fin M)
    (cols : FiniteExtension.ExtensionArc C (Residue D.rank) ≃ Fin N) (i : Fin M) :
    ((program C D c rows cols).rhs i).natAbs ≤ 1 := by
  have h := bound_bit_bound C (AlgorithmComputedNetwork.target D.rank) (rows.symm i)
  have h2 := Nat.size_le.mp h
  change (bound C _ (rows.symm i)).natAbs ≤ 1
  omega

theorem perturbed_le (Cmax : ℕ) (hc : ∀ e, c e ≤ Cmax) (e : Fin m) :
    perturbed c e ≤ 2 ^ (m + 1) * (Cmax + 1) := by
  unfold perturbed
  have h1 : 2 ^ (m + 1) * c e ≤ 2 ^ (m + 1) * Cmax := Nat.mul_le_mul_left _ (hc e)
  have h2 : 2 ^ (e : ℕ) ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  nlinarith

/-- Objective numerators are twice the perturbed costs. -/
theorem program_objective_natAbs_le (Cmax : ℕ) (hc : ∀ e, c e ≤ Cmax) {M N : ℕ}
    (rows : InequalityRow C (G := Residue D.rank) D.rank ≃ Fin M)
    (cols : FiniteExtension.ExtensionArc C (Residue D.rank) ≃ Fin N) (j : Fin N) :
    ((program C D c rows cols).objective j).natAbs ≤ 2 ^ (m + 2) * (Cmax + 1) := by
  change (2 * (perturbed c _ : ℤ)).natAbs ≤ _
  have h := perturbed_le c Cmax hc (originalEdge C (cols.symm j))
  have he : (2 * (perturbed c (originalEdge C (cols.symm j)) : ℤ)).natAbs =
      2 * perturbed c (originalEdge C (cols.symm j)) := by omega
  rw [he, pow_succ]
  nlinarith

/-- The magnitude of the network program. -/
theorem program_magnitude_le (K Cmax : ℕ)
    (hK : ∀ e d, (D.free (Pi.single e 1) d).natAbs ≤ K) (hc : ∀ e, c e ≤ Cmax) {M N : ℕ}
    (rows : InequalityRow C (G := Residue D.rank) D.rank ≃ Fin M)
    (cols : FiniteExtension.ExtensionArc C (Residue D.rank) ≃ Fin N) :
    magnitude (program C D c rows cols) ≤
      1 + M * N * (K + 1) + M + N * (2 ^ (m + 2) * (Cmax + 1)) := by
  have h := magnitude_le_of_bounds (program C D c rows cols) (K + 1) 1 (2 ^ (m + 2) * (Cmax + 1))
    (program_coefficient_natAbs_le C D c K hK rows cols)
    (program_rhs_natAbs_le C D c rows cols)
    (program_objective_natAbs_le C D c Cmax hc rows cols)
  simpa using h

/-- The magnitude of a thresholded query program. -/
theorem query_magnitude_le (K Cmax : ℕ)
    (hK : ∀ e d, (D.free (Pi.single e 1) d).natAbs ≤ K) (hc : ∀ e, c e ≤ Cmax) {M N : ℕ}
    (rows : InequalityRow C (G := Residue D.rank) D.rank ≃ Fin M)
    (cols : FiniteExtension.ExtensionArc C (Residue D.rank) ≃ Fin N) (t : ℤ) :
    magnitude ((program C D c rows cols).withThreshold t) ≤
      1 + M * N * (K + 1) + M + 2 * N * (2 ^ (m + 2) * (Cmax + 1)) + t.natAbs := by
  rw [magnitude_withThreshold]
  have h1 := program_magnitude_le C D c K Cmax hK hc rows cols
  have h2 : (∑ j, ((program C D c rows cols).objective j).natAbs) ≤
      N * (2 ^ (m + 2) * (Cmax + 1)) := by
    calc _ ≤ ∑ _j : Fin N, 2 ^ (m + 2) * (Cmax + 1) :=
          Finset.sum_le_sum fun j _ => program_objective_natAbs_le C D c Cmax hc rows cols j
      _ = _ := by simp
  nlinarith

end Program

/-! ## Threshold search -/

section Search

variable {m : ℕ} (c : Fin m → ℕ)

theorem total_le (Cmax : ℕ) (hc : ∀ e, c e ≤ Cmax) :
    total c ≤ m * (2 ^ (m + 1) * (Cmax + 1)) := by
  unfold total
  calc _ ≤ ∑ _e : Fin m, 2 ^ (m + 1) * (Cmax + 1) :=
        Finset.sum_le_sum fun e _ => perturbed_le c Cmax hc e
    _ = _ := by simp

/-- Twice the total, the largest searched value, is below `2 ^ searchBits`. -/
theorem two_total_lt : 2 * total c < 2 ^ searchBits c := Nat.lt_size_self _

/-- The search width is at most twice the total plus one, in powers of two. -/
theorem pow_searchBits_le : 2 ^ searchBits c ≤ 4 * total c + 1 := by
  unfold searchBits
  rcases Nat.eq_zero_or_pos (2 * total c) with h | h
  · rw [h]; simp
  · have hs : 0 < (2 * total c).size := Nat.size_pos.mpr h
    have hlt := Nat.lt_size.mp (show (2 * total c).size - 1 < (2 * total c).size by omega)
    have he : 2 ^ (2 * total c).size = 2 * 2 ^ ((2 * total c).size - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega

/-- Every threshold queried by the search corresponds to a dense threshold of
absolute value at most `10 · total + 2`. -/
theorem query_threshold_natAbs_le (q : ℕ) (hq : q < 2 ^ searchBits c) :
    (2 * (total c : ℤ) - 2 * (q : ℤ)).natAbs ≤ 10 * total c + 2 := by
  have h := pow_searchBits_le c
  omega

theorem searchBits_le (Cmax : ℕ) (hc : ∀ e, c e ≤ Cmax) :
    searchBits c ≤ m.size + m + (Cmax + 1).size + 4 := by
  unfold searchBits
  have ht := total_le c Cmax hc
  have h1 : (2 * total c).size ≤ (2 * (m * (2 ^ (m + 1) * (Cmax + 1)))).size :=
    Nat.size_le_size (by omega)
  have h2 := AlgorithmBounds.product_address_bits 2 (m * (2 ^ (m + 1) * (Cmax + 1)))
  have h3 := AlgorithmBounds.product_address_bits m (2 ^ (m + 1) * (Cmax + 1))
  have h4 := AlgorithmBounds.product_address_bits (2 ^ (m + 1)) (Cmax + 1)
  have h5 : (2 ^ (m + 1)).size = m + 2 := by rw [Nat.size_pow]
  have h6 : (2 : ℕ).size = 2 := by decide
  omega

/-- The number of queries made by the threshold search is the search width. -/
theorem queries_length (test : ℕ → Bool) :
    (AlgorithmThresholdSearch.run test (searchBits c) 0).queries.length = searchBits c :=
  AlgorithmThresholdSearch.queries_length test (searchBits c) 0

end Search

end MWIS.FPTHard

end
