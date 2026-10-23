module

public import Mathlib.Combinatorics.Colex
public import Mathlib.Data.Nat.Size
public import Mathlib.Data.Int.NatAbs
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Lean.Elab.Tactic.Omega

/-!
# Recovery by binary perturbation of an integer objective

Prepared 2026-10-23.

Vertices are numbered by natural numbers below `n`. The encoded objective
multiplies every integer weight by `2^n` and adds the vertex's distinct binary
digit. Its quotient is the original objective and its remainder identifies
the selected set. Negative original weights are permitted.

These results prove the recovery step for any finite family of feasible sets;
they do not supply the value algorithm or a machine running-time bound.
-/

@[expose] public section

namespace MWIS.Recovery

open scoped BigOperators

/-- The incidence mask of a finite set of numbered vertices. -/
def mask (I : Finset ℕ) : ℕ := ∑ i ∈ I, 2 ^ i

/-- The unperturbed integer objective. -/
def weight (w : ℕ → ℤ) (I : Finset ℕ) : ℤ := ∑ i ∈ I, w i

/-- The integer weight used by the single call to the value algorithm. -/
def encodedWeight (n : ℕ) (w : ℕ → ℤ) (i : ℕ) : ℤ :=
  2 ^ n * w i + 2 ^ i

/-- The total encoded objective, expressed as its high and low parts. -/
def encodedValue (n : ℕ) (w : ℕ → ℤ) (I : Finset ℕ) : ℤ :=
  2 ^ n * weight w I + mask I

theorem encoded_objective (n : ℕ) (w : ℕ → ℤ) (I : Finset ℕ) :
    weight (encodedWeight n w) I = encodedValue n w I := by
  simp [weight, encodedWeight, encodedValue, mask, Finset.sum_add_distrib,
    Finset.mul_sum]

/-- All binary digits strictly below `n` fit below `2^n`. -/
theorem range_mask_lt (n : ℕ) : mask (Finset.range n) < 2 ^ n := by
  induction n with
  | zero => simp [mask]
  | succ n ih =>
    simp only [mask, Finset.sum_range_succ] at *
    rw [pow_succ]
    omega

/-- Every subset of the numbered vertices has a bounded nonnegative mask. -/
theorem mask_lt {n : ℕ} {I : Finset ℕ} (hI : I ⊆ Finset.range n) :
    mask I < 2 ^ n := by
  apply lt_of_le_of_lt _ (range_mask_lt n)
  exact Finset.sum_le_sum_of_subset hI

theorem mask_injective : Function.Injective mask := by
  exact Finset.geomSum_injective (by omega : 2 ≤ (2 : ℕ))

/-- The decoder lists exactly the vertices whose mask digits are one. -/
def decode (value : ℤ) (n : ℕ) : Finset ℕ :=
  ((value % (2 ^ n)).toNat).bitIndices.toFinset

/-- Integer remainder, including when the encoded value is negative. -/
theorem encoded_remainder (n : ℕ) (w : ℕ → ℤ) (I : Finset ℕ)
    (hI : I ⊆ Finset.range n) :
    encodedValue n w I % 2 ^ n = (mask I : ℤ) := by
  have hlo : (0 : ℤ) ≤ mask I := by omega
  have hhi : (mask I : ℤ) < 2 ^ n := by exact_mod_cast mask_lt hI
  simp [encodedValue, Int.add_emod, Int.emod_eq_of_lt hlo hhi]

/-- The original optimum value is the high part of the encoded value. -/
theorem encoded_quotient (n : ℕ) (w : ℕ → ℤ) (I : Finset ℕ)
    (hI : I ⊆ Finset.range n) :
    encodedValue n w I / 2 ^ n = weight w I := by
  have hpos : (0 : ℤ) < 2 ^ n := pow_pos (by omega) _
  have hlo : (0 : ℤ) ≤ mask I := by omega
  have hhi : (mask I : ℤ) < 2 ^ n := by exact_mod_cast mask_lt hI
  rw [encodedValue, Int.mul_add_ediv_left _ _ (ne_of_gt hpos)]
  rw [Int.ediv_eq_zero_of_lt hlo hhi]
  omega

/-- Decoding is exact for every subset of the numbered vertex set. -/
theorem decode_encoded (n : ℕ) (w : ℕ → ℤ) (I : Finset ℕ)
    (hI : I ⊆ Finset.range n) : decode (encodedValue n w I) n = I := by
  rw [decode, encoded_remainder n w I hI]
  rw [Int.toNat_natCast]
  exact Finset.toFinset_bitIndices_sum_two_pow I

/-- A strict improvement in original weight dominates all possible low bits. -/
theorem encoded_strict_of_weight_lt (n : ℕ) (w : ℕ → ℤ)
    (I J : Finset ℕ) (hI : I ⊆ Finset.range n) (_hJ : J ⊆ Finset.range n)
    (hweight : weight w I < weight w J) :
    encodedValue n w I < encodedValue n w J := by
  have hpos : (0 : ℤ) < 2 ^ n := pow_pos (by omega) _
  have hIlo : (0 : ℤ) ≤ mask I := by omega
  have hIhi : (mask I : ℤ) < 2 ^ n := by exact_mod_cast mask_lt hI
  have hJlo : (0 : ℤ) ≤ mask J := by omega
  have hw : weight w I + 1 ≤ weight w J := by omega
  have hm := mul_le_mul_of_nonneg_left hw (le_of_lt hpos)
  unfold encodedValue
  nlinarith

/-- Encoding orders feasible sets lexicographically by weight, then mask. -/
theorem encoded_le_iff (n : ℕ) (w : ℕ → ℤ)
    (I J : Finset ℕ) (hI : I ⊆ Finset.range n) (hJ : J ⊆ Finset.range n) :
    encodedValue n w I ≤ encodedValue n w J ↔
      weight w I < weight w J ∨ (weight w I = weight w J ∧ mask I ≤ mask J) := by
  constructor
  · intro h
    have hw : weight w I ≤ weight w J := by
      by_contra hn
      have hs := encoded_strict_of_weight_lt n w J I hJ hI (lt_of_not_ge hn)
      omega
    rcases lt_or_eq_of_le hw with hl | he
    · exact Or.inl hl
    · refine Or.inr ⟨he, ?_⟩
      unfold encodedValue at h
      rw [he] at h
      omega
  · rintro (hl | ⟨he, hm⟩)
    · exact le_of_lt (encoded_strict_of_weight_lt n w I J hI hJ hl)
    · unfold encodedValue
      rw [he]
      have hm' : (mask I : ℤ) ≤ (mask J : ℤ) := by exact_mod_cast hm
      omega

/-- No two bounded vertex sets have the same encoded objective. -/
theorem encoded_injective (n : ℕ) (w : ℕ → ℤ)
    (I J : Finset ℕ) (hI : I ⊆ Finset.range n) (hJ : J ⊆ Finset.range n)
    (he : encodedValue n w I = encodedValue n w J) : I = J := by
  rw [← decode_encoded n w I hI, he, decode_encoded n w J hJ]

/-- An encoded optimum is an original optimum and is recovered from its value.
The feasibility predicate may, in particular, be graph independence. -/
theorem recovery_of_encoded_optimum (n : ℕ) (w : ℕ → ℤ)
    (feasible : Finset ℕ → Prop)
    (hbound : ∀ I, feasible I → I ⊆ Finset.range n)
    (I : Finset ℕ) (hI : feasible I)
    (hmax : ∀ J, feasible J → encodedValue n w J ≤ encodedValue n w I) :
    (∀ J, feasible J → weight w J ≤ weight w I) ∧
      decode (encodedValue n w I) n = I ∧
      (∀ J, feasible J → encodedValue n w J = encodedValue n w I → J = I) := by
  refine ⟨?_, decode_encoded n w I (hbound I hI), ?_⟩
  · intro J hJ
    have h := (encoded_le_iff n w J I (hbound J hJ) (hbound I hI)).mp (hmax J hJ)
    rcases h with h | ⟨h, _⟩ <;> omega
  · intro J hJ he
    exact encoded_injective n w J I (hbound J hJ) (hbound I hI) he

/-- Every nonempty bounded family has a unique encoded maximizing set. -/
theorem exists_encoded_optimum (n : ℕ) (w : ℕ → ℤ)
    (feasible : Finset ℕ → Prop)
    (hbound : ∀ I, feasible I → I ⊆ Finset.range n)
    (hne : ∃ I, feasible I) :
    ∃ I, feasible I ∧
      (∀ J, feasible J → encodedValue n w J ≤ encodedValue n w I) ∧
      (∀ J, feasible J → weight w J ≤ weight w I) ∧
      decode (encodedValue n w I) n = I ∧
      (∀ J, feasible J → encodedValue n w J = encodedValue n w I → J = I) := by
  classical
  let candidates := (Finset.range n).powerset.filter feasible
  have hmem (I : Finset ℕ) : I ∈ candidates ↔ feasible I := by
    simp only [candidates, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨fun h => h.2, fun h => ⟨hbound I h, h⟩⟩
  obtain ⟨J, hJ⟩ := hne
  obtain ⟨I, hI, hm⟩ := Finset.exists_max_image candidates (encodedValue n w)
    ⟨J, (hmem J).mpr hJ⟩
  have hfeasible := (hmem I).mp hI
  have hmax : ∀ J, feasible J → encodedValue n w J ≤ encodedValue n w I :=
    fun J hJ => hm J ((hmem J).mpr hJ)
  exact ⟨I, hfeasible, hmax,
    recovery_of_encoded_optimum n w feasible hbound I hfeasible hmax⟩

/-- Binary perturbation adds at most `n + 1` magnitude bits to each weight. -/
theorem encoded_weight_size (n : ℕ) (w : ℕ → ℤ) (i : ℕ) (hi : i < n) :
    (encodedWeight n w i).natAbs.size ≤ n + (w i).natAbs.size + 1 := by
  apply Nat.size_le.mpr
  have hweight := Nat.lt_size_self (w i).natAbs
  have hbit : (2 : ℕ) ^ i < 2 ^ n := Nat.pow_lt_pow_right (by omega) hi
  have htri := Int.natAbs_add_le ((2 : ℤ) ^ n * w i) ((2 : ℤ) ^ i)
  norm_num [Int.natAbs_mul, Int.natAbs_pow] at htri
  change (2 ^ n * w i + 2 ^ i).natAbs < _
  calc
    (2 ^ n * w i + 2 ^ i).natAbs ≤ 2 ^ n * (w i).natAbs + 2 ^ i := htri
    _ < 2 ^ n * 2 ^ (w i).natAbs.size + 2 ^ n := by
      exact Nat.add_lt_add_of_le_of_lt (Nat.mul_le_mul_left _ (le_of_lt hweight)) hbit
    _ ≤ 2 ^ (n + (w i).natAbs.size + 1) := by
      rw [pow_succ, pow_add]
      have hp : 1 ≤ (2 : ℕ) ^ (w i).natAbs.size := Nat.one_le_pow _ _ (by omega)
      have hm := Nat.mul_le_mul_left (2 ^ n) hp
      omega

end MWIS.Recovery
