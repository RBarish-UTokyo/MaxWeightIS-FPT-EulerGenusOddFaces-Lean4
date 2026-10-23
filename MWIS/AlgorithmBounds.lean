module

public import MWIS.GroupSize
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Nat.Size
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-!
# Sizes of the finite-group extension and numerical runtime bounds

Prepared 2026-10-23.

The state type keeps one hub for each group element and a separate state for
all pairs of distinct base vertices. Arc indices retain the base copy, the
original arc, and the group state. The results count these finite types and
bound their binary address lengths. The final arithmetic lemmas describe how
a polynomial solver bound composes with the finite-group size; they do not
assert existence or correctness of such a solver.
-/

@[expose] public section

namespace MWIS.AlgorithmBounds

/-- The non-hub positions of a based graph copy. -/
abbrev OffDiagonal (U : Type*) := {p : U × U // p.1 ≠ p.2}

/-- Canonical hub-extension states after identifying every based diagonal. -/
abbrev HubState (U Γ : Type*) := Γ ⊕ (Σ v : U, {u : U // u ≠ v} × Γ)

/-- An extension arc retains its base copy, original arc, and initial group state. -/
abbrev HubArc (U E Γ : Type*) := U × E × Γ

private def diagonalEquiv (U : Type*) : {p : U × U // p.1 = p.2} ≃ U where
  toFun p := p.val.1
  invFun u := ⟨(u, u), rfl⟩
  left_inv := by
    rintro ⟨⟨u, v⟩, h⟩
    simp only at h
    subst v
    rfl
  right_inv _ := rfl

/-- Distinct ordered pairs have cardinality `u*(u-1)`, including the empty case. -/
theorem offDiagonal_card (U : Type*) [Fintype U] [DecidableEq U] :
    Fintype.card (OffDiagonal U) = Fintype.card U * (Fintype.card U - 1) := by
  change Fintype.card {p : U × U // ¬p.1 = p.2} = _
  rw [Fintype.card_subtype_compl, Fintype.card_prod,
    Fintype.card_congr (diagonalEquiv U)]
  simp [Nat.mul_sub_left_distrib]

/-- Exact number of vertices in the finite-group hub construction. -/
theorem hubState_card (U Γ : Type*) [Fintype U] [DecidableEq U] [Fintype Γ] :
    Fintype.card (HubState U Γ) =
      Fintype.card Γ * (1 + Fintype.card U * (Fintype.card U - 1)) := by
  have hcard (v : U) : Fintype.card {u : U // u ≠ v} = Fintype.card U - 1 := by
    simp [Fintype.card_subtype_compl]
  simp only [HubState, Fintype.card_sum, Fintype.card_sigma, Fintype.card_prod, hcard,
    Finset.sum_const, Finset.card_univ, smul_eq_mul]
  ring

/-- Exact number of arcs in the finite-group hub construction. -/
theorem hubArc_card (U E Γ : Type*) [Fintype U] [Fintype E] [Fintype Γ] :
    Fintype.card (HubArc U E Γ) = Fintype.card Γ * Fintype.card U * Fintype.card E := by
  simp only [HubArc, Fintype.card_prod]
  ring

/-- Both vertices and arcs are bounded by the group size times a quadratic. -/
theorem hub_counts_bound (U E Γ : Type*) [Fintype U] [DecidableEq U]
    [Fintype E] [Fintype Γ] (N : ℕ)
    (hU : Fintype.card U ≤ N) (hE : Fintype.card E ≤ N) :
    Fintype.card (HubState U Γ) + Fintype.card (HubArc U E Γ) ≤
      2 * Fintype.card Γ * (N + 1) ^ 2 := by
  rw [hubState_card, hubArc_card]
  have hpair : Fintype.card U * (Fintype.card U - 1) ≤ N * N :=
    Nat.mul_le_mul hU ((Nat.sub_le _ _).trans hU)
  have harc : Fintype.card U * Fintype.card E ≤ N * N := Nat.mul_le_mul hU hE
  have hsum : 1 + Fintype.card U * (Fintype.card U - 1) +
      Fintype.card U * Fintype.card E ≤ 2 * (N + 1) ^ 2 := by
    nlinarith
  have hm := Nat.mul_le_mul_left (Fintype.card Γ) hsum
  nlinarith only [hm]

/-- The exponent in the explicit finite-group estimate. -/
def parameterExponent (p : ℕ) : ℕ := 1 + p * (3 + Nat.log2 (p + 1))

/-- Storing a residue-group index requires only polynomially many parameter bits. -/
theorem residue_address_bits (r p : ℕ) (hrp : r ≤ p) :
    (GroupSize.residueCount r).size ≤ parameterExponent p + 1 := by
  have hs := Nat.size_le_size (GroupSize.residueCount_le_exponential r p hrp)
  simpa [Nat.size_pow, parameterExponent] using hs

/-- A simple quadratic upper bound for the bit length of a residue-group index. -/
theorem residue_address_bits_quadratic (r N : ℕ) (hrN : r ≤ N) :
    (GroupSize.residueCount r).size ≤ 2 + N * (N + 4) := by
  have hs := residue_address_bits r N hrN
  have hl := Nat.log2_le_self (N + 1)
  unfold parameterExponent at hs
  nlinarith

/-- Address lengths multiply additively, with a harmless extra bit. -/
theorem product_address_bits (a b : ℕ) : (a * b).size ≤ a.size + b.size := by
  apply Nat.size_le.mpr
  rw [pow_add]
  exact lt_of_le_of_lt (Nat.mul_le_mul_right _ (le_of_lt (Nat.lt_size_self a)))
    (Nat.mul_lt_mul_of_pos_left (Nat.lt_size_self b) (by positivity))

/-- Exact exponent arithmetic for a polynomial in the extension size. -/
theorem polynomial_size_bound (r p N d c : ℕ) (hrp : r ≤ p) :
    (GroupSize.residueCount r * (N + 1) ^ d) ^ c ≤
      2 ^ (c * parameterExponent p) * (N + 1) ^ (d * c) := by
  rw [mul_pow, ← pow_mul]
  apply Nat.mul_le_mul_right
  calc
    GroupSize.residueCount r ^ c ≤ (2 ^ parameterExponent p) ^ c :=
      Nat.pow_le_pow_left (GroupSize.residueCount_le_exponential r p hrp) c
    _ = 2 ^ (c * parameterExponent p) := by rw [← pow_mul, Nat.mul_comm]

/-- Polynomially many polynomial-size subproblems preserve an absolute exponent.
This is an arithmetic composition lemma, with no solver or machine oracle. -/
theorem polynomial_calls_bound (r p N a b c d : ℕ) (hrp : r ≤ p) :
    (N + 1) ^ a + (N + 1) ^ b *
        (GroupSize.residueCount r * (N + 1) ^ d) ^ c ≤
      2 ^ (1 + c * parameterExponent p) * (N + 1) ^ (a + b + d * c) := by
  let B := N + 1
  let Q := 2 ^ (c * parameterExponent p)
  have hB : 1 ≤ B := by simp [B]
  have hQ : 1 ≤ Q := Nat.one_le_pow _ _ (by omega)
  have hmain := polynomial_size_bound r p N d c hrp
  have hba : B ^ a ≤ B ^ (a + b + d * c) :=
    Nat.pow_le_pow_right hB (by omega)
  have hbc : B ^ (b + d * c) ≤ B ^ (a + b + d * c) :=
    Nat.pow_le_pow_right hB (by omega)
  have hterm : B ^ b * (GroupSize.residueCount r * B ^ d) ^ c ≤
      Q * B ^ (a + b + d * c) := by
    calc
      B ^ b * (GroupSize.residueCount r * B ^ d) ^ c ≤
          B ^ b * (Q * B ^ (d * c)) := Nat.mul_le_mul_left _ hmain
      _ = Q * B ^ (b + d * c) := by rw [pow_add]; ring
      _ ≤ Q * B ^ (a + b + d * c) := Nat.mul_le_mul_left _ hbc
  have hfirst : B ^ a ≤ Q * B ^ (a + b + d * c) :=
    hba.trans (Nat.le_mul_of_pos_left _ (by omega))
  change B ^ a + B ^ b * (GroupSize.residueCount r * B ^ d) ^ c ≤ _
  calc
    B ^ a + B ^ b * (GroupSize.residueCount r * B ^ d) ^ c ≤
        2 * Q * B ^ (a + b + d * c) := by
      calc
        _ ≤ Q * B ^ (a + b + d * c) + Q * B ^ (a + b + d * c) :=
          Nat.add_le_add hfirst hterm
        _ = _ := by ring
    _ = _ := by rw [Nat.pow_add 2 1 (c * parameterExponent p)]

end MWIS.AlgorithmBounds
