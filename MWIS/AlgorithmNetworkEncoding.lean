module

public import MWIS.FiniteExtension
public import MWIS.AlgorithmBounds
public import MWIS.AlgorithmSeparation
public import MWIS.SurfaceNetworkSize

/-!
# Explicit integer encoding of the finite-group network LP

Every row and coefficient is defined from the actual finite hub network and
integer coordinate columns. Nonnegativity and the two signs of each equality
form an integer inequality system. The coefficient bounds include the actual
projection, so free-coordinate rows retain their original integer entries.

Prepared 2026-10-23.
-/

@[expose] public section

namespace MWIS.AlgorithmNetworkEncoding

open scoped BigOperators
open Walks FiniteExtension GroupNetwork

variable {Row Edge G : Type*} [Fintype Row] [Fintype Edge] [Fintype G]
    [DecidableEq Row] [DecidableEq Edge] [DecidableEq G] [AddCommGroup G]

local instance nodeDecidableEq : DecidableEq (Node (State Row) G) :=
  @instDecidableEqSum G (Σ v : State Row, {u : State Row // u ≠ v} × G)
    inferInstance inferInstance

variable (C : Edge → Column Row)

/-- The original primal edge represented by an actual extension arc. -/
def originalEdge (a : ExtensionArc C G) : Edge := a.2.1.val.1

/-- The hub-balance rows followed by the integral free-coordinate rows. -/
abbrev EqualityRow (r : ℕ) := Node (State Row) G ⊕ Fin r

/-- Nonnegativity rows and both signs of all equality rows. -/
abbrev InequalityRow (r : ℕ) := ExtensionArc C G ⊕ (EqualityRow (Row := Row) (G := G) r × Bool)

/-- Actual directed hub-incidence coefficients; loops cancel in the same column. -/
def incidenceCoefficient (ell : (Edge → ℤ) →+ G)
    (u : Node (State Row) G) (a : ExtensionArc C G) : ℤ :=
  (if hubTarget (target C) (arcLabel C ell) a = u then 1 else 0) -
    (if hubSource (source C) a = u then 1 else 0)

/-- The integer equality matrix of the concrete network and its free-coordinate slice. -/
def equalityCoefficient {r : ℕ} (W : (Edge → ℤ) →+ (Fin r → ℤ))
    (ell : (Edge → ℤ) →+ G) : EqualityRow (Row := Row) (G := G) r → ExtensionArc C G → ℤ
  | .inl u, a => incidenceCoefficient C ell u a
  | .inr d, a => W (Pi.single (originalEdge C a) 1) d

/-- The only nonzero right-hand sides are the source and target hub demands. -/
def equalityBound {r : ℕ} (η : G) : EqualityRow (Row := Row) (G := G) r → ℤ
  | .inl u => demand η u
  | .inr _ => 0

/-- The two signs used to replace every exact equality with two inequalities. -/
def rowSign (b : Bool) : ℤ := if b then 1 else -1

/-- The dense integer inequality matrix, including nonnegativity. -/
def matrix {r : ℕ} (W : (Edge → ℤ) →+ (Fin r → ℤ))
    (ell : (Edge → ℤ) →+ G) : InequalityRow C (G := G) r → ExtensionArc C G → ℤ
  | .inl a, b => if a = b then -1 else 0
  | .inr (u, s), b => rowSign s * equalityCoefficient C W ell u b

/-- Integer right-hand sides for the dense inequality matrix. -/
def bound {r : ℕ} (η : G) : InequalityRow C (G := G) r → ℤ
  | .inl _ => 0
  | .inr (u, s) => rowSign s * equalityBound η u

/-- An integral objective numerator is repeated on every copy of its primal edge. -/
def objectiveNumerator (c : Edge → ℤ) (a : ExtensionArc C G) : ℤ := c (originalEdge C a)

omit [DecidableEq G] [AddCommGroup G] in
/-- The projection simply sums the variables representing each original edge. -/
theorem weighted_projection (f : Edge → ℝ) (z : ExtensionArc C G → ℝ) :
    (∑ e, f e * rho C z e) = ∑ a, f (originalEdge C a) * z a := by
  simp only [rho, LinearMap.comp_apply, coverProjectionReal, LinearMap.coe_mk,
    AddHom.coe_mk, GroupExtension.projectionLinear, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [Fintype.sum_prod_type, originalEdge]
  rw [Finset.sum_comm]

/-- Evaluating a hub incidence row gives the actual network balance. -/
theorem incidence_dot (ell : (Edge → ℤ) →+ G)
    (u : Node (State Row) G) (z : ExtensionArc C G → ℝ) :
    (∑ a, (incidenceCoefficient C ell u a : ℝ) * z a) =
      GroupNetwork.boundary (U := Node (State Row) G)
        (hubSource (source C)) (hubTarget (target C) (arcLabel C ell)) z u := by
  simp [incidenceCoefficient, boundary, sub_mul, Finset.sum_sub_distrib]

omit [DecidableEq G] [AddCommGroup G] in
/-- Free-coordinate rows retain exactly the original coordinate columns. -/
theorem coordinate_dot {r : ℕ} (W : (Edge → ℤ) →+ (Fin r → ℤ))
    (d : Fin r) (z : ExtensionArc C G → ℝ) :
    (∑ a, (W (Pi.single (originalEdge C a) 1) d : ℝ) * z a) =
      RealCoordinates.extension W (rho C z) d := by
  rw [← weighted_projection C (fun e => (W (Pi.single e 1) d : ℝ)) z]
  simp only [RealCoordinates.extension, LinearMap.coe_mk, AddHom.coe_mk]
  apply Finset.sum_congr rfl
  intro e _
  ring

/-- The equality rows express exactly the hub balances and the zero free class. -/
theorem equality_rows_iff {r : ℕ} (W : (Edge → ℤ) →+ (Fin r → ℤ))
    (ell : (Edge → ℤ) →+ G) (η : G) (z : ExtensionArc C G → ℝ) :
    (∀ u, (∑ a, (equalityCoefficient C W ell u a : ℝ) * z a) =
      (equalityBound η u : ℝ)) ↔
    (∀ u, GroupNetwork.boundary (U := Node (State Row) G)
      (hubSource (source C)) (hubTarget (target C) (arcLabel C ell)) z u =
        (demand η u : ℝ)) ∧ RealCoordinates.extension W (rho C z) = 0 := by
  constructor
  · intro h
    refine ⟨fun u => ?_, ?_⟩
    · simpa only [equalityCoefficient, equalityBound, incidence_dot] using h (.inl u)
    · ext d
      simpa only [equalityCoefficient, equalityBound, Int.cast_zero, coordinate_dot,
        Pi.zero_apply] using h (.inr d)
  · rintro ⟨hb, hw⟩ (u | d)
    · simpa only [equalityCoefficient, equalityBound, incidence_dot] using hb u
    · simp only [equalityCoefficient, equalityBound, Int.cast_zero, coordinate_dot,
        hw, Pi.zero_apply]

/-- The explicit integer inequality matrix has exactly the intended real
feasible set, including nonnegativity and every free-coordinate equation. -/
theorem feasible_iff {r : ℕ} (W : (Edge → ℤ) →+ (Fin r → ℤ))
    (ell : (Edge → ℤ) →+ G) (η : G) (z : ExtensionArc C G → ℝ) :
    (∀ i, (∑ a, (matrix C W ell i a : ℝ) * z a) ≤ (bound C η i : ℝ)) ↔
      z ∈ polyhedron C ell η ∧ RealCoordinates.extension W (rho C z) = 0 := by
  have hrow (a : ExtensionArc C G) :
      (∑ b, (matrix C W ell (.inl a) b : ℝ) * z b) = -z a := by
    simp only [matrix, Int.cast_ite, Int.cast_neg, Int.cast_one, Int.cast_zero,
      ite_mul, zero_mul, neg_one_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have he := equality_rows_iff C W ell η z
  constructor
  · intro h
    have hn : ∀ a, 0 ≤ z a := by
      intro a
      have ha := h (.inl a)
      rw [hrow] at ha
      simp only [bound, Int.cast_zero] at ha
      linarith
    have hh : ∀ u, (∑ a, (equalityCoefficient C W ell u a : ℝ) * z a) =
        (equalityBound η u : ℝ) := by
      intro u
      have hp := h (.inr (u, true))
      have hm := h (.inr (u, false))
      simp only [matrix, bound, rowSign, Bool.false_eq_true, ite_false, ite_true,
        Int.cast_neg, one_mul, neg_mul, Finset.sum_neg_distrib] at hp hm
      linarith
    have hh' := he.mp hh
    exact ⟨⟨hn, hh'.1⟩, hh'.2⟩
  · rintro ⟨⟨hn, hb⟩, hw⟩
    have hh := he.mpr ⟨hb, hw⟩
    rintro (a | ⟨u, s⟩)
    · rw [hrow]
      simp only [bound, Int.cast_zero]
      linarith [hn a]
    · cases s <;> simp only [matrix, bound, rowSign, Bool.false_eq_true, ite_false,
        ite_true, one_mul, Int.cast_neg, neg_mul, Finset.sum_neg_distrib, hh, le_refl]

omit [DecidableEq G] [AddCommGroup G] in
/-- Clearing the common cost denominator two changes only the objective,
with no increase in the integer constraint coefficients. -/
theorem objective_twice {c : Edge → ℚ} (n : Edge → ℤ)
    (hn : ∀ e, c e = (n e : ℚ) / 2) (z : ExtensionArc C G → ℝ) :
    (∑ a, (objectiveNumerator C n a : ℝ) * z a) =
      2 * RealCoordinates.cost c (rho C z) := by
  simp only [objectiveNumerator]
  rw [← weighted_projection C (fun e => (n e : ℝ)) z]
  simp only [RealCoordinates.cost, LinearMap.coe_mk, AddHom.coe_mk, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [hn, Rat.cast_div, Rat.cast_intCast, Rat.cast_ofNat]
  ring

omit [Fintype Row] [Fintype Edge] [Fintype G] in
/-- Hub-incidence entries lie in `{-1,0,1}`, including loops. -/
theorem incidenceCoefficient_natAbs_le (ell : (Edge → ℤ) →+ G)
    (u : Node (State Row) G) (a : ExtensionArc C G) :
    (incidenceCoefficient C ell u a).natAbs ≤ 1 := by
  unfold incidenceCoefficient
  split_ifs <;> norm_num

omit [Fintype Row] [Fintype G] in
/-- The unit-flow demand has only signed-unit or zero entries. -/
theorem equalityBound_natAbs_le {r : ℕ} (η : G)
    (u : EqualityRow (Row := Row) (G := G) r) :
    (equalityBound η u).natAbs ≤ 1 := by
  cases u with
  | inl u =>
    change (((if u = .inl η then 1 else 0) - (if u = .inl 0 then 1 else 0)) : ℤ).natAbs ≤ 1
    split_ifs <;> norm_num
  | inr d => simp [equalityBound]

/-- Every actual matrix entry uses at most the original coordinate bit bound
or one bit for an incidence/nonnegativity coefficient. -/
theorem matrix_bit_bound {r : ℕ} (W : (Edge → ℤ) →+ (Fin r → ℤ))
    (ell : (Edge → ℤ) →+ G) (B : ℕ) (hB : 1 ≤ B)
    (hW : ∀ e d, (W (Pi.single e 1) d).natAbs.size ≤ B)
    (i : InequalityRow C (G := G) r) (a : ExtensionArc C G) :
    (matrix C W ell i a).natAbs.size ≤ B := by
  rcases i with b | ⟨u, s⟩
  · simp only [matrix]
    split_ifs
    · simpa using hB
    · simp
  · have hu : (equalityCoefficient C W ell u a).natAbs.size ≤ B := by
      cases u with
      | inl u =>
        exact (Nat.size_le_size (incidenceCoefficient_natAbs_le C ell u a)).trans
          (by simpa using hB)
      | inr d => exact hW (originalEdge C a) d
    cases s <;> simpa [matrix, rowSign] using hu

omit [Fintype Edge] [DecidableEq Edge] in
/-- Both signs of a demand still require at most one magnitude bit. -/
theorem bound_bit_bound {r : ℕ} (η : G) (i : InequalityRow C (G := G) r) :
    (bound C η i).natAbs.size ≤ 1 := by
  rcases i with a | ⟨u, s⟩
  · simp [bound]
  · have hu := Nat.size_le_size (equalityBound_natAbs_le η u)
    cases s <;> simpa [bound, rowSign] using hu

omit [Fintype Row] [Fintype Edge] [Fintype G] [DecidableEq Row]
  [DecidableEq Edge] [DecidableEq G] [AddCommGroup G] in
/-- The objective numerator copies, without arithmetic growth, one original cost. -/
theorem objective_bit_bound (n : Edge → ℤ) (B : ℕ)
    (hn : ∀ e, (n e).natAbs.size ≤ B) (a : ExtensionArc C G) :
    (objectiveNumerator C n a).natAbs.size ≤ B := hn (originalEdge C a)

/-- An actual dense integer program, with its integer objective numerator. -/
structure DenseProgram (m n : ℕ) where
  coefficient : Fin m → Fin n → ℤ
  rhs : Fin m → ℤ
  objective : Fin n → ℤ

/-- Explicit finite indexing of the actual network coefficients. -/
def toDense {r m n : ℕ} (W : (Edge → ℤ) →+ (Fin r → ℤ))
    (ell : (Edge → ℤ) →+ G) (η : G) (c : Edge → ℤ)
    (rows : InequalityRow C (G := G) r ≃ Fin m)
    (cols : ExtensionArc C G ≃ Fin n) : DenseProgram m n where
  coefficient i j := matrix C W ell (rows.symm i) (cols.symm j)
  rhs i := bound C η (rows.symm i)
  objective j := objectiveNumerator C c (cols.symm j)

/-- Dense enumeration is an explicit finite list construction. -/
def DenseProgram.entries {m n : ℕ} (P : DenseProgram m n) : List ℤ :=
  (List.ofFn fun i => List.ofFn (P.coefficient i)).flatten ++
    List.ofFn P.rhs ++ List.ofFn P.objective

/-- The number of coefficient reads in this dense enumeration is exact. -/
theorem DenseProgram.entries_length {m n : ℕ} (P : DenseProgram m n) :
    P.entries.length = m * n + m + n := by
  simp [DenseProgram.entries, Function.comp_def, List.ofFn_const, Nat.add_assoc]

/-- Signed magnitude encoding of all entries, with a conservative dimension header. -/
def DenseProgram.encodingLength {m n : ℕ} (P : DenseProgram m n) : ℕ :=
  m + n + (∑ i, ∑ j, (1 + (P.coefficient i j).natAbs.size)) +
    (∑ i, (1 + (P.rhs i).natAbs.size)) + ∑ j, (1 + (P.objective j).natAbs.size)

/-- The finite-index integer inequalities agree with the actual network LP
at the real embedding of every rational point. -/
theorem toDense_feasible_iff {r m n : ℕ} (W : (Edge → ℤ) →+ (Fin r → ℤ))
    (ell : (Edge → ℤ) →+ G) (η : G) (c : Edge → ℤ)
    (rows : InequalityRow C (G := G) r ≃ Fin m)
    (cols : ExtensionArc C G ≃ Fin n) (x : Fin n → ℚ) :
    AlgorithmSeparation.Feasible (toDense C W ell η c rows cols).coefficient
      (toDense C W ell η c rows cols).rhs x ↔
    (fun a => (x (cols a) : ℝ)) ∈ polyhedron C ell η ∧
      RealCoordinates.extension W (rho C (fun a => (x (cols a) : ℝ))) = 0 := by
  rw [← feasible_iff]
  constructor
  · intro h i
    have hi := h (rows i)
    simp only [AlgorithmSeparation.rationalDot, toDense, Equiv.symm_apply_apply] at hi
    have hs := cols.sum_comp (fun j => (matrix C W ell i (cols.symm j) : ℚ) * x j)
    simp only [Equiv.symm_apply_apply] at hs
    rw [← hs] at hi
    exact_mod_cast hi
  · intro h i
    have hi := h (rows.symm i)
    have hs := cols.sum_comp
      (fun j => (matrix C W ell (rows.symm i) (cols.symm j) : ℝ) * (x j : ℝ))
    simp only [Equiv.symm_apply_apply] at hs
    rw [hs] at hi
    change (∑ j, (matrix C W ell (rows.symm i) (cols.symm j) : ℚ) * x j) ≤
      bound C η (rows.symm i)
    exact_mod_cast hi

omit [DecidableEq Edge] [DecidableEq G] [AddCommGroup G] in
/-- The exact number of inequality rows accounts for both equality signs. -/
theorem inequalityRow_card (r : ℕ) :
    Fintype.card (InequalityRow C (G := G) r) =
      Fintype.card (ExtensionArc C G) +
        2 * (Fintype.card (Node (State Row) G) + r) := by
  simp only [InequalityRow, EqualityRow, Fintype.card_sum, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_bool]
  ring

/-- Rows plus columns are bounded by group size times a quadratic in the
original signed-cover dimensions and the free-coordinate rank. -/
theorem dimensions_bound (r N : ℕ)
    (hstate : Fintype.card (State Row) ≤ N)
    (harc : Fintype.card (Walks.Arc C) ≤ N) (hr : r ≤ N) :
    Fintype.card (InequalityRow C (G := G) r) +
      Fintype.card (ExtensionArc C G) ≤ 6 * Fintype.card G * (N + 1) ^ 2 := by
  have hh := AlgorithmBounds.hub_counts_bound (State Row) (Walks.Arc C) G N hstate harc
  have hG : 1 ≤ Fintype.card G := Fintype.card_pos_iff.mpr ⟨0⟩
  rw [inequalityRow_card]
  change Fintype.card (Node (State Row) G) + Fintype.card (ExtensionArc C G) ≤ _ at hh
  have hN : N ≤ Fintype.card G * (N + 1) ^ 2 := by nlinarith
  nlinarith

/-- A uniform entry-bit bound gives a quadratic bound for the dense encoding. -/
theorem DenseProgram.encodingLength_le {m n : ℕ} (P : DenseProgram m n)
    (B : ℕ) (hA : ∀ i j, (P.coefficient i j).natAbs.size ≤ B)
    (hb : ∀ i, (P.rhs i).natAbs.size ≤ B)
    (hc : ∀ j, (P.objective j).natAbs.size ≤ B) :
    P.encodingLength ≤ (m + n + 1) ^ 2 * (B + 3) := by
  have hA' : (∑ i, ∑ j, (1 + (P.coefficient i j).natAbs.size)) ≤ m * n * (B + 1) := by
    calc
      _ ≤ ∑ _i : Fin m, ∑ _j : Fin n, (B + 1) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by have := hA i j; omega
      _ = _ := by simp [Nat.mul_assoc]
  have hb' : (∑ i, (1 + (P.rhs i).natAbs.size)) ≤ m * (B + 1) := by
    calc
      _ ≤ ∑ _i : Fin m, (B + 1) := Finset.sum_le_sum fun i _ => by have := hb i; omega
      _ = _ := by simp
  have hc' : (∑ j, (1 + (P.objective j).natAbs.size)) ≤ n * (B + 1) := by
    calc
      _ ≤ ∑ _j : Fin n, (B + 1) := Finset.sum_le_sum fun j _ => by have := hc j; omega
      _ = _ := by simp
  unfold DenseProgram.encodingLength
  calc
    _ ≤ m + n + m * n * (B + 1) + m * (B + 1) + n * (B + 1) := by omega
    _ ≤ _ := by nlinarith [sq_nonneg (m : ℤ), sq_nonneg (n : ℤ)]

/-- The dense encoding of the actual network LP is bounded by the square of
the residue-group size times a fixed polynomial in dimensions and coefficient bits. -/
theorem toDense_encoding_bound {r m n : ℕ} (W : (Edge → ℤ) →+ (Fin r → ℤ))
    (ell : (Edge → ℤ) →+ G) (η : G) (c : Edge → ℤ)
    (rows : InequalityRow C (G := G) r ≃ Fin m)
    (cols : ExtensionArc C G ≃ Fin n) (N B : ℕ)
    (hstate : Fintype.card (State Row) ≤ N)
    (harc : Fintype.card (Walks.Arc C) ≤ N) (hr : r ≤ N) (hB : 1 ≤ B)
    (hW : ∀ e d, (W (Pi.single e 1) d).natAbs.size ≤ B)
    (hc : ∀ e, (c e).natAbs.size ≤ B) :
    (toDense C W ell η c rows cols).encodingLength ≤
      (Fintype.card G) ^ 2 * (N + B + 8) ^ 7 := by
  have hsize := DenseProgram.encodingLength_le (toDense C W ell η c rows cols) B
    (fun i j => matrix_bit_bound C W ell B hB hW (rows.symm i) (cols.symm j))
    (fun i => (bound_bit_bound C η (rows.symm i)).trans hB)
    (fun j => objective_bit_bound C c B hc (cols.symm j))
  have hm : Fintype.card (InequalityRow C (G := G) r) = m := by
    simpa using Fintype.card_congr rows
  have hn : Fintype.card (ExtensionArc C G) = n := by
    simpa using Fintype.card_congr cols
  have hd := dimensions_bound (G := G) C r N hstate harc hr
  rw [hm, hn] at hd
  have hG : 1 ≤ Fintype.card G := Fintype.card_pos_iff.mpr ⟨0⟩
  have hpos : 1 ≤ Fintype.card G * (N + 1) ^ 2 := by
    have hgt : 0 < Fintype.card G * (N + 1) ^ 2 := by positivity
    omega
  have hdim : m + n + 1 ≤ 7 * Fintype.card G * (N + 1) ^ 2 := by nlinarith
  let T := N + B + 8
  have hseven : 7 ^ 2 ≤ T ^ 2 := Nat.pow_le_pow_left (by dsimp [T]; omega) 2
  have hN : (N + 1) ^ 4 ≤ T ^ 4 := Nat.pow_le_pow_left (by dsimp [T]; omega) 4
  have hbit : B + 3 ≤ T := by dsimp [T]; omega
  calc
    (toDense C W ell η c rows cols).encodingLength ≤ (m + n + 1) ^ 2 * (B + 3) := hsize
    _ ≤ (7 * Fintype.card G * (N + 1) ^ 2) ^ 2 * (B + 3) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hdim 2)
    _ = (Fintype.card G) ^ 2 * (7 ^ 2 * ((N + 1) ^ 4 * (B + 3))) := by ring
    _ ≤ (Fintype.card G) ^ 2 * (T ^ 2 * (T ^ 4 * T)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul hseven (Nat.mul_le_mul hN hbit))
    _ = (Fintype.card G) ^ 2 * (N + B + 8) ^ 7 := by dsimp [T]; ring

/-- The signed-cover dimension assumptions have an explicit bound in terms of
the original facial rows, primal edges, and coordinate rank. -/
theorem toDense_encoding_bound_explicit {r m n : ℕ}
    (W : (Edge → ℤ) →+ (Fin r → ℤ)) (ell : (Edge → ℤ) →+ G)
    (η : G) (c : Edge → ℤ)
    (rows : InequalityRow C (G := G) r ≃ Fin m)
    (cols : ExtensionArc C G ≃ Fin n) (B : ℕ) (hB : 1 ≤ B)
    (hW : ∀ e d, (W (Pi.single e 1) d).natAbs.size ≤ B)
    (hc : ∀ e, (c e).natAbs.size ≤ B) :
    (toDense C W ell η c rows cols).encodingLength ≤
      (Fintype.card G) ^ 2 *
        (2 * Fintype.card Row + 2 * Fintype.card Edge + r + B + 9) ^ 7 := by
  have hs := Walks.state_card (Row := Row)
  have ha := Walks.arc_card_le C
  have h := toDense_encoding_bound C W ell η c rows cols
    (2 * Fintype.card Row + 2 * Fintype.card Edge + r + 1) B
    (by omega) (by omega) (by omega) hB hW hc
  convert h using 1
  congr 2
  omega

/-- An integer objective threshold adds one explicitly stored inequality row. -/
def DenseProgram.withThreshold {m n : ℕ} (P : DenseProgram m n) (t : ℤ) :
    DenseProgram (m + 1) n where
  coefficient := Fin.cases P.objective P.coefficient
  rhs := Fin.cases t P.rhs
  objective := P.objective

/-- The thresholded system has exactly its intended optimization meaning. -/
theorem DenseProgram.withThreshold_feasible_iff {m n : ℕ}
    (P : DenseProgram m n) (t : ℤ) (x : Fin n → ℚ) :
    AlgorithmSeparation.Feasible (P.withThreshold t).coefficient (P.withThreshold t).rhs x ↔
      AlgorithmSeparation.Feasible P.coefficient P.rhs x ∧
      AlgorithmSeparation.rationalDot P.objective x ≤ t := by
  constructor
  · intro h
    exact ⟨fun i => h i.succ, h 0⟩
  · rintro ⟨h, ht⟩ i
    refine Fin.cases ht (fun j => h j) i

/-- Adding a threshold with the same bit bound keeps a quadratic dense size. -/
theorem DenseProgram.withThreshold_encoding_bound {m n : ℕ}
    (P : DenseProgram m n) (t : ℤ) (B : ℕ)
    (hA : ∀ i j, (P.coefficient i j).natAbs.size ≤ B)
    (hb : ∀ i, (P.rhs i).natAbs.size ≤ B)
    (hc : ∀ j, (P.objective j).natAbs.size ≤ B)
    (ht : t.natAbs.size ≤ B) :
    (P.withThreshold t).encodingLength ≤ (m + n + 2) ^ 2 * (B + 3) := by
  have h := (P.withThreshold t).encodingLength_le B
    (fun i => Fin.cases hc hA i) (fun i => Fin.cases ht hb i) hc
  convert h using 1
  congr 2
  omega

/-- Stored finite tables sufficient to enumerate the integer LP; no additive
map needs to be evaluated during dense matrix enumeration. -/
structure CoefficientTables (Edge G : Type*) (r : ℕ) where
  coordinate : Fin r → Edge → ℤ
  residue : Edge → G
  cost : Edge → ℤ

/-- The finite tables are the unit-coordinate columns of the proved maps. -/
def tablesOfMaps {r : ℕ} (W : (Edge → ℤ) →+ (Fin r → ℤ))
    (ell : (Edge → ℤ) →+ G) (c : Edge → ℤ) : CoefficientTables Edge G r where
  coordinate d e := W (Pi.single e 1) d
  residue e := ell (Pi.single e 1)
  cost := c

/-- Direct table-based enumeration of one equality coefficient. -/
def tableEqualityCoefficient {r : ℕ} (T : CoefficientTables Edge G r) :
    EqualityRow (Row := Row) (G := G) r → ExtensionArc C G → ℤ
  | .inl u, a =>
    (if hubTarget (target C) (fun b => T.residue b.val.1) a = u then 1 else 0) -
      (if hubSource (source C) a = u then 1 else 0)
  | .inr d, a => T.coordinate d (originalEdge C a)

/-- Direct table-based enumeration of the actual dense integer program. -/
def toDenseTables {r m n : ℕ} (T : CoefficientTables Edge G r) (η : G)
    (rows : InequalityRow C (G := G) r ≃ Fin m)
    (cols : ExtensionArc C G ≃ Fin n) : DenseProgram m n where
  coefficient i j := match rows.symm i with
    | .inl a => if a = cols.symm j then -1 else 0
    | .inr (u, s) => rowSign s * tableEqualityCoefficient C T u (cols.symm j)
  rhs i := bound C η (rows.symm i)
  objective j := T.cost (originalEdge C (cols.symm j))

/-- Table-based enumeration produces exactly the proved network matrix. -/
theorem toDenseTables_eq {r m n : ℕ} (W : (Edge → ℤ) →+ (Fin r → ℤ))
    (ell : (Edge → ℤ) →+ G) (η : G) (c : Edge → ℤ)
    (rows : InequalityRow C (G := G) r ≃ Fin m)
    (cols : ExtensionArc C G ≃ Fin n) :
    toDenseTables C (tablesOfMaps W ell c) η rows cols = toDense C W ell η c rows cols := by
  unfold toDenseTables toDense
  congr 1
  funext i j
  rcases rows.symm i with a | ⟨u, s⟩
  · rfl
  · cases u <;> rfl

/-- Dense enumeration from the stored tables has the same exact correctness. -/
theorem toDenseTables_feasible_iff {r m n : ℕ} (W : (Edge → ℤ) →+ (Fin r → ℤ))
    (ell : (Edge → ℤ) →+ G) (η : G) (c : Edge → ℤ)
    (rows : InequalityRow C (G := G) r ≃ Fin m)
    (cols : ExtensionArc C G ≃ Fin n) (x : Fin n → ℚ) :
    AlgorithmSeparation.Feasible
      (toDenseTables C (tablesOfMaps W ell c) η rows cols).coefficient
      (toDenseTables C (tablesOfMaps W ell c) η rows cols).rhs x ↔
    (fun a => (x (cols a) : ℝ)) ∈ polyhedron C ell η ∧
      RealCoordinates.extension W (rho C (fun a => (x (cols a) : ℝ))) = 0 := by
  rw [toDenseTables_eq]
  exact toDense_feasible_iff C W ell η c rows cols x

end MWIS.AlgorithmNetworkEncoding

end
