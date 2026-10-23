module

public import MWIS.Midpoint
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Lean.Elab.Tactic.Omega

/-!
# Direct conformal splitting for unsigned incidence

Rounding vertex potentials according to their residues modulo four gives a
conformal half of every edge vector whose incidence class is divisible by four.
The proof applies to arbitrary endpoint maps, including loops and parallel edges.
Prepared 2026-10-23.
-/

@[expose] public section

namespace MWIS.IncidenceSplit

/-- The unsigned edge-incidence homomorphism; a loop counts its vertex twice. -/
def incidence {V E : Type*} (left right : E → V) :
    (V → ℤ) →+ (E → ℤ) where
  toFun z e := z (left e) + z (right e)
  map_zero' := by
    funext e
    exact add_zero (0 : ℤ)
  map_add' := by
    intro x y
    funext e
    exact add_add_add_comm (x (left e)) (y (left e)) (x (right e)) (y (right e))

/-- Half-rounding of a vertex potential, with residue one rounded down and
residue three rounded up. Even integers are divided by two exactly. -/
def halfRound (z : ℤ) : ℤ :=
  2 * (z / 4) + if z % 4 = 3 then 2 else if z % 4 = 2 then 1 else 0

theorem halfRound_conformal (u v w : ℤ) :
    min 0 (4 * w + u + v) ≤ 2 * w + halfRound u + halfRound v ∧
      2 * w + halfRound u + halfRound v ≤ max 0 (4 * w + u + v) := by
  have hu := Int.emod_nonneg u (by omega : (4 : ℤ) ≠ 0)
  have hu' := Int.emod_lt_of_pos u (by omega : (0 : ℤ) < 4)
  have hv := Int.emod_nonneg v (by omega : (4 : ℤ) ≠ 0)
  have hv' := Int.emod_lt_of_pos v (by omega : (0 : ℤ) < 4)
  unfold halfRound
  split_ifs <;> omega

/-- The rounded summand of `4 • v + A z` is conformal to the original vector.
This is a purely integral incidence identity and requires no surface structure. -/
theorem conformal_rounding {V E : Type*} (left right : E → V)
    (v : E → ℤ) (z : V → ℤ) :
    Midpoint.Conformal
      (2 • v + incidence left right (fun t => halfRound (z t)))
      (4 • v + incidence left right z) := by
  intro e
  simpa [incidence, Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, add_assoc] using
    halfRound_conformal (z (left e)) (z (right e)) (v e)

/-- An explicit incidence representative yields a conformal half with the
expected cycle class. -/
theorem split_incidence_representative {V E K H : Type*}
    [AddCommGroup K] [AddCommGroup H]
    (left right : E → V) (B : (E → ℤ) →+ K) (Q : (E → ℤ) →+ H)
    (hBA : ∀ z, B (incidence left right z) = 0)
    (hQA : ∀ z, Q (incidence left right z) = 0)
    (v : E → ℤ) (z : V → ℤ) (hv : B v = 0) :
    ∃ a, B a = 0 ∧ Q a = 2 • Q v ∧
      Midpoint.Conformal a (4 • v + incidence left right z) := by
  refine ⟨2 • v + incidence left right (fun t => halfRound (z t)), ?_, ?_,
    conformal_rounding left right v z⟩
  · rw [map_add, map_nsmul, hv, hBA, nsmul_zero, add_zero]
  · rw [map_add, map_nsmul, hQA, add_zero]

/-- Cycle classes modulo unsigned vertex incidence have exact conformal
splitting at multiples of four. Only the usual kernel and representative
properties of the quotient are needed. -/
theorem split_class {V E K H : Type*}
    [AddCommGroup K] [AddCommGroup H]
    (left right : E → V) (B : (E → ℤ) →+ K) (Q : (E → ℤ) →+ H)
    (hBA : ∀ z, B (incidence left right z) = 0)
    (hQA : ∀ z, Q (incidence left right z) = 0)
    (hrep : ∀ b, ∃ v, B v = 0 ∧ Q v = b)
    (hker : ∀ x, B x = 0 → Q x = 0 → ∃ z, incidence left right z = x)
    (x : E → ℤ) (b : H) (hBx : B x = 0) (hQx : Q x = 4 • b) :
    ∃ a, B a = 0 ∧ Q a = 2 • b ∧ Midpoint.Conformal a x := by
  obtain ⟨v, hBv, hQv⟩ := hrep b
  have hBdiff : B (x - 4 • v) = 0 := by
    rw [map_sub, map_nsmul, hBx, hBv, nsmul_zero, sub_zero]
  have hQdiff : Q (x - 4 • v) = 0 := by
    rw [map_sub, map_nsmul, hQx, hQv, sub_self]
  obtain ⟨z, hz⟩ := hker (x - 4 • v) hBdiff hQdiff
  obtain ⟨a, hBa, hQa, hconf⟩ :=
    split_incidence_representative left right B Q hBA hQA v z hBv
  refine ⟨a, hBa, by simpa [hQv] using hQa, ?_⟩
  have hx : 4 • v + incidence left right z = x := by rw [hz]; abel
  rwa [hx] at hconf

/-- Minimum nonnegative-cycle cost is midpoint convex on every doubled coset
of the unsigned-incidence quotient. The splitting premise is discharged by
explicit vertex-potential rounding. -/
theorem midpoint_from_incidence {V E K H : Type*}
    [AddCommGroup K] [AddCommGroup H]
    (left right : E → V) (B : (E → ℤ) →+ K) (Q : (E → ℤ) →+ H)
    (hBA : ∀ z, B (incidence left right z) = 0)
    (hQA : ∀ z, Q (incidence left right z) = 0)
    (hrep : ∀ b, ∃ v, B v = 0 ∧ Q v = b)
    (hker : ∀ x, B x = 0 → Q x = 0 → ∃ z, incidence left right z = x)
    (cost : (E → ℤ) →+ ℝ) (F : H → ℝ)
    (hattain : ∀ h, ∃ y, Midpoint.Feasible B y ∧ Q y = h ∧ cost y = F h)
    (hlower : ∀ h y, Midpoint.Feasible B y → Q y = h → F h ≤ cost y)
    (h₀ z d : H) :
    2 * F (h₀ + 2 • z) ≤
      F (h₀ + 2 • (z - d)) + F (h₀ + 2 • (z + d)) := by
  apply Midpoint.midpoint_from_conformal_splitting B Q cost F hattain hlower
  exact split_class left right B Q hBA hQA hrep hker

/-- Unsigned incidence as a homomorphism into the cycle subgroup. -/
def cycleIncidence {V E K : Type*} [AddCommGroup K]
    (left right : E → V) (B : (E → ℤ) →+ K)
    (hBA : ∀ z, B (incidence left right z) = 0) :
    (V → ℤ) →+ B.ker where
  toFun z := ⟨incidence left right z, hBA z⟩
  map_zero' := Subtype.ext (map_zero (incidence left right))
  map_add' u v := Subtype.ext (map_add (incidence left right) u v)

/-- Exact conformal splitting expressed directly in the cycle subgroup.
This version requires no extension of the quotient map to ambient vectors. -/
theorem split_cycle_class {V E K H : Type*}
    [AddCommGroup K] [AddCommGroup H]
    (left right : E → V) (B : (E → ℤ) →+ K)
    (hBA : ∀ z, B (incidence left right z) = 0)
    (Q : B.ker →+ H)
    (hQA : ∀ z, Q (cycleIncidence left right B hBA z) = 0)
    (hrep : Function.Surjective Q)
    (hker : ∀ x, Q x = 0 → ∃ z, cycleIncidence left right B hBA z = x)
    (x : B.ker) (b : H) (hQx : Q x = 4 • b) :
    ∃ a : B.ker, Q a = 2 • b ∧ Midpoint.Conformal a.val x.val := by
  obtain ⟨v, hQv⟩ := hrep b
  have hQdiff : Q (x - 4 • v) = 0 := by
    rw [map_sub, map_nsmul, hQx, hQv, sub_self]
  obtain ⟨z, hz⟩ := hker (x - 4 • v) hQdiff
  let a : B.ker := 2 • v + cycleIncidence left right B hBA (fun t => halfRound (z t))
  refine ⟨a, ?_, ?_⟩
  · dsimp [a]
    rw [map_add, map_nsmul, hQA, add_zero, hQv]
  · have hx : 4 • v + cycleIncidence left right B hBA z = x := by rw [hz]; abel
    have hxval : 4 • v.val + incidence left right z = x.val :=
      congrArg Subtype.val hx
    have hc := conformal_rounding left right v.val z
    rw [hxval] at hc
    exact hc

end MWIS.IncidenceSplit

end
