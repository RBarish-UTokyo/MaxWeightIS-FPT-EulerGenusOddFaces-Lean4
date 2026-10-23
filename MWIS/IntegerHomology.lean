module

public import MWIS.SignedIncidence
public import MWIS.Splitting

/-!
# Integer presentations and relative homology

These algebraic lemmas transfer the signed-incidence torsion theorem through
exact presentations. They also isolate the relative-chain argument that gives
the cokernel input to exact splitting.
-/

@[expose] public section

namespace MWIS.IntegerHomology

/-- Every finite-order element of the additive group is killed by two. -/
def TorsionExponentTwo (H : Type*) [AddCommGroup H] : Prop :=
  ∀ (h : H) (n : ℕ), 0 < n → n • h = 0 → 2 • h = 0

/-- Torsion exponent two passes to subgroups, expressed by an injective map. -/
theorem torsionExponentTwo_of_injective {G H : Type*} [AddCommGroup G]
    [AddCommGroup H] (f : G →+ H) (hf : Function.Injective f)
    (hH : TorsionExponentTwo H) : TorsionExponentTwo G := by
  intro g n hn hg
  apply hf
  rw [map_nsmul, map_zero]
  apply hH (f g) n hn
  rw [← map_nsmul, hg, map_zero]

/-- A presented group inherits the torsion bound of its relation map. -/
theorem torsionExponentTwo_of_presentation {X Y H : Type*}
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup H]
    (A : X →+ Y) (p : Y →+ H) (hp : Function.Surjective p)
    (hexact : ∀ y, p y = 0 ↔ ∃ x, A x = y)
    (hA : ∀ y n, 0 < n → (∃ x, A x = n • y) → ∃ x, A x = 2 • y) :
    TorsionExponentTwo H := by
  intro h n hn hnh
  obtain ⟨y, rfl⟩ := hp h
  have hny : p (n • y) = 0 := by simpa using hnh
  obtain ⟨x, hx⟩ := hA y n hn ((hexact _).mp hny)
  rw [← map_nsmul]
  exact (hexact _).mpr ⟨x, hx⟩

/-- The cokernel group of a two-port signed incidence matrix has no torsion
other than elements killed by two, for any exact presentation of that group. -/
theorem signed_incidence_presentation {E V H : Type*} [AddCommGroup H]
    (A : SignedIncidence.Matrix E V) (p : (E → ℤ) →+ H)
    (hp : Function.Surjective p)
    (hexact : ∀ y, p y = 0 ↔ ∃ x, A.map x = y) :
    TorsionExponentTwo H :=
  torsionExponentTwo_of_presentation A.map p hp hexact (SignedIncidence.two_torsion_cokernel A)

/-- In a connected unsigned incidence presentation, every torsion class is
zero or the class represented by the all-one edge vector. -/
theorem unsigned_torsion_classification {E V H : Type*} [AddCommGroup H]
    (A : SignedIncidence.Matrix E V) (hA : A.Connected) (hs : A.Unsigned)
    (root : V) (p : (E → ℤ) →+ H) (hp : Function.Surjective p)
    (hexact : ∀ y, p y = 0 ↔ ∃ x, A.map x = y)
    (h : H) (n : ℕ) (hn : 0 < n) (hnh : n • h = 0) :
    h = 0 ∨ h = p (fun _ => 1) := by
  obtain ⟨y, rfl⟩ := hp h
  have hny : p (n • y) = 0 := by simpa using hnh
  rcases SignedIncidence.torsion_incidence_or_shift A hA hs root y n hn
    ((hexact _).mp hny) with h | h
  · exact Or.inl ((hexact _).mpr h)
  · right
    have hh := (hexact _).mpr h
    rw [map_sub, sub_eq_zero] at hh
    exact hh

/-- The distinguished all-one class in a nonbipartite unsigned incidence
presentation is nonzero and has order two. -/
theorem unsigned_distinguished_class_order_two {E V H : Type*} [AddCommGroup H]
    (A : SignedIncidence.Matrix E V) (hs : A.Unsigned) (hn : ¬ A.Bipartite)
    (p : (E → ℤ) →+ H) (hexact : ∀ y, p y = 0 ↔ ∃ x, A.map x = y) :
    p (fun _ => 1) ≠ 0 ∧ 2 • p (fun _ => 1) = 0 := by
  constructor
  · intro h
    exact SignedIncidence.one_not_in_range A hs hn ((hexact _).mp h)
  · rw [← map_nsmul]
    apply (hexact _).mpr
    refine ⟨fun _ => 1, ?_⟩
    ext e
    simp [SignedIncidence.unsigned_apply A hs]

/-- The cokernel of the map from supported cycles to absolute homology has
exponent-two torsion if the relative relation map does. Here `Z` denotes
absolute cycles, `X` absolute two-chains, `R` relative one-chains, and `C`
cycles supported in the distinguished subspace. The hypotheses are exactness
at cycles and at the projection to relative chains. -/
theorem relative_cokernel_two_torsion
    {X Z R C H : Type*} [AddCommGroup X] [AddCommGroup Z]
    [AddCommGroup R] [AddCommGroup C] [AddCommGroup H]
    (boundary : X →+ Z) (project : Z →+ R) (inclusion : C →+ Z)
    (classOf : Z →+ H) (hclass : Function.Surjective classOf)
    (hboundary : ∀ z, classOf z = 0 ↔ ∃ x, boundary x = z)
    (hproject : ∀ z, project z = 0 ↔ ∃ c, inclusion c = z)
    (hrelative : ∀ r n, 0 < n →
      (∃ x, project (boundary x) = n • r) →
      ∃ x, project (boundary x) = 2 • r) :
    ∀ h n, 0 < n → (∃ c, classOf (inclusion c) = n • h) →
      ∃ c, classOf (inclusion c) = 2 • h := by
  intro h n hn hmultiple
  obtain ⟨z, rfl⟩ := hclass h
  obtain ⟨c, hc⟩ := hmultiple
  have hrel : classOf (n • z - inclusion c) = 0 := by
    rw [map_sub, map_nsmul, hc, sub_self]
  obtain ⟨x, hx⟩ := (hboundary _).mp hrel
  have hpi : project (inclusion c) = 0 := (hproject _).mpr ⟨c, rfl⟩
  have hpx : project (boundary x) = n • project z := by
    rw [hx, map_sub, map_nsmul, hpi, sub_zero]
  obtain ⟨t, ht⟩ := hrelative (project z) n hn ⟨x, hpx⟩
  have hz : project (2 • z - boundary t) = 0 := by
    rw [map_sub, map_nsmul, ht, sub_self]
  obtain ⟨d, hd⟩ := (hproject _).mp hz
  refine ⟨d, ?_⟩
  rw [hd, map_sub, map_nsmul,
    (hboundary _).mpr ⟨t, rfl⟩, sub_zero]

end MWIS.IntegerHomology

end
