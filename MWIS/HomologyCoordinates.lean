module

public import MWIS.CycleQuotient
public import MWIS.HomologyStructure

/-!
# Coordinates for the integral incidence quotient

The actual quotient of integral cycles by unsigned incidence has one parity
coordinate and a finite free part. The all-one class is exactly its nonzero
parity element.
-/

@[expose] public section

namespace MWIS.HomologyCoordinates

variable {V E K : Type*} [AddCommGroup K]

/-- The signed-port presentation of ordinary unsigned incidence. -/
def incidenceMatrix (left right : E → V) : SignedIncidence.Matrix E V :=
  ⟨left, right, fun _ => true, fun _ => true⟩

@[simp] theorem incidenceMatrix_unsigned (left right : E → V) :
    (incidenceMatrix left right).Unsigned := ⟨fun _ => rfl, fun _ => rfl⟩

@[simp] theorem incidenceMatrix_map (left right : E → V) :
    (incidenceMatrix left right).map = IncidenceSplit.incidence left right := by
  ext x e
  rfl

/-- Every torsion class of the actual cycle quotient is zero or its
characteristic all-one class. -/
theorem torsion_classification (left right : E → V) (B : (E → ℤ) →+ K)
    (hBA : ∀ z, B (IncidenceSplit.incidence left right z) = 0)
    (hB1 : B (fun _ => 1) = 0) (root : V)
    (hconnected : (incidenceMatrix left right).Connected)
    (h : CycleQuotient.Homology left right B hBA) (n : ℕ)
    (hn : 0 < n) (hnh : n • h = 0) :
    h = 0 ∨ h = CycleQuotient.characteristicClass left right B hBA hB1 := by
  obtain ⟨y, rfl⟩ := CycleQuotient.classMap_surjective left right B hBA h
  have hny : CycleQuotient.classMap left right B hBA (n • y) = 0 := by
    simpa using hnh
  obtain ⟨x, hx⟩ := (CycleQuotient.classMap_eq_zero_iff left right B hBA _).mp hny
  have hx' : (incidenceMatrix left right).map x = n • (y : E → ℤ) := by
    simpa [incidenceMatrix_map] using hx
  rcases SignedIncidence.torsion_incidence_or_shift (incidenceMatrix left right)
    hconnected (incidenceMatrix_unsigned left right) root y n hn ⟨x, hx'⟩ with hz | hz
  · left
    apply (CycleQuotient.classMap_eq_zero_iff left right B hBA y).mpr
    simpa only [incidenceMatrix_map] using hz
  · right
    apply (CycleQuotient.classMap_eq_iff left right B hBA y ⟨fun _ => 1, hB1⟩).mpr
    simpa only [incidenceMatrix_map] using hz

/-- Nonbipartiteness makes the characteristic class nonzero in the actual
cycle quotient. -/
theorem characteristicClass_ne_zero (left right : E → V) (B : (E → ℤ) →+ K)
    (hBA : ∀ z, B (IncidenceSplit.incidence left right z) = 0)
    (hB1 : B (fun _ => 1) = 0) (hn : ¬ (incidenceMatrix left right).Bipartite) :
    CycleQuotient.characteristicClass left right B hBA hB1 ≠ 0 := by
  intro hzero
  apply SignedIncidence.one_not_in_range (incidenceMatrix left right)
    (incidenceMatrix_unsigned left right) hn
  obtain ⟨x, hx⟩ := (CycleQuotient.classMap_eq_zero_iff left right B hBA
    ⟨fun _ => 1, hB1⟩).mp hzero
  exact ⟨x, by simpa only [incidenceMatrix_map] using hx⟩

/-- The actual integral cycle quotient is finitely generated because its
cycles form a submodule of the finite-rank free edge module. -/
theorem finite_homology [Fintype E] (left right : E → V) (B : (E → ℤ) →+ K)
    (hBA : ∀ z, B (IncidenceSplit.incidence left right z) = 0) :
    Module.Finite ℤ (CycleQuotient.Homology left right B hBA) := by
  have : Module.Finite ℤ B.ker := by
    change Module.Finite ℤ B.toIntLinearMap.ker
    infer_instance
  exact Module.Finite.of_surjective
    (CycleQuotient.classMap left right B hBA).toIntLinearMap
    (CycleQuotient.classMap_surjective left right B hBA)

/-- Integral homology coordinates for a connected nonbipartite graph and an
integer cycle equation annihilating its unsigned incidence. The parity
coordinate of the characteristic all-one class is exactly one. -/
theorem exists_coordinates [Fintype E]
    (left right : E → V) (B : (E → ℤ) →+ K)
    (hBA : ∀ z, B (IncidenceSplit.incidence left right z) = 0)
    (hB1 : B (fun _ => 1) = 0) (root : V)
    (hconnected : (incidenceMatrix left right).Connected)
    (hn : ¬ (incidenceMatrix left right).Bipartite) :
    ∃ (r : ℕ) (e : CycleQuotient.Homology left right B hBA ≃+
      (Fin r → ℤ) × ZMod 2),
      e (CycleQuotient.characteristicClass left right B hBA hB1) = (0, 1) := by
  have := finite_homology left right B hBA
  apply HomologyStructure.exists_free_prod_two_with_class
    (CycleQuotient.characteristicClass left right B hBA hB1)
    (characteristicClass_ne_zero left right B hBA hB1 hn)
    (by simpa only [two_smul] using
      CycleQuotient.twice_characteristicClass left right B hBA hB1)
  exact torsion_classification left right B hBA hB1 root hconnected

end MWIS.HomologyCoordinates

end
