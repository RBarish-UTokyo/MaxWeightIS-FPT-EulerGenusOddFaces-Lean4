module

public import MWIS.AlgorithmNetworkEncoding
public import MWIS.GroupSize
public import MWIS.ResidueJensen
public import Mathlib.Data.FinEnum.Option

/-!
# Computable finite enumeration of the hub network

Every row and column is numbered using exhaustive finite lists. The numbering
is executable, including the residue group and the allowed signed-cover arcs.
Prepared 2026-10-23.
-/

@[expose] public section

namespace MWIS.AlgorithmNetworkEnumeration

instance boolEnumeration : FinEnum Bool :=
  FinEnum.ofList [false, true] (by intro b; cases b <;> simp)

instance zmodEnumeration (n : ℕ) [NeZero n] : FinEnum (ZMod n) :=
  FinEnum.ofEquiv (Fin n) (ZMod.finEquiv n).toEquiv.symm

variable {f m : ℕ} (C : Fin m → Walks.Column (Fin f)) (r : ℕ)

/-- The actual computable enumeration of the finite residue group. -/
@[instance_reducible] def residueEnumeration : FinEnum (ResidueJensen.Residue r) := inferInstance

/-- The actual computable enumeration of all network arcs. -/
@[instance_reducible] def arcEnumeration : FinEnum (FiniteExtension.ExtensionArc C (ResidueJensen.Residue r)) :=
  inferInstance

/-- The actual computable enumeration of all inequality rows. -/
@[instance_reducible] def rowEnumeration : FinEnum
    (AlgorithmNetworkEncoding.InequalityRow C (G := ResidueJensen.Residue r) r) :=
  inferInstance

/-- Number of columns produced by the exhaustive enumeration. -/
def columnCount : ℕ := (arcEnumeration C r).card

/-- Number of rows produced by the exhaustive enumeration. -/
def rowCount : ℕ := (rowEnumeration C r).card

/-- Executable column numbering, with an executable inverse. -/
def columns : FiniteExtension.ExtensionArc C (ResidueJensen.Residue r) ≃
    Fin (columnCount C r) := (arcEnumeration C r).equiv

/-- Executable row numbering, with an executable inverse. -/
def rows : AlgorithmNetworkEncoding.InequalityRow C (G := ResidueJensen.Residue r) r ≃
    Fin (rowCount C r) := (rowEnumeration C r).equiv

/-- Enumeration does not change the cardinality of the residue group. -/
theorem residue_card : (residueEnumeration r).card = GroupSize.residueCount r := by
  change FinEnum.card (ResidueJensen.Residue r) = _
  rw [FinEnum.card_eq_fintypeCard]
  exact GroupSize.residue_group_card r

/-- The executable column count is the usual mathematical cardinality. -/
theorem columnCount_eq : columnCount C r =
    Fintype.card (FiniteExtension.ExtensionArc C (ResidueJensen.Residue r)) := by
  exact FinEnum.card_eq_fintypeCard

/-- The executable row count is the usual mathematical cardinality. -/
theorem rowCount_eq : rowCount C r =
    Fintype.card (AlgorithmNetworkEncoding.InequalityRow C
      (G := ResidueJensen.Residue r) r) := by
  exact FinEnum.card_eq_fintypeCard

/-- A dense program built only from finite input tables and executable numbering. -/
def dense (T : AlgorithmNetworkEncoding.CoefficientTables (Fin m)
    (ResidueJensen.Residue r) r) (η : ResidueJensen.Residue r) :
    AlgorithmNetworkEncoding.DenseProgram (rowCount C r) (columnCount C r) :=
  AlgorithmNetworkEncoding.toDenseTables C T η (rows C r) (columns C r)

end MWIS.AlgorithmNetworkEnumeration
