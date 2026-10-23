module

public import MWIS.ResidueJensen

/-!
# The characteristic residue

The residue of the characteristic class in the finite quotient group: parity
`1` and free coordinates `0`. It is the target of the finite-group network.
-/

@[expose] public section
namespace MWIS.AlgorithmComputedNetwork

open ResidueJensen

/-- The fixed characteristic residue. -/
def target (r : ℕ) : Residue r := (1, 0)

end MWIS.AlgorithmComputedNetwork
end
