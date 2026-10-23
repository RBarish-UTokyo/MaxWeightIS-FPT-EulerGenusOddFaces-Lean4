module

public import MWIS.Statement

/-!
# The fixed-parameter main claim

This module adds the fixed-parameter statement to the machine, cost, surface,
drawing, encoding and output definitions of `MWIS.Statement`.

The weights are arbitrary integers. They are written into the input heap by the
same encoding `Spec.encode` as rationals with denominator one. With
`p = γ + k`, `N = |V| + |E| + 1` and `M = max(1, max_v |w_v|)`, the bound has the
form `2 ^ (c · (p · ⌈log₂(p + 1)⌉ + 1)) · (N · ⌈log₂(M + 1)⌉) ^ c` for one absolute
constant `c`. Here `Nat.size x = ⌈log₂(x + 1)⌉` is the binary length of `x`.
This is `2^{O(p log(p+1))} · poly(N, log(M+1))` with an absolute polynomial
exponent. The binary length of the encoded input lies between `N` and a fixed
polynomial in `N` and `log(M+1)`, so the bound in `N` is the stronger form.
-/

@[expose] public section

namespace MWIS.Spec

open MWIS.PointerMemory MWIS.RegisterMachine

/-- Integer weights, viewed as rationals for the input encoding and for the
weight of a vertex set. -/
def intWeights {n : ℕ} (w : Fin n → ℤ) : Fin n → ℚ := fun v => (w v : ℚ)

/-- The weight magnitude `M = max(1, max_v |w_v|)`. -/
def weightBound {n : ℕ} (w : Fin n → ℤ) : ℕ :=
  max 1 (Finset.univ.sup fun v => (w v).natAbs)

/-- The running-time bound `2 ^ (c · (p · size p + 1)) · (N · size M) ^ c`, where
`size x = ⌈log₂(x + 1)⌉` is the binary length. -/
def fptBound (c p N M : ℕ) : ℕ :=
  2 ^ (c * (p * Nat.size p + 1)) * (N * Nat.size M) ^ c

/-- **Fixed-parameter main claim.** One fixed finite program and one absolute
constant `c` such that, for every closed-surface map `A`, every drawing `D` in `A`
and all integer vertex weights `w`, the program runs on the encoded input, every
run returns a maximum-weight independent set, and every run costs at most
`fptBound c (γ + k) N M` bit operations. Here `γ` is the Euler genus of `A`, `k`
is the number of complementary regions of `D` whose total boundary length is odd,
`N = |V| + |E| + 1` and `M = max(1, max_v |w_v|)`. -/
def FPTClaim : Prop :=
  ∃ (P : ℕ) (code : Code P) (entry : Fin P) (c : ℕ),
    ∀ (A : Map), A.IsClosedSurface → ∀ (D : Drawing) (W : D.In A) (w : Fin D.vertices → ℤ),
      (∃ r t, Runs code entry D (intWeights w) r t) ∧
      ∀ r t, Runs code entry D (intWeights w) r t →
        (∃ I, Outputs D r I ∧ D.IsMaximum (intWeights w) I) ∧
        stackBitCost t.compile ≤
          fptBound c (A.eulerGenus + A.oddRegionCount W.drawn) D.size (weightBound w)

end MWIS.Spec

end
