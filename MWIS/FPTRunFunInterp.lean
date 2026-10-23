module

public import MWIS.FPTRunFun
public import MWIS.Fun.Interp

/-!
# The interpreter contract from the `Fun` interpreter

The wrappers of `MWIS.FPTRunFun` assume the contract `FPTRunFun.EvalSpec`.
It follows from the per-expression contract `Fun.Interp.EvalSpec` of the
interpreter procedures, with the interpreter constant `Fun.Interp.K`.
-/

@[expose] public section

namespace MWIS.FPTRunFun

open MWIS.PointerMemory MWIS.RegisterMachine MWIS.Fun

variable {p : ℕ}

/-- If the interpreter meets its contract on every expression, its entry procedure
meets the wrapper contract with constant `Interp.K`. -/
theorem evalSpec_of_interp {code : Code p} {d : Interp.Procedures p}
    (hd : ∀ {Γ : List Ty} {τ : Ty} (e : Expr Γ τ), Interp.EvalSpec code d e) :
    EvalSpec code d.eval Interp.K := by
  intro Γ τ e env h hh ep envp hep henv
  obtain ⟨out, outs, ⟨hx, hv, q, rfl, hq⟩, hw⟩ := hd e env hh hep henv
  exact ⟨out, q, hx, hv, hq, hw⟩

end MWIS.FPTRunFun

end
