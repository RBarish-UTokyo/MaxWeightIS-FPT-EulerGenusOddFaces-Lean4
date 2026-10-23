module

public import MWIS.Fun.InterpBinders
public import MWIS.RegisterMachineBounds

/-!
# The `Fun` interpreter: correctness and event bound

Every typed expression meets the evaluation contract `Interp.EvalSpec`: from a
valid heap holding the encoded expression and the stored environment, the eval
procedure returns a stored copy of the value within `K * e.cost env` events.
-/

@[expose] public section

namespace MWIS.Fun.Interp

open MWIS.PointerMemory MWIS.RegisterMachine MWIS.Fun.Arith

variable {p : ℕ} {code : Code p} {d : Procedures p}

/-- The evaluation contract holds for every expression. -/
theorem evalSpec (hm : d.Matches code) :
    ∀ {Γ : List Ty} {τ : Ty} (e : Expr Γ τ), EvalSpec code d e := by
  intro Γ τ e
  induction e with
  | var v => exact spec_var hm v
  | int z => exact spec_int hm z
  | bool b => exact spec_bool hm b
  | unit => exact spec_unit hm
  | arith op x y hx hy => exact spec_arith hm op hx hy
  | cmp op x y hx hy => exact spec_cmp hm op hx hy
  | ite c t e hc ht he => exact spec_ite hm hc ht he
  | pair x y hx hy => exact spec_pair hm hx hy
  | fst x hx => exact spec_fst hm hx
  | snd x hx => exact spec_snd hm hx
  | nil => exact spec_nil hm
  | cons x xs hx hxs => exact spec_cons hm hx hxs
  | listCase xs n c hxs hn hc => exact spec_listCase hm hxs hn hc
  | foldl xs i s hxs hi hs => exact spec_foldl hm hxs hi hs
  | iter n i s hn hi hs => exact spec_iter hm hn hi hs
  | letE x b hx hb => exact spec_letE hm hx hb
  | treeCase t a b c f k q ht ha hb hc hf hk hq => exact spec_treeCase hm ht ha hb hc hf hk hq
  | treeNil => exact spec_treeNil hm
  | treeBit b t hb ht => exact spec_treeBit hm hb ht
  | treeCons x t hx ht => exact spec_treeCons hm hx ht
  | treePair x y hx hy => exact spec_treePair hm hx hy
  | items t ht => exact spec_items hm ht
  | ofItems ts ht => exact spec_ofItems hm ht
  | wordValue t ht => exact spec_wordValue hm ht
  | word w k hw hk => exact spec_word hm hw hk
  | size x hx => exact spec_size hm hx

/-- A standalone layout of the 31 interpreter procedures. -/
def standard : Procedures 31 where
  arith := {
    add := 0,
    sub := 1,
    cmp := 2,
    lenLe := 3,
    mul := 4,
    div := 5,
    halve := 6,
    size := 7,
    mkInt := 8,
    addSigned := 9,
    mulAny := 10,
    iadd := 11,
    isub := 12,
    imul := 13,
    idiv := 14,
    imod := 15,
    ilt := 16,
    ile := 17,
    ieq := 18,
    isize := 19 }
  eval := 20
  lookup := 21
  fold := 22
  iter := 23
  evalStep := 24
  items := 25
  rev := 26
  skip := 27
  wordStep := 28
  iterW := 29
  word := 30

/-- The standalone interpreter program. -/
def standardCode : Code 31 := fun i =>
  match i.val with
  | 0 => addBody (0 : Fin 31)
  | 1 => subBody (1 : Fin 31)
  | 2 => cmpBody (2 : Fin 31)
  | 3 => lenLeBody (3 : Fin 31)
  | 4 => mulBody (4 : Fin 31) (0 : Fin 31)
  | 5 => divBody (5 : Fin 31) (2 : Fin 31) (1 : Fin 31)
  | 6 => halveBody (6 : Fin 31)
  | 7 => sizeBody (7 : Fin 31) (6 : Fin 31)
  | 8 => mkIntBody
  | 9 => addSignedBody (0 : Fin 31) (2 : Fin 31) (1 : Fin 31) (8 : Fin 31)
  | 10 => mulAnyBody (3 : Fin 31) (4 : Fin 31)
  | 11 => iaddBody (9 : Fin 31)
  | 12 => isubBody (9 : Fin 31)
  | 13 => imulBody (10 : Fin 31) (8 : Fin 31)
  | 14 => idivBody (5 : Fin 31) (0 : Fin 31) (8 : Fin 31)
  | 15 => imodBody (5 : Fin 31) (1 : Fin 31) (8 : Fin 31)
  | 16 => iltBody (2 : Fin 31)
  | 17 => ileBody (2 : Fin 31)
  | 18 => ieqBody (2 : Fin 31)
  | 19 => isizeBody (7 : Fin 31)
  | 20 => evalBody standard
  | 21 => lookupBody (21 : Fin 31)
  | 22 => foldBody (22 : Fin 31) (20 : Fin 31)
  | 23 => iterBody (23 : Fin 31) (24 : Fin 31)
  | 24 => evalStepBody (20 : Fin 31)
  | 25 => itemsBody (25 : Fin 31)
  | 26 => revBody (26 : Fin 31)
  | 27 => skipBody (27 : Fin 31) (26 : Fin 31)
  | 28 => wordStepBody
  | 29 => iterBody (29 : Fin 31) (28 : Fin 31)
  | 30 => wordBody (29 : Fin 31)
  | _ => .fail

theorem standard_matches : standard.Matches standardCode :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The standalone program meets the evaluation contract for every expression. -/
theorem standard_evalSpec {Γ : List Ty} {τ : Ty} (e : Expr Γ τ) :
    EvalSpec standardCode standard e :=
  evalSpec standard_matches e

end MWIS.Fun.Interp

namespace MWIS.Fun.Interpreter

open MWIS.PointerMemory MWIS.RegisterMachine MWIS.Fun.Interp

variable {p : ℕ} {code : Code p} {d : Interp.Procedures p}

/-- The interpreter theorem: the eval procedure computes `e.denote env` as a
stored value on an extended valid heap, within `K * e.cost env` events. -/
theorem eval_compiled (hm : d.Matches code) {Γ : List Ty} {τ : Ty} (e : Expr Γ τ)
    (env : Env Γ) {h : Heap} (hh : Valid h) {ep envp : Ptr}
    (he : TreeAt h ep e.encode) (henv : EnvAt Γ h envp env) :
    ∃ out vp, Extends h out ∧ Valid out ∧ ValAt τ out vp (e.denote env) ∧
      Within code h (initialRegisters [.pointer ep, .pointer envp]) (code d.eval)
        [.pointer vp] out (K * e.cost env) := by
  obtain ⟨out, outs, ⟨hext, hv, q, rfl, ht⟩, hw⟩ := evalSpec hm e env hh he henv
  exact ⟨out, q, hext, hv, ht, hw⟩

/-- The initial registers of an interpreter call are bounded by the heap length,
as required by XP's final cost conversion (`FinalCost.stackBitCost_le_of_steps`). -/
theorem initialRegisters_bound {Γ : List Ty} {τ : Ty} {e : Expr Γ τ} {env : Env Γ} {h : Heap}
    {ep envp : Ptr} (he : TreeAt h ep e.encode) (henv : EnvAt Γ h envp env) :
    RegistersBound h.length (initialRegisters [.pointer ep, .pointer envp]) := by
  have h1 := he.allocated
  have h2 := TreeAt.allocated henv
  refine initialRegisters_bounded (lt_of_le_of_lt (Nat.zero_le _) h1) ?_
  intro v hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl
  · exact h1
  · exact h2

end MWIS.Fun.Interpreter

end
