module

public import MWIS.FunCoordinatesCostTables
public import MWIS.FunNetworkEncode

/-!
# Coordinate data in the network input format

`netCoordFn` returns the free rank and, for every edge `e`, the free coordinates of `1_e`
and the network residue code `FunNetwork.residueCode` of its residue label: exactly the
coordinate parts of `FunNetwork.edgeInput`. Its input lists are in the parser format:
endpoint pairs `(left e, right e)` and network column codes, in edge order.
-/

@[expose] public section

namespace MWIS.FunCoordinates

open MWIS.Fun MWIS.FunLP MWIS.TreeCotree

/-- The output of `netCoordFn`: the rank and, per edge, free coordinates and residue code. -/
abbrev NetCoordOut : Ty := .prod .int (.list (.prod (.list .int) (.list .int)))

/-- `(_, row) ↦ (free, parity :: residue)`. -/
def rowOutFn : Fn (.prod .unit RowTy) (.prod (.list .int) (.list .int)) :=
  .pair (.fst (.snd v0)) (.cons (.fst (.snd (.snd (.snd v0)))) (.snd (.snd (.snd (.snd v0)))))

/-- The coordinate data in the network input format. -/
def netCoordFn : Fn CoordArg NetCoordOut :=
  .letE (call coordFn v0) (.pair (.fst v0) (call (cmapFn rowOutFn) (.pair .unit (.snd v0))))

theorem netCoordFn_apply (x : CoordArg.denote) :
    netCoordFn.apply x = ((coordFn.apply x).1,
      (coordFn.apply x).2.map fun row => (row.1, row.2.2.1 :: row.2.2.2)) := by
  rw [Fn.apply]
  simp only [netCoordFn, Expr.denote, Var.get, denote_call, cmapFn_apply']
  rfl

variable {f m n : ℕ} (left right : Fin m → Fin n) (C : Fin m → Walks.Column (Fin f))
  (root : Fin n)

theorem edgeList_eq_map :
    edgeList left right = (List.finRange m).map fun e => (((left e : ℕ) : ℤ), ((right e : ℕ) : ℤ)) := by
  rw [edgeList, List.ofFn_eq_map]

theorem colList_eq_map :
    colList C = (List.finRange m).map fun e => FunNetwork.columnCode (C e) := by
  rw [colList, List.ofFn_eq_map]
  congr 1

/-- **The network coordinate program computes the rank, the free coordinates and the residue
codes of the unit edge vectors.** -/
theorem netCoordFn_coordinates :
    netCoordFn.apply ((List.finRange m).map (fun e => (((left e : ℕ) : ℤ), ((right e : ℕ) : ℤ))),
      ((List.finRange m).map (fun e => FunNetwork.columnCode (C e)),
        ((n : ℤ), ((f : ℤ), ((root : ℕ) : ℤ))))) =
      ((rank left right C root : ℤ), List.ofFn fun e =>
        (List.ofFn fun i => freeMap left right C root (Pi.single e 1) i,
          FunNetwork.residueCode (residueLabel left right C root (Pi.single e 1)))) := by
  rw [← edgeList_eq_map, ← colList_eq_map, netCoordFn_apply, coordFn_tables, List.map_ofFn]
  rfl

theorem netCoordFn_costN {N : ℕ} (hN5 : 5 ≤ N) (hm : m ≤ N) (hn : n ≤ N) (hf : f ≤ N) :
    netCoordFn.costAt ((List.finRange m).map (fun e => (((left e : ℕ) : ℤ), ((right e : ℕ) : ℤ))),
      ((List.finRange m).map (fun e => FunNetwork.columnCode (C e)),
        ((n : ℤ), ((f : ℤ), ((root : ℕ) : ℤ))))) ≤ 17100 * N ^ 5 := by
  have hN : 1 ≤ N := by omega
  rw [← edgeList_eq_map, ← colList_eq_map]
  have hc := coordFn_costN left right C root hN5 hm hn hf
  have hrows : ((coordFn.apply (edgeList left right, (colList C, ((n : ℤ), ((f : ℤ),
      ((root : ℕ) : ℤ)))))).2).length ≤ N := by
    rw [coordFn_tables]; simpa using hm
  have hmap := cmapFn_costN rowOutFn () _ (K := 20) (d := 1) hN le_rfl hrows (fun _ _ => by
    rw [Fn.costAt]; simp only [rowOutFn, Expr.cost, Var.index, pow_one]; omega)
  simp only [Nat.reduceAdd] at hmap
  have q1 := pow_mono hN (show 2 ≤ 5 by norm_num)
  have q2 := const_le_pow hN 20 5
  have q3 : 5 ^ 5 ≤ N ^ 5 := Nat.pow_le_pow_left hN5 5
  rw [Fn.costAt, netCoordFn]
  refine (cost_letE_le _ _ _ (fun r => r = coordFn.apply (edgeList left right, (colList C,
    ((n : ℤ), ((f : ℤ), ((root : ℕ) : ℤ)))))) (A := 17000 * N ^ 5 + 5) (B := 80 * N ^ 2 + 20)
    ?_ ?_ ?_).trans (by omega)
  · simp only [cost_call, Expr.cost, Var.index, Expr.denote, Var.get]
    omega
  · simp only [Expr.denote, Var.get, denote_call]
  intro r hr
  subst hr
  simp only [Expr.cost, cost_call, Var.index, Expr.denote, Var.get]
  omega

/-- **Cost of the network coordinate program**, as an explicit polynomial in the numbers of
edges, vertices and face rows. -/
theorem netCoordFn_cost :
    netCoordFn.costAt ((List.finRange m).map (fun e => (((left e : ℕ) : ℤ), ((right e : ℕ) : ℤ))),
      ((List.finRange m).map (fun e => FunNetwork.columnCode (C e)),
        ((n : ℤ), ((f : ℤ), ((root : ℕ) : ℤ))))) ≤ 17100 * (m + n + f + 5) ^ 5 :=
  netCoordFn_costN left right C root (by omega) (by omega) (by omega) (by omega)

end MWIS.FunCoordinates

end
