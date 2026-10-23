# Source and reuse record

Prepared 2026-10-23.

## Mathematical source

The formalized result is a fixed-parameter theorem of the forthcoming paper
*Maximum-weight independent set in embedded graphs parameterized by Euler genus
and number of odd faces*. The manuscript is forthcoming and is not included in
this repository.

The coarse Jensen argument follows the method of Lemmas 3–4 of *4-Block Integer
Programming is in FPT* (arXiv:2609.26746v1). The finite-group network is the
one described in the paper and compared there with Theorem 2 of *Small
Extended Formulations for Group-Constrained Flows and Cographic Integer Hulls*;
its projection and integrality are proved in this project.

## The registered XP formalization

432 of the 467 modules of
[PALOMAR-2026-10-22-000006, version 1](https://palomar-registry.org/entry?id=PALOMAR-2026-10-22-000006&version=1),
immutable source commit `00f581e7401feedce30699ae94763d4afbfb2f6f`, are included in
`MWIS/` verbatim except that the namespace and directory `WeightedMIS` are
renamed to `MWIS`. A byte comparison after the renaming is recorded in
`verification/`. The remaining 35 XP modules (the XP program table, the
XP main theorem and helpers used only by them) are not needed and are omitted;
`source-reuse.json` lists both sets. They provide the machine, the cost, the surface model and the
input encoding of the statement, and the whole program except the hard-component
solver.

Modules written for this project that adapt XP code: `Generic*` (generic copies
of XP's component, assembly and top-level chain with the hard solver as a
parameter), `FPTRegister*` and `FPTTrees` (they call XP procedures), and
`scripts/gen_fpt_program.py` (adapted from XP's `scripts/gen_program_table.py`).
The XP theorem itself is not used for the fixed-parameter bound.

## Other reused sources

The rounded LP feasibility development adapts accepted proofs from
[Formalpedia](https://github.com/prove2me/formalpedia), commit
`07bfe4bbb3858db507bb6ac0d725951c228119fc`. Exact source paths and adaptation
notes appear in `third_party/formalpedia/provenance.json`; its Apache-2.0
licence is retained there.

## Licence and authored content

This project and the reused sources use Apache-2.0; the root `LICENSE` holds the
licence text. Historical registry identifiers, immutable commit hashes,
dependency revisions and licence wording keep their true values.
