# NRRF778 — Translational truth equality of the continuum halting substrate operation and its closure relative form selection

Module: `NRRF778ContinuumHaltingSubstrateOperationClosureRelativeFormSelectionTranslationalTruthEquality.lean`
(namespace `NRRF778`, added as a library in `lakefile.toml`).  Builds cleanly, no `sorry`, every
headline theorem audits to only `propext`, `Classical.choice`, `Quot.sound`.

## The two things being equated

* **Continuum halting substrate operation.**  The loop sensor of NRRF776 iterates the relative ball
  self limit `ballInv` on the continuum `ℂ` and stops on the closure form.  Its truth reading at a
  datum is `subHalt z := Halts sensorStep z`.
* **Closure relative form selection.**  The natural form selector of NRRF775 applied to the
  *closure relative relation* `closureRel z`, which at every site admits exactly one symbol — the
  closure form on `z`'s own ray.  The relation is rigid, so the selector applies and returns
  `dir z` at every site (`closureSel_eq_dir`).  Its truth reading is
  `Selected z := closureSel z 0 = z`.

## What is proved

* `halting_iff_selected` — pointwise, on nonzero data: the operation halts iff the selection returns
  the datum itself.
* `haltRead_eq_selRead` — the **translational truth equality** in its strongest form: as readings on
  the substrate `NZ` of nonzero data the two are *literally the same function*, not merely
  equivalent; `transEq_halt_sel` records this as `NRRF772.TransEq`, i.e. each is a translation of
  the other.
* `halt_state_eq_selection` — where the operation halts, the state it halts at is exactly the
  selected form; `continues_iff_not_selected` is the complementary trace.
* `run_even` / `run_odd` — away from the closure form the substrate operation is a genuine two-cycle,
  so continuation is not an escape.
* `closureSel_mem_closureForm`, `subHalt_closureSel`, `radEq_closureSel_eq_zero` — the selection
  always lands on the closure form, where the operation halts immediately; `closureSel_idem`.
* `zero_separates` — at the degenerate datum `0` the two readings come apart (selection succeeds,
  the operation never halts).  So the nonzero hypothesis is load-bearing and the equality is a
  statement about the substrate, not a tautology.
* `subHalt_subOp`, `selected_subOp` — both readings are invariant under the substrate operator group
  of NRRF776; `radEq_refines_haltRead` / `haltRead_not_refines_radEq` — the unified equality function
  translates into the common truth reading, strictly one-way.
* `closureRel_subOpTransport`, `radEq_closureSel_subOp_invariant` — INTEGRATE with the live selector
  of NRRF777: transporting the closure relative relation by a substrate operator transports its
  selection by the same operator and leaves the unified equality function of the selection untouched.

`nrrf778_answer` collects the clauses in one statement.
