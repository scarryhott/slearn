# Closure Translation: Common Operation (NRRF652)

## Status

[`NRRF652ClosureTranslationCommonOperationKakeyaTokenResuperposition.lean`](../Slearn/NRRF652ClosureTranslationCommonOperationKakeyaTokenResuperposition.lean)
implements the supplied common-operation contract on top of the existing
translation episode, generated-map, and token-resuperposition layers.

The governing operation is:

\[
\boxed{
\mathrm{ClosureOp}=(Ch,Ka,\sim_{\mathcal C},\mathrm{Diff})
}
\qquad
\operatorname{round}=Ka\circ Ch,
\qquad
\Omega(\Gamma)=\mathrm{Diff}(\Gamma,Ka(Ch(\Gamma))).
\]

`ClosureOp` is generic in the plurality, contracted reading, and residue
coordinate. Its relation is a `Prop`; it is not silently replaced by literal
equality.

## Properties table

| Supplied idea | Lean carrier | Certified statement |
| --- | --- | --- |
| One common closure level | `ClosureOp` | Stores `contract`, `reopen`, `related`, and `diff`. |
| Reciprocal pass | `ClosureOp.round` | `reopen ∘ contract`. |
| Relation-relative return | `ClosureOp.Recovers` | `related Γ (round Γ)`. |
| Retained difference | `ClosureOp.residue` | `diff Γ (round Γ)`. |
| Contraction is not closure | `contraction_alone_not_closure` | One reopening function cannot literally return two distinct pluralities that contraction identified. |
| Closure is reciprocal ability | `ReciprocalClosure`, `relational_recovery`, `many_one_many` | Relational recovery for every plurality can coexist with a witnessed literal non-return. |
| Four runtime outcomes | `DifferenceReading`, `ReturnStructure`, `ClosureVerdict`, `verdictOf` | `CURRENT_CLOSURE`, `NEW_OPENING`, `OPEN`, and `COLLAPSE` are computed from residue reading plus structure. |
| Ball/hair counterexample | `ballHairOp` | A selected two-cell route has relational recovery, residue `2`, and no literal return. |
| Mirror warning | `mirrorParentOp` | A parent can have zero residue while contraction still identifies distinct routes and one route is not literally returned. |
| Finite Kakeya grain role | `KakeyaResolution` | Every positive readout can be non-injective, while equality at every grain determines the direction. |
| Aggregate plus route | `OrderedResuperposition` | An order-blind pair aggregate cannot determine route when a route residue distinguishes the orders. |
| Four-phase coordinate model | `ComplexCoordinate.iShift` | Four shifts return the visible coordinate; named coordinate sectors meet only at zero. |
| Per-dimension turn | `metavec_shiftDim` | A selected dimension changes, other dimensions remain fixed, and four turns restore the net. |
| Slearn runtime law | `SlearnClosureRuntime` | `zoomOut = Ch`, `zoomIn = Ka`, and `executeZoom = round`. |

## Verdicts: why three residue readings yield four states

`DifferenceReading` has three cases:

```text
vanishing | retained | unresolved
```

`verdictOf` deliberately uses the separate structural readout:

| Residue reading | Return structure | Runtime verdict |
| --- | --- | --- |
| vanishing | supported | `CURRENT_CLOSURE` |
| vanishing | degenerate | `COLLAPSE` |
| retained | either | `NEW_OPENING` |
| unresolved | either | `OPEN` |

Therefore a zero or vanishing readout is never promoted to absolute
completion. It means closure only at the selected level and only when the
return has the required support.

## Slearn runtime implication

For a perspective path \(\Gamma\), an admitted Slearn recentering is:

\[
\text{perspective/WHY/lesson path}
\xrightarrow{Ch}
\text{goal or contracted reading}
\xrightarrow{Ka}
\text{reopened path}
\xrightarrow{\mathrm{Diff}}
\Omega.
\]

The displayed map remains governed by the witnessed-kernel admission rules:
three WHY witnesses admit a lesson, an attempt admits a project, and a return
receipt changes prospective to returned. This module adds the rule that zoom,
goal reduction, perspective expansion, and resuperposition must be projections
of the same `Ch → Ka → Ω` operation, not independent UI mechanics.

## Scope boundary

The `Nat` examples are finite readouts of explicitly stated witnesses. They do
not identify \(\Omega\) with a Chaitin halting probability, a measure of
learning, or a physical quantity. The "Kakeya" layer is a theorem about the
given finite-resolution interface, not about a set containing a unit segment in
every direction. The `ComplexCoordinate` model is an integer pair with the
algebraic quarter-turn `(a,b) ↦ (-b,a)`; its light/dark terminology is only a
name for two coordinate subspaces and carries no cosmological, gravitational,
or matter claim.

The module does not prove a complete universal equivalence between every
Slearn presentation, prove empirical return independence, or derive the map
from no educational assumptions. Those remain explicit runtime and research
obligations.
