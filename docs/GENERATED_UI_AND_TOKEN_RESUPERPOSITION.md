# Closure-generated Slearn field and token resuperposition

## Status and boundary

This refactor joins the browser surface to the closure vocabulary without
treating a designed diagram as a theorem.

1. [`NRRF651SlearnUIHairOfClosureGeneratedMap.lean`](../Slearn/NRRF651SlearnUIHairOfClosureGeneratedMap.lean)
   formalizes a relation-generated spatial field and bridge-required closure
   transitions.
2. [`ChaitinKakeyaTokenResuperposition.lean`](../Slearn/ChaitinKakeyaTokenResuperposition.lean)
   formalizes the separate directional-token and assumption-grain reading.

The reported `NRRF653LeanClosureFrozenAxiometryVersusTranslation.lean` source
was not present in the fetched repository refs while this change was made. Its
stated criterion is therefore used as an explicit local contract here — a new
level needs a relation-preserving bridge — rather than being represented as an
audited import of that unavailable module.

Neither module proves a physical light/matter model, a literal Kakeya set, a
Chaitin halting probability, a theorem about consciousness, or an empirical
learning outcome.

## 1. The Slearn UI is a projection of an interaction field

There is no canonical sequence of UI nodes in the formal model. In particular,
there is no predeclared

```text
core → brain → value → belief → WHY → goal → lesson → project → world
```

that gets merely gated by evidence. Instead the source is one interaction
field:

```text
source presentation
target presentation
translated trace
relative re-reading
preserved relation (bridge)
attempt
return receipt
successor presentation
relative position
```

The browser holds this same kind of record. It derives its points, lines, and
their force-field positions from the currently admitted records. It stores no
canonical graph or hand-positioned diagram.

The generated field has four possible visible roles:

| Role | What it means | Admission condition |
| --- | --- | --- |
| Presentation | A local reading of an interaction | The interaction is translated |
| Translation | The WHY relation that connects readings | The interaction is translated |
| Closure | The target reading where traces recombine | Expanded: translated; contracted: bridged |
| Successor | A perspective after a recorded return | Bridged, attempted, and receipted |

`SpatialClosure` is a predicate over these occurrences, not an object holding
screen coordinates. `SpatialOccurrence` retains the source trace for every
role. This is the checked boundary that prevents a rendered node from becoming
an unrelated UI object.

## 2. Zoom, topic selection, and definition changes

The central UI operation is not camera navigation. A selected relation can be
shown in three closure presentations:

```text
expanded   — source, WHY translation, and target are visible
contracted — only bridged target closures are visible and can recombine
returned   — a successful return adds a successor presentation
```

A topic click selects a trace; it does not select an independent page or tab.
Its relative re-reading and its preserved relation form the required `Bridge`:

\[
\operatorname{Bridge}(t)=
\operatorname{translated}(t)
\wedge\operatorname{redefined}(t)
\wedge\operatorname{preserved}(t).
\]

This affects every closure decision:

| User operation | Required closure data | Result without it |
| --- | --- | --- |
| Contract a topic to a shared direction | Relative re-reading + preserved bridge | `OPEN`; no contracted map is generated |
| Reopen a closure as local relations | The same bridge | `OPEN`; no re-reading transition |
| Change language/definition | Re-reading plus what remains preserved | A new unbridged relation, not a renamed view |
| Return to a next perspective | Bridge + attempt + return receipt + successor | `OPEN`; no successor presentation |

The machine-checked theorems `contracted_requires_bridge`,
`no_bridge_no_contracted_occurrence`, `successor_requires_return`,
`transition_to_contracted_requires_bridge`, and
`transition_to_returned_requires_return` state these admission boundaries.

The browser’s controls mirror only those transitions. A control is disabled
when its closure evidence is absent; it is not replaced with an inert visual
mode. This distinguishes a translation that moves and continues a relation
from a frozen re-labeling. The formal `Frozen` and `Translating` predicates
also prove that a frozen round step cannot be translating.

## 3. Natural, dual, obstructed, and OPEN positions

The status of a trace is derived from its interaction field:

```text
dual position        → DUAL
obstructed position  → OBSTRUCTION
natural + returned   → RETURNED
natural + bridge     → PATH
natural without bridge → OPEN
```

This does not turn a dual or obstructed view into a separate operator. Both
remain relative readings of the same trace. `no_bridge_is_open`,
`dual_is_relative_position`, and `obstruction_is_recorded` formalize this
small classification.

The natural-rhythm triangle is therefore not a background illustration. It
appears only when an expanded relation is contracted through a bridge and a
return makes a successor relation available:

\[
\text{relation}
\rightarrow\text{relative re-reading}
\rightarrow\text{preserved bridge}
\rightarrow\text{return}
\rightarrow\text{successor relation}.
\]

The layout is spatial and interactive, but this is a software operation model,
not a claim that the UI instantiates a physical manifold.

## 4. Bridge chains and levels

`LevelBridge` records an injective, relation-reflecting map between levels.
`LevelBridge.compose` proves that the bridge record composes. This is the
formal analogue of retaining an explicit return path when a topic is zoomed,
redefined, or changed from language to operative definition.

It does **not** prove that a text entered in the browser is genuinely
injective, relation-reflecting, or independently grounded. The browser records
the user-supplied bridge; validation of its truth is an external task.

## 5. Directional tokens and resuperposition

The token layer remains independent from the Slearn field. A
`PerspectiveToken` is subject- and dimension-indexed. An `AssumptionGrain`
states which directions are currently permitted; narrower grains can remove
directions but cannot invent unavailable ones. Resonance, dissonance, and
open are scoped to a stated token network, not global truth or moral scores.

A token becomes structurally `IntangiblyVerified` only through a supplied,
grounded receipt. The contract/reopen cycle preserves an ordered
`MetaVectorTrace`, so a returned basis may retain route history. Those are
formal representation choices, not a physical theory of time.

## 6. Exact scope

Machine-checked here:

- only traces admitted by an `InteractionField` can generate spatial roles;
- contracting and reopening require a bridge;
- successor views require bridge, attempt, and a receipt;
- a changed successor is not literal repetition of its source;
- a frozen round step is not translating;
- relation-reflecting bridges compose;
- the stated non-global-hair result for the stated finite quarter turn.

Educational or metaphysical interpretation only:

- that a supplied return receipt is independent or true;
- that a user’s bridge is adequate or natural;
- that the layout is a physical closure, curvature, or learning mechanism;
- any physical, cosmological, or quantum reading of the token layer.
