# Ledger-derived perspectival closure hull

The Slearn maze is not an authored graph, learner profile, curriculum, or UI
coordinate system. It is the closure hull of the repository's source-grounded
packet ledger:

```text
M_t = ClosureHull(packet₀, …, packetₜ)
```

The input is the primitive packet contract in
[`PERSPECTIVAL_CURVATURE_CLOSURE_PRIMITIVES.md`](PERSPECTIVAL_CURVATURE_CLOSURE_PRIMITIVES.md).
The output is a map-shaped relation that contains only roles derived from
those packets.

## What a packet may project

A `PATH` packet projects a prospective branch:

```text
source → observation → perspective → belief limit → WHY
  ↔ semantic / operative explanation ↔ definition
  → prospective lesson → forward path → goal
  → counter-path → perspective
  → OPEN remainder
```

The forward and counter paths give the two orientations of the same declared
translation. `zoomOut` is derived as perspective → belief limit → WHY → lesson
→ forward path → goal; `zoomIn` is goal → counter path → operative explanation
→ definition → WHY → belief limit → perspective. These are ledger readings,
not free camera moves.

A `RETURNED (RECORDED)` packet adds exactly six derived roles:

```text
prospective lesson → attempted project → experience fibre → successor perspective
goal → returned basis ────────────────┘
     → world continuation → next OPEN remainder
```

An experience fibre is impossible for a `PATH` packet. It appears only when
the packet has material, attempt, counter-reading, comparison, review,
receipt, changed successor, explicit returned-basis identifier, and next
relation. Two returns merge only when their supplied returned-basis identifiers
are equal; shared wording or an AI similarity score cannot merge nodes.

## Formal and executable projections

[`DerivedPerspectivalClosureHull.lean`](../Slearn/DerivedPerspectivalClosureHull.lean)
machine-checks the generator shape:

- a PATH item projects a prospective lesson and OPEN remainder;
- a returned item projects its attempted project, experience fibre, and world continuation, and still reopens;
- equal returned witness bases become the same basis node; and
- successor perspectives appear only in the update stream of returned items.

[`framework/closure-ledger.json`](../framework/closure-ledger.json) is the
current ledger and [`project-closure-hull.mjs`](../scripts/project-closure-hull.mjs)
is its deterministic projection. Run:

```sh
node scripts/project-closure-hull.mjs --summary
```

The present source ledger deliberately yields one `PATH` branch, no experience
fibre, and one OPEN region. It is a projection of the foundational source
packet—not a fictional example of completed learning.

## Scope boundary

The code does not infer a learner's perspective, make an educational
recommendation, decide whether a review is sound, or claim that the map is a
physical geometry. It gives a strict source-to-ledger-to-hull route through
which a future interface may be generated. Any interface that adds a node,
link, position, project, experience, or completion state lacking this route is
outside this closure-derived Slearn contract.
