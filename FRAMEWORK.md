# Slearn Framework

Slearn is a **framed repository for perspectival curvature and closure**, not
a website with some Lean files behind it. The repository’s basic unit is a
source-grounded perspectival-curvature / closure packet:

```text
OPEN source / observation
  → perspectival relation (perspective, belief/value, WHY, goal)
  → curvature (how belief and goal limit, bend, or open the available path)
  → admitted translation (re-reading and preserved bridge)
  → interaction (attempt through the relation)
  → verification (material, counter-reading, comparison, review)
  → truth-admission (a relation that can continue under translation)
  → recorded return (receipt, Ω, successor / further relation)
  → next OPEN relation
```

This is not a linear production pipeline. Each frame is a reciprocal reading
of the same relation. Curvature is not assumed to be a physical metric: it is
the specified difference made by moving an observation through belief, goal,
WHY, explanation, definition, and counter-reading. A return supplies a new
perspective and a retained difference; it does not erase the source,
counter-reading, or question.

The machine-readable repository map is
[`framework/registry.json`](framework/registry.json). Run
`node scripts/validate-framework.mjs` to verify that the registered resources,
their frame assignments, and their dependencies still exist. That command
checks organization only; it does not prove a source claim or a human return.

## The frames

| Frame | It holds | It may admit | It must not silently become |
| --- | --- | --- | --- |
| `OPEN` | original notes, observations, questions, unresolved distinctions | a source anchor and claim | a theorem or a completed learner state |
| `PERSPECTIVE` | local perspective, belief/value context, WHY, goal, world relation | a stated relation to examine | a fixed profile, folder, or objective identity |
| `CURVATURE` | the differential constraint between perspective, belief/value, goal, WHY, and explanatory route | a stated limit/fold/path problem | a numerical geometry, a quality score, or a physical curvature claim |
| `TRANSLATION` | language/definition flip, bridge, local/global orientations | an admitted forward/backward contract | literal local/global identity or an arbitrary unrelated operator |
| `INTERACTION` | paths, attempts, reciprocal passes, obstructions | a concrete comparison episode | evidence merely because an operation ran |
| `VERIFICATION` | material examined, counter-reading, method, review, proof obligations | a reviewable evidence record | independent empirical truth or universal completion |
| `ADMISSION` | the stated truth condition by which relative presentations may continue together | a relation-relative, revisable truth admission | a terminal preserved truth, closed entropy, or an origin-language privilege |
| `RETURN` | receipt, relation-relative recovery, Ω, successor, inherited opening | a recorded continuation into a further relation | final completion or replay of the origin |
| `PROJECTION` | Lean views, documentation, runtime, UI, diagrams | a representation of an admitted packet | the authority that creates its own source, evidence, or proof |

`PROJECTION` is deliberately last. The browser field is in this frame; it is
not the Slearn framework and it is not the center of the repository.

## What each repository surface is for

```text
docs/SLEARN_SOURCE_PROVENANCE.md       → OPEN provenance boundary
docs/SLEARN_ORIGINAL_VISION.md         → OPEN / PERSPECTIVE source grammar
docs/RESEARCH_FRAMEWORK.md              → canonical-source interpretation and claim-level boundary
docs/SLEARN_CLOSURE_RESEARCH_LEDGER.md → packet, verification, and OPEN remainder
docs/SLEARN_PERSPECTIVAL_CURVATURE_SPECIFICATION.md
                                         → source-defined curvature, truth-admission, goal, and path mechanism

Slearn/UniversalRelative…lean          → TRANSLATION contract and uniqueness scope
Slearn/NaturalRhythmClosure.lean        → TRANSLATION orientations/positions
Slearn/ClosedTopologicalTranslation.lean→ INTERACTION / RETURN episode structure
Slearn/Interactive…lean                 → INTERACTION / VERIFICATION finite-limit boundary
Slearn/NRRF654…lean                     → frame integration adapter
Slearn/NRRF655…lean                     → RETURN predecessor-typed continuation
Slearn/DerivedPerspectival…lean          → PERSPECTIVE / RETURN ledger-derived closure hull
Slearn/AuditableChangingAxiometry…lean   → VERIFICATION / ADMISSION bounded changing-frame protocol
Slearn/DerivedSlearnClosureVersion.lean  → PERSPECTIVE / VERIFICATION / RETURN derived version succession
Slearn/ReplayableSlearnClosureAudit.lean → VERIFICATION / ADMISSION / RETURN replayable lawful succession
Slearn/TransactionalCompletionEvaluation.lean → TRANSLATION / ADMISSION limited-frame answer equality

ui/                                    → optional PROJECTION only
```

The full map is maintained in the registry so a contributor must identify the
role and boundary of a resource before it can be treated as part of Slearn.

## Admission rules for repository changes

1. A direct source, observation, or user statement enters through `OPEN` with
   provenance and an explicit question or proposed relation. It does not enter
   as a theorem.
2. A perspective/goal/WHY record enters `PERSPECTIVE`. Its belief and goal
   constraints, possible reasons, explanations, definitions, and alternative
   paths must be named in `CURVATURE`; its local and global readings then need
   an explicit bridge before they enter `TRANSLATION`.
3. A formal module can establish only its stated structure. Its assumptions,
   model carrier, and unproved interpretation must be registered at
   `VERIFICATION` or remain `OPEN`.
4. An interaction has to retain an attempt and its counter-reading. A rendered
   action or typed sentence does not by itself qualify as verification.
5. `ADMISSION` is the point at which a truth condition is stated: relative
   presentations can continue together under the declared translation. It is
   not a final truth value. A return is **recorded** only after its material,
   comparison method, review, receipt, residue, and successor/further relation
   are present. Independent review remains a distinct obligation.
6. A UI, diagram, or generated prose can project a packet, but cannot create a
   source anchor, authenticate evidence, or upgrade a source claim to truth.

## How to work in this repository

Start at the frame that matches the work, not at the UI:

- New note, transcript, or source: add an anchor and question to the closure
  research ledger; preserve raw sources outside public documentation unless
  publication is authorized.
- New educational relation: create a closure packet with the perspective,
  belief/goal curvature, WHY, explanations/definitions, bridge, and a named
  counter-reading.
- New formal result: add it to the registry with the actual Lean file, its
  machine-checked scope, and its missing evidence obligation.
- New runtime or visualization: register it as a projection of specific packet
  fields; it may not introduce independent navigation, content, or completion
  state.
- New map branch: add a packet to `framework/closure-ledger.json` and run the
  hull projector. A prospective branch may appear from a `PATH`; an experience,
  successor, or merged returned basis may appear only from a recorded continued
  admission.

The central open problem is not “make more screens” or “assert one theory.” It
is to organize real source-grounded episodes whose translations, counter-
readings, evidence, and continuations can be inspected without collapsing the
open remainder.

## Claim-level rule

`docs/SLEARN_ORIGINAL_VISION.md` remains the canonical source; its statements
do not acquire formal or empirical status by being placed beside Lean, a UI, or
a runtime. The required levels and the translation of each manifesto section
are in [`docs/RESEARCH_FRAMEWORK.md`](docs/RESEARCH_FRAMEWORK.md): product
design, phenomenology, metaphor, metaphysical hypothesis, mathematical
definition, proved theorem, empirical/runtime result, and open question.

The repository-wide closure relation is:

```text
Perspective → Why → Goal → Learning → Insight → Action → Experience
            → Return → Perspective′.
```

The prime marks a changed successor relation. It never silently means literal
endpoint equality, ordinary equality of `0` and `∞`, or a completed account of
spacetime, consciousness, nature, or spirit.
