# Slearn: perspectival curvature and translational admission

## Status

This document organizes direct Slearn source material supplied on 2026-08-18
with the earlier lineage in
[`SLEARN_SOURCE_PROVENANCE.md`](SLEARN_SOURCE_PROVENANCE.md). It is a
source-grounded design specification, not a theorem, physical model, or
empirical validation. It intentionally does not reproduce the complete private
source text.

It corrects a framing error: Slearn's mechanism is not a generic sequence of
fields and receipts. It is **perspectival curvature under translational
limits**. Belief and goal limit and bend an observation's available paths;
WHY, explanations, definitions, and interaction make that curvature
inspectable; translation and return determine whether the relation can
continue without privileging an origin language.

```text
OPEN → PERSPECTIVE → CURVATURE → TRANSLATION → INTERACTION
     → VERIFICATION → ADMISSION → RETURN → OPEN
```

The canonical repository contract is [`../FRAMEWORK.md`](../FRAMEWORK.md).

## 1. Frame: curvature of observation

The source asks whether a translation can be independent of a chosen origin
language while its relations form reference frames. It describes an adaptive
map in which deep WHY–goal relations transform a learner's perspective.

| Element | Mechanism | It is not |
| --- | --- | --- |
| Perspective `P` | Current local reading and position | a fixed profile or category |
| Belief/value `B` | A limit: what is possible, relevant, or obstructed | a permanent label or scalar preference |
| Goal `G` | A directional limit that pulls paths from `P` | an endpoint that validates its own path |
| WHY `W` | Reason/path joining `P`, `B`, and `G` | a generic explanation detached from a relation |
| Explanations/definitions `E₁`, `E₂`, `D` | Alternative presentations that expose a language/definition flip | interchangeable wording or a fixed glossary |
| Interaction/attempt `A` | A path through which the relation meets practice or another perspective | a click, metric, or automated completion |
| Counter-reading `C` | A dual, limiting, or obstructed path | noise to remove |

A curvature record is consequently not a number and not a claim about
spacetime. It is the structured difference

\[
\mathsf{Curv}_{\mathcal R}=(P,B,G,W,E_1,E_2,D,A,C;\mathcal R),
\]

where \(\mathcal R\) is the declared comparison relation. It records how
changing a belief or goal changes meaningful WHY paths, explanations,
definitions, and possible next interactions. This is the repository meaning of
**observational curvature**.

“Translation cost” is not a numeric optimizer by default. It is the identified
work or obstruction needed to carry a relevant relation across languages,
definitions, cultural contexts, or perspectives. Until a comparison procedure
is supplied, cost remains `OPEN`.

## 2. Translation: no privileged origin language

The source's central question remains an `OPEN` foundation:

> Can a translation be independent of the selection of an origin language,
> with relations themselves acting as reference frames?

Slearn's working contract is not that every presentation is identical:

\[
P \xrightarrow{\tau} G,
\qquad G \xrightarrow{\tau^{-1}} P',
\qquad P' \sim_{\mathcal R} P.
\]

The apparent inversion changes orientation within one admitted relation.
Language and definition may flip roles: one reading exposes a semantic
explanation, another an operative definition, lesson, test, or project. Return
is structural continuation, not literal endpoint identity.

The source's claim that local/global—or zero/infinity—may be equal *in truth*
is a proposed admission problem, not a theorem that all numbers, physical
limits, or languages are equal. The current Lean code formalizes conditional
relation-relative closure, not this broader claim.

## 3. Truth admission: closure continues

The source distinguishes closure from preservation of a closed proposition. A
truth admission must translate into a further relation:

\[
\operatorname{Admit}_{\mathcal R}(P,G)
\Longrightarrow (P' \sim_{\mathcal R} P)
\;\land\;\exists\,\mathcal R_{\mathrm{next}}.
\]

This is a design condition, not a proved implication. An admitted relation
must leave a successor relation available for inspection, translation, and
revision. That is the operational meaning of “potential gate as a truth
condition rather than a closed entropy.”

Natural choice is not a predefined best path or a separate natural operator.
It is a candidate admission only when the relation has met its counter-reading,
declared its comparison, returned in its stated witness relation, and exposed
a further relation. A duality or obstruction blocks an unjustified admission;
it is not discarded as an error.

## 4. Goal: reduce limits while expanding questions

The direct educational goal is a framework that:

- makes perspective, belief, WHY, goal, method, and project explicit enough to
  be revised;
- reduces unnecessary translation cost without replacing learner choice with a
  fixed institutional definition;
- expands questions and paths rather than forming an attention-driven echo
  chamber; and
- lets people negotiate value or credit by relative translation rather than a
  privileged origin language.

The historical “genius upload” wording is an aspiration for transformative
learning, not a claim that this repository can upload intelligence or that a
technical mechanism has been demonstrated.

## 5. Universe–perspective path: educational grammar

The source describes a grammar for records and interactions, not a mandate for
a particular website:

```text
life experience / current brain position
  ↔ philosophical value or belief
  ↔ WHY branch
  ↔ goal, dream, passion, or simpler direction
  ↔ lesson with two explanations and connective questions
  ↔ method / practice / project
  ↔ experienced return
  ↔ goal → world → universe continuation
```

Zooming inward resumes a lesson or practice. Zooming outward re-reads the same
relation from brain/perspective to goal, then goal to world/universe. It is
valid only if the path, translation, and bridge persist; it is not a free
camera, folder tree, or category switch.

WHY trees organize insights as branches that can be traversed, challenged, and
related in sequence or hierarchy. The two-explanation lesson requirement keeps
the language/definition curvature visible instead of hiding it behind one
formulation.

## 6. Interactive open network

In the source, “open” means **accessible through interaction**, not merely
cryptographically open or automatic. A genuine attempt at an open connection
is proposed to incur and reveal a cost through a perspectival receipt. That is
a `VERIFICATION` and `ADMISSION` requirement: it needs a concrete receipt
protocol, counter-reading, and governance rule before it determines credit,
curation, or access.

The proposed institution of translation must test whether its invariants remain
translational rather than hardening into a fixed institution. This is a
research/governance question; it is not implemented by current code.

## 7. Existing support and the missing mechanism

| Requirement | Existing support | Still OPEN |
| --- | --- | --- |
| Origin-language-independent frame | `UniversalRelativeTranslationalCompletion.lean` proves uniqueness only after its frame/admissibility conditions are supplied | Deriving a relevant frame from actual perspectives, languages, and observations |
| Inverse local/global orientations | `NaturalRhythmClosure.lean` defines an admitted two-way translation | A curvature interface binding belief/goal limits, WHY, explanations, and definitions to a concrete translation |
| Interaction, obstruction, residue, next opening | `ClosedTopologicalTranslation.lean`, `NRRF652…`, `NRRF655…` | Which source-grounded interactions justify a truth admission |
| Finite interaction versus continued completion | `InteractiveTranslationalOpenFoundation.lean` | An independent-review or interactive-proof protocol for Slearn relations |
| Universe–perspective/WHY-tree grammar | Original sources and source ledger | Real sources, lessons, projects, and reviewed returns |
| Open network/institution | Direct source proposal | Governance, consent, curation, cost, and invariant protocol |

The next formal work is not a generic curvature theorem. It is a concrete
`PerspectivalCurvature` interface with carriers for observation, belief/goal
limits, WHY, explanations/definitions, counter-path, comparison relation, and
next relation—then proofs only from those stated assumptions.

## 8. Comparative sources still OPEN

The current source names a “Kramer interpretation” and Whitehead as possible
supporting readings. Neither is registered as evidence yet: no exact
author/work/passage has been supplied for “Kramer,” and no precise Whitehead
claim has been selected. Both remain `OPEN` comparative sources. They must not
validate the curvature or truth-admission mechanism until their texts and the
proposed translation are recorded.
