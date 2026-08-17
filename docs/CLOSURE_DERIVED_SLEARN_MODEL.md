# Closure-Derived Slearn Model

## Status

This document reunifies the original Slearn interface geometry with the
translation-closure and natural-rhythm work.

- **Primary interface source:** the 2024 [Slearn universe-perspective path](https://docs.google.com/document/d/14NIKWn5tKkPD86Nasz6wVwBySTno2_VEiE0EtUdHSlk/edit?usp=drivesdk).
- **Closure synthesis:** the 2026 [Slearn source-disciplined synthesis](https://docs.google.com/document/d/12vL3JfYMtZMW8QuFU7XSoTL4kQ0EtvihRgI7wXRkgrI/edit?usp=drivesdk) and companion [translational-completion manuscript](https://docs.google.com/document/d/1_6C2V7XG-RbMmw5d1LL8zCTbeAtM7qS-ZuZaGTfI9C4/edit?usp=drivesdk).
- **Machine-checked carrier:** `Slearn/ClosureDerivedSlearn.lean` proves only the typed witness coherence explicitly encoded in its structures. It does not prove a generated UI, independently grounded returns, a topology-generation theorem, or empirical world effects.

The original 3D map is retained. Translation closure changes what its nodes,
paths, zooms, and completed experiences mean and how they may change.

## The original geometry is the local map

The source geometry is not a generic dashboard:

```text
Slearn root / shared WHY
            ↓
current brain / perspective viewport
            ↓
values and beliefs around the brain
            ↓
goals and unexperienced futures
            ↓
WHY-connected lessons, questions, and methods
            ↓
broad learning node
            └── 90° turn ── project steps ── world relation
```

Lesson depth and project depth are joined by **rungs**. A user can move from a
project step to the lesson, value, or question that makes it intelligible, and
from a lesson to an applicable step in a project. The persistent chat bar and
the compact previous/current/next lesson and project paths are local readings
of this same map.

The brain is a current viewport origin. It is not the origin of the system or
the owner of all meanings.

## Closure changes the map's state law

The map is a projection of a closure state, rather than a visual surface with
separate logic behind it:

\[
\mathbb S_t =
(\widehat{\mathcal C}_t, P_t, B_t, G_t, M_t, Y_t, A_t, X_t,
R_t, H_t, \Omega_t, \theta_t).
\]

| Part | Meaning |
| --- | --- |
| `P` | active perspective / temporary viewport origin |
| `B` | belief and value orientations around the viewport |
| `G` | goals, dreams, and broad future orientations |
| `M` | generated maze: nodes, WHY relations, rungs, paths, and walls |
| `Y` | WHATs: questions, lessons, methods, activities, and candidate experiences |
| `A` | learner attempts and project actions |
| `X` | project artifacts, world contacts, reflections, and other return surfaces |
| `R` | translation and return witnesses / receipts |
| `H` | retained route order or learning holonomy |
| `Ω` | unresolved relations and obligations: `OPEN` |
| `θ` | current scale, orientation, selected node, and passage/wall reading |

There is no separate goal, lesson, or project interface with its own meaning.
Each is a recentering of `\mathbb S_t`.

## Natural-rhythm triangle as the map's dynamic

The natural-rhythm triangle is not a decorative triangle beside the map. It is
the rule that converts a selected local map relation into its next map.

\[
\boxed{
\text{global continuation}
\longrightarrow
\text{local opening}
\longrightarrow
\text{returned continuation field}
}
\]

For Slearn, one episode has two readable triangles:

```text
Prospective / differentiating triangle
goal → WHY → lesson or method → attempt or project action

Returned / integrating triangle
attempt or project action → return → revised WHY → next goal or perspective
```

The second apex may be closure-compatible with the first without being the
same local goal or perspective. Its retained difference is learning holonomy:
the route returned, but the available field changed.

The triangle lies between two explicit degeneracies:

| Degeneracy | Slearn failure | Required response |
| --- | --- | --- |
| Isolated local/global view | A curriculum, goal, score, or current self-description is treated as exhaustive. | Reopen another view through a recorded translation. |
| Unreturned partition | Many methods or futures appear without a relation that selects, obstructs, or returns them. | Preserve `OPEN`; do not convert possibility into experience. |

The triangle is an **interpretive runtime geometry**. The checked Lean model
only records admitted translations, witness coherence, named relative positions,
and the minimal refined-opening relation.

## Node and relation semantics

| Original map object | Closure-derived state |
| --- | --- |
| Belief/value hair | A local orientation that can open one or more goal relations; not a score or permanent trait. |
| Goal/future image | A prospective continuation: `PATH`, `WALL`, or `OPEN`. |
| Lesson/question/method | A WHAT node whose three WHY witnesses are domain, perspective, and goal relations. |
| Lesson-project rung | A translation between learning depth and application depth that preserves a named witness, not literal identity. |
| Project step / artifact | An attempted relation to a world, community, collaborator, or other return surface. |
| Experience image/reflection | A returned presentation only when an episode receipt admits it; it may carry success, failure, obstruction, or a new opening. |
| World-impact model | A prospective scenario until its stated relation has a separate return; it must not certify its own prediction. |
| Gray value area | An underexplored or obstructed orientation, not a personal defect or missing score. |

Each WHY is separate:

\[
W_D(\text{lesson}),\qquad
W_P(\text{perspective},\text{lesson}),\qquad
W_G(\text{lesson},\text{goal}).
\]

An explanation lacking any one of these remains generic domain material,
unsupported personalization, or detached content. It is not silently promoted
into a personal path.

## Projection and zoom

| Projection | What it shows |
| --- | --- |
| Current 2D strip | previous → current → next lesson or project occurrence, with immediate WHY and open question |
| Perspective map | active brain, values/beliefs, reachable goals, and immediate lesson maze |
| Goal map | a desired goal reduced into needed relations, methods, questions, and present constraints |
| Project/world plane | the 90° extension from broad learning to project steps, artifacts, collaborators, schedules, and world relations |
| Passage view | currently witnessed traversals |
| Wall view | positive prerequisites, contradictions, unavailable resources, or failed translations |
| Returned view | experiences, receipts, route history, and the new perspective field |

Zoom is semantic, not magnification:

\[
\operatorname{ZoomIn}(b)=W^{-1}(b),
\qquad
\operatorname{ZoomOut}(Y)=Y/\ker W.
\]

Zooming inward unfolds questions, attempts, artifacts, reflections, and
relations through which a returned identity was formed. Zooming outward renders
its broader lesson, capability, goal, value, project, world, or universe
relation. A visible goal/perspective flip changes local orientation and the
language-definition presentation; it does not establish literal endpoint
identity.

## Minimal runtime transaction

```text
1. Recenter: choose a perspective, value/belief orientation, and opening.
2. Reason: render PATH, WALL, or OPEN with the three WHY relations.
3. Traverse: select a lesson, method, conversation, or project step.
4. Attempt: create an answer, activity record, artifact, or reflection.
5. Return: relate the attempt through another admissible presentation.
6. Admit: attach a receipt; only then can the WHAT appear as returned experience.
7. Rebuild: regenerate reachable paths, walls, OPEN relations, and local projections.
8. Retain: preserve route order and nontrivial difference as holonomy.
9. Resuperpose: expose next translations without deleting unresolved ones.
```

A real-world expert, collaborator, or project outcome is a valuable return
surface, but not the only possible one. The runtime must not invent an external
authority requirement where the relevant closure is conceptual and relational.
Conversely, it must not use an AI-produced proposal as evidence for that same
proposal.

## Current formal bridge

`Slearn/ClosureDerivedSlearn.lean` provides a deliberately small typed bridge:

- an existing `ContinualInversion` supplies perspective ↔ WHY ↔ goal closure;
- belief → goal, WHY → lesson, lesson → project, and project → world are
  witness-coherent extensions;
- Lean proves the belief-goal route closes with the active perspective;
- Lean proves lesson-project and project-world rungs preserve their witnesses;
- a rendered `returned` occurrence requires a receipt matching its active
  perspective and goal.

It does **not** yet derive the graph, validate a return's independence, persist
events, construct a general topology, or render the original 2D/3D interface.
Those are the next runtime slices, not properties to pretend the proof already
establishes.

## Implementation consequences

1. Replace hard-coded UI hairs with persisted node and relation records.
2. Make the UI consume the canonical state; it must not manufacture receipts,
   `PATH`, `WALL`, `OPEN`, or returned experiences locally.
3. Implement the original brain/value/goal/lesson/project/world geometry as
   projections over that state.
4. Keep the 2D lesson/project strips and persistent input bar: they are local
   closure projections, not secondary dashboard widgets.
5. Preserve the difference between a proposed future, attempted action, and
   returned experience.
6. Store holonomy and `OPEN` rather than flattening revisits into duplicates or
   unresolved alternatives into a progress score.
