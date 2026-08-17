# Natural-Rhythm Closure Geometry

## Status and scope

This is the consolidated vocabulary and runtime contract for the natural-rhythm refactor.

**Machine-checked:** `Slearn/NaturalRhythmClosure.lean` defines admitted two-way translations, relative positions, and a minimal refined-opening cone; its return and opening-containment theorems are checked by Lean. The pre-existing universal-relative completion uniqueness theorem remains unchanged.

**Interpretive only:** “natural-rhythm triangle,” “shape-dynamical light cone,” and “unitary translational curvature.” The repository makes no formal or empirical claim about physical light cones, quantum mechanics, consciousness, automation ethics, or a privileged natural perspective.

## One translation, two orientations

`AdmittedTranslation Local Global Witness` has a forward map, a backward map, and witness projections for both presentations:

\[
L \xrightarrow{\tau} G,
\qquad
G \xrightarrow{\tau^{-1}} L,
\qquad
w_G(\tau(l))=w_L(l),
\qquad
w_L(\tau^{-1}(g))=w_G(g).
\]

Local and global are inverse orientations of this one admitted relation. “Inverse” means returned witness equality; it does not require the maps to be inverse as functions.

## Triangle and boundaries

The natural-rhythm triangle is rendered as

\[
\text{global continuation}
\rightarrow
\text{local opening}
\rightarrow
\text{returned compatible field}.
\]

For a `NaturalRhythmCone`, `localView` refines `globalView`; Lean proves the local opening at the apex is contained in the global opening. The runtime names two caller-supplied boundary conditions:

| Boundary | Meaning | Runtime response |
| --- | --- | --- |
| Total isolated local/global view | One view is treated as exhaustive. | Require an admitted translation or comparison view. |
| Unresolved temporal/superposed partition | Alternatives lack a selected return relation. | Remain open; issue no completion receipt. |

The structure does not assert that these boundaries exhaust all possible degeneracies.

## Natural and non-natural positions

`TranslationPosition` keeps a local presentation, a global presentation, and a tag:

- `natural` requires closure evidence in the common witness language;
- `dual` is a relative alternative position;
- `obstructed` is a relative position with failed comparison or return evidence.

The latter two remain positions in the same admitted translation. A different comparison map must be recorded as a new admitted translation, not silently treated as a disagreement about the old map.

## Recentered interface

All user-visible labels are projections of a single persisted closure state:

\[
\text{perspective}
\leftrightarrow
\text{belief}
\leftrightarrow
\text{WHY}
\leftrightarrow
\text{goal}
\leftrightarrow
\text{lesson}
\leftrightarrow
\text{project}
\leftrightarrow
\text{world}.
\]

```text
frame + relevant views + active opening + orientation
translation path + comparison language + typed projection
return witness | dual position | obstruction witness
completion status + receipt provenance
```

`OPEN_LOCAL`, `LOCALLY_COMPATIBLE`, `DUAL_POSITION`, `OBSTRUCTION_WITNESSED`, `RETURNED_COMPLETE`, and `OUTSIDE_FRAME` are distinct states. In particular, local compatibility must never be presented as universal-relative completion.

## Relation to the completion theorem

This layer does not alter the theorem:

\[
C=\operatorname{TC}_F
\]

only when `C` satisfies both local conservativity and returned sufficiency over every admitted view of `F`. It makes the frame’s translations and recenterings legible to the runtime without selecting a privileged initial view or resolving dual and obstructed positions without evidence.

## Closed episode and reopened continuation

The natural-rhythm layer gives the shape of an admitted translation. The
episode layer in [`CLOSED_TOPOLOGICAL_TRANSLATION.md`](CLOSED_TOPOLOGICAL_TRANSLATION.md)
states when an interaction may honestly be rendered as a closure that opens a
new continuation.

It models an unprioritized reciprocal pair, two interacting paths, and an
orientation swap. A return recovers a caller-selected base relation; it does
not assert literal equality with the origin. A residue is admitted only when
another successful return at the same base has a different caller-selected
residue coordinate. `CLOSED_TO_NEW_OPENING` additionally requires that the
successor’s continuation field differ from the origin’s.

This keeps the triangle’s recurrence exact:

\[
\text{OPEN interaction}
\rightarrow
\text{returned relation}
\rightarrow
\text{distinguishing residue}
\rightarrow
\text{inherited opening}.
\]

## Generated map and hair admission

The recentered interface is now constrained in the one-way direction

\[
\text{witnessed learner kernel}
\Longrightarrow
\text{generated Slearn map}
\Longrightarrow
\text{local hair/view atlas}.
\]

The bounded formal model in
[`NRRF651SlearnUIHairOfClosureGeneratedMap.lean`](../Slearn/NRRF651SlearnUIHairOfClosureGeneratedMap.lean)
therefore admits a lesson only with all three WHY witnesses, a project only
with an attempt, and a returned experience reading only with a return receipt.
Its saturation theorem identifies the resulting bounded relation with the
specified core/brain/value/lesson/project/impact/balance/Slearn/dream map.
Unwitnessed or unattempted content remains `OPEN`; a generic screen, card, or
mechanic is not an independent source of map structure. The later
token-resuperposition layer is documented with the same boundary in
[`GENERATED_UI_AND_TOKEN_RESUPERPOSITION.md`](GENERATED_UI_AND_TOKEN_RESUPERPOSITION.md).

It is still not a theorem about physical curvature, consciousness, or a
privileged natural choice.
