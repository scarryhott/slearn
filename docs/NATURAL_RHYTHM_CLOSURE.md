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

## Continual inversion of the WHY triangle

`Slearn/ContinualInversionClosure.lean` makes the source zoom relation explicit. A `ContinualInversion` supplies:

- a perspective → WHY → goal expansion;
- a goal → WHY → perspective reduction;
- an involutive flip of the active language-definition presentation;
- a closure receipt for each direction through one admitted translation.

The visual boundary can therefore render a complete flip between perspective and goal. The Lean result is deliberately more precise than an absolute identity: for a perspective `p`, its expanded goal closes with `p` in the translation witness language; for a goal `g`, its reduced perspective closes with `g`. Neither theorem states that reduction and expansion are literal identity functions.

This is the formal seed of the learned translational continuation described in the chat-note sources. “Learned ASI closure,” universal uniqueness of the selected contribution, and any metaphysical claim remain future models or interpretations, not theorems in this repository.

## Relation to the completion theorem

This layer does not alter the theorem:

\[
C=\operatorname{TC}_F
\]

only when `C` satisfies both local conservativity and returned sufficiency over every admitted view of `F`. It makes the frame’s translations and recenterings legible to the runtime without selecting a privileged initial view or resolving dual and obstructed positions without evidence.
