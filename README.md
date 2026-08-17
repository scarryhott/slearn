# Slearn

Slearn is a speed-learning interface organized around **returned translation**. Perspectives, beliefs, WHY relations, goals, lessons, projects, and world views are not independent record types: they are recenterings of one closure geometry.

> The project explores how a learner can cross languages, definitions, disciplines, and lived perspectives while retaining a checkable route back to the relation from which they began. It does not claim that literal one-hour intelligence upload exists.

## Core geometry

For an admitted translation, local and global are inverse orientations of the same path:

\[
L \xrightarrow{\tau} G \xrightarrow{\tau^{-1}} L'.
\]

They are not independently primary levels joined by arbitrary operators. The return is evaluated in a specified witness language:

\[
L' \sim_{\mathcal C} L.
\]

For a relative frame `F`, translational completion of a target `S` is

\[
\operatorname{TC}_F(S)(x)
\iff
\forall a,\;\exists s\in S,\;x\equiv_a s.
\]

The Lean core proves this operator is extensive, monotone, idempotent, and the **only** operator satisfying the stated universal-relative admissibility contract. That is a conditional uniqueness result about this frame and contract—not a claim that every use of “closure,” every translation map, or every worldview is unique.

## Natural-rhythm triangle

The natural-rhythm triangle is the interface primitive for a shape-dynamical light cone of unitary translational curvature:

\[
\text{global continuation}
\xrightarrow{\text{projection}}
\text{current local opening}
\xrightarrow{\text{recenter / return}}
\text{compatible continuation field}.
\]

It sits between two boundary failures:

- **isolated local/global view**: one presentation is treated as the whole, so no meaningful translation remains;
- **unresolved temporal/superposed partition**: alternatives remain unreturned, so no trajectory acquires a determinate relation.

“Light cone,” “unitary curvature,” and these social or phenomenological readings are design interpretations. Lean formalizes only the selected structure: refined openings, an admitted forward/backward translation, a common witness, named relative positions, and explicit boundary exclusions supplied by a caller.

Natural choice means closure evidence under the admitted translation and its return. A non-natural perspective is not modeled as an unrelated competing translation operator; it is a `dual` or `obstructed` position inside the same translation and comparison language.

## Runtime contract

Every interaction works on one persisted closure state:

```text
frame → active opening → translation path → comparison language
      → perspective / belief / WHY / goal / lesson / project / world projection
      → return witness or obstruction → receipt
```

Thus a zoom from perspective to belief, WHY to goal, lesson to project, or project to world is a recentering of the same opening—not a move between disconnected tables. A valid receipt records the frame, active view, target, translation, return witness, obstruction evidence, and status. A local success is never silently promoted to universal-relative completion.

## Machine-checked scope

- [`Slearn/UniversalRelativeTranslationalCompletion.lean`](Slearn/UniversalRelativeTranslationalCompletion.lean) proves completion laws, the universal-relative uniqueness theorem, and cofinal relevance preservation.
- [`Slearn/NaturalRhythmClosure.lean`](Slearn/NaturalRhythmClosure.lean) defines an admitted two-orientation translation, relative natural/dual/obstructed positions, and the minimal cone/opening relation.
- [`Slearn/InteractiveTranslationalOpenFoundation.lean`](Slearn/InteractiveTranslationalOpenFoundation.lean) proves finite-stage incompleteness, continuous completion for prefix views, inverse-limit return, and selected gluing/obstruction examples.

The repository has no theorem about physical spacetime, consciousness, societal automation, moral value, or a privileged “natural” perspective. Those are educational and metaphysical interpretations, deliberately kept outside the certified theorem surface.

## Further design documents

- [`docs/UNIVERSAL_RELATIVE_TRANSLATIONAL_COMPLETION.md`](docs/UNIVERSAL_RELATIVE_TRANSLATIONAL_COMPLETION.md): completion contract, uniqueness, relevance, and receipt requirements.
- [`docs/NATURAL_RHYTHM_CLOSURE.md`](docs/NATURAL_RHYTHM_CLOSURE.md): consolidated terminology, triangle geometry, runtime projections, and scope boundaries.
- [`docs/INTERACTIVE_TRANSLATIONAL_OPEN_FOUNDATION.md`](docs/INTERACTIVE_TRANSLATIONAL_OPEN_FOUNDATION.md): finite interaction, inverse limits, and gluing examples.

Run `lake build` to build the Lean project. CI also rejects `sorry` and `admit` in Lean sources.
