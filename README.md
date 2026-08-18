# Slearn

Slearn is a **framed repository for perspectival curvature and closure**. It
is not centered on a website or on one finite model. Perspectives, beliefs,
WHY relations, goals, lessons, projects, world views, formal modules, and
runtime projections are all located within one source-grounded
perspectival-curvature closure packet.

Start with [`FRAMEWORK.md`](FRAMEWORK.md). It defines the repository’s nine
frames—`OPEN`, `PERSPECTIVE`, `CURVATURE`, `TRANSLATION`, `INTERACTION`,
`VERIFICATION`, `ADMISSION`, `RETURN`, and `PROJECTION`—and their admission
rules. The optional `ui/` directory is in the final projection frame; it has
no authority to create sources, verify returns, or define Slearn.

> The project explores how a learner can cross languages, definitions, disciplines, and lived perspectives while retaining a checkable route back to the relation from which they began. It does not claim that literal one-hour intelligence upload exists.

Any visible map is a projection, not the framework. It must be generated from
the witnessed learner kernel: a lesson requires all three WHY witnesses, a
project requires an attempt, and a recorded return requires source material,
a counter-reading, comparison, review, and a successor. Unwitnessed or
unattempted material is `OPEN`, not an admissible mechanic.

## Core geometry

For an admitted translation, local and global are inverse orientations of the same path:

\[
L \xrightarrow{\tau} G \xrightarrow{\tau^{-1}} L'.
\]

They are not independently primary levels joined by arbitrary operators. The return is evaluated in a specified witness language:

\[
L' \sim_{\mathcal C} L.
\]

At the episode level, a returned relation is not literal replay. Two reciprocal
paths can interact and return to the same selected base relation while retaining
a residue that distinguishes this successful realization from another. The
inherited successor then has the same base but a changed continuation field:

\[
\operatorname{baseOf}(\mathcal C_1)=\operatorname{baseOf}(\mathcal C_0),
\qquad
\operatorname{continuationOf}(\mathcal C_1)
\ne\operatorname{continuationOf}(\mathcal C_0).
\]

This stronger `CLOSED_TO_NEW_OPENING` status is issued only with a returned
witness, an alternative successful realization that distinguishes the residue,
and evidence of the changed continuation field. It is not a general claim that
every completed interaction is generative.

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

## Projection contract

Every projection works from one persisted closure state:

```text
frame → active opening → translation path → comparison language
      → witnessed kernel → generated perspective / belief / WHY / goal / lesson / project / world map
      → return witness or obstruction → residue comparison → inherited opening → receipt
```

Thus a zoom from perspective to belief, WHY to goal, lesson to project, or project to world is a recentering of the same opening—not a move between disconnected tables. A recorded return requires a source anchor and claim, material examined, attempt, counter-reading, comparison method, review, receipt, and changed successor. It is a reviewable evidence record, not an automatic truth verdict. A local success is never silently promoted to universal-relative completion.

Every admitted recentering executes the common operation:

\[
\Gamma \xrightarrow{Ch} Ch(\Gamma) \xrightarrow{Ka} Ka(Ch(\Gamma))
\xrightarrow{\mathrm{Diff}} \Omega.
\]

`Ch` is semantic contraction (zoom out), `Ka` is reciprocal reopening (zoom
in), and `Ω` is the retained closure-relative difference. Relational recovery
does not require literal endpoint identity; a zero readout at one level does
not exhaust local route distinction. This operation is the projection law, not
a decorative display transition.

## Machine-checked scope

- [`Slearn/UniversalRelativeTranslationalCompletion.lean`](Slearn/UniversalRelativeTranslationalCompletion.lean) proves completion laws, the universal-relative uniqueness theorem, and cofinal relevance preservation.
- [`Slearn/NaturalRhythmClosure.lean`](Slearn/NaturalRhythmClosure.lean) defines an admitted two-orientation translation, relative natural/dual/obstructed positions, and the minimal cone/opening relation.
- [`Slearn/ClosedTopologicalTranslation.lean`](Slearn/ClosedTopologicalTranslation.lean) formalizes reciprocal interaction episodes, orientation inversion, returned-base witnesses, comparator-defined residues, and inherited openings.
- [`Slearn/NRRF651SlearnUIHairOfClosureGeneratedMap.lean`](Slearn/NRRF651SlearnUIHairOfClosureGeneratedMap.lean) formally gates the source-derived map/hair interface by WHY witnesses, attempts, receipts, and bounded occurrence depth.
- [`Slearn/ChaitinKakeyaTokenResuperposition.lean`](Slearn/ChaitinKakeyaTokenResuperposition.lean) models directional token fields, assumption grains, receipt-gated IVI, contraction/reopening roles, and ordered trace history.
- [`Slearn/NRRF652ClosureTranslationCommonOperationKakeyaTokenResuperposition.lean`](Slearn/NRRF652ClosureTranslationCommonOperationKakeyaTokenResuperposition.lean) supplies the shared `Ch → Ka → Ω` operator, four-way verdict classification, finite-resolution/readout contract, ordered route residue, and Slearn semantic-zoom binding.
- [`Slearn/InteractiveTranslationalOpenFoundation.lean`](Slearn/InteractiveTranslationalOpenFoundation.lean) proves finite-stage incompleteness, continuous completion for prefix views, inverse-limit return, and selected gluing/obstruction examples.

The repository has no theorem about physical spacetime, consciousness, societal automation, moral value, or a privileged “natural” perspective. Those are educational and metaphysical interpretations, deliberately kept outside the certified theorem surface.

## Further design documents

- [`FRAMEWORK.md`](FRAMEWORK.md): canonical repository frames, admission rules, and the separation of sources, relations, verification, return, and projections.
- [`framework/registry.json`](framework/registry.json): machine-readable map of every registered repository resource and its closure frame; `node scripts/validate-framework.mjs` validates it.
- [`docs/SLEARN_SOURCE_PROVENANCE.md`](docs/SLEARN_SOURCE_PROVENANCE.md): privacy-preserving historical record of the original/raw Slearn notes, later synthesis boundary, and the WHY-first → returned-experience design continuity.
- [`docs/SLEARN_CLOSURE_RESEARCH_LEDGER.md`](docs/SLEARN_CLOSURE_RESEARCH_LEDGER.md): the source-grounded packet protocol that keeps questions, counter-readings, comparison records, runtime traces, formal claims, and open remainders distinct.
- [`docs/UNIVERSAL_RELATIVE_TRANSLATIONAL_COMPLETION.md`](docs/UNIVERSAL_RELATIVE_TRANSLATIONAL_COMPLETION.md): completion contract, uniqueness, relevance, and receipt requirements.
- [`docs/NATURAL_RHYTHM_CLOSURE.md`](docs/NATURAL_RHYTHM_CLOSURE.md): consolidated terminology, triangle geometry, runtime projections, and scope boundaries.
- [`docs/CLOSED_TOPOLOGICAL_TRANSLATION.md`](docs/CLOSED_TOPOLOGICAL_TRANSLATION.md): the episode-level return, residue, and inherited-opening contract.
- [`docs/GENERATED_UI_AND_TOKEN_RESUPERPOSITION.md`](docs/GENERATED_UI_AND_TOKEN_RESUPERPOSITION.md): source-generated map/hair admission and directional token resuperposition boundaries.
- [`docs/CLOSURE_TRANSLATION_COMMON_OPERATION_NRRF652_NOTES.md`](docs/CLOSURE_TRANSLATION_COMMON_OPERATION_NRRF652_NOTES.md): the common `Ch → Ka → Ω` operation, runtime verdicts, and scope limits.
- [`docs/INTERACTIVE_TRANSLATIONAL_OPEN_FOUNDATION.md`](docs/INTERACTIVE_TRANSLATIONAL_OPEN_FOUNDATION.md): finite interaction, inverse limits, and gluing examples.

Run `lake build` to build the Lean project. CI also rejects `sorry` and `admit` in Lean sources.
