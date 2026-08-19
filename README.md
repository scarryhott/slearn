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

[`docs/SLEARN_ORIGINAL_VISION.md`](docs/SLEARN_ORIGINAL_VISION.md) is the
canonical, verbatim Speed Learn manifesto. Its companion
[`docs/RESEARCH_FRAMEWORK.md`](docs/RESEARCH_FRAMEWORK.md) classifies the
surrounding work as product design, phenomenology, metaphor, metaphysical
hypothesis, mathematical definition, proved theorem, empirical/runtime result,
or open question. In particular, Speed Learn means reducing unnecessary
translation cost between perspectives and generative insight—not compressing
information or claiming a literal one-hour intelligence upload.

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

The repository’s common completion contract is answer-preserving translation:

\[
x =_{\mathcal C} y
\iff
\forall q\in Q_{\mathcal C},\;A(q,x)=A(Tq,y).
\]

An individual question-language, scalar aggregate, finite verifier, or
resolution grain is a bounded reading, not the whole relation. Where a
declared family of relational questions separates the admitted translation
orbits, closure relation, true translation, and natural choice coincide
**within that frame**. See
[`docs/RELATIONAL_CLOSURE_UNIFICATION.md`](docs/RELATIONAL_CLOSURE_UNIFICATION.md)
for the full depth map and its limits.

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
- [`Slearn/PerspectivalCurvatureClosurePrimitives.lean`](Slearn/PerspectivalCurvatureClosurePrimitives.lean) makes the source-defined perspective, belief/goal limits, WHY, paired explanation/definition, counter-path, reviewed interaction, and nonterminal admission conditions explicit before a return can be recorded.
- [`Slearn/DerivedPerspectivalClosureHull.lean`](Slearn/DerivedPerspectivalClosureHull.lean) derives prospective branches, reciprocal zoom readings, OPEN regions, experience fibres, returned-basis merges, and successor updates from closure packets rather than from an authored map.
- [`Slearn/AuditableChangingAxiometryProtocol.lean`](Slearn/AuditableChangingAxiometryProtocol.lean) defines a bounded auditable changing-axiometry run: relative axiom–geometry closure truth, residue-derived next axiometry and verifier, held-out capability separation, and a prediction-before-outcome record.
- [`Slearn/DerivedSlearnClosureVersion.lean`](Slearn/DerivedSlearnClosureVersion.lean) joins the source-derived Slearn return to that bounded audit: each closure version derives its map projection, changed verifier/frame, and held-out next relation from one admitted packet.
- [`Slearn/ReplayableSlearnClosureAudit.lean`](Slearn/ReplayableSlearnClosureAudit.lean) proves, in the bounded model, that truth agreement alone cannot certify a closure succession: a publisher's returned perspective, derived verifier/frame, and re-entered relation must reconstruct the successor and be replayed by a distinct modeled identity.
- [`Slearn/TransactionalCompletionEvaluation.lean`](Slearn/TransactionalCompletionEvaluation.lean) evaluates frozen language/definition frames only through a declared relevant question-language; it identifies completion with answer-preserving admitted translation and proves endpoint/trajectory markers neither necessary nor sufficient in an explicit finite model.
- [`Slearn/CompletionInTranslationalTruthEquality.lean`](Slearn/CompletionInTranslationalTruthEquality.lean) separates a presentation's truth answers from its local/global, trajectory, and endpoint markers; it proves marker-blind completion, propositional answer transport, and a direct bridge into the transactional-admitted-translation adapter.
- [`Slearn/RecalculationAgainstTranslatedTruthAnswers.lean`](Slearn/RecalculationAgainstTranslatedTruthAnswers.lean) derives translated truth equality for frozen question-languages, its exact extension law, and the conditional reopening of an equal relation by a supplied discriminator.
- [`Slearn/PartitionAggregateClosure.lean`](Slearn/PartitionAggregateClosure.lean) gives a finite four-form calculation in which equal scalar aggregates close transactionally while retained phase placement opens a successor question; it proves that the next phase reading cannot be recovered from that aggregate alone.
- [`Slearn/RelationalClosureUnification.lean`](Slearn/RelationalClosureUnification.lean) unifies answer-preserving translation, relational-orbit closure, finite/all-depth distinction, partition reopening, Topos/Turing witness return, and Kakeya-style resolution as separate but connected closure depths.
- [`Slearn/GodelTarskiRelativeClosureBoundary.lean`](Slearn/GodelTarskiRelativeClosureBoundary.lean) provides bounded diagonal, level-tower, liar, and basis-capacity models that distinguish local incompleteness, selected limit closure, internal-truth obstruction, and relative certification depth without claiming a formalization or refutation of Gödel, Tarski, or Chaitin.
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
- [`docs/PERSPECTIVAL_CURVATURE_CLOSURE_PRIMITIVES.md`](docs/PERSPECTIVAL_CURVATURE_CLOSURE_PRIMITIVES.md): the primitive source contract and its deterministic `PATH` run; `node scripts/run-source-closure.mjs` checks that the direct source is not promoted to an unearned return.
- [`docs/DERIVED_PERSPECTIVAL_CLOSURE_HULL.md`](docs/DERIVED_PERSPECTIVAL_CLOSURE_HULL.md): the source-packet ledger to dynamic-map projection; `node scripts/project-closure-hull.mjs --summary` runs the current closure hull without invoking the optional UI.
- [`docs/AUDITABLE_CHANGING_AXIOMETRY_EXPERIMENT.md`](docs/AUDITABLE_CHANGING_AXIOMETRY_EXPERIMENT.md): the bounded grant experiment and its falsifiable stage requirements; `node scripts/run-changing-axiometry-protocol.mjs` confirms that the current protocol is only design-ready.
- [`docs/DERIVED_SLEARN_CLOSURE_VERSION.md`](docs/DERIVED_SLEARN_CLOSURE_VERSION.md): the Slearn-specific version/succession derivation that prevents map, verifier, frame, and next opening from becoming separate systems.
- [`docs/REPLAYABLE_SLEARN_CLOSURE_AUDIT.md`](docs/REPLAYABLE_SLEARN_CLOSURE_AUDIT.md): the bounded replay record that distinguishes relation-level truth agreement from an independently replayable succession.
- [`docs/TRANSACTIONAL_COMPLETION_EVALUATION.md`](docs/TRANSACTIONAL_COMPLETION_EVALUATION.md): the limited language/definition transaction adapter and its marker-separation boundary.
- [`docs/COMPLETION_TRANSLATIONAL_TRUTH_EQUALITY.md`](docs/COMPLETION_TRANSLATIONAL_TRUTH_EQUALITY.md): the bounded truth-answer/isolated-marker separation and its direct transactional bridge.
- [`docs/RECALCULATION_TRANSLATED_TRUTH_ANSWERS.md`](docs/RECALCULATION_TRANSLATED_TRUTH_ANSWERS.md): translated question-language recalculation, finite ball/hair and polar readings, and its discriminator-generation boundary.
- [`docs/PARTITION_AGGREGATE_CLOSURE.md`](docs/PARTITION_AGGREGATE_CLOSURE.md): finite four-form aggregate closure, retained partition distinction, and the boundary between a discrete turn and a continuous/physical interpretation.
- [`docs/RELATIONAL_CLOSURE_UNIFICATION.md`](docs/RELATIONAL_CLOSURE_UNIFICATION.md): the canonical unification of closure relation, true translation, natural choice, relative completion depth, and the Slearn/Topos–Turing/Kakeya readings.
- [`docs/GODEL_TARSKI_RELATIVE_CLOSURE_BOUNDARY.md`](docs/GODEL_TARSKI_RELATIVE_CLOSURE_BOUNDARY.md): the bounded local-stage, selected-closure, internal-truth, and relative-depth distinctions, including the boundary with the unavailable NRRF667 report.
- [`docs/UNIVERSAL_RELATIVE_TRANSLATIONAL_COMPLETION.md`](docs/UNIVERSAL_RELATIVE_TRANSLATIONAL_COMPLETION.md): completion contract, uniqueness, relevance, and receipt requirements.
- [`docs/NATURAL_RHYTHM_CLOSURE.md`](docs/NATURAL_RHYTHM_CLOSURE.md): consolidated terminology, triangle geometry, runtime projections, and scope boundaries.
- [`docs/CLOSED_TOPOLOGICAL_TRANSLATION.md`](docs/CLOSED_TOPOLOGICAL_TRANSLATION.md): the episode-level return, residue, and inherited-opening contract.
- [`docs/GENERATED_UI_AND_TOKEN_RESUPERPOSITION.md`](docs/GENERATED_UI_AND_TOKEN_RESUPERPOSITION.md): source-generated map/hair admission and directional token resuperposition boundaries.
- [`docs/CLOSURE_TRANSLATION_COMMON_OPERATION_NRRF652_NOTES.md`](docs/CLOSURE_TRANSLATION_COMMON_OPERATION_NRRF652_NOTES.md): the common `Ch → Ka → Ω` operation, runtime verdicts, and scope limits.
- [`docs/INTERACTIVE_TRANSLATIONAL_OPEN_FOUNDATION.md`](docs/INTERACTIVE_TRANSLATIONAL_OPEN_FOUNDATION.md): finite interaction, inverse limits, and gluing examples.

Run `lake build` to build the Lean project. CI also rejects `sorry` and `admit` in Lean sources.
