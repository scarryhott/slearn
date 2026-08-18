# Slearn Closure Research Ledger

> This is the `OPEN` / `PERSPECTIVE` / `VERIFICATION` / `RETURN` ledger inside
> the canonical repository frame. Start with
> [`../FRAMEWORK.md`](../FRAMEWORK.md) for the frame contract and
> [`../framework/registry.json`](../framework/registry.json) for the resource
> map. It is not a substitute for the raw private source materials.

## Why this exists

Slearn cannot be organized as a set of finished answers, a generic graph, or a
series of small illustrative models. Its primary unit is a **reviewable closure
packet**: a source-grounded question in which a perspective, reason, and goal
are put into interaction, met by a counter-reading, and returned only as far as
the recorded comparison warrants.

This ledger is the repository's source-of-record for that organization. It
does not reproduce private notes. Source descriptors are privacy-preserving
anchors; their provenance and classification are in
[`SLEARN_SOURCE_PROVENANCE.md`](SLEARN_SOURCE_PROVENANCE.md).

## Non-negotiable separation

| Record | What it can establish | What it cannot establish |
| --- | --- | --- |
| Direct note or direct conversational passage | A design intention, question, or proposed relation | The truth of the proposal |
| Closure packet | What a learner or collaborator actually compared, attempted, and reviewed | Independent validation merely because fields were completed |
| Lean declaration | A theorem of its explicitly supplied structures and axioms | The truth of a source, a browser event, or an educational result |
| Runtime projection | A deterministic record and visible trace of a packet | A proof that its prose, source, or review is sufficient |
| Interpretive vocabulary | A research direction for reading the structure | A physical, psychological, or metaphysical conclusion |

No status may be promoted across these rows implicitly. In particular,
`RETURNED` means **a reviewed return has been recorded**. It never means that
Slearn, a learner, a source claim, or a theory has become finally true.

## The closure packet

Every interaction admitted to the map must carry this chain. Empty entries are
not silently filled by AI, layout, or a formal analogy.

```text
source anchor + source claim / observation
  → current perspective + value/belief context
  → curvature: belief/goal limits, WHY paths, explanations, definitions, and counter-path
  → WHY relation
  → goal / global reading
  → re-reading + preserved bridge
  → concrete material examined + attempt
  → counter-reading, duality, or obstruction
  → stated comparison method + review
  → admission: a continued relation rather than a terminal truth badge
  → return receipt + changed successor
  → Ω: retained source, comparison, and open remainder
  → next question / next opening
```

The packet has four evaluation states. They are information states, not truth
scores:

| State | Minimum record | Runtime consequence |
| --- | --- | --- |
| `OPEN` | A source claim, perspective, WHY, or goal is missing; or a bridge has not been stated | It may be visible as an open question, never as a completed path |
| `PATH` | Source anchor and claim, perspective, WHY, goal, re-reading, and bridge are present | The forward and reciprocal translations may be executed |
| `REOPENED` | The ordered forward and reciprocal translations have been executed | It is eligible for comparison, not yet for return |
| `RETURNED (RECORDED)` | Concrete material, attempt, counter-reading, method, review, receipt, and changed successor accompany the executed path | Ω and the successor may be persisted; the review's unresolved remainder seeds the next opening |

`DUAL` and `OBSTRUCTION` are not failures to hide. They are positions of the
same packet that prevent an unwarranted return.

`ADMISSION` is not a fifth global truth score. It is the explicit condition
between verification and return: the relation may be admitted only as a
continued translation into a further relation. The source-defined curvature and
truth-admission mechanism is specified in
[`SLEARN_PERSPECTIVAL_CURVATURE_SPECIFICATION.md`](SLEARN_PERSPECTIVAL_CURVATURE_SPECIFICATION.md).

## Source anchors and questions to preserve

| Anchor | Direct contribution to retain | Closure question it opens | Required interaction before any returned claim |
| --- | --- | --- | --- |
| `SRC-2023-WHY` | WHY-first, project/failure learning, individual assistance | Does this WHY lead to a learner-chosen practice rather than a preselected answer? | Record an attempt and a failure/success comparison, not merely a lesson title |
| `SRC-2024-MAP` | Perspective → values/beliefs → goals → lessons/projects → world; zoom and lived return | Does a zoom preserve one relation while changing its orientation? | Execute both orientations, state the bridge, and compare the local rereading with the goal reading |
| `SRC-2024-ADAPTIVE` | AI offers paths relative to learner choice rather than replacing it | Does a suggested path enlarge questions without deciding the learner's relation? | Preserve the learner's counter-reading and evaluate the suggestion against it |
| `SRC-2025-TRIANGLE` | Downward decomposition, upward return, revised goal/depth, multiple WHY paths | Which retained difference makes an upward return a continuation rather than a replay? | Compare at least two possible paths or state why the alternative remains OPEN |
| `SRC-2026-WHY-TREE` | Insights beneath perspective maps have inspectable WHY branches | Does each insight have a reviewable reason branch rather than a free-floating label? | Attach source/observation, branch relation, and a testable lesson/project route |
| `SRC-2026-MAZE` | Perspectival maze-map; ball/hair and translation vocabulary | What line, fold, or bridge is preserved by the two readings? | Name the witness language and an obstruction or alternative traversal |
| `SRC-2026-CURVATURE` | Perspective curvature under belief/goal limits; language/definition/explanation flips; truth admission must continue into further relation | How does a change in belief or goal bend the available WHY paths, and what next relation makes an admission nonterminal? | State the limits, two explanations/definitions, counter-path, comparison, and successor relation; do not substitute a score or UI operation |
| `SRC-2026-AUDITABLE-AXIOMETRY` | A bounded changing-axiometry experiment: relative axiom/geometry closure truth, residue-derived next axiometry/verifier, held-out relation, and independent consequence | Can completed translation change both an axiometry and its verifier while preserving auditable comparison? | Freeze a generated frame, discover/validate a native translation, record independent return, retain a closure witness/residue, test changed derivations on held-out material, and register prediction before an external outcome |
| `CHAT-EDUCATION-MAP` | An open spatial interface: drawn relations, paths to sources/lessons, reframing, shared maps | Can the interface make the change in perspective legible without reducing it to engagement, folders, or a chatbot answer? | Record a human-drawn or supplied relation, its opposing reading, and the evidence used to revise it |
| `OBSERVED-INTERACTION` / `EXTERNAL-SOURCE` | A concrete new observation or supplied reference | What has actually been observed or cited in this episode? | Identify the material and method; no inherited prose is treated as evidence |

These entries are **research obligations**, not axioms. A new original note,
conversation, source, or formal result should be registered here before it is
used to change the runtime or documentation.

## Existing formal and executable projections

| Ledger need | Current repository support | Deliberate boundary |
| --- | --- | --- |
| Local/global are inverse orientations of one admitted translation | `NaturalRhythmClosure.lean`, `NRRF654IntegratedFrameworkClosure.lean` | The application-specific witness still has to be supplied |
| Source-defined curvature and nonterminal admission | `PerspectivalCurvatureClosurePrimitives.lean`, `framework/source-closure-primitives.json`, `scripts/run-source-closure.mjs` | The primitive source packet reaches `PATH`; no source text is treated as a reviewed attempt, return, or truth admission |
| Ledger-derived Slearn maze | `DerivedPerspectivalClosureHull.lean`, `framework/closure-ledger.json`, `scripts/project-closure-hull.mjs` | A PATH contributes only a prospective branch and OPEN remainder; experience fibres, successor updates, and returned-basis merges require a continued admission |
| Bounded changing-axiometry audit | `AuditableChangingAxiometryProtocol.lean`, `framework/changing-axiometry-experiment.json`, `scripts/run-changing-axiometry-protocol.mjs` | The protocol is `DESIGN_READY`; it has no generated frame, independent return, held-out result, or external consequence yet |
| Derived Slearn closure version | `DerivedSlearnClosureVersion.lean`, `DERIVED_SLEARN_CLOSURE_VERSION.md` | A version joins the source curvature packet to the bounded audit; it proves only supplied structural links, not that any learning episode has independently occurred |
| Replayable Slearn closure audit | `ReplayableSlearnClosureAudit.lean`, `REPLAYABLE_SLEARN_CLOSURE_AUDIT.md` | `auditor ≠ publisher` is only modeled identity separation; it does not establish an independent human, data source, or experiment |
| Transactional completion evaluation | `TransactionalCompletionEvaluation.lean`, `TRANSACTIONAL_COMPLETION_EVALUATION.md` | The relevant question-language and translation are supplied; this does not select a warranted contact relation or independently generate a frame |
| Completion in translational truth equality | `CompletionInTranslationalTruthEquality.lean`, `COMPLETION_TRANSLATIONAL_TRUTH_EQUALITY.md` | The truth answers, their shared language, and the finite marker model are supplied; the theorem does not make a real contact relation or a universal semantics warranted |
| Recalculation against translated truth answers | `RecalculationAgainstTranslatedTruthAnswers.lean`, `RECALCULATION_TRANSLATED_TRUTH_ANSWERS.md` | The next discriminator is explicitly supplied; raw presentation inequality does not by itself discover a warranted new question or independent return |
| Relation-relative return with residue and a next opening | `ClosedTopologicalTranslation.lean`, `NRRF652ClosureTranslationCommonOperationKakeyaTokenResuperposition.lean`, `NRRF655ExecutablePerspectivalClosureEpisode.lean` | The theorem does not decide whether a human receipt is adequate |
| Source-derived Slearn roles and trace-gated map | `NRRF651SlearnUIHairOfClosureGeneratedMap.lean` | It proves a modeled bounded generator, not the historic notes or browser equality |
| Continuous completion versus a finite interaction | `InteractiveTranslationalOpenFoundation.lean` | A finite browser session cannot certify a global completion |
| Runtime source, counter-reading, review, residue, and successor | `ui/app/closureSources.ts`, `ui/app/closureRuntime.ts` | It records declared comparisons; it performs no external retrieval or independent review |

## Current running protocol

1. Select or register the source anchor; enter the claim or observed relation.
2. State the current perspective, WHY, goal, re-reading, and bridge. The
   relation is now a `PATH`, not a conclusion.
3. Execute contract and reopen. The map must visibly change orientation through
   the same relation; this is not a free camera switch.
4. Attach the actual material examined and what was attempted.
5. State the counter-reading, the comparison method, and what the review found
   to hold, fail, or remain open.
6. Only then record a return. Ω retains those elements and the successor begins
   the next packet with its inherited difference.

The next work is therefore not another finite “model of Slearn.” It is the
progressive population, review, and—where admissible—formalization of these
packets from primary material and real learning interactions.
