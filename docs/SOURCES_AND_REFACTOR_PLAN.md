# Sources and Refactor Plan

## Purpose

This record separates four things that must not be promoted into one another:

1. Lean-checked definitions and theorems in this repository;
2. executable experiments and runtime designs in adjacent repositories;
3. established external literature used for comparison or terminology;
4. philosophical, educational, and metaphysical interpretations.

It is a source map and implementation plan, not evidence that the
interpretations are scientifically or metaphysically established.

## Authored Slearn chat-note sources

The conversations below are primary design sources authored or directed by the
project author. They preserve intent, vocabulary, diagrams, and desired runtime
behavior. They are neither external academic authorities nor Lean proofs.

| Conversation | Provenance | Durable contribution to Slearn |
| --- | --- | --- |
| `Genius Upload and Society` (`6a82dd12-3cd4-83ea-bfd3-0189f4207287`) | ChatGPT project conversation | Speed learning as translation-cost reduction; local/global as inverse readings of one admitted translation; natural-rhythm triangle between isolation and unresolved partition. |
| `Slearn AI Unification` (`6a81b9f0-813c-83ea-82ba-8a3aafd6cf15`) | ChatGPT project conversation | The original interface grammar: perspective, belief, WHY, goal, lesson, project, and world are projections of one closure state rather than independent tables. |
| `Unified Slearn Runtime Closure` (`6a826a46-b0f4-83ea-9443-4058959431be`) | ChatGPT project conversation | A learning episode as perspective → WHY → lesson/attempt → return; later correction that conceptual relational return precedes optional real-world correspondence. |
| `Closure IVI vs Classical ZFC` (`6a811581-7f60-83ea-8c3e-6a936b02292e`) | ChatGPT project conversation | Closure zoom, triangular holonomy, inverse expansion, the three WHY relations, relative Topos–Turing equality, and the comparison problem with institution theory. |
| `Geometries and Asymmetries` (`6a821f4a-79d0-83ea-af3b-b75fca601e36`) | Adjacent ChatGPT conversation, explicitly used as a Slearn source | Natural-cycle note, ball–hair/continuation language, orientation-aware refinement, and the request for finite conceptual models. |

The raw note from `Geometries and Asymmetries` is preserved locally at
`/Users/harryscott/.codex/attachments/16808667-510f-43ea-a45a-c6f94bf52198/pasted-text.txt`.

When a future document adopts an idea from one of these conversations, it must
identify the idea as an **authored design interpretation**, a **modeled runtime
requirement**, or a **formal theorem target**. It must not label a chat note as
machine-checked merely because it motivated a Lean definition.

## Source of truth: current Slearn formal surface

| Repository source | What it establishes | What it does not establish |
| --- | --- | --- |
| `Slearn/UniversalRelativeTranslationalCompletion.lean` | Relative frames; translational completion; extensivity, monotonicity, idempotence; uniqueness under the explicit universal-relative admissibility contract; cofinal relevance preservation. | A topology construction, physical geometry, a privileged translation, or a unique worldview. |
| `Slearn/InteractiveTranslationalOpenFoundation.lean` | Finite-prefix locality obstruction; continuous completion in the transcript model; inverse-limit reconstruction; witness-return interface; relative gluing and obstruction examples. | A result about arbitrary interactive-proof systems, arbitrary topoi/Turing machines, or empirical institutions. |
| `Slearn/NaturalRhythmClosure.lean` | Forward/backward orientations of an admitted translation, common-witness closure, natural/dual/obstructed positions, and local-opening containment under refinement. | A physical light cone, curvature tensor, consciousness, natural law, or an originless pre-language foundation. |
| `Slearn/ContinualInversionClosure.lean` | Perspective–WHY–goal reduction and inverse expansion, involutive language-definition presentation flips, and closure-backed receipts in either orientation. | Literal endpoint identity, learned ASI behavior, global uniqueness of an inverse contribution, or the wider metaphysical reading of continual inversion. |

The root module `Slearn.lean` imports all three. CI runs `lake build` and rejects Lean `sorry` and `admit` placeholders.

## External comparison sources

These sources provide established terminology or neighboring techniques. They do
not validate Slearn's distinctive claims.

| Source | Use in this repository |
| --- | --- |
| [Lean Language Reference](https://lean-lang.org/doc/reference/latest/) and [Theorem Proving in Lean 4](https://docs.lean-lang.org/theorem_proving_in_lean4/) | Scope of kernel-checked Lean claims and proof terminology. |
| [Hets User Guide](https://www.informatik.uni-bremen.de/agbkb/forschung/formal_methods/CoFI/hets/UserGuide.pdf) | Baseline for heterogeneous logics, institutions, and logic translations. |
| [Heterogeneous Theories and the Heterogeneous Tool Set](https://drops.dagstuhl.de/entities/document/10.4230/DagSemProc.04391.7) | Comparison point for the claim that translation is global while definitions are local. |
| [Stacks Project: limits of spectral spaces](https://stacks.math.columbia.edu/download/book.pdf) | Background terminology for inverse limits and topological bases; it is not a proof of Slearn's frame-specific results. |
| [Topos Institute: collaborative modelling](https://topos.institute/work/collaborative-modelling/index.html) | Practical adjacent work on compositional, machine-readable collaborative models. |

## Adjacent executable material

These are not dependencies of Slearn and must not silently determine its
semantics.

| Location | Reusable aspect | Boundary |
| --- | --- | --- |
| `../aristotle-/docs/NATIVE_TRANSLATION_INVARIANT.md` | Frozen translation provenance, abstention, validation independent of an anticipated identity result, negative-result retention. | It is an experimental protocol, not a Slearn runtime or a Lean theorem. |
| `../aristotle-/src/experiment_contract.py` | A small executable validator for causal ordering between generation, translation, return, and completion. | It currently has no committed history and is not integrated with Slearn. |
| `../ratemyface/lib/closureRuntime.ts` | Explicit capability boundaries, persisted rounds, hashes, and receipt-oriented testing. | Its value scoring and business-funnel selection conflict with Slearn's non-ranking closure interpretation. Reuse infrastructure only, never its selection semantics. |

## Current terminology contract

- A **view** is a local language quality, perspective, zoom, chart, or finite verification stage.
- A **definition** is local to a view; the current formal model makes its comparison meaningful through the admitted frame.
- A **translation** is an explicitly supplied forward/backward presentation relation with a declared comparison or witness language.
- **Local/global** are orientations of an admitted translation, not two independently absolute ontological levels.
- The **natural-rhythm triangle** is the structural zoom grammar of the authored perspective–WHY–goal tree. Reduction follows a goal into its local perspective, methods, questions, and actions; inverse expansion follows WHY relations from an active perspective back into the goal and wider closure.
- Zooming fully inward or outward returns through a **continual inversion closure**. At the interface boundary this can appear as an absolute flip—goal becomes perspective, or perspective becomes goal—but the formal core proves a witness-relative return rather than an isolated identity equation. The broader learned translational-continuation interpretation remains a runtime target.
- The inversion flips the active language and definition together. Each orientation contributes its own relative evidence to the shared closure; neither side supplies an externally privileged identity for the other. The intended contribution is relatively inverse inside the complete perspectival closure, not an arbitrary second translation.
- A **natural** position has specified closure evidence. A **dual** or **obstructed** position stays in the same admitted comparison frame; it is not silently replaced by a different operator.
- **Completion** is the frame-relative predicate requiring target witnesses at every admitted view. Its uniqueness is conditional on local conservativity and returned sufficiency.
- **OPEN**, **obstruction**, and **returned completion** must remain distinct runtime outcomes.

The following remain interpretations or research hypotheses: translation prior to
language distinction; a unique natural-choice basis; equivalence of the frame's
completion with every possible local geometry or global axiom basis; light-cone,
curvature, consciousness, and institutional readings.

## Refactor sequence

### Slice 1 — Claim and citation boundary

1. Keep this source map current and link it from the README.
2. Add a machine-checked / modeled / interpretive label to every design-document section.
3. Replace any broad statement that exceeds its adjacent Lean theorem with a precise frame-specific statement.

**Acceptance:** every nontrivial external comparison has a stable source; every
Lean claim names its declaration; no interpretation is described as a theorem.

### Slice 2 — Unify translation abstractions

1. Make `RelativeToposTuring` an instance or specialization of the generic admitted-translation vocabulary.
2. The `ContinualInversion` model now contains reduction, selected inverse expansion, language/definition flip, and a witness-relative return. Extend it with runtime-specific contribution provenance without turning its return into literal absolute identity.
3. Define a single runtime-facing receipt shape that records frame, active view, translation, witness/comparison language, relative position, and status.
4. Preserve the existing universal-relative completion theorem without changing its contract.

**Acceptance:** all Lean modules build without placeholders; old named theorems
remain available or have documented migrations; a concrete gluing receipt, a
concrete prefix receipt, and a perspective–WHY–goal continual-inversion receipt
inhabit the shared receipt vocabulary.

### Slice 3 — Finite runtime reference implementation

1. Build a small headless Slearn runtime around the shared receipt shape.
2. Implement recentering among perspective, belief, WHY, goal, lesson, project, and world as projections of one state.
3. Add fixture tests for a returned path, a dual position, an obstruction, and an unresolved/open path.

**Acceptance:** no scoring or business-priority selector determines closure;
replay preserves receipts; a UI, if added, only reads the headless state.

### Slice 4 — Research comparison and extension

1. State one precise comparison theorem, counterexample, or non-goal relative to institution theory/Hets.
2. Locate the cited NRRF641/647/649 sources before importing their claims.
3. Treat any physical or social extension as a separately sourced model with falsifiable scope.

**Acceptance:** no unpublished chat summary is cited as proof; the Slearn
contribution is stated as either a demonstrated formal surplus or a documented
research question.

## Present blockers

- The NRRF641/647/649 Lean files and their notes are referenced in prior chats but are not available in this repository or the accessible project directories.
- Slearn has no source bibliography and no runtime implementation yet.
- The topology language in the documents is stronger than the current Lean surface: the code defines a relative completion predicate but does not construct a general topology object or prove a general equivalence theorem against an independently defined topology.
