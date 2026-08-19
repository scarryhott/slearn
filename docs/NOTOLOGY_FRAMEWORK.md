# Slearn notology framework

## Purpose

Slearn needs a way to organize named things without quietly turning any name
into a fixed ontology, a completed truth, or a UI object. This document calls
that discipline **notology**: the repository's account of how an admitted
framework name may be registered as a relative closure claim.

Notology is deliberately **not** an ontology. It does not settle what exists,
whether mind and matter have a particular relation, whether a natural rhythm
is a physical law, or which values a learner should adopt. It records what a
repository resource is allowed to say, the relation in which it is being read,
and what still has to be supplied before a stronger claim can be made.

The new synthesis gives each address the same shape:

\[
\boxed{
\mathsf{Address} =
(\text{name},\text{frame},\text{claim kind},\text{depth},\text{translation},
\text{verification},\text{closure state},\text{boundary},\text{next opening}).
}
\]

A presentation may change its language, definition, local/global orientation,
or resolution. Its address is maintained only when those changes preserve the
declared relation and retain their scope boundary. This makes notology the
organizational counterpart of the repository's closure relation:

\[
x =_{\mathcal C} y
\Longleftrightarrow
\forall q\in Q_{\mathcal C},\;A(q,x)=A(Tq,y).
\]

The equation is a formal rule only when the carrier, question family,
translation, and proof are separately declared. Elsewhere it is a research
discipline, not a theorem.

The checked representation is
[`../framework/notology.json`](../framework/notology.json). Run

```text
node scripts/validate-notology.mjs
```

to verify that every registered address has a valid kind, depth, state,
registered resource, boundary, and next opening. This check validates
repository organization only; it does not verify a source or create a return.

## Claim kinds

| Claim kind | It can name | It cannot become merely by being named |
| --- | --- | --- |
| `DIRECT_SOURCE` | A supplied note, observation, historical intention, or question | A proof, independently reviewed learner episode, or causal result |
| `PRODUCT_DESIGN` | An intended relation, interface behavior, or safety requirement | Evidence that learners learn or that the design is effective |
| `MATHEMATICAL_DEFINITION` | A declared carrier, translation, question family, or predicate | A description of reality without an additional argument |
| `PROVED_THEOREM` | A machine-checked statement under named assumptions | A physical, psychological, educational, or metaphysical conclusion outside those assumptions |
| `RUNTIME_RECORD` | A deterministic packet state or bounded run | External review, general-world evidence, or a proof |
| `INTERPRETIVE_READING` | A disciplined metaphor or a way to connect source and formal work | A literal causal model or an ontology |
| `METAPHYSICAL_HYPOTHESIS` | A contestable thesis about truth, mind, nature, value, or existence | A conclusion produced by source authority, UI behavior, or a finite model |
| `RESEARCH_BOUNDARY` | A missing bridge, limitation, or obligation | A solution to the limitation |

This subsumes the older source/formal/runtime/interpretation separation. The
change is that every claim is now also located by a relation and a depth,
rather than only placed in a prose category.

## Relative depth

| Depth | The admitted comparison | A positive result says | It leaves OPEN |
| --- | --- | --- | --- |
| `QUESTION` | Answers in a named language \(Q_n\) | These presentations agree on \(Q_n\) | A successor question can separate them |
| `TRANSLATION` | A declared bridge between two orientations | The bridge preserves the stated relation | The presentations can remain literally and route-wise distinct |
| `RESOLUTION` | A finite grain, partition, aggregate, or zoom | The selected readout agrees | A finer or differently structured reading can reopen the relation |
| `ALL_STATED_DEPTHS` | Every member of a declared refinement family | The formal model satisfies its all-depth condition | The family can still omit a real question or relation |
| `EVIDENCE` | Source, attempt, counter-reading, comparison, review, receipt, successor | A packet is reviewable at the stated level | Independent adequacy remains a separate task |

The finite partition calculation is the key protection against collapsing
these depths. Its scalar aggregate is a valid current reading, while the
retained phase arrangement can be separated by a supplied next question. A
finite result is therefore not invalid; it is **relative to the readout it
actually answers**. The same rule applies to a learner's selected goal,
belief, explanation, definition, lesson, project, or world zoom.

### Form depth is relational, not intrinsic

The synthesis uses **form depth** for the first stated question, translation,
or resolution at which two presentations cease to agree. It must not be read
as an inherent rank of an object. The current formal language calls the
general structure `RelativeCompletionDepth`: a form is shallow or deep only
relative to a declared refinement family and its answer relation. A scalar
aggregate can therefore close at one depth while a retained partition
distinction opens the next. No unavailable or reported form-depth module is
registered as a repository result.

## Closure state is not truth status

| State | Meaning | Minimum requirement |
| --- | --- | --- |
| `OPEN` | A name, question, claim, or relation has been registered | An explicit boundary and next opening |
| `PATH` | A source-grounded relation and reciprocal bridge are declared | Source anchor, perspective/WHY/goal relation, and bridge; no return implied |
| `REOPENED` | Reciprocal passes have executed and await comparison | Ordered interaction plus a named counter-reading or obstruction |
| `RETURNED_RECORDED` | A reviewed packet has a receipt and changed successor | Material, attempt, counter-reading, method, review, receipt, residue, and successor |
| `NOT_APPLICABLE` | A formal, editorial, or interpretive resource is not a learner-packet state | Its claim kind, scope, and boundary remain explicit |

`RETURNED_RECORDED` is deliberately demanding. No current source packet is
promoted to it. A formal theorem uses `NOT_APPLICABLE`: proving a model is not
the same event as recording a person's returned learning relation.

## The Slearn address grammar

For Slearn, the primary named relation remains:

```text
perspective → belief/value → WHY → goal → lesson/project/world
            → counter-reading → comparison → returned perspective′
```

The goal-facing and perspective-facing readings are not two separate maps:

```text
perspective → WHY → goal
goal → WHY⁻¹ → perspective
```

Both must name the maintained bridge and their changed return. A lesson,
project, world view, language explanation, operative definition, local view,
or global view is admitted only as a presentation of that relation. It may not
be used as an arbitrary independent navigation label.

The natural-rhythm triangle is registered here as an `INTERPRETIVE_READING`.
It can guide a source-grounded product relation: a downward prospective pass,
an upward return, a residue, and a further opening. It does **not** prove a
physical light cone, a cosmic natural choice, or a universal learner path.

## Resource addresses in the present repository

| Address | Resource | What it contributes | Boundary |
| --- | --- | --- | --- |
| Original Slearn vision | `docs/SLEARN_ORIGINAL_VISION.md` | Direct source for the learning and perspective-path grammar | Source intent is not proof or an executed return |
| Curvature source packet | `framework/source-closure-primitives.json` | Deterministic `PATH` state for declared perspective/WHY/goal translations | No material, attempt, review, receipt, or successor is present |
| Slearn map product | `docs/SLEARN_EDUCATION_MODEL.md` | Product relation for perspective, belief/value, WHY, goal, and zoom | No efficacy or runtime-closure claim |
| Relational closure unification | `Slearn/RelationalClosureUnification.lean` | Formal equivalence of closure, true translation, and natural choice under supplied hypotheses | Does not choose the real question family |
| Transactional truth equality | `Slearn/CompletionInTranslationalTruthEquality.lean` | Formal separation of answer-preserving completion from local/global, sign, and endpoint markers | The answer language and translations are supplied, not discovered |
| Partition aggregate closure | `Slearn/PartitionAggregateClosure.lean` | Finite current-closure and successor-question calculation | Not continuous physics or a validated learner discriminator |
| Gödel/Tarski boundary | `Slearn/GodelTarskiRelativeClosureBoundary.lean` | Bounded diagonal and local/global truth boundary models | Not a formalization, refutation, or bypass of the named metatheorems |
| Closure hull runtime | `scripts/project-closure-hull.mjs` | A deterministic prospective-branch / OPEN-remainder projection | Not an independent return or external review |
| Natural-rhythm reading | `docs/NATURAL_RHYTHM_CLOSURE.md` | An interpretive connection between triangle, recentering, and return | Not an established natural or physical law |

The full fields for these entries are in `framework/notology.json`. Do not add
a raw private note to this table: add a privacy-preserving source anchor in
the [research ledger](SLEARN_CLOSURE_RESEARCH_LEDGER.md) first.

## Admission rules

1. Give a new term a relative closure address before using it as a framework
   primitive. A name without a frame, relation, depth, boundary, and next
   opening is not admitted as repository infrastructure.
2. Preserve the claim kind while translating a term across source prose, Lean,
   runtime, documentation, and UI. A translation can change presentation; it
   cannot silently upgrade evidence.
3. State the depth of every apparent closure. A scalar, a finite route, a UI
   projection, a theorem over a declared family, and a reviewed human episode
   answer different questions.
4. Keep literal distinction available. Local/global, language/definition,
   goal/perspective, and form/aggregate need not be identical for their
   declared answers to translate.
5. Preserve residue and next opening. A recorded return is a continued
   relation, not a terminal truth badge. A state with no named remainder must
   be treated as incomplete or `NOT_APPLICABLE`.
6. Keep the physical, social, moral, and metaphysical readings outside the
   formal and runtime surfaces until an independently stated model and method
   supports them.

## Relationship to the repository frame

`NOTOLOGY` is registered as a cross-frame layer in
[`../framework/registry.json`](../framework/registry.json). It is not a ninth
temporal stage after `RETURN`, and it is not a UI. It is the address system
that prevents every frame from being mistaken for every other frame:

```text
OPEN / PERSPECTIVE / CURVATURE / TRANSLATION / INTERACTION
VERIFICATION / ADMISSION / RETURN / PROJECTION
                         ↓
            NOTOLOGY: address, depth, scope, next opening
```

This is why the refactor does not turn the new synthesis into a fixed
“theory of everything.” It organizes the relations that are actually named,
the closures that are actually proved or recorded, and the questions that are
still open.
