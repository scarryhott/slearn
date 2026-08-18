# Perspectival-curvature closure primitives

This document records the executable repository contract derived from the
direct 2026 Slearn source specification. It is neither a new metaphysical
claim nor a claim that the foundational source has completed a learner
interaction. The source enters as the first `PATH`: it specifies a relation
that can be translated and examined, while its practical return remains open.

## The primitive closure

[`PerspectivalCurvatureClosurePrimitives.lean`](../Slearn/PerspectivalCurvatureClosurePrimitives.lean)
starts before the older forward/return episode module. Its primitive record is
not a generic graph node. It requires exactly the source elements:

```text
source anchor + claim + observation
  → perspective + belief/value limit + goal limit + WHY
  → semantic explanation + operative explanation + definition
  → forward path + counter-path in one declared curvature relation
  → one admitted local/global translation and its witness language
```

`curves` is a caller-supplied relation from belief, goal, WHY, and path. This
is intentional: the repository has no certified way to calculate a learner's
psychological curvature or a physical curvature from prose. It instead
requires the relation to be named before a path can be treated as part of the
packet. The same relation must contain both the forward and counter-path.

The perspective–WHY–goal triangle is therefore bounded by belief/value and
goal limits rather than drawn as an independent UI motif. `semanticExplanation`
and `operativeExplanation` must both present the selected definition and WHY,
which preserves the source's language/definition flip rather than silently
collapsing the lesson to one sentence.

## From path to nonterminal admission

The formal sequence is:

```text
CurvaturePrimitives
  → DeclaredInteraction (attempt; forward and counter paths retained)
  → ReviewedInteraction (material; counter-reading; comparison; review)
  → ContinuedAdmission (receipt; changed successor; next relation)
  → recorded return and inherited next opening
```

`ContinuedAdmission` is deliberately the only constructor that can create the
older predecessor-typed return input. It has `nextRelation` as a mandatory
field. The checked result `has_further_relation` therefore says only that a
recorded admission carries a supplied successor relation, while
`successor_is_not_source_perspective` says the returned successor is not a
literal replay in the stated model.

It does **not** prove that a supplied review is adequate, the source claim is
true, the relation is natural, the new relation is meaningful, or any learner
has changed. Those remain `VERIFICATION` / `OPEN` obligations in the
[research ledger](SLEARN_CLOSURE_RESEARCH_LEDGER.md).

## Deterministic source run

[`framework/source-closure-primitives.json`](../framework/source-closure-primitives.json)
contains a privacy-preserving paraphrase of the current direct source as the
initial packet. Run:

```sh
node scripts/run-source-closure.mjs
```

The expected result is `PATH`, not `RETURNED (RECORDED)`. The source supplies
the perspective, limits, WHY, paired presentations, paths, and inverse bridge;
it does not supply a real executed attempt, material, comparison, review,
receipt, changed successor, or next relation. The runner therefore makes the
boundary observable instead of inventing a completion from the foundational
text.
