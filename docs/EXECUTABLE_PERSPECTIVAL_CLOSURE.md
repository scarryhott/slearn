# Executable perspectival closure

## What “interactive closure translation” means here

The UI is not a closure translation merely because it draws a triangle or
because a person can type a perspective, a WHY, and a goal. It becomes one
only when interaction changes the same relation through an ordered state
transition:

```text
P (local perspective)
  -- contract through WHY/bridge --> G (global goal reading)
  -- reopen through the same bridge --> P~ (re-read local perspective)
  -- record reviewed return after comparison --> Ω + P' (residue and successor)
  -- continue --> next open perspective, carrying Ω
```

`P~` is not asserted to be literally `P`, and `P'` is explicitly recorded as
changed. `Ω` is not a score or a decorative value. It is the persisted record
of the source anchor and claim, concrete material, bridge, attempt,
counter-reading, comparison method, review, receipt, and changed successor
that distinguishes a reviewed return from an unexecuted or different one.

## Runtime behavior

`ui/app/closureRuntime.ts` stores an `Interaction.machine` for each trace:

- `open` has local perspective, WHY, goal, and possibly bridge evidence, but
  no completed translation.
- `contracted` contains the executed forward goal record. Only this phase can
  display the contracted projection.
- `reopened` contains the executed reciprocal local re-reading. Only this
  phase can accept a return.
- `returned` contains a **recorded** residue and successor perspective. It
  requires concrete material, an attempt, a counter-reading, a stated
  comparison method, a review, a receipt, and a changed successor. Only this
  phase can display the Ω point and seed another relation.

The controls execute those transitions; they are not orientation toggles.
Changing a field that determines translation clears the executed state. A
return is also invalidated when its material, attempt, counter-reading,
comparison, review, receipt, or successor changes.
This prevents completed-looking records from being silently reused after their
meaning has changed.

## Formal counterpart

[`NRRF655ExecutablePerspectivalClosureEpisode.lean`](../Slearn/NRRF655ExecutablePerspectivalClosureEpisode.lean)
defines `OpenPerspective`, `ContractedPerspective`, `ReopenedPerspective`, and
`ReturnedPerspective`. Its constructors make the ordering structural:

1. `OpenPerspective.contract` computes the forward translation.
2. `ContractedPerspective.reopen` computes the reciprocal translation.
3. `ReopenedPerspective.commitReturn` requires a return input with a changed
   successor and closure witness.
4. `ReturnedPerspective.nextOpening` makes that successor the next local
   opening and preserves its residue.

The checked results show that both forward and reopened states close in the
admitted witness language, the retained residue differs from its origin, the
successor closes with the contracted goal, and continuation keeps exactly that
residue.

## Important boundary

The TypeScript runtime mirrors this state discipline and is exercised by
`npm run test:closure`, but it is not extracted from Lean and no theorem
currently proves their implementation equality. The runtime records a
learner’s declared source, bridge, attempt, counter-reading, comparison, and
review; it does not determine whether they are true, sufficient, natural,
independently verified, or educationally effective. Those questions require
an evidence protocol. The packet and its source questions are specified in
[`SLEARN_CLOSURE_RESEARCH_LEDGER.md`](SLEARN_CLOSURE_RESEARCH_LEDGER.md).
