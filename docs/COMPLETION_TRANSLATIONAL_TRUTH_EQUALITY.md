# Completion in translational truth equality

[`CompletionInTranslationalTruthEquality.lean`](../Slearn/CompletionInTranslationalTruthEquality.lean)
re-derives a bounded form of the closure distinction from the current source
and repository contracts:

\[
\boxed{
\text{completion}
=
\text{transport of every answer in a declared closure question-language}.}
\]

Each `Presentation` separates:

- `truth`: a Boolean answer for every declared question; and
- `isolated`: basis (`local`/`global`), trajectory
  (`negative`/`positive`), and endpoint (`zero`/`infinity`) markers.

`Completion` is a transport of every truth answer between two presentations;
`Completable` means that such a transport exists. The module proves that this
relation is reflexive, symmetric, and transitive; that any two completion
records carry the same answer transport; and that it is strictly coarser than
literal presentation identity.

Every such completion also instantiates
`TransactionalCompletionEvaluation.CompletionTransaction`: the two answer
functions become frozen frames, their answer equality supplies both directions
of the transaction, and `completion_closes_in_transactional_adapter` proves
closure in the shared admitted-translation witness.

It also proves that retagging either presentation leaves completion unchanged,
and that completion depends only on the two truth-answer functions. Every
propositional formula built from the closure questions is preserved by a
completion and unchanged by retagging.

## What the finite model separates

The finite model gives two concrete counterexamples.

\[
\begin{aligned}
\text{same basis/sign/endpoint} &\not\Rightarrow \text{completable},\\
\text{local, negative, 0}\quad\text{vs.}\quad
\text{global, positive, }\infty &\not\Rightarrow \text{not completable}.
\end{aligned}
\]

The second pair is completable because its supplied truth answers agree, while
each of its three markers remains provably distinct. Consequently no predicate
of the marker pair alone decides completion in that finite model. Agreement on
one selected question is also insufficient for whole-language completion.

## Scope boundary

This is not a proof that `0 = ∞`, that a local basis is a global basis, or that
negative and positive trajectories are identical. The module proves the
opposite for its marker values. It also does not select the closure
question-language, discover a contact relation, establish empirical truth, or
create an independent return. Those remain open work governed by the source
ledger and replayable-audit protocol.
