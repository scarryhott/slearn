# Recalculation against translated truth answers

[`RecalculationAgainstTranslatedTruthAnswers.lean`](../Slearn/RecalculationAgainstTranslatedTruthAnswers.lean)
re-derives the closure engine behind the reported recalculation in a bounded,
source-honest form.

At a frozen level \(n\), it defines:

\[
x =_{C_n} y
\quad\Longleftrightarrow\quad
\forall q\in Q_n,\quad A_n(q,x)=A_n(T_n(q),y).
\]

The module proves reflexivity under identity translation, symmetry under an
involutive translation, and transitivity along composed translations. It then
extends the question-language by a supplied discriminator \(D\) and proves:

\[
x =_{C_{n+1}} y
\quad\Longleftrightarrow\quad
x =_{C_n} y\ \land\ D(x)=D(y).
\]

So a current truth equality plus an explicitly supplied perspectival
asymmetry reopens at the next level. The theorem is deliberately conditional:
`PerspectiveAsymmetry` carries the discriminator and its separating proof. It
does not infer a warranted new question merely from \(x\ne y\).

## Finite recalculations

The included ball/hair model has a frozen level that cannot see the Boolean
route distinction. Therefore its two presentations are truth-equal and
unitary-quotient equal while remaining literally and route-wise distinct. The
lifted marker is distinct, and `ballHairResidue = 2` is a finite witness
readout. Adding the route discriminator separates the same pair at the
successor language.

The zero/infinity model similarly keeps endpoint, quantity, locality, and
orientation markers distinct while its frozen truth answers agree. It then
proves that this translated truth equality closes through the existing
transactional `AdmittedTranslation` adapter. It never proves ordinary
\(0=\infty\).

## Open boundary

The unavailable NRRF663/664 report also describes numerical physics,
predual, maze, fractal, Ricci, Chaitin, and Topos/Turing instances. Those
Lean modules were not present in the repository, so this re-derivation does
not register their formulas or conclusions as verified work. The choice of
questions, supplied discriminators, contact relation, external evidence, and
independent return all remain OPEN under the source ledger.
