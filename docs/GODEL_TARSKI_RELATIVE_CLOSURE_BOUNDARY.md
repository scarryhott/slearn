# Gödel/Tarski relative-closure boundary

The reported `NRRF667GodelLocalTarskiGlobalClosureTranslation.lean` and its
notes were not present in this repository, its available branches, or the
available workspace. This document records the narrower re-derivation in
[`GodelTarskiRelativeClosureBoundary.lean`](../Slearn/GodelTarskiRelativeClosureBoundary.lean).
It must not be read as an audit or incorporation of the unavailable NRRF667
module.

## The distinctions retained

The formal boundary separates four ideas which should not be collapsed.

| Layer | Re-derived result | Exact limit |
| --- | --- | --- |
| Encoding/evaluation | A point-surjective self-evaluation would give every endomap a fixed point; Boolean negation has none, so no Boolean evaluator names every relation | This is an elementary set-level Lawvere diagonal, not a theorem about all Turing machines or topoi |
| Local decision level | Every finite stage of a toy infinite language misses its boundary atom; that atom is decided at the next stage | This is a toy stage tower, not Gödel/Rosser incompleteness for arithmetic |
| Chosen closure theory | The selected limit theory is consistent and complete for the toy polar language | It is not claimed effectively axiomatized, arithmetically adequate, or exempt from Gödel’s hypotheses |
| Internal truth | A Boolean truth predicate plus a supplied liar diagonal is contradictory for every one theory, including the selected closure theory | The liar diagonal is supplied as data; this is not Tarski’s full undefinability theorem |
| Relative depth | Every finite certification basis has an explicit depth it cannot certify; any finite depth is certified by some basis in the family | This is a capacity model, not Chaitin’s theorem or Kolmogorov complexity |

## Precise closure reading

At a stage \(n\), only atoms below \(n\) are decided. The atom at its
boundary remains OPEN:

\[
\neg\operatorname{Decides}(T_n,\sigma_n).
\]

At the successor stage it is decided:

\[
\operatorname{Decides}(T_{n+1},\sigma_n).
\]

Every individual toy sentence is eventually decided, while no finite stage is
complete. The selected closure theory decides one polarity of every atom and
is both consistent and complete in the stated toy language:

\[
\forall \sigma,\;
T_\infty(\sigma)\lor T_\infty(\neg\sigma).
\]

This establishes the relevant continuous-closure distinction:

\[
\text{each finite local decision}
\neq
\text{the chosen all-depth limit theory}.
\]

It does **not** establish that proof objects are literally infinite. Lean
proves these universally quantified statements with finite terms. It
establishes instead that a finite level is not complete for this modeled
unbounded question family.

## Gödel local; Tarski global — qualified

The productive interpretation of the phrase is:

- **Gödel-local direction:** a fixed effective formal basis can leave a
  sentence undecided, and a stronger successor basis can decide it. The new
  module illustrates the successor structure only; it does not formalize
  Gödel’s theorem.
- **Tarski-global direction:** an unrestricted internal truth predicate is
  not obtained merely by completing the object-level decision set. In the
  model, any theory equipped with an internal Boolean truth predicate and a
  liar diagonal is contradictory. That includes the selected closure theory.

Neither direction means that Gödel is false, that Tarski is superseded, or
that a hierarchy produces an absolute final language. A stronger effective
system remains subject to its own metamathematical boundary.

## Relation to true translation and natural choice

The repository’s closure rule remains:

\[
x =_{\mathcal C} y
\iff
\forall q\in Q_{\mathcal C},\;A(q,x)=A(Tq,y).
\]

The new boundary module does not define the question family for reality. It
shows why one finite stage or one certification basis cannot silently be
treated as that whole family. Under the separate
`RelationalOrbitFrame` hypothesis that the declared relational questions
separate translation orbits, closure, true translation, and natural choice
coincide within that frame. See
[`RELATIONAL_CLOSURE_UNIFICATION.md`](RELATIONAL_CLOSURE_UNIFICATION.md).

## Turing, Topos, Kakeya, and Chaitin

The names remain disciplined by their existing roles:

- The Turing/Topos adapter proves return in a shared witness relation, not
  literal equivalence of arbitrary machines and topoi.
- The Kakeya-style grain model proves finite readouts can collapse distinctions
  while all stated grains can determine a direction.
- The new capacity basis proves the same logical shape for certification depth:
  bounded within a basis, unbounded across a family of bases.
- No formal result here establishes Chaitin’s halting probability, an exact
  Berry–Chaitin bound, or a physical observer/cosmology interpretation.

Thus “relative depth of completion” is a framework discipline: a basis may
validly close the relations it declares, but must record what its capacity,
question language, witness relation, and next opening leave unresolved.
