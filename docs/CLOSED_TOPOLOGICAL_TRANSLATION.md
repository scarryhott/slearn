# Closed Topological Translation Episodes

## Status and boundary

[`Slearn/ClosedTopologicalTranslation.lean`](../Slearn/ClosedTopologicalTranslation.lean)
is a machine-checked **episode model**. It extends the repository’s runtime
vocabulary without changing the universal-relative completion operator or its
uniqueness theorem.

The model proves consequences of explicitly supplied data. It does **not**
prove that a particular social interaction, learner attempt, optical path,
physical process, Chaitin construction, or Topos/Turing program has a return,
a nontrivial residue, or a new opening. Those require a concrete model and
evidence.

## The event before interpretation

The primitive carrier is an unprioritized reciprocal pair:

\[
[P_A\mid P_B].
\]

`ReciprocalPair` calls its fields `first` and `second`, not local and global.
It supports one structural operation:

\[
\sigma[P_A\mid P_B]=[P_B\mid P_A].
\]

Lean proves that this inversion is involutive:

\[
\sigma^2=\operatorname{id}.
\]

`OpenTranslationEpisode` holds the origin pair, the jointly extended pair,
two selected path values, their interaction, and an inverted pair with a proof
that it is the orientation swap of the extension. Before an explicit returned
witness it has status `open`.

This deliberately models

\[
[P_A\mid P_B]
\rightsquigarrow
(a_i,b_j)
\rightsquigarrow
[P_A'\mid P_B']
\rightsquigarrow
[P_B''\mid P_A'']
\]

without declaring either side independently complete or making inversion an
ontological reversal.

## Return is base recovery, not literal state equality

For a caller-selected function

\[
\operatorname{baseOf}:
\operatorname{Pair}(P)\to B,
\]

a `ReturnedTranslationEpisode` supplies

\[
\operatorname{baseOf}(R)=\operatorname{baseOf}(\mathcal C_0).
\]

This is the checked meaning of a returned topology in the module. It does
not require `R = C₀`, require either path to be invertible as a function, or
declare all successful histories identical.

The distinction is essential:

\[
\operatorname{forget}(\mathcal C_1)
\sim_{\mathrm{base}}
\mathcal C_0
\quad\not\Rightarrow\quad
\mathcal C_1
=
\mathcal C_0.
\]

Here the left side is represented by the caller’s `baseOf` relation; the
right side concerns the continuation field described below.

## Residue is a distinction between successful returns

The module does not postulate a number `Ω`. Instead, for arbitrary types
`Episode`, `Base`, and `Residue`, `ReturnDistinction` requires an alternative
episode such that

\[
\operatorname{recoveredBase}(e')
=
\operatorname{recoveredBase}(e)
\quad\land\quad
\operatorname{residueOf}(e')
\ne
\operatorname{residueOf}(e).
\]

Lean proves this supplies a comparator and that the residue coordinate cannot
be constant. Therefore the assertion

\[
\Omega_0\ne0
\]

is justified only after a model supplies both a comparison realization and a
specified coordinate in which they differ. The formal layer does not choose
whether that coordinate is trajectory lineage, route order, chirality, changed
WHY/goal relation, operational ordering, or something else.

## Closed to a new opening

`ClosedToNewOpening` is deliberately stronger than `ReturnedTranslationEpisode`.
It requires all of the following:

1. a returned episode;
2. a `ReturnDistinction` for that episode;
3. a successor pair whose `baseOf` value still recovers the origin; and
4. a continuation field that differs from the origin’s continuation field.

Only then does its checked status become `closedToNewOpening`:

\[
\boxed{
\mathcal C_0
\rightarrow
[P_A\mid P_B]
\rightarrow
(a_i,b_j)
\rightarrow
\sigma
\rightarrow
R
\rightarrow
\Omega_0
\rightarrow
\mathcal C_1
}
\]

with

\[
\operatorname{baseOf}(\mathcal C_1)
=
\operatorname{baseOf}(\mathcal C_0),
\qquad
\operatorname{continuationOf}(\mathcal C_1)
\ne
\operatorname{continuationOf}(\mathcal C_0).
\]

The four conditions prevent an implementation from issuing
`CLOSED_TO_NEW_OPENING` merely because a path finished or because a system
stored a value called `Ω`.

## Readings are caller-level projections

The same formal episode can be projected into domain vocabularies without
equating those vocabularies:

| Reading | Possible residue coordinate |
| --- | --- |
| Ball/hair | retained trajectory or lineage |
| Ellipse | relative route order or extension |
| Slearn | witnessed difference between prospective and returned WHY/goal relation |
| Topos/Turing | operational ordering retained beyond a contextual quotient |

These are design or research readings. The Lean module proves only the generic
episode properties above. The existing
[`NaturalRhythmClosure`](NATURAL_RHYTHM_CLOSURE.md) layer remains responsible
for admitted two-orientation translations and relative natural/dual/obstructed
positions. The existing universal-relative completion theorem remains the only
claim of closure-operator uniqueness.

## Runtime consequence for Slearn

A Slearn receipt needs more than a completion flag. For a status stronger than
`RETURNED_COMPLETE`, it must retain:

```text
origin pair and selected orientation
two attempted WHY/experience paths and their interaction
orientation inversion
returned-base witness
alternative successful realization / residue comparison
inherited continuation field
```

The Slearn residue is not a progress percentage. It is the inspectable
difference between a prospective learning relation and its returned relation.
If no returned witness exists, the episode remains `OPEN`; if a return exists
but no changed continuation field is evidenced, it is returned rather than
`CLOSED_TO_NEW_OPENING`.
