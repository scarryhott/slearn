# Partition aggregate closure

[`PartitionAggregateClosure.lean`](../Slearn/PartitionAggregateClosure.lean) is a
finite re-derivation of the closure-relevant core of the reported
partition-wave scenario. The reported
`NRRF665PartitionWaveClosureUnitaryCurvature.lean` module was not available in
this repository or its available remote branches, so this file does not
register that report as an existing result.

## The finite calculation

The model has four retained orientations, represented by integer coordinate
readouts:

\[
1,\quad i,\quad -1,\quad -i.
\]

Its canonical four-block presentation has aggregate

\[
1+i-1-i=(0,0).
\]

`quadrature_aggregate_zero` proves that calculation. `rearranged` is a second
placement of those four forms. `rearranged_aggregate_zero` and
`same_scalar_aggregate` prove it has the same scalar aggregate, while
`first_phase_separates` and `presentations_are_distinct` prove that its
retained first-position form differs from the canonical placement.

This is the relevant distinction:

\[
\operatorname{aggregate}(\Pi_1)=\operatorname{aggregate}(\Pi_2)
\quad\not\Rightarrow\quad
\Pi_1=\Pi_2.
\]

It is not a claim that an aggregate is false. At the scalar language it is a
valid, explicitly bounded truth reading.

## Closure and reopening

`scalarLanguage` has exactly one current question and reads only the scalar
aggregate. `scalar_truth_equal` therefore proves

\[
\Pi_1 =_{C_n} \Pi_2.
\]

`scalar_truth_closes_in_transaction` connects that equality to the existing
transactional `AdmittedTranslation` adapter: the aggregate agreement is a
closure at this declared language, rather than a UI or narrative assertion.

The retained `firstPhase` is then supplied as a successor discriminator.
`scalar_closure_reopens` proves the exact extension result:

\[
\Pi_1 =_{C_n} \Pi_2,
\qquad
\Pi_1 \ne_{C_{n+1}} \Pi_2.
\]

The new question is not guessed from scalar equality. It is represented by
`phaseAsymmetry`, which carries both the question and evidence that it
separates the two particular presentations. This is the same discipline as
the broader Slearn closure framework: a new opening needs a named relation,
not an arbitrary visual or algorithmic distinction.

`continuation_not_determined_by_aggregate` strengthens the finite statement.
No function from this scalar aggregate alone can recover the next
first-position phase reading. Thus the aggregate legitimately closes its
current question while not determining the next question-language:

\[
\text{scalar closure} \;\not\Rightarrow\; \text{complete continuation}.
\]

## Finite turn

`Phase.turn` rotates the four finite orientations; `Phase.turn_four` and
`fold_four` prove its four-step return. `fold_moves_quadrature` confirms that
this return is not a frozen presentation. The return is a finite cyclic fact,
not evidence of a continuous orbit.

`partition_aggregate_closure_scenario` bundles the model's precise claims:

1. scalar translated-truth equality;
2. literal distinction of the retained presentations;
3. reopening after the supplied phase question;
4. failure of aggregate-only continuation; and
5. four-fold return of the finite orientation operation.

## Boundaries

The module proves facts only about a four-element orientation datatype,
integer-pair aggregation, and the existing translated-question-language
model. In particular, it does **not** prove or claim:

- a physical wave equation, quantum mechanics, spacetime curvature, matter,
  dark matter, time, holonomy, or a Kakeya construction;
- a continuous `U_t = e^{it}` action or non-finitude of proof;
- that scalar aggregation identifies all meaningful distinctions in a learner
  episode; or
- that the chosen `firstPhase` discriminator is warranted for any actual
  person, source, or Slearn map.

Those are separate research questions. An actual Slearn packet still requires
source anchor, perspective/WHY/goal relation, attempt, counter-reading,
comparison, review, receipt, and a successor before a returned learner state
can be recorded.
