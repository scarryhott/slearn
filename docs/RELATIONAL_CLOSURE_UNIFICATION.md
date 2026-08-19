# Relational closure unification

This document is the repository’s single framing of the current Slearn
formal layers. It does not replace the source ledger, and it does not turn the
models into a theorem about education, consciousness, physics, Gödel,
Tarski, Chaitin, Topos theory, or Turing machines in general.

Its governing distinction is:

\[
\boxed{
\text{a finite evaluation is a reading at a declared depth};
\qquad
\text{closure is the relation maintained across admitted translations.}
}
\]

## One common contract

For presentations \(x,y\), an admitted question family \(Q\), translated
questions \(T\), and answers \(A\), the repository uses:

\[
x =_{\mathcal C} y
\quad\Longleftrightarrow\quad
\forall q\in Q,\;A(q,x)=A(Tq,y).
\]

This is **not** literal identity, equality of endpoint labels, equality of
local/global markers, a probability, or an optimisation score. It is
answer-preserving translation at the named closure language.

`RelationalOrbitFrame` adds the complementary orbit reading. If a supplied
translation family preserves every declared relational answer, and those
answers separate its translation orbits, Lean proves:

\[
\boxed{
\text{closure relation}
\iff
\text{true translation}
\iff
\text{natural choice}.}
\]

Here “natural choice” means only a relation-preserving return in that stated
frame. The proof does not choose the translation family, prove that the
questions are exhaustive in reality, or elevate a social, physical, or moral
preference into a theorem.

The precise formal statement is in
[`RelationalClosureUnification.lean`](../Slearn/RelationalClosureUnification.lean).

## Relative depth of completion

Completion has different depths which must not be collapsed into one status.

| Depth | What is compared | What a positive result means | What remains open |
| --- | --- | --- | --- |
| Question depth | Answers to a declared language \(Q_n\) | Presentations close at \(Q_n\) | A successor question can separate them |
| Translation depth | Local/global, language/definition, or Topos/Turing orientations | A common witness is preserved | Presentations and routes can remain distinct |
| Resolution depth | A finite grain or zoom \(n\) | The selected readout agrees | A finer grain can separate directions |
| All-depth closure | Every stated refinement | The model’s continuous/limit condition holds | The model may still omit relevant real questions |
| Evidence depth | Source, attempt, counter-reading, method, review, receipt, successor | A return is recorded and reviewable | Independent empirical adequacy remains separate |

The `RelativeCompletionDepth` structure represents the first and fourth rows:

\[
x\equiv_n y
\iff
R_n(x)=R_n(y),
\qquad
x\equiv_\infty y
\iff
\forall n,\;x\equiv_n y.
\]

“Continuous” in the current code means all members of a stated refinement
tower, not an automatically supplied real-number topology. A finite Lean term
can prove a proposition quantified over all depths; that does not give a
finite observer access to all of those depths.

## The partition/fold calculation

The finite orientation model is the repository’s current concrete calculation:

\[
\Pi_A=(1,i,-1,-i),
\qquad
\Pi_B=(i,1,-i,-1).
\]

Both scalar aggregates are zero:

\[
Z(\Pi_A)=Z(\Pi_B)=0.
\]

At the scalar question-language they therefore close. A retained
first-position phase is supplied as a successor question and separates them.
The module proves:

\[
\Pi_A =_{C_n}\Pi_B,
\qquad
\Pi_A\ne_{C_{n+1}}\Pi_B,
\]

and proves that no function of the aggregate alone reconstructs that successor
phase. The quarter-turn fold visibly moves the presentation and returns after
four steps:

\[
U^4(\Pi)=\Pi.
\]

This realizes the minimal closure cycle:

```text
relative forms → scalar/contracted reading → retained relational difference
               → supplied next question → reopened closure language
```

It is a finite integer-coordinate calculation, not a physical wave equation,
quantum dynamics, or a proof of continuous non-finitude. See
[`PARTITION_AGGREGATE_CLOSURE.md`](PARTITION_AGGREGATE_CLOSURE.md).

## Turing, Topos, Kakeya, and Chaitin names

The repository gives each name one exact role.

| Reading | Formal role | Verified statement | Not established |
| --- | --- | --- | --- |
| Turing / Topos | Operational and contextual presentations | `encode` and `evaluate` return through a common witness relation | That arbitrary topoi and Turing machines are equivalent or definitionally identical |
| Kakeya grain | Resolution family | A positive finite grain can identify distinct directions; all stated grains can determine a direction | A mathematical Kakeya-set result |
| Chaitin | Token/residue vocabulary and an explicit boundary | Ordered aggregate may fail to determine route residue | A theorem about Chaitin’s halting probability or a numerical intelligence measure |
| Gödel / Tarski | Boundary vocabulary for fixed formal languages and their meta-level readings | A bounded diagonal/stage/liar model distinguishes local incompleteness, selected closure, and internal-truth obstruction | A formalization of either metatheorem, or that closure refutes, supersedes, or evades their scope |

The Turing/Topos adapter proves relational return:

\[
W(\operatorname{evaluate}(\operatorname{encode}(t)))=W(t),
\]

not literal equality of the two presentations. The Kakeya-style interface
expresses the depth distinction:

\[
\forall n>0,\;\exists d_1\ne d_2,
\operatorname{read}_n(d_1)=\operatorname{read}_n(d_2),
\]

while equality at every stated grain determines a direction. The Chaitin name
does not add an oracle: no finite aggregate or ordered trace is promoted to
complete information merely by that name.

## Slearn realization

The educational grammar is one translation packet, not a collection of
separate interfaces:

\[
\text{perspective}
\rightarrow
\text{belief/value}
\rightarrow
\text{WHY}
\rightarrow
\text{goal}
\rightarrow
\text{lesson/project/world}
\rightarrow
\text{returned perspective}^{\prime}.
\]

The operational reading is:

\[
\Gamma
\xrightarrow{Ch}
\text{goal / contracted reading}
\xrightarrow{Ka}
\Gamma^{\prime}
\xrightarrow{\mathrm{Diff}}
\Omega.
\]

`Ch` and `Ka` are contraction and reciprocal reopening; \(\Omega\) is the
retained relation-relative difference. A valid runtime projection can expose
these states, but cannot invent the source, bridge, WHY, attempt,
counter-reading, review, return, or successor that makes them admissible.

Thus the UI’s map, if used, is a recentering surface for the closure packet:

```text
perspective ↔ goal
language ↔ definition
Turing ↔ Topos
local ↔ global
prospective path ↔ returned experience
```

Each pair is a different orientation of a maintained relation. They are not
literal identity claims and should not become independent UI mechanics.

## What is now derivable

- Universal-relative completion is uniquely forced **after** its relative
  frame and admissibility contract are supplied.
- Local/global and language/definition can close through answer-preserving
  translation without marker or literal identity.
- A finite evaluation can be insufficient for a modeled all-depth property.
- A finite scalar/aggregate result can be a valid current closure while
  failing to determine the next relational question.
- A return can be relationally closed yet retain nonzero route, residue, or
  successor distinction.
- Slearn zoom is derivable only as the same contract/reopen/return operation
  when its runtime carries the required bridge and receipt data.

## What remains OPEN

- A continuous \(S^1\) action with a specified topology and a theorem that a
  chosen correlation family exactly separates its physical or educational
  orbits.
- A formal account of Gödel’s and Tarski’s metatheorems and a proof relating
  their exact hypotheses—not merely the bounded diagonal/stage/liar model—to
  this framework.
- Any conclusion that a particular physical wave, a person’s perspective,
  natural value, or educational path is warranted by the formal structures.
- Independent source-grounded learning episodes that satisfy the repository’s
  verification and return requirements.

The correct research direction is therefore not to declare a final global
closure. It is to extend the admitted question, translation, resolution, and
evidence families while preserving an auditable return into the next opening.
