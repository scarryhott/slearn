# Transactional completion evaluation

The present Slearn language, definitions, and formal adapters are finite,
frozen presentations. They are not the origin of a completed theory. This
document gives their narrower common evaluation rule:

\[
\boxed{
\text{transactional completion}
=
\text{equality of relevant relational answers under a declared translation}.
}
\]

[`TransactionalCompletionEvaluation.lean`](../Slearn/TransactionalCompletionEvaluation.lean)
introduces four layers.

1. A `ClosureQuestionLanguage` supplies a finite question type and an explicit
   relevance predicate. The model does not select the questions or claim that
   they are independently warranted.
2. A `FrozenFrame` gives a language or definition presentation its answers to
   those questions.
3. A `CompletionTransaction` supplies forward and return translations and
   requires each to preserve every relevant answer.
4. `EqualTranslation` compares a language presentation and a definition
   presentation only by those relevant answers. Its theorem
   `equalTranslation_iff_admitted_closes` identifies it with the existing
   `AdmittedTranslation.closes` relation, using the vector of relevant answers
   as the common witness.

Thus the existing closure core can evaluate a limited language/definition
transaction without asserting that their presentations, endpoint labels, or
local/global marker values are literally identical.

## Marker separation

The module's explicit Boolean example has one relevant question. The language
answers with its Boolean presentation, the definition answers with its
negation, and the declared translation negates the presentation. Lean proves:

\[
\begin{aligned}
\text{different markers} &\not\Rightarrow \text{failure of closure},\\
\text{same markers} &\not\Rightarrow \text{closure}.
\end{aligned}
\]

This is the formal scope of “not determined by local/global basis,
positive/negative trajectory, or \(0/\infty\) endpoint labels.” A marker is
only a caller-supplied presentation function. The model never identifies the
Boolean example with physical zero, infinity, polarity, time, or any external
system.

## Relation to the open program

This adapter deliberately does **not** decide the remaining decisive issue:
which relational contact/question-language is warranted, whether it was
independently generated, or whether a return is empirically independent. The
source pipeline therefore stays `PATH`, and the changing-axiometry protocol
stays `DESIGN_READY`. The replayable audit requires a lawful published
succession but does not supply the independent people, sources, experiments,
or fresh questions that a real audit would need.
