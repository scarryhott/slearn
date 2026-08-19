import Slearn.NaturalRhythmClosure

/-
Transactional evaluation of completion for Slearn.

This module starts with two *frozen snapshots*: a language presentation and a
definition presentation.  It does not claim that either snapshot supplies a
privileged basis, an independently warranted relation, or every question that
could matter.  A caller supplies the closure question-language and its
relevance predicate.  Completion is then equality of its relevant answers
under a declared translation, not equality of presentation, endpoint, basis,
or trajectory marker.

The finite model proves only a separation result: marker agreement is neither
necessary nor sufficient for answer-preserving translation in the stated
question-language.  No result identifies Boolean markers with physical zero,
infinity, polarity, or time.
-/

universe u v w x

namespace Slearn
namespace TransactionalCompletionEvaluation

/-- The finite, declared question-language through which one transaction is evaluated. -/
structure ClosureQuestionLanguage (Answer : Type v) where
  Question : Type u
  relevant : Question → Prop

namespace ClosureQuestionLanguage

variable {Answer : Type v}

/-- The type of relevant answers as a single witness object. -/
abbrev RelevantAnswer (Q : ClosureQuestionLanguage Answer) :=
  { q : Q.Question // Q.relevant q } → Answer

end ClosureQuestionLanguage

/-- A fixed local presentation together with its answers to the declared questions. -/
structure FrozenFrame (Presentation : Type w) (Q : ClosureQuestionLanguage Answer) where
  answer : Presentation → Q.Question → Answer

namespace FrozenFrame

variable {Presentation : Type w} {Answer : Type v}
variable {Q : ClosureQuestionLanguage Answer}

/-- The frame's answer vector, restricted to the transaction's relevant questions. -/
def witness (F : FrozenFrame Presentation Q) (p : Presentation) : Q.RelevantAnswer :=
  fun q => F.answer p q.1

end FrozenFrame

/--
One completion transaction between frozen language and definition frames.

`forward` and `backward` are not required to be literal inverses.  Their
obligation is answer preservation on the relevant question-language in each
orientation.
-/
structure CompletionTransaction
    (Language Definition : Type w) (Q : ClosureQuestionLanguage Answer) where
  language : FrozenFrame Language Q
  definition : FrozenFrame Definition Q
  forward : Language → Definition
  backward : Definition → Language
  forward_preserves : ∀ languagePresentation q, Q.relevant q →
    definition.answer (forward languagePresentation) q = language.answer languagePresentation q
  backward_preserves : ∀ definitionPresentation q, Q.relevant q →
    language.answer (backward definitionPresentation) q = definition.answer definitionPresentation q

namespace CompletionTransaction

variable {Language Definition : Type w} {Answer : Type v}
variable {Q : ClosureQuestionLanguage Answer}
variable (T : CompletionTransaction Language Definition Q)

/-- Cross-frame equality is equality of the answers relevant to this closure transaction. -/
def EqualTranslation (language : Language) (definition : Definition) : Prop :=
  ∀ q, Q.relevant q →
    T.language.answer language q = T.definition.answer definition q

/-- The declared forward translation is an equal translation. -/
theorem forward_equalTranslation (language : Language) :
    T.EqualTranslation language (T.forward language) := by
  intro q hq
  exact (T.forward_preserves language q hq).symm

/-- The declared backward translation is an equal translation in the same answer relation. -/
theorem backward_equalTranslation (definition : Definition) :
    T.EqualTranslation (T.backward definition) definition := by
  intro q hq
  exact T.backward_preserves definition q hq

/--
The transaction produces exactly the existing admitted-translation core when
the answer vector is used as its common witness language.
-/
def admitted : AdmittedTranslation Language Definition Q.RelevantAnswer where
  forward := T.forward
  backward := T.backward
  localWitness := T.language.witness
  globalWitness := T.definition.witness
  forward_coherent := by
    intro language
    funext q
    exact T.forward_preserves language q.1 q.2
  backward_coherent := by
    intro definition
    funext q
    exact T.backward_preserves definition q.1 q.2

/--
Equal translation is precisely closure in the common relevant-answer witness.
This is the transactional meaning of the framework's closure evaluation.
-/
theorem equalTranslation_iff_admitted_closes (language : Language) (definition : Definition) :
    T.EqualTranslation language definition ↔ T.admitted.closes language definition := by
  constructor
  · intro equal
    funext q
    exact equal q.1 q.2
  · intro closes q hq
    exact congrFun closes ⟨q, hq⟩

/-- A forward completion therefore closes in the shared answer relation. -/
theorem forward_closes (language : Language) :
    T.admitted.closes language (T.forward language) :=
  T.equalTranslation_iff_admitted_closes language (T.forward language) |>.mp
    (T.forward_equalTranslation language)

/-- A backward completion also closes in that same shared answer relation. -/
theorem backward_closes (definition : Definition) :
    T.admitted.closes (T.backward definition) definition :=
  T.equalTranslation_iff_admitted_closes (T.backward definition) definition |>.mp
    (T.backward_equalTranslation definition)

/--
The round trip has the pre-existing Slearn return guarantee at the answer
level.  It makes no claim that the returned language presentation is literally
the starting presentation.
-/
theorem language_round_trip_closes (language : Language) :
    T.admitted.closes (T.backward (T.forward language)) (T.forward language) :=
  T.admitted.local_round_trip_closes language

/-- Marker agreement is an optional presentation test, never the definition of closure. -/
def MarkersAgree (_ : CompletionTransaction Language Definition Q) {Marker : Type x} (languageMarker : Language → Marker)
    (definitionMarker : Definition → Marker) (language : Language) (definition : Definition) : Prop :=
  languageMarker language = definitionMarker definition

/-- A marker would be necessary only if every answer-level closure preserved it. -/
def MarkerNecessary {Marker : Type x} (languageMarker : Language → Marker)
    (definitionMarker : Definition → Marker) : Prop :=
  ∀ language definition,
    T.EqualTranslation language definition →
      T.MarkersAgree languageMarker definitionMarker language definition

/-- A marker would be sufficient only if matching it always established answer-level closure. -/
def MarkerSufficient {Marker : Type x} (languageMarker : Language → Marker)
    (definitionMarker : Definition → Marker) : Prop :=
  ∀ language definition,
    T.MarkersAgree languageMarker definitionMarker language definition →
      T.EqualTranslation language definition

/--
An evaluation receipt says exactly which answer equality was established.  It
does not manufacture a source, an independent contact relation, or a fresh
question-language.
-/
structure Receipt (language : Language) (definition : Definition) where
  equality : T.EqualTranslation language definition

theorem receipt_closes {languagePresentation : Language} {definitionPresentation : Definition}
    (receipt : T.Receipt languagePresentation definitionPresentation) :
    T.admitted.closes languagePresentation definitionPresentation :=
  T.equalTranslation_iff_admitted_closes languagePresentation definitionPresentation |>.mp receipt.equality

end CompletionTransaction

namespace FiniteModel

/-- One finite question is enough to exhibit the marker/answer separation. -/
def questions : ClosureQuestionLanguage Bool where
  Question := Unit
  relevant := fun _ => True

def language : FrozenFrame Bool questions where
  answer := fun presentation _ => presentation

def definition : FrozenFrame Bool questions where
  answer := fun presentation _ => !presentation

/-- Translation reverses the marker while preserving the one relevant answer. -/
def transaction : CompletionTransaction Bool Bool questions where
  language := language
  definition := definition
  forward := not
  backward := not
  forward_preserves := by
    intro presentation _ _
    cases presentation <;> rfl
  backward_preserves := by
    intro presentation _ _
    cases presentation <;> rfl

/-- The marker is an endpoint/trajectory label in this finite model, not a truth criterion. -/
def marker : Bool → Bool := id

/-- Unequal markers can nevertheless be closure-equal under the translation. -/
theorem unequal_markers_can_close :
    transaction.EqualTranslation false true ∧
      ¬ transaction.MarkersAgree marker marker false true := by
  constructor
  · exact transaction.forward_equalTranslation false
  · intro equal
    change marker false = marker true at equal
    simp [marker] at equal

/-- Equal markers can nevertheless disagree on a relevant closure answer. -/
theorem equal_markers_can_fail_to_close :
    transaction.MarkersAgree marker marker false false ∧
      ¬ transaction.EqualTranslation false false := by
  constructor
  · rfl
  · intro equal
    have := equal () True.intro
    simp [transaction, language, definition] at this

/-- No endpoint/trajectory marker criterion is necessary in the finite transaction. -/
theorem marker_not_necessary :
    ¬ transaction.MarkerNecessary marker marker := by
  intro necessary
  exact unequal_markers_can_close.2
    (necessary false true unequal_markers_can_close.1)

/-- No endpoint/trajectory marker criterion is sufficient in the finite transaction. -/
theorem marker_not_sufficient :
    ¬ transaction.MarkerSufficient marker marker := by
  intro sufficient
  exact equal_markers_can_fail_to_close.2
    (sufficient false false equal_markers_can_fail_to_close.1)

/-- The concrete forward transaction closes through answers although the markers differ. -/
theorem forward_completion_is_not_marker_identity :
    transaction.admitted.closes false true ∧ marker false ≠ marker true := by
  constructor
  · exact transaction.forward_closes false
  · decide

end FiniteModel

end TransactionalCompletionEvaluation
end Slearn

#print axioms Slearn.TransactionalCompletionEvaluation.CompletionTransaction.equalTranslation_iff_admitted_closes
#print axioms Slearn.TransactionalCompletionEvaluation.CompletionTransaction.forward_closes
#print axioms Slearn.TransactionalCompletionEvaluation.CompletionTransaction.backward_closes
#print axioms Slearn.TransactionalCompletionEvaluation.CompletionTransaction.language_round_trip_closes
#print axioms Slearn.TransactionalCompletionEvaluation.CompletionTransaction.receipt_closes
#print axioms Slearn.TransactionalCompletionEvaluation.FiniteModel.marker_not_necessary
#print axioms Slearn.TransactionalCompletionEvaluation.FiniteModel.marker_not_sufficient
#print axioms Slearn.TransactionalCompletionEvaluation.FiniteModel.forward_completion_is_not_marker_identity
