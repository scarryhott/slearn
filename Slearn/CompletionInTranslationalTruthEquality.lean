import Slearn.TransactionalCompletionEvaluation

/-
Completion in translational truth equality for Slearn.

This is a bounded re-derivation of the reported NRRF662 distinction.  A
presentation carries two separate kinds of data:

* `truth`: answers to one already-declared closure question-language; and
* `isolated`: local/global basis, negative/positive trajectory, and zero/infty
  endpoint markers.

Completion is the transport of every truth answer in that shared question
language.  The module proves that isolated markers are neither necessary nor
sufficient for completion in an explicit finite model.  It does not choose a
question-language, establish an independently warranted contact relation, or
identify any markers with physical objects or quantities.
-/

universe u

namespace Slearn
namespace CompletionInTranslationalTruthEquality

/-- A basis marker is a presentation label, not the equality criterion. -/
inductive Basis
  | local
  | global
  deriving DecidableEq, Repr

/-- A trajectory marker is a presentation label, not the equality criterion. -/
inductive Trajectory
  | negative
  | positive
  deriving DecidableEq, Repr

/-- An endpoint marker is a presentation label, not the equality criterion. -/
inductive Endpoint
  | zero
  | infinity
  deriving DecidableEq, Repr

/-- The isolated labels carried by a presentation. -/
structure IsolatedIdentification where
  basis : Basis
  trajectory : Trajectory
  endpoint : Endpoint
  deriving DecidableEq, Repr

/-- One presentation of truth answers plus its separate isolated labels. -/
structure Presentation (Question : Type u) where
  truth : Question → Bool
  isolated : IsolatedIdentification

namespace Presentation

variable {Question : Type u}

/-- Change all isolated labels without changing the truth answers. -/
def retag (isolated : IsolatedIdentification) (presentation : Presentation Question) :
    Presentation Question :=
  { presentation with isolated }

end Presentation

/-- A completion transports every answer in the already shared closure question-language. -/
structure Completion {Question : Type u} (left right : Presentation Question) where
  transport : ∀ question, left.truth question = right.truth question

namespace Completion

variable {Question : Type u} {left middle right : Presentation Question}

theorem refl (presentation : Presentation Question) : Completion presentation presentation where
  transport := fun _ => rfl

theorem symm (completion : Completion left right) : Completion right left where
  transport := fun question => (completion.transport question).symm

theorem trans (first : Completion left middle) (second : Completion middle right) :
    Completion left right where
  transport := fun question => (first.transport question).trans (second.transport question)

/-- Any two completion records carry the same answer transport. -/
theorem transports_equal (first second : Completion left right) :
    first.transport = second.transport := by
  funext question
  exact Subsingleton.elim _ _

end Completion

/-- Two presentations are completable exactly when at least one answer transport exists. -/
def Completable {Question : Type u} (left right : Presentation Question) : Prop :=
  Nonempty (Completion left right)

theorem completable_iff_nonempty_completion {Question : Type u}
    (left right : Presentation Question) :
    Completable left right ↔ Nonempty (Completion left right) :=
  Iff.rfl

/-- An explicit form of completion: all answers in the closure language agree. -/
theorem completable_iff_truth_answers_equal {Question : Type u}
    (left right : Presentation Question) :
    Completable left right ↔ ∀ question, left.truth question = right.truth question := by
  constructor
  · rintro ⟨completion⟩
    exact completion.transport
  · intro equal
    exact ⟨⟨equal⟩⟩

theorem completable_refl {Question : Type u} (presentation : Presentation Question) :
    Completable presentation presentation :=
  ⟨Completion.refl presentation⟩

theorem completable_symm {Question : Type u} {left right : Presentation Question} :
    Completable left right → Completable right left := by
  rintro ⟨completion⟩
  exact ⟨completion.symm⟩

theorem completable_trans {Question : Type u}
    {left middle right : Presentation Question} :
    Completable left middle → Completable middle right → Completable left right := by
  rintro ⟨first⟩ ⟨second⟩
  exact ⟨first.trans second⟩

/-- Completion ignores any replacement of either presentation's isolated labels. -/
theorem completable_retag {Question : Type u} (left right : Presentation Question)
    (leftTag rightTag : IsolatedIdentification) :
    Completable left right ↔
      Completable (left.retag leftTag) (right.retag rightTag) := by
  constructor
  · rintro ⟨completion⟩
    exact ⟨⟨completion.transport⟩⟩
  · rintro ⟨completion⟩
    exact ⟨⟨completion.transport⟩⟩

/-- Completion depends only on truth-answer functions, not on presentation labels. -/
theorem completable_marker_blind {Question : Type u}
    {left left' right right' : Presentation Question}
    (leftTruth : left.truth = left'.truth)
    (rightTruth : right.truth = right'.truth) :
    Completable left right ↔ Completable left' right' := by
  constructor
  · rintro ⟨completion⟩
    refine ⟨⟨?_⟩⟩
    intro question
    rw [← leftTruth, ← rightTruth]
    exact completion.transport question
  · rintro ⟨completion⟩
    refine ⟨⟨?_⟩⟩
    intro question
    rw [leftTruth, rightTruth]
    exact completion.transport question

/-- Marker agreement is a separate relation on isolated presentation labels. -/
def MarkersAgree {Question : Type u} (left right : Presentation Question) : Prop :=
  left.isolated = right.isolated

/-- A marker-only decision rule sees only the two isolated labels. -/
def MarkerOnlyCriterion {Question : Type u}
    (criterion : IsolatedIdentification → IsolatedIdentification → Prop) : Prop :=
  ∀ (left right : Presentation Question),
    Completable left right ↔ criterion left.isolated right.isolated

/-- Boolean propositional formulas over the closure questions. -/
inductive Formula (Question : Type u)
  | atom : Question → Formula Question
  | neg : Formula Question → Formula Question
  | and : Formula Question → Formula Question → Formula Question
  deriving Repr

/-- Interpret a formula from a presentation's truth answers. -/
def eval {Question : Type u} (presentation : Presentation Question) : Formula Question → Bool
  | .atom question => presentation.truth question
  | .neg formula => !(eval presentation formula)
  | .and first second => (eval presentation first) && (eval presentation second)

/-- A completion carries every propositional reading of the closure language. -/
theorem eval_translate {Question : Type u} {left right : Presentation Question}
    (completion : Completion left right) :
    ∀ formula, eval left formula = eval right formula := by
  intro formula
  induction formula with
  | atom question => exact completion.transport question
  | neg formula induction => simp [eval, induction]
  | and first second firstInduction secondInduction =>
      simp [eval, firstInduction, secondInduction]

/-- Retagging changes no formula reading because formulas see truth answers, not markers. -/
theorem eval_retag {Question : Type u} (presentation : Presentation Question)
    (isolated : IsolatedIdentification) :
    ∀ formula, eval (presentation.retag isolated) formula = eval presentation formula := by
  intro formula
  induction formula with
  | atom question => rfl
  | neg formula induction => simp [eval, induction]
  | and first second firstInduction secondInduction =>
      simp [eval, firstInduction, secondInduction]

/-- The all-question reading used to connect this result to the transaction adapter. -/
def allQuestions (Question : Type u) :
    TransactionalCompletionEvaluation.ClosureQuestionLanguage Bool where
  Question := Question
  relevant := fun _ => True

/--
Every completion witness instantiates the existing transactional evaluation
adapter.  The two frozen frames are the two supplied answer functions, while
the transaction has one occurrence on each side.
-/
def transactionOf {Question : Type u} {left right : Presentation Question}
    (completion : Completion left right) :
    TransactionalCompletionEvaluation.CompletionTransaction Unit Unit
      (allQuestions Question) where
  language := {
    answer := fun _ question => left.truth question
  }
  definition := {
    answer := fun _ question => right.truth question
  }
  forward := id
  backward := id
  forward_preserves := by
    intro _ question _
    exact (completion.transport question).symm
  backward_preserves := by
    intro _ question _
    exact completion.transport question

/-- The translated truth equality is an admitted closure of the transaction adapter. -/
theorem completion_closes_in_transactional_adapter {Question : Type u}
    {left right : Presentation Question} (completion : Completion left right) :
    (transactionOf completion).admitted.closes () () :=
  (transactionOf completion).forward_closes ()

namespace FiniteModel

def commonTag : IsolatedIdentification where
  basis := .local
  trajectory := .negative
  endpoint := .zero

def oppositeTag : IsolatedIdentification where
  basis := .global
  trajectory := .positive
  endpoint := .infinity

def falsePresentation (isolated : IsolatedIdentification := commonTag) : Presentation Unit where
  truth := fun _ => false
  isolated := isolated

def truePresentation (isolated : IsolatedIdentification := commonTag) : Presentation Unit where
  truth := fun _ => true
  isolated := isolated

/-- Equal isolated markers do not establish truth-answer completion. -/
theorem same_marker_not_completable :
    MarkersAgree (falsePresentation commonTag) (truePresentation commonTag) ∧
      ¬ Completable (falsePresentation commonTag) (truePresentation commonTag) := by
  constructor
  · rfl
  · rintro ⟨completion⟩
    have contradiction := completion.transport ()
    simp [falsePresentation, truePresentation] at contradiction

/-- The polar markers stay distinct in all three fields. -/
theorem zero_inf_markers_disagree :
    (commonTag.basis ≠ oppositeTag.basis) ∧
      (commonTag.trajectory ≠ oppositeTag.trajectory) ∧
        (commonTag.endpoint ≠ oppositeTag.endpoint) := by
  decide

/-- A local/negative/zero presentation and global/positive/infinity presentation can close. -/
theorem zero_inf_completable :
    Completable (falsePresentation commonTag) (falsePresentation oppositeTag) :=
  ⟨⟨fun _ => rfl⟩⟩

/-- Completion is strictly coarser than literal presentation identity. -/
theorem completable_strictly_coarser_than_presentation_identity :
    ∃ left right : Presentation Unit, left ≠ right ∧ Completable left right := by
  refine ⟨falsePresentation commonTag, falsePresentation oppositeTag, ?_, zero_inf_completable⟩
  intro equal
  have markerEqual := congrArg Presentation.isolated equal
  exact zero_inf_markers_disagree.2.2 (by
    simpa [falsePresentation, commonTag, oppositeTag] using congrArg IsolatedIdentification.endpoint markerEqual)

/-- No criterion that sees markers alone decides completion in this finite model. -/
theorem no_marker_only_criterion :
    ¬ ∃ criterion : IsolatedIdentification → IsolatedIdentification → Prop,
      MarkerOnlyCriterion (Question := Unit) criterion := by
  rintro ⟨criterion, hcriterion⟩
  have closed : criterion commonTag commonTag := by
    simpa [falsePresentation] using
      ((hcriterion (falsePresentation commonTag) (falsePresentation commonTag)).mp
        (completable_refl _))
  have notClosed : ¬ criterion commonTag commonTag := by
    intro markerDecision
    exact same_marker_not_completable.2
      ((hcriterion (falsePresentation commonTag) (truePresentation commonTag)).mpr (by
          simpa [falsePresentation, truePresentation] using markerDecision))
  exact notClosed closed

/-- One matching isolated question probe does not decide completion of the whole language. -/
def probeLeft : Presentation Bool where
  truth := fun _ => false
  isolated := commonTag

def probeRight : Presentation Bool where
  truth := fun question => question
  isolated := commonTag

theorem single_question_agreement_not_completable :
    probeLeft.truth false = probeRight.truth false ∧ ¬ Completable probeLeft probeRight := by
  constructor
  · rfl
  · rintro ⟨completion⟩
    have contradiction := completion.transport true
    simp [probeLeft, probeRight] at contradiction

/-- Marker agreement and completability are incomparable relations in the finite model. -/
theorem marker_agreement_and_completability_incomparable :
    (∃ left right : Presentation Unit,
      MarkersAgree left right ∧ ¬ Completable left right) ∧
      (∃ left right : Presentation Unit,
        Completable left right ∧ ¬ MarkersAgree left right) := by
  constructor
  · exact ⟨falsePresentation commonTag, truePresentation commonTag,
      same_marker_not_completable.1, same_marker_not_completable.2⟩
  · refine ⟨falsePresentation commonTag, falsePresentation oppositeTag,
      zero_inf_completable, ?_⟩
    intro equal
    exact zero_inf_markers_disagree.1 (by
      simpa [falsePresentation, commonTag, oppositeTag] using congrArg IsolatedIdentification.basis equal)

end FiniteModel

end CompletionInTranslationalTruthEquality
end Slearn

#print axioms Slearn.CompletionInTranslationalTruthEquality.completable_iff_truth_answers_equal
#print axioms Slearn.CompletionInTranslationalTruthEquality.Completion.transports_equal
#print axioms Slearn.CompletionInTranslationalTruthEquality.completable_retag
#print axioms Slearn.CompletionInTranslationalTruthEquality.completable_marker_blind
#print axioms Slearn.CompletionInTranslationalTruthEquality.eval_translate
#print axioms Slearn.CompletionInTranslationalTruthEquality.eval_retag
#print axioms Slearn.CompletionInTranslationalTruthEquality.completion_closes_in_transactional_adapter
#print axioms Slearn.CompletionInTranslationalTruthEquality.FiniteModel.same_marker_not_completable
#print axioms Slearn.CompletionInTranslationalTruthEquality.FiniteModel.zero_inf_completable
#print axioms Slearn.CompletionInTranslationalTruthEquality.FiniteModel.no_marker_only_criterion
#print axioms Slearn.CompletionInTranslationalTruthEquality.FiniteModel.single_question_agreement_not_completable
