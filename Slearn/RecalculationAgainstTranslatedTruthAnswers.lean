import Slearn.TransactionalCompletionEvaluation

/-
Recalculation against translated truth answers for Slearn.

The re-derived core is intentionally small.  A level is a frozen question
language, a translation of its questions, and an answer relation.  Equality at
that level compares the left answer at `q` with the right answer at the
translated question.  Extending the language by a discriminator makes exactly
one new comparison required.

The module proves the closure laws of this construction and two finite Slearn
readings (ball/hair and zero/infinity).  The numerical `H = 2` is a witness
readout in the finite ball/hair example; it is not asserted as a universal
physical, mathematical, or educational constant.  A new discriminator is
always supplied by the `PerspectiveAsymmetry` record: the theorem does not
claim to discover a warranted question from raw presentation inequality.
-/

universe u v w

namespace Slearn
namespace RecalculationAgainstTranslatedTruthAnswers

/-- One frozen level: questions, their translation, and answers from a presentation. -/
structure FrozenQuestionLanguage (Presentation : Type u) (Answer : Type v) where
  Question : Type w
  translate : Question → Question
  answer : Question → Presentation → Answer

namespace FrozenQuestionLanguage

variable {Presentation : Type u} {Answer : Type v}
variable (L : FrozenQuestionLanguage Presentation Answer)

/-- Equality at a level is equality of answers after translating the question. -/
def TruthEq (left right : Presentation) : Prop :=
  ∀ question, L.answer question left = L.answer (L.translate question) right

/-- Change only the question translation, keeping the frozen answer relation. -/
def withTranslation (translate : L.Question → L.Question) :
    FrozenQuestionLanguage Presentation Answer where
  Question := L.Question
  translate := translate
  answer := L.answer

/-- Identity translation gives reflexivity. -/
theorem truthEq_refl (identity : ∀ question, L.translate question = question)
    (presentation : Presentation) : L.TruthEq presentation presentation := by
  intro question
  rw [identity question]

/-- An involutive question translation makes truth equality symmetric. -/
theorem truthEq_symm (involutive : ∀ question, L.translate (L.translate question) = question)
    {left right : Presentation} : L.TruthEq left right → L.TruthEq right left := by
  intro equality question
  calc
    L.answer question right = L.answer (L.translate (L.translate question)) right := by
      rw [involutive question]
    _ = L.answer (L.translate question) left := (equality (L.translate question)).symm

/-- Translated truth equality composes along the composed question translation. -/
theorem truthEq_trans (first second : L.Question → L.Question)
    {left middle right : Presentation}
    (firstEquality : (L.withTranslation first).TruthEq left middle)
    (secondEquality : (L.withTranslation second).TruthEq middle right) :
    (L.withTranslation (second ∘ first)).TruthEq left right := by
  intro question
  exact (firstEquality question).trans (secondEquality (first question))

/-- Add one new question while retaining the old translated question structure. -/
def extend (newAnswer : Presentation → Answer) :
    FrozenQuestionLanguage Presentation Answer where
  Question := Option L.Question
  translate := fun
    | none => none
    | some question => some (L.translate question)
  answer := fun question presentation =>
    match question with
    | none => newAnswer presentation
    | some question => L.answer question presentation

/--
The recalculation law: extending a question-language preserves prior truth
equality exactly when the new discriminator also agrees.
-/
theorem truthEq_extend_iff (newAnswer : Presentation → Answer)
    (left right : Presentation) :
    (L.extend newAnswer).TruthEq left right ↔
      L.TruthEq left right ∧ newAnswer left = newAnswer right := by
  constructor
  · intro equality
    constructor
    · intro question
      simpa [extend] using equality (some question)
    · simpa [extend] using equality none
  · rintro ⟨previous, newest⟩ question
    cases question with
    | none => simpa [extend] using newest
    | some question => simpa [extend] using previous question

/-- A supplied perspectival difference that can become the next question. -/
structure PerspectiveAsymmetry (L : FrozenQuestionLanguage Presentation Answer)
    (left right : Presentation) where
  discriminator : Presentation → Answer
  separates : discriminator left ≠ discriminator right

/-- An equal current truth relation and a supplied asymmetry reopen at the successor language. -/
theorem successor_reopens {left right : Presentation}
    (current : L.TruthEq left right) (asymmetry : L.PerspectiveAsymmetry left right) :
    L.TruthEq left right ∧ ¬ (L.extend asymmetry.discriminator).TruthEq left right := by
  constructor
  · exact current
  · intro successor
    have discriminatorEqual := (L.truthEq_extend_iff asymmetry.discriminator left right).mp successor |>.2
    exact asymmetry.separates discriminatorEqual

/-- Use the translated answers as the definition frame of the existing transaction adapter. -/
def transactionQuestions : TransactionalCompletionEvaluation.ClosureQuestionLanguage Answer where
  Question := L.Question
  relevant := fun _ => True

/-- A truth-equality witness supplies a concrete two-occurrence transaction. -/
def transactionOf {left right : Presentation} (equality : L.TruthEq left right) :
    TransactionalCompletionEvaluation.CompletionTransaction Unit Unit L.transactionQuestions where
  language := {
    answer := fun _ question => L.answer question left
  }
  definition := {
    answer := fun _ question => L.answer (L.translate question) right
  }
  forward := id
  backward := id
  forward_preserves := by
    intro _ question _
    exact (equality question).symm
  backward_preserves := by
    intro _ question _
    exact equality question

/-- Thus truth equality closes as one of the existing admitted translations. -/
theorem truthEq_closes_in_transaction {left right : Presentation}
    (equality : L.TruthEq left right) :
    (L.transactionOf equality).admitted.closes () () :=
  (L.transactionOf equality).forward_closes ()

end FrozenQuestionLanguage

namespace FiniteModel

/-- The current frozen level answers every question alike, so it cannot yet see the Boolean route distinction. -/
def current : FrozenQuestionLanguage Bool Bool where
  Question := Unit
  translate := id
  answer := fun _ _ => false

theorem current_translation_is_identity : ∀ question, current.translate question = question := by
  intro question
  rfl

/-- The ball/hair pair is truth-equal at the current level but literally and route-wise distinct. -/
theorem ball_hair_truth_equal : current.TruthEq false true := by
  intro question
  cases question
  rfl

theorem ball_hair_literal_distinct : false ≠ true := by decide

theorem ball_hair_route_distinct : false ≠ true := by decide

/-- The quotient reading is the current level's truth equality. -/
theorem ball_hair_unitary_quotient_equal : current.TruthEq false true :=
  ball_hair_truth_equal

/-- The lifted history is intentionally retained as a different finite marker. -/
theorem ball_hair_lifted_holonomy_distinct : (0 : Nat) ≠ 2 := by decide

/-- `H = 2` is a declared finite witness readout for this one model. -/
def ballHairResidue : Nat := 2

theorem ball_hair_residue_is_two : ballHairResidue = 2 := rfl

/-- The current pair supplies a separating next question: its Boolean route label. -/
def ballHairAsymmetry : current.PerspectiveAsymmetry false true where
  discriminator := id
  separates := by decide

/-- The pair closes at the frozen level and reopens at the successor level. -/
theorem ball_hair_successor_separates :
    ¬ (current.extend ballHairAsymmetry.discriminator).TruthEq false true :=
  (current.successor_reopens ball_hair_truth_equal ballHairAsymmetry).2

/-- The source's polar terms remain isolated markers, not literal equalities. -/
inductive Endpoint
  | zero
  | infinity
  deriving DecidableEq, Repr

structure PolarPresentation where
  visible : Bool
  endpoint : Endpoint
  quantity : Bool
  locality : Bool
  orientation : Bool

def zeroPresentation : PolarPresentation where
  visible := false
  endpoint := .zero
  quantity := false
  locality := false
  orientation := false

def infinityPresentation : PolarPresentation where
  visible := false
  endpoint := .infinity
  quantity := true
  locality := true
  orientation := true

/-- The same frozen answer relation treats both polar presentations equally. -/
def polarLanguage : FrozenQuestionLanguage PolarPresentation Bool where
  Question := Unit
  translate := id
  answer := fun _ _ => false

theorem zero_inf_truth_equal : polarLanguage.TruthEq zeroPresentation infinityPresentation := by
  intro question
  cases question
  rfl

theorem zero_inf_markers_distinct :
    zeroPresentation.endpoint ≠ infinityPresentation.endpoint ∧
      zeroPresentation.quantity ≠ infinityPresentation.quantity ∧
        zeroPresentation.locality ≠ infinityPresentation.locality ∧
          zeroPresentation.orientation ≠ infinityPresentation.orientation := by
  decide

/-- The polar truth equality itself becomes a closure transaction. -/
theorem zero_inf_closes_in_transaction :
    (polarLanguage.transactionOf zero_inf_truth_equal).admitted.closes () () :=
  polarLanguage.truthEq_closes_in_transaction zero_inf_truth_equal

end FiniteModel

end RecalculationAgainstTranslatedTruthAnswers
end Slearn

#print axioms Slearn.RecalculationAgainstTranslatedTruthAnswers.FrozenQuestionLanguage.truthEq_refl
#print axioms Slearn.RecalculationAgainstTranslatedTruthAnswers.FrozenQuestionLanguage.truthEq_symm
#print axioms Slearn.RecalculationAgainstTranslatedTruthAnswers.FrozenQuestionLanguage.truthEq_trans
#print axioms Slearn.RecalculationAgainstTranslatedTruthAnswers.FrozenQuestionLanguage.truthEq_extend_iff
#print axioms Slearn.RecalculationAgainstTranslatedTruthAnswers.FrozenQuestionLanguage.successor_reopens
#print axioms Slearn.RecalculationAgainstTranslatedTruthAnswers.FrozenQuestionLanguage.truthEq_closes_in_transaction
#print axioms Slearn.RecalculationAgainstTranslatedTruthAnswers.FiniteModel.ball_hair_successor_separates
#print axioms Slearn.RecalculationAgainstTranslatedTruthAnswers.FiniteModel.zero_inf_truth_equal
#print axioms Slearn.RecalculationAgainstTranslatedTruthAnswers.FiniteModel.zero_inf_closes_in_transaction
