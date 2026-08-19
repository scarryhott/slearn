import Slearn.NRRF654IntegratedFrameworkClosure
import Slearn.PartitionAggregateClosure

/-
Relational closure unification for Slearn.

This adapter makes one repository-wide distinction explicit:

* a finite or otherwise selected evaluation answers only its declared
  questions; and
* a closure relation is answer-preserving translation across the complete
  admitted question family.

`RelationalOrbitFrame` is deliberately abstract about its parameter family.
It can model a finite rotation, an interval, a circle, a collection of
languages, or another supplied family of translations.  It does not introduce
topology, measure, physics, a privileged natural perspective, or a proof that
the supplied family is actually continuous.  Its completeness field is a
model assumption stating that the declared relational questions separate the
translation orbits.
-/

universe u v w

namespace Slearn
namespace RelationalClosureUnification

/-- A family of translations whose invariant answers define its closure relation. -/
structure RelationalOrbitFrame
    (Presentation : Type u) where
  Phase : Type u
  Question : Type u
  Answer : Type u
  translate : Phase → Presentation → Presentation
  origin : Phase
  origin_returns : ∀ presentation, translate origin presentation = presentation
  answer : Question → Presentation → Answer
  answer_invariant : ∀ phase question presentation,
    answer question (translate phase presentation) = answer question presentation
  answers_separate_orbits : ∀ {left right},
    (∀ question, answer question left = answer question right) →
      ∃ phase, translate phase left = right

namespace RelationalOrbitFrame

variable {Presentation : Type u}
variable (F : RelationalOrbitFrame Presentation)

/-- Equality of all declared relational answers. -/
def TrueTranslation (left right : Presentation) : Prop :=
  ∀ question, F.answer question left = F.answer question right

/-- Return through one member of the admitted translation family. -/
def ClosureRelation (left right : Presentation) : Prop :=
  ∃ phase, F.translate phase left = right

/-- Natural choice is a relation-preserving return, not an optimisation score. -/
def NaturalChoice (left right : Presentation) : Prop :=
  F.ClosureRelation left right

/-- The origin translation makes every presentation close to itself. -/
theorem closure_refl (presentation : Presentation) :
    F.ClosureRelation presentation presentation :=
  ⟨F.origin, F.origin_returns presentation⟩

/-- Every admitted translation preserves the declared relational truth. -/
theorem closure_implies_trueTranslation {left right : Presentation}
    (closed : F.ClosureRelation left right) :
    F.TrueTranslation left right := by
  obtain ⟨phase, returnWitness⟩ := closed
  intro question
  calc
    F.answer question left = F.answer question (F.translate phase left) :=
      (F.answer_invariant phase question left).symm
    _ = F.answer question right := congrArg (F.answer question) returnWitness

/-- Separation of declared relational answers supplies an admitted return. -/
theorem trueTranslation_implies_closure {left right : Presentation}
    (trueTranslation : F.TrueTranslation left right) :
    F.ClosureRelation left right :=
  F.answers_separate_orbits trueTranslation

/-- Under the stated separation condition, closure is exactly true translation. -/
theorem closure_iff_trueTranslation (left right : Presentation) :
    F.ClosureRelation left right ↔ F.TrueTranslation left right :=
  ⟨F.closure_implies_trueTranslation, F.trueTranslation_implies_closure⟩

/-- Natural choice has no extra score: it is the established closure relation. -/
theorem naturalChoice_iff_trueTranslation (left right : Presentation) :
    F.NaturalChoice left right ↔ F.TrueTranslation left right :=
  F.closure_iff_trueTranslation left right

end RelationalOrbitFrame

/-- A tower of evaluation bases; a level may be finite even when the tower is unbounded. -/
structure RelativeCompletionDepth (Presentation : Type u) (Reading : Type v) where
  read : Nat → Presentation → Reading

namespace RelativeCompletionDepth

variable {Presentation : Type u} {Reading : Type v}
variable (D : RelativeCompletionDepth Presentation Reading)

/-- Equality visible at one selected depth. -/
def AtDepth (depth : Nat) (left right : Presentation) : Prop :=
  D.read depth left = D.read depth right

/-- Equality retained through every supplied depth. -/
def ThroughAllDepths (left right : Presentation) : Prop :=
  ∀ depth, D.AtDepth depth left right

theorem throughAllDepths_refl (presentation : Presentation) :
    D.ThroughAllDepths presentation presentation := by
  intro depth
  rfl

theorem throughAllDepths_symm {left right : Presentation} :
    D.ThroughAllDepths left right → D.ThroughAllDepths right left := by
  intro agreement depth
  exact (agreement depth).symm

theorem throughAllDepths_trans {first second third : Presentation} :
    D.ThroughAllDepths first second → D.ThroughAllDepths second third →
      D.ThroughAllDepths first third := by
  intro firstSecond secondThird depth
  exact (firstSecond depth).trans (secondThird depth)

end RelativeCompletionDepth

/-- The existing Turing/Topos witness is a true translation at its stated witness depth. -/
theorem topos_turing_internal_closes
    {Turing : Type u} {Topos : Type v} {Witness : Type w}
    (R : RelativeToposTuring Turing Topos Witness) (turing : Turing) :
    R.crossEq turing (R.encode turing) :=
  (R.encode_coherent turing).symm

/-- The reverse Topos/Turing orientation closes at that same stated witness depth. -/
theorem topos_turing_external_closes
    {Turing : Type u} {Topos : Type v} {Witness : Type w}
    (R : RelativeToposTuring Turing Topos Witness) (topos : Topos) :
    R.crossEq (R.evaluate topos) topos :=
  R.evaluate_coherent topos

/-- Finite prefix access cannot decide the imported model's global soundness. -/
theorem finite_prefix_is_not_global_closure
    (depth : Nat) (verifier : InteractiveOpenFoundation.StageVerifier depth) :
    ¬ ∀ transcript,
      (InteractiveOpenFoundation.stageVerdict verifier transcript = true ↔
        InteractiveOpenFoundation.Sound transcript) :=
  InteractiveOpenFoundation.no_finite_stage_decides depth verifier

/-- In the imported prefix model, all-depth completion is its translational closure. -/
theorem all_prefix_depths_are_translational_closure
    (transcript : InteractiveOpenFoundation.Transcript) :
    InteractiveOpenFoundation.ContinuousCompletion transcript ↔
      InteractiveOpenFoundation.transcriptFrame.completion
        InteractiveOpenFoundation.Sound transcript :=
  InteractiveOpenFoundation.continuousCompletion_eq_translationalClosure transcript

/-- The finite partition model closes scalar equality before its supplied successor question reopens it. -/
theorem scalar_partition_reopens_at_successor :
    PartitionAggregateClosure.scalarLanguage.TruthEq
        PartitionAggregateClosure.quadrature PartitionAggregateClosure.rearranged ∧
      ¬ (PartitionAggregateClosure.scalarLanguage.extend
        PartitionAggregateClosure.phaseAsymmetry.discriminator).TruthEq
          PartitionAggregateClosure.quadrature PartitionAggregateClosure.rearranged :=
  PartitionAggregateClosure.scalar_closure_reopens

/-- A finite aggregate cannot determine the retained successor phase in the partition model. -/
theorem scalar_aggregate_is_not_complete_continuation :
    ¬ PartitionAggregateClosure.DeterminedByAggregate
      PartitionAggregateClosure.firstPhase :=
  PartitionAggregateClosure.continuation_not_determined_by_aggregate

/-- A positive finite Kakeya-style grain may collapse directions; all grains are required to resolve them. -/
theorem finite_grain_remains_open
    {Direction : Type u} {Readout : Type v}
    (resolution : CommonClosureOperation.KakeyaResolution Direction Readout)
    {depth : Nat} (positive : 0 < depth) :
    ¬ Function.Injective (resolution.read depth) :=
  CommonClosureOperation.KakeyaResolution.finite_grain_not_injective resolution positive

/-- Agreement through every stated grain is the corresponding resolution-relative closure. -/
theorem all_grains_close_direction
    {Direction : Type u} {Readout : Type v}
    (resolution : CommonClosureOperation.KakeyaResolution Direction Readout)
    {left right : Direction}
    (agreement : ∀ depth, resolution.read depth left = resolution.read depth right) :
    left = right :=
  CommonClosureOperation.KakeyaResolution.all_grains_determine_direction resolution agreement

end RelationalClosureUnification
end Slearn

#print axioms Slearn.RelationalClosureUnification.RelationalOrbitFrame.closure_iff_trueTranslation
#print axioms Slearn.RelationalClosureUnification.RelationalOrbitFrame.naturalChoice_iff_trueTranslation
#print axioms Slearn.RelationalClosureUnification.RelativeCompletionDepth.throughAllDepths_trans
#print axioms Slearn.RelationalClosureUnification.topos_turing_internal_closes
#print axioms Slearn.RelationalClosureUnification.finite_prefix_is_not_global_closure
#print axioms Slearn.RelationalClosureUnification.all_prefix_depths_are_translational_closure
#print axioms Slearn.RelationalClosureUnification.scalar_partition_reopens_at_successor
#print axioms Slearn.RelationalClosureUnification.finite_grain_remains_open
