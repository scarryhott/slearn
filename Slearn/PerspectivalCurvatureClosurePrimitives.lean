import Slearn.NRRF655ExecutablePerspectivalClosureEpisode

/-
Source-grounded perspectival-curvature primitives for Slearn.

This is the formal contract for the mechanism stated in the direct Slearn
source: an observation is read through a perspective, belief/value limit, WHY,
and goal; two explanations and an operative definition expose the
language/definition flip; both a forward and counter-path remain available;
and an admission is nonterminal only when a reviewed interaction carries a
changed successor and a further relation.

The structures make those data dependencies explicit.  They do not establish
that an entered source is accurate, an attempt happened, a review is
independent, a relation is true, or that the supplied values have educational,
physical, or metaphysical meanings.
-/

universe u

namespace Slearn
namespace PerspectivalCurvature

/--
The source-defined curvature record.  `curves` is intentionally supplied by a
caller: the formal layer preserves a stated relation between belief, goal, WHY
and a path; it does not calculate a psychological or physical curvature.
-/
structure CurvaturePrimitives
    (Anchor Claim Observation Perspective Belief Goal Why Explanation Definition Path Witness : Type u) where
  sourceAnchor : Anchor
  sourceClaim : Claim
  observation : Observation
  perspective : Perspective
  beliefLimit : Belief
  goalLimit : Goal
  why : Why
  semanticExplanation : Explanation
  operativeExplanation : Explanation
  definition : Definition
  forwardPath : Path
  counterPath : Path
  curves : Belief → Goal → Why → Path → Prop
  forwardPath_available : curves beliefLimit goalLimit why forwardPath
  counterPath_available : curves beliefLimit goalLimit why counterPath
  presentsDefinition : Explanation → Definition → Why → Prop
  semantic_presents : presentsDefinition semanticExplanation definition why
  operative_presents : presentsDefinition operativeExplanation definition why
  translation : AdmittedTranslation Perspective Goal Witness

namespace CurvaturePrimitives

variable {Anchor Claim Observation Perspective Belief Goal Why Explanation Definition Path Witness : Type u}

/-- The source's perspective–WHY–goal triangle, with its belief/value limit. -/
def triangle
    (C : CurvaturePrimitives Anchor Claim Observation Perspective Belief Goal Why Explanation Definition Path Witness) :
    Perspective × Why × Goal × Belief :=
  (C.perspective, C.why, C.goalLimit, C.beliefLimit)

/-- The same declared relation makes both selected paths inspectable. -/
theorem paths_are_relative_to_one_curvature
    (C : CurvaturePrimitives Anchor Claim Observation Perspective Belief Goal Why Explanation Definition Path Witness) :
    C.curves C.beliefLimit C.goalLimit C.why C.forwardPath ∧
      C.curves C.beliefLimit C.goalLimit C.why C.counterPath :=
  ⟨C.forwardPath_available, C.counterPath_available⟩

/-- The paired explanation requirement keeps both readings tied to one WHY/definition relation. -/
theorem explanations_share_the_declared_relation
    (C : CurvaturePrimitives Anchor Claim Observation Perspective Belief Goal Why Explanation Definition Path Witness) :
    C.presentsDefinition C.semanticExplanation C.definition C.why ∧
      C.presentsDefinition C.operativeExplanation C.definition C.why :=
  ⟨C.semantic_presents, C.operative_presents⟩

/-- The open local source presentation of this packet. -/
def opened
    (C : CurvaturePrimitives Anchor Claim Observation Perspective Belief Goal Why Explanation Definition Path Witness) :
    FrameworkClosure.OpenPerspective C.translation :=
  ⟨C.perspective⟩

/-- Its forward translation is fixed by the admitted translation, not by a new operator. -/
def contracted
    (C : CurvaturePrimitives Anchor Claim Observation Perspective Belief Goal Why Explanation Definition Path Witness) :
    FrameworkClosure.ContractedPerspective C.translation :=
  C.opened.contract

/-- Its reciprocal re-reading is fixed by the same admitted translation. -/
def reopened
    (C : CurvaturePrimitives Anchor Claim Observation Perspective Belief Goal Why Explanation Definition Path Witness) :
    FrameworkClosure.ReopenedPerspective C.translation :=
  C.contracted.reopen

/-- Forward contraction and reciprocal reopening retain the declared witness relation. -/
theorem reopen_closes_source_goal
    (C : CurvaturePrimitives Anchor Claim Observation Perspective Belief Goal Why Explanation Definition Path Witness) :
    C.translation.closes C.reopened.perspective C.contracted.goal :=
  C.reopened.closes_goal

end CurvaturePrimitives

/--
An interaction is an externally declared attempt through both selected paths.
Its type ties it to a curvature packet; it is not evidence that an attempt was
actually made outside this formal record.
-/
structure DeclaredInteraction
    {Anchor Claim Observation Perspective Belief Goal Why Explanation Definition Path Witness : Type u}
    (C : CurvaturePrimitives Anchor Claim Observation Perspective Belief Goal Why Explanation Definition Path Witness)
    (Attempt : Type u) where
  attempt : Attempt
  forwardPath_used : C.curves C.beliefLimit C.goalLimit C.why C.forwardPath
  counterPath_used : C.curves C.beliefLimit C.goalLimit C.why C.counterPath

namespace DeclaredInteraction

variable {Anchor Claim Observation Perspective Belief Goal Why Explanation Definition Path Witness Attempt : Type u}
variable {C : CurvaturePrimitives Anchor Claim Observation Perspective Belief Goal Why Explanation Definition Path Witness}

/-- An interaction cannot drop the source packet's counter-path. -/
theorem retains_counter_path (I : DeclaredInteraction C Attempt) :
    C.curves C.beliefLimit C.goalLimit C.why C.counterPath :=
  I.counterPath_used

end DeclaredInteraction

/--
The material comparison layer.  It is deliberately distinct from the attempt:
the record carries the counter-reading, method, and review needed before an
admission can be formed.
-/
structure ReviewedInteraction
    {Anchor Claim Observation Perspective Belief Goal Why Explanation Definition Path Witness : Type u}
    (C : CurvaturePrimitives Anchor Claim Observation Perspective Belief Goal Why Explanation Definition Path Witness)
    (Attempt Material CounterReading Comparison Review : Type u) where
  interaction : DeclaredInteraction C Attempt
  material : Material
  counterReading : CounterReading
  comparison : Comparison
  review : Review

/--
A truth-admission is a continued, reviewed translation.  `nextRelation` is a
required primitive, so this structure cannot express a terminal return.  The
field records that a further relation was supplied; it does not by itself say
that the relation is meaningful, independent, or universally valid.
-/
structure ContinuedAdmission
    {Anchor Claim Observation Perspective Belief Goal Why Explanation Definition Path Witness : Type u}
    (C : CurvaturePrimitives Anchor Claim Observation Perspective Belief Goal Why Explanation Definition Path Witness)
    (Attempt Material CounterReading Comparison Review Receipt NextRelation : Type u) where
  reviewed : ReviewedInteraction C Attempt Material CounterReading Comparison Review
  receipt : Receipt
  successor : Perspective
  successorCloses : C.translation.closes successor C.contracted.goal
  successorChanged : successor ≠ C.perspective
  nextRelation : NextRelation

namespace ContinuedAdmission

variable {Anchor Claim Observation Perspective Belief Goal Why Explanation Definition Path Witness : Type u}
variable {Attempt Material CounterReading Comparison Review Receipt NextRelation : Type u}
variable {C : CurvaturePrimitives Anchor Claim Observation Perspective Belief Goal Why Explanation Definition Path Witness}

/-- Convert a continued admission into the existing predecessor-typed return input. -/
def returnInput
    (A : ContinuedAdmission C Attempt Material CounterReading Comparison Review Receipt NextRelation) :
    FrameworkClosure.ReturnInput C.translation Receipt C.reopened where
  receipt := A.receipt
  successor := A.successor
  successorCloses := A.successorCloses
  successorChanged := A.successorChanged

/-- The recorded return is available only from a continued admission. -/
def recordedReturn
    (A : ContinuedAdmission C Attempt Material CounterReading Comparison Review Receipt NextRelation) :
    FrameworkClosure.ReturnedPerspective C.translation Receipt :=
  C.reopened.commitReturn A.returnInput

/-- An admission supplies a further relation rather than terminating at its receipt. -/
theorem has_further_relation
    (A : ContinuedAdmission C Attempt Material CounterReading Comparison Review Receipt NextRelation) :
    ∃ next : NextRelation, next = A.nextRelation :=
  ⟨A.nextRelation, rfl⟩

/-- The recorded successor closes with the original contracted goal. -/
theorem successor_closes_goal
    (A : ContinuedAdmission C Attempt Material CounterReading Comparison Review Receipt NextRelation) :
    C.translation.closes A.recordedReturn.input.successor C.contracted.goal :=
  A.recordedReturn.successor_closes_goal

/-- A continued admission cannot record literal repetition of its source perspective. -/
theorem successor_is_not_source_perspective
    (A : ContinuedAdmission C Attempt Material CounterReading Comparison Review Receipt NextRelation) :
    A.recordedReturn.residue.successor ≠ A.recordedReturn.residue.origin :=
  A.recordedReturn.residue_changes_origin

/-- The next opening inherits exactly the recorded residue. -/
theorem continuation_inherits_residue
    (A : ContinuedAdmission C Attempt Material CounterReading Comparison Review Receipt NextRelation) :
    A.recordedReturn.nextOpening.inheritedResidue = A.recordedReturn.residue :=
  A.recordedReturn.continue_preserves_residue

end ContinuedAdmission

end PerspectivalCurvature
end Slearn

#print axioms Slearn.PerspectivalCurvature.CurvaturePrimitives.paths_are_relative_to_one_curvature
#print axioms Slearn.PerspectivalCurvature.CurvaturePrimitives.explanations_share_the_declared_relation
#print axioms Slearn.PerspectivalCurvature.CurvaturePrimitives.reopen_closes_source_goal
#print axioms Slearn.PerspectivalCurvature.DeclaredInteraction.retains_counter_path
#print axioms Slearn.PerspectivalCurvature.ContinuedAdmission.has_further_relation
#print axioms Slearn.PerspectivalCurvature.ContinuedAdmission.successor_closes_goal
#print axioms Slearn.PerspectivalCurvature.ContinuedAdmission.successor_is_not_source_perspective
#print axioms Slearn.PerspectivalCurvature.ContinuedAdmission.continuation_inherits_residue
