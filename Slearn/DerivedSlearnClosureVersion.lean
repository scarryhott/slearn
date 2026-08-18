import Slearn.DerivedPerspectivalClosureHull
import Slearn.AuditableChangingAxiometryProtocol

/-
Derived Slearn closure version.

This module joins the source-defined Slearn curvature/admission packet to the
bounded changing-axiometry audit. A version is therefore not a screen state,
an authored curriculum, or an automatically trusted answer. It is a reviewed
perspective--WHY--goal return whose same admitted translation is used as the
axiom/geometry closure witness of a supplied audit run. Its next relation is
the audit's held-out relation, hence a new opening for the next version.

The record stores supplied evidence tokens. The theorems prove their stated
structural dependencies only; they do not establish that a human attempt,
review, return, or external evidence was independent outside the record.
-/

universe u

namespace Slearn
namespace DerivedSlearnClosureVersion

open PerspectivalCurvature
open PerspectivalClosureHull
open AuditableChangingAxiometry

/-- A returned Slearn closure packet joined to one bounded changing-frame audit. -/
structure ClosureVersion
    (Anchor Claim Observation Perspective Belief Goal Why Explanation Definition Path Witness
      Attempt Material CounterReading Comparison Review Receipt
      Frame NativeTranslation Validation ReturnEvidence Residue
      FrameGeneration FrameFreeze Relation Verdict HeldOutEvidence ExternalEvidence Outcome : Type u) where
  curvature : CurvaturePrimitives
    Anchor Claim Observation Perspective Belief Goal Why Explanation Definition Path Witness
  relationOfObservation : Observation → Relation
  admission : ContinuedAdmission curvature Attempt Material CounterReading Comparison Review Receipt Relation
  returnEvidenceOf : Receipt → ReturnEvidence
  audit : AuditRun Frame Perspective Goal Witness NativeTranslation Validation ReturnEvidence Residue
    FrameGeneration FrameFreeze Relation Verdict HeldOutEvidence ExternalEvidence Outcome
  auditPerspective : audit.completion.current.axiomPresentation = curvature.perspective
  auditGoal : audit.completion.current.geometryPresentation = curvature.goalLimit
  auditTranslation : audit.completion.translation = curvature.translation
  auditReturn : audit.completion.independentReturn = returnEvidenceOf admission.receipt
  nextRelationHeldOut : admission.nextRelation = audit.heldOutRelation

namespace ClosureVersion

variable {Anchor Claim Observation Perspective Belief Goal Why Explanation Definition Path Witness
  Attempt Material CounterReading Comparison Review Receipt
  Frame NativeTranslation Validation ReturnEvidence Residue
  FrameGeneration FrameFreeze Relation Verdict HeldOutEvidence ExternalEvidence Outcome : Type u}

local notation "Version" => ClosureVersion
  Anchor Claim Observation Perspective Belief Goal Why Explanation Definition Path Witness
  Attempt Material CounterReading Comparison Review Receipt
  Frame NativeTranslation Validation ReturnEvidence Residue
  FrameGeneration FrameFreeze Relation Verdict HeldOutEvidence ExternalEvidence Outcome

/-- The current Slearn packet is a returned packet, never a free map input. -/
def packet (V : Version) : LedgerPacket
    Anchor Claim Observation Perspective Belief Goal Why Explanation Definition Path Witness
    Attempt Material CounterReading Comparison Review Receipt Relation :=
  .returned V.curvature V.admission

/-- Slearn's map nodes are generated solely from the version packet. -/
def generatedNodes (V : Version) :=
  DerivedNode.nodesOf V.packet

/-- The version's relations are generated in parallel from the same packet. -/
def generatedLinks (V : Version) :=
  DerivedNode.linksOf V.packet

/-- The verifier that assessed the completed version. -/
def currentVerifier (V : Version) := V.audit.oldVerifier

/-- The verifier derived by the completed version and its residue. -/
def derivedVerifier (V : Version) := V.audit.nextVerifier

/-- The next axiom/geometry presentation derived from this version. -/
def derivedAxiometry (V : Version) := V.audit.nextAxiometry

/-- The source perspective and goal close in exactly the audit's witness relation. -/
theorem source_goal_has_relative_closureTruth (V : Version) :
    V.curvature.translation.closes V.curvature.perspective V.curvature.goalLimit := by
  rw [← V.auditTranslation, ← V.auditPerspective, ← V.auditGoal]
  exact V.audit.completion.has_closureTruth

/-- A Slearn version retains the nonliteral perspective change required by its admission. -/
theorem successor_perspective_changes (V : Version) :
    V.admission.successor ≠ V.curvature.perspective :=
  V.admission.successorChanged

/-- The audit's independent-return evidence is explicitly attached to the Slearn receipt. -/
theorem audit_return_tracks_receipt (V : Version) :
    V.audit.completion.independentReturn = V.returnEvidenceOf V.admission.receipt :=
  V.auditReturn

/-- The Slearn further relation is the method's held-out relation, not an invented extra field. -/
theorem further_relation_is_held_out (V : Version) :
    V.admission.nextRelation = V.audit.heldOutRelation :=
  V.nextRelationHeldOut

/-- The predecessor verifier has no verdict for the further relation. -/
theorem predecessor_leaves_further_relation_open (V : Version) :
    V.currentVerifier.evaluate V.admission.nextRelation = none := by
  rw [further_relation_is_held_out]
  exact V.audit.oldCannotEvaluate

/-- The version-derived verifier has a declared verdict for that same relation. -/
theorem derived_verifier_evaluates_further_relation (V : Version) :
    V.derivedVerifier.evaluate V.admission.nextRelation = some V.audit.newVerdict := by
  rw [further_relation_is_held_out]
  exact V.audit.newCanEvaluate

/-- A return cannot call its derived verifier a frozen replay in the supplied audit model. -/
theorem derived_verifier_changes (V : Version) :
    V.derivedVerifier ≠ V.currentVerifier :=
  V.audit.nextVerifier_changed

/-- A return cannot call its derived axiom/geometry presentation a frozen replay. -/
theorem derived_axiometry_changes (V : Version) :
    V.derivedAxiometry ≠ V.audit.completion.current :=
  V.audit.nextAxiometry_changed

/-- A project appears in the Slearn map only through the reviewed attempted interaction. -/
theorem generated_map_has_attempted_project (V : Version) :
    .project V.admission.reviewed.interaction.attempt ∈ V.generatedNodes := by
  simpa [generatedNodes, packet] using
    (DerivedNode.returned_projects_attempt V.curvature V.admission)

/-- A receipt appears in the Slearn map only through this recorded return. -/
theorem generated_map_has_returned_experience (V : Version) :
    .experience V.admission.receipt ∈ V.generatedNodes := by
  simpa [generatedNodes, packet] using
    (DerivedNode.returned_projects_experience V.curvature V.admission)

/-- Even a returned version projects its further relation as an OPEN remainder. -/
theorem generated_map_reopens (V : Version) :
    .openRemainder V.curvature.sourceAnchor ∈ V.generatedNodes := by
  simpa [generatedNodes, packet] using
    (DerivedNode.returned_reopens V.curvature V.admission)

/--
One Slearn closure version can continue into another only through the prior
returned perspective, the prior derived verifier/frame, and the prior further
relation re-entered as the successor's observed material. The successor then
has its own fresh held-out relation. This is a structural continuation
condition, not literal identity of all presentations.
-/
structure Succession (first second : Version) where
  perspectiveRecentered : second.curvature.perspective = first.admission.successor
  verifierContinues : second.audit.oldVerifier = first.audit.nextVerifier
  frameContinues : second.audit.completion.current.frame = first.audit.nextAxiometry.frame
  reenteredRelationObserved :
    second.relationOfObservation second.curvature.observation = first.admission.nextRelation
  freshHeldOutRelation :
    second.admission.nextRelation ≠ second.relationOfObservation second.curvature.observation

namespace Succession

/-- The second version begins from the first version's returned perspective. -/
theorem next_perspective_is_prior_return {first second : Version}
    (S : Succession first second) :
    second.curvature.perspective = first.admission.successor :=
  S.perspectiveRecentered

/-- The current verifier is literally the prior version's derived verifier. -/
theorem next_verifier_is_prior_derivation {first second : Version}
    (S : Succession first second) :
    second.currentVerifier = first.derivedVerifier :=
  S.verifierContinues

/-- The successor frame is the prior closure's derived axiometry frame. -/
theorem next_frame_is_prior_derivation {first second : Version}
    (S : Succession first second) :
    second.audit.completion.current.frame = first.derivedAxiometry.frame :=
  S.frameContinues

/-- The previously OPEN further relation re-enters the successor as observed material. -/
theorem further_relation_reenters {first second : Version}
    (S : Succession first second) :
    second.relationOfObservation second.curvature.observation = first.admission.nextRelation :=
  S.reenteredRelationObserved

/-- The successor's inherited verifier can evaluate the relation returned by the prior version. -/
theorem reentered_relation_is_evaluated_by_successor {first second : Version}
    (S : Succession first second) :
    second.currentVerifier.evaluate (second.relationOfObservation second.curvature.observation) =
      some first.audit.newVerdict := by
  rw [S.reenteredRelationObserved, S.next_verifier_is_prior_derivation]
  exact first.derived_verifier_evaluates_further_relation

/-- The successor's own held-out relation remains a fresh opening. -/
theorem fresh_held_out_relation_is_open {first second : Version}
    (_S : Succession first second) :
    second.currentVerifier.evaluate second.admission.nextRelation = none :=
  second.predecessor_leaves_further_relation_open

/-- Re-entered material is not silently reused as the successor's fresh question. -/
theorem fresh_held_out_relation_is_distinct {first second : Version}
    (S : Succession first second) :
    second.admission.nextRelation ≠ second.relationOfObservation second.curvature.observation :=
  S.freshHeldOutRelation

/-- The cycle's structural receipt: closure, changed successor, derived method, and a re-entered opening. -/
theorem receipt {first second : Version} (S : Succession first second) :
    first.curvature.translation.closes first.curvature.perspective first.curvature.goalLimit ∧
      first.admission.successor ≠ first.curvature.perspective ∧
      first.derivedVerifier ≠ first.currentVerifier ∧
      second.curvature.perspective = first.admission.successor ∧
      second.currentVerifier.evaluate (second.relationOfObservation second.curvature.observation) =
        some first.audit.newVerdict ∧
      second.currentVerifier.evaluate second.admission.nextRelation = none :=
  ⟨first.source_goal_has_relative_closureTruth,
    first.successor_perspective_changes,
    first.derived_verifier_changes,
    S.next_perspective_is_prior_return,
    S.reentered_relation_is_evaluated_by_successor,
    S.fresh_held_out_relation_is_open⟩

end Succession

/-
Small consistency model for the version/succession contract.  Its tokens have
no educational interpretation.  It establishes only that a returned relation
can become observed material for the next version while that next version keeps
a distinct fresh relation OPEN.
-/
namespace FiniteModel

def translation : AdmittedTranslation Bool Bool Unit where
  forward := id
  backward := id
  localWitness := fun _ => ()
  globalWitness := fun _ => ()
  forward_coherent := fun _ => rfl
  backward_coherent := fun _ => rfl

def curvature (perspective observation : Bool) :
    CurvaturePrimitives Unit Unit Bool Bool Unit Bool Unit Unit Unit Unit Unit where
  sourceAnchor := ()
  sourceClaim := ()
  observation := observation
  perspective := perspective
  beliefLimit := ()
  goalLimit := perspective
  why := ()
  semanticExplanation := ()
  operativeExplanation := ()
  definition := ()
  forwardPath := ()
  counterPath := ()
  curves := fun _ _ _ _ => True
  forwardPath_available := True.intro
  counterPath_available := True.intro
  presentsDefinition := fun _ _ _ => True
  semantic_presents := True.intro
  operative_presents := True.intro
  translation := translation

def admission (perspective observation successor nextRelation : Bool)
    (changed : successor ≠ perspective) :
    ContinuedAdmission (curvature perspective observation) Unit Unit Unit Unit Unit Unit Bool where
  reviewed := {
    interaction := {
      attempt := ()
      forwardPath_used := True.intro
      counterPath_used := True.intro
    }
    material := ()
    counterReading := ()
    comparison := ()
    review := ()
  }
  receipt := ()
  successor := successor
  successorCloses := rfl
  successorChanged := changed
  nextRelation := nextRelation

def axiometry (frame presentation : Bool) : Axiometry Bool Bool Bool where
  frame := frame
  axiomPresentation := presentation
  geometryPresentation := presentation

def completion (current : Axiometry Bool Bool Bool) :
    CompletedRelation Bool Bool Bool Unit Unit Unit Unit Unit where
  current := current
  translation := translation
  translationDiscoveredAfterFreeze := ()
  identityIndependentValidation := ()
  independentReturn := ()
  closureWitness := rfl
  residue := ()

def verifierNone (basis : Bool) : Verifier Bool Bool Bool where
  basis := basis
  evaluate := fun _ => none

/-- It evaluates `false` but leaves `true` OPEN. -/
def firstDerivedVerifier : Verifier Bool Bool Bool where
  basis := true
  evaluate := fun relation => if relation then none else some true

/-- It evaluates `true`, the fresh relation of the second version. -/
def secondDerivedVerifier : Verifier Bool Bool Bool where
  basis := false
  evaluate := fun relation => if relation then some false else none

def firstCurrent : Axiometry Bool Bool Bool := axiometry false false
def firstNext : Axiometry Bool Bool Bool := axiometry true true
def secondCurrent : Axiometry Bool Bool Bool := axiometry true true
def secondNext : Axiometry Bool Bool Bool := axiometry false false

def firstAudit : AuditRun Bool Bool Bool Unit Unit Unit Unit Unit Unit Unit Bool Bool Unit Unit Unit where
  frameGeneration := ()
  frameFreeze := ()
  completion := completion firstCurrent
  deriveNextAxiometry := fun _ _ => firstNext
  nextAxiometry := firstNext
  nextAxiometry_derived := rfl
  nextAxiometry_changed := by
    intro h
    have frameEquality := congrArg Axiometry.frame h
    simp [completion, firstCurrent, firstNext, axiometry] at frameEquality
  oldVerifier := verifierNone false
  deriveNextVerifier := fun _ _ => firstDerivedVerifier
  nextVerifier := firstDerivedVerifier
  nextVerifier_derived := rfl
  nextVerifier_changed := by
    intro h
    have basisEquality := congrArg Verifier.basis h
    simp [verifierNone, firstDerivedVerifier] at basisEquality
  oldVerifier_is_current := rfl
  nextVerifier_is_derived_frame := rfl
  heldOutRelation := false
  heldOutEvidence := ()
  oldCannotEvaluate := rfl
  newVerdict := true
  newCanEvaluate := rfl
  externalEvidence := ()
  predictedOutcome := ()
  observedOutcome := ()
  precedes := fun _ _ => True
  predictionPrecedesOutcome := True.intro
  predictionMatchesOutcome := rfl

def secondAudit : AuditRun Bool Bool Bool Unit Unit Unit Unit Unit Unit Unit Bool Bool Unit Unit Unit where
  frameGeneration := ()
  frameFreeze := ()
  completion := completion secondCurrent
  deriveNextAxiometry := fun _ _ => secondNext
  nextAxiometry := secondNext
  nextAxiometry_derived := rfl
  nextAxiometry_changed := by
    intro h
    have frameEquality := congrArg Axiometry.frame h
    simp [completion, secondCurrent, secondNext, axiometry] at frameEquality
  oldVerifier := firstDerivedVerifier
  deriveNextVerifier := fun _ _ => secondDerivedVerifier
  nextVerifier := secondDerivedVerifier
  nextVerifier_derived := rfl
  nextVerifier_changed := by
    intro h
    have basisEquality := congrArg Verifier.basis h
    simp [firstDerivedVerifier, secondDerivedVerifier] at basisEquality
  oldVerifier_is_current := rfl
  nextVerifier_is_derived_frame := rfl
  heldOutRelation := true
  heldOutEvidence := ()
  oldCannotEvaluate := rfl
  newVerdict := false
  newCanEvaluate := rfl
  externalEvidence := ()
  predictedOutcome := ()
  observedOutcome := ()
  precedes := fun _ _ => True
  predictionPrecedesOutcome := True.intro
  predictionMatchesOutcome := rfl

abbrev SampleClosureVersion := ClosureVersion
  Unit Unit Bool Bool Unit Bool Unit Unit Unit Unit Unit
  Unit Unit Unit Unit Unit Unit
  Bool Unit Unit Unit Unit Unit Unit Bool Bool Unit Unit Unit

def firstVersion : SampleClosureVersion where
  curvature := curvature false false
  relationOfObservation := id
  admission := admission false false true false (by decide)
  returnEvidenceOf := id
  audit := firstAudit
  auditPerspective := rfl
  auditGoal := rfl
  auditTranslation := rfl
  auditReturn := rfl
  nextRelationHeldOut := rfl

def secondVersion : SampleClosureVersion where
  curvature := curvature true false
  relationOfObservation := id
  admission := admission true false false true (by decide)
  returnEvidenceOf := id
  audit := secondAudit
  auditPerspective := rfl
  auditGoal := rfl
  auditTranslation := rfl
  auditReturn := rfl
  nextRelationHeldOut := rfl

/-- A concrete two-version run is inhabited without treating a re-entered relation as fresh. -/
theorem succession : Succession firstVersion secondVersion where
  perspectiveRecentered := rfl
  verifierContinues := rfl
  frameContinues := rfl
  reenteredRelationObserved := rfl
  freshHeldOutRelation := by decide

theorem succession_exists : Nonempty (Succession firstVersion secondVersion) :=
  ⟨succession⟩

/-- The re-entered relation is `false`; the second version's fresh opening is `true`. -/
theorem reentry_and_fresh_opening_are_distinct :
    secondVersion.relationOfObservation secondVersion.curvature.observation = false ∧
      secondVersion.admission.nextRelation = true :=
  ⟨rfl, rfl⟩

end FiniteModel

end ClosureVersion
end DerivedSlearnClosureVersion
end Slearn

#print axioms Slearn.DerivedSlearnClosureVersion.ClosureVersion.source_goal_has_relative_closureTruth
#print axioms Slearn.DerivedSlearnClosureVersion.ClosureVersion.successor_perspective_changes
#print axioms Slearn.DerivedSlearnClosureVersion.ClosureVersion.audit_return_tracks_receipt
#print axioms Slearn.DerivedSlearnClosureVersion.ClosureVersion.further_relation_is_held_out
#print axioms Slearn.DerivedSlearnClosureVersion.ClosureVersion.predecessor_leaves_further_relation_open
#print axioms Slearn.DerivedSlearnClosureVersion.ClosureVersion.derived_verifier_evaluates_further_relation
#print axioms Slearn.DerivedSlearnClosureVersion.ClosureVersion.derived_verifier_changes
#print axioms Slearn.DerivedSlearnClosureVersion.ClosureVersion.derived_axiometry_changes
#print axioms Slearn.DerivedSlearnClosureVersion.ClosureVersion.generated_map_has_attempted_project
#print axioms Slearn.DerivedSlearnClosureVersion.ClosureVersion.generated_map_has_returned_experience
#print axioms Slearn.DerivedSlearnClosureVersion.ClosureVersion.generated_map_reopens
#print axioms Slearn.DerivedSlearnClosureVersion.ClosureVersion.Succession.next_perspective_is_prior_return
#print axioms Slearn.DerivedSlearnClosureVersion.ClosureVersion.Succession.next_verifier_is_prior_derivation
#print axioms Slearn.DerivedSlearnClosureVersion.ClosureVersion.Succession.next_frame_is_prior_derivation
#print axioms Slearn.DerivedSlearnClosureVersion.ClosureVersion.Succession.further_relation_reenters
#print axioms Slearn.DerivedSlearnClosureVersion.ClosureVersion.Succession.reentered_relation_is_evaluated_by_successor
#print axioms Slearn.DerivedSlearnClosureVersion.ClosureVersion.Succession.fresh_held_out_relation_is_open
#print axioms Slearn.DerivedSlearnClosureVersion.ClosureVersion.Succession.fresh_held_out_relation_is_distinct
#print axioms Slearn.DerivedSlearnClosureVersion.ClosureVersion.Succession.receipt
#print axioms Slearn.DerivedSlearnClosureVersion.ClosureVersion.FiniteModel.succession_exists
#print axioms Slearn.DerivedSlearnClosureVersion.ClosureVersion.FiniteModel.reentry_and_fresh_opening_are_distinct
