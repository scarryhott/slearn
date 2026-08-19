import Slearn.DerivedSlearnClosureVersion

/-
Replayable audit for a derived Slearn closure succession.

This module formalizes a narrow reading of the current source requirement:
truth-level closure and historical succession are distinct. A published step
record is auditable only if an identity distinct from the publisher can replay
the exact returned-perspective, verifier, frame, and re-entered-relation
bridges that make it lawful.

`auditor ≠ publisher` is an identity separation inside the model. It is not a
proof that any real person, process, evidence source, or outcome is
independent. The module proves no empirical fact and no general translation
invariance beyond the imported contracts.
-/

universe u

namespace Slearn
namespace ReplayableSlearnClosureAudit

open PerspectivalCurvature
open AuditableChangingAxiometry
open DerivedSlearnClosureVersion
open DerivedSlearnClosureVersion.ClosureVersion

/-- The named carrier types in which a Slearn closure succession is replayed. -/
structure Context where
  Anchor : Type u
  Claim : Type u
  Observation : Type u
  Perspective : Type u
  Belief : Type u
  Goal : Type u
  Why : Type u
  Explanation : Type u
  Definition : Type u
  Path : Type u
  Witness : Type u
  Attempt : Type u
  Material : Type u
  CounterReading : Type u
  Comparison : Type u
  Review : Type u
  Receipt : Type u
  Frame : Type u
  NativeTranslation : Type u
  Validation : Type u
  ReturnEvidence : Type u
  Residue : Type u
  FrameGeneration : Type u
  FrameFreeze : Type u
  Relation : Type u
  Verdict : Type u
  HeldOutEvidence : Type u
  ExternalEvidence : Type u
  Outcome : Type u

namespace Context

abbrev Version (C : Context) := DerivedSlearnClosureVersion.ClosureVersion
  C.Anchor C.Claim C.Observation C.Perspective C.Belief C.Goal C.Why C.Explanation C.Definition C.Path C.Witness
  C.Attempt C.Material C.CounterReading C.Comparison C.Review C.Receipt
  C.Frame C.NativeTranslation C.Validation C.ReturnEvidence C.Residue
  C.FrameGeneration C.FrameFreeze C.Relation C.Verdict C.HeldOutEvidence C.ExternalEvidence C.Outcome

end Context

/--
The publishable information needed to replay one claimed version succession.
The record can be forged: `Lawful` below, rather than construction alone,
checks whether its values connect the predecessor and successor.
-/
structure StepRecord (C : Context) (first second : C.Version) (Publisher : Type u) where
  publisher : Publisher
  returnedPerspective : C.Perspective
  derivedVerifier : Verifier C.Frame C.Relation C.Verdict
  derivedFrame : C.Frame
  reenteredRelation : C.Relation

namespace StepRecord

variable {C : Context} {Publisher : Type u} {auditor : Publisher}
variable {first second : C.Version}

/--
The exact replay obligations. They rebuild the four closure-version bridges
from published fields and additionally prevent the successor's fresh held-out
relation from being confused with its observed re-entry.
-/
def Lawful (record : StepRecord C first second Publisher) : Prop :=
  record.returnedPerspective = first.admission.successor ∧
    second.curvature.perspective = record.returnedPerspective ∧
    record.derivedVerifier = first.derivedVerifier ∧
    second.currentVerifier = record.derivedVerifier ∧
    record.derivedFrame = first.derivedAxiometry.frame ∧
    second.audit.completion.current.frame = record.derivedFrame ∧
    record.reenteredRelation = first.admission.nextRelation ∧
    second.relationOfObservation second.curvature.observation = record.reenteredRelation ∧
    second.admission.nextRelation ≠ record.reenteredRelation

/-- Both versions carry relation-relative perspective/goal closure. -/
def TruthAgreement (_record : StepRecord C first second Publisher) : Prop :=
  first.curvature.translation.closes first.curvature.perspective first.curvature.goalLimit ∧
    second.curvature.translation.closes second.curvature.perspective second.curvature.goalLimit

/-- Truth-level agreement is supplied by every `ClosureVersion`; it says nothing yet about lineage. -/
theorem truthAgreement (record : StepRecord C first second Publisher) :
    record.TruthAgreement :=
  ⟨first.source_goal_has_relative_closureTruth,
    second.source_goal_has_relative_closureTruth⟩

/-- A lawful published record reconstructs the actual closure-version succession. -/
theorem Lawful.toSuccession {record : StepRecord C first second Publisher}
    (lawful : record.Lawful) : Succession first second := by
  rcases lawful with ⟨returned, perspective, verifier, currentVerifier,
    derivedFrame, currentFrame, reentered, observation, fresh⟩
  refine {
    perspectiveRecentered := perspective.trans returned
    verifierContinues := ?_
    frameContinues := currentFrame.trans derivedFrame
    reenteredRelationObserved := observation.trans reentered
    freshHeldOutRelation := by
      intro same
      exact fresh (same.trans observation)
  }
  change second.currentVerifier = first.derivedVerifier
  exact currentVerifier.trans verifier

/-- Publishing the fields of an actual succession makes a lawful replay record. -/
def ofSuccession (publisher : Publisher) (_succession : Succession first second) :
    StepRecord C first second Publisher where
  publisher := publisher
  returnedPerspective := first.admission.successor
  derivedVerifier := first.derivedVerifier
  derivedFrame := first.derivedAxiometry.frame
  reenteredRelation := first.admission.nextRelation

theorem ofSuccession_lawful (publisher : Publisher) (succession : Succession first second) :
    (ofSuccession publisher succession).Lawful := by
  refine ⟨rfl, succession.next_perspective_is_prior_return, rfl, ?_, rfl, ?_, rfl,
    succession.further_relation_reenters, ?_⟩
  · exact succession.next_verifier_is_prior_derivation
  · exact succession.next_frame_is_prior_derivation
  · intro same
    exact succession.fresh_held_out_relation_is_distinct
      (same.trans succession.further_relation_reenters.symm)

/-- A replay audit accepts only an identity-distinct, lawful published record. -/
def auditStep (auditor : Publisher) (record : StepRecord C first second Publisher) : Prop :=
  auditor ≠ record.publisher ∧ record.Lawful

/-- The truth condition for one audited closure step: truth relation plus replayable lineage. -/
def TrueClosure (auditor : Publisher) (record : StepRecord C first second Publisher) : Prop :=
  record.TruthAgreement ∧ auditStep auditor record

/-- Under stated identity separation, auditability is exactly lawful replayability. -/
theorem auditStep_iff_lawful (record : StepRecord C first second Publisher)
    (independent : auditor ≠ record.publisher) :
    auditStep auditor record ↔ record.Lawful := by
  constructor
  · exact fun audited => audited.2
  · exact fun lawful => ⟨independent, lawful⟩

/-- With a separated auditor, true closure is exactly a lawful succession record. -/
theorem trueClosure_iff_lawful (record : StepRecord C first second Publisher)
    (independent : auditor ≠ record.publisher) :
    TrueClosure auditor record ↔ record.Lawful := by
  constructor
  · exact fun closed => closed.2.2
  · intro lawful
    exact ⟨record.truthAgreement, ⟨independent, lawful⟩⟩

/-- A publisher cannot accept its own record as an independent replay. -/
theorem self_authored_fails_audit (record : StepRecord C first second Publisher) :
    ¬ auditStep record.publisher record := by
  intro audited
  exact audited.1 rfl

/-- A true closure record always carries a reconstructible Slearn succession. -/
theorem trueClosure_has_succession (record : StepRecord C first second Publisher)
    (closed : TrueClosure auditor record) :
    Nonempty (Succession first second) :=
  ⟨closed.2.2.toSuccession⟩

end StepRecord

namespace FiniteModel

open DerivedSlearnClosureVersion.ClosureVersion.FiniteModel

def context : Context where
  Anchor := Unit
  Claim := Unit
  Observation := Bool
  Perspective := Bool
  Belief := Unit
  Goal := Bool
  Why := Unit
  Explanation := Unit
  Definition := Unit
  Path := Unit
  Witness := Unit
  Attempt := Unit
  Material := Unit
  CounterReading := Unit
  Comparison := Unit
  Review := Unit
  Receipt := Unit
  Frame := Bool
  NativeTranslation := Unit
  Validation := Unit
  ReturnEvidence := Unit
  Residue := Unit
  FrameGeneration := Unit
  FrameFreeze := Unit
  Relation := Bool
  Verdict := Bool
  HeldOutEvidence := Unit
  ExternalEvidence := Unit
  Outcome := Unit

/-- A truth-agreeing but forged successor record: it does not recenter on the prior return. -/
def forgedRecord : StepRecord context firstVersion firstVersion Bool where
  publisher := false
  returnedPerspective := true
  derivedVerifier := firstDerivedVerifier
  derivedFrame := true
  reenteredRelation := false

/-- Relative truth agreement alone does not establish a lawful historical succession. -/
theorem truth_agreement_does_not_certify_succession :
    forgedRecord.TruthAgreement ∧ ¬ forgedRecord.Lawful := by
  constructor
  · exact forgedRecord.truthAgreement
  · intro lawful
    have perspective := lawful.2.1
    change false = true at perspective
    cases perspective

/-- An actual published record has true closure when replayed by a distinct identity. -/
theorem independent_replay_accepts_actual_succession :
    (StepRecord.ofSuccession (C := context) (first := firstVersion) (second := secondVersion)
      false succession).TrueClosure true := by
  apply (StepRecord.trueClosure_iff_lawful _ (by decide)).mpr
  exact StepRecord.ofSuccession_lawful false succession

/-- A withheld/forged lineage cannot be replaced by truth agreement in the finite model. -/
theorem forged_record_is_not_true_closure :
    ¬ forgedRecord.TrueClosure true := by
  intro closed
  exact truth_agreement_does_not_certify_succession.2 closed.2.2

end FiniteModel

end ReplayableSlearnClosureAudit
end Slearn

#print axioms Slearn.ReplayableSlearnClosureAudit.StepRecord.truthAgreement
#print axioms Slearn.ReplayableSlearnClosureAudit.StepRecord.Lawful.toSuccession
#print axioms Slearn.ReplayableSlearnClosureAudit.StepRecord.ofSuccession_lawful
#print axioms Slearn.ReplayableSlearnClosureAudit.StepRecord.auditStep_iff_lawful
#print axioms Slearn.ReplayableSlearnClosureAudit.StepRecord.trueClosure_iff_lawful
#print axioms Slearn.ReplayableSlearnClosureAudit.StepRecord.self_authored_fails_audit
#print axioms Slearn.ReplayableSlearnClosureAudit.StepRecord.trueClosure_has_succession
#print axioms Slearn.ReplayableSlearnClosureAudit.FiniteModel.truth_agreement_does_not_certify_succession
#print axioms Slearn.ReplayableSlearnClosureAudit.FiniteModel.independent_replay_accepts_actual_succession
#print axioms Slearn.ReplayableSlearnClosureAudit.FiniteModel.forged_record_is_not_true_closure
