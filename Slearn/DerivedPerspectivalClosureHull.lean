import Slearn.PerspectivalCurvatureClosurePrimitives

/-
Ledger-derived perspectival closure hull for Slearn.

This module builds the map-facing structure only from source curvature packets.
A PATH packet contributes a prospective branch and its OPEN remainder.  A
continued, reviewed admission additionally contributes an experience fibre, a
returned-basis node, a successor perspective, and a next relation.  There is
no independent graph, profile, curriculum, layout, or completion flag.

The result is a structural generator, not a claim that a list of declared
packets is true, sufficient, pedagogically valuable, or an implementation of a
particular user interface.
-/

universe u

namespace Slearn
namespace PerspectivalClosureHull

open PerspectivalCurvature

abbrev PacketCurvature
    (Anchor Claim Observation Perspective Belief Goal Why Explanation Definition Path Witness : Type u) :=
  CurvaturePrimitives Anchor Claim Observation Perspective Belief Goal Why Explanation Definition Path Witness

/-- A ledger contains either a prospective source path or a reviewed continued admission. -/
inductive LedgerPacket
    (Anchor Claim Observation Perspective Belief Goal Why Explanation Definition Path Witness
      Attempt Material CounterReading Comparison Review Receipt NextRelation : Type u) where
  | path (curvature : PacketCurvature Anchor Claim Observation Perspective Belief Goal Why Explanation Definition Path Witness) :
      LedgerPacket Anchor Claim Observation Perspective Belief Goal Why Explanation Definition Path Witness
        Attempt Material CounterReading Comparison Review Receipt NextRelation
  | returned
      (curvature : PacketCurvature Anchor Claim Observation Perspective Belief Goal Why Explanation Definition Path Witness)
      (admission : ContinuedAdmission curvature Attempt Material CounterReading Comparison Review Receipt NextRelation) :
      LedgerPacket Anchor Claim Observation Perspective Belief Goal Why Explanation Definition Path Witness
        Attempt Material CounterReading Comparison Review Receipt NextRelation

namespace LedgerPacket

variable {Anchor Claim Observation Perspective Belief Goal Why Explanation Definition Path Witness
  Attempt Material CounterReading Comparison Review Receipt NextRelation : Type u}

def curvature
    (P : LedgerPacket Anchor Claim Observation Perspective Belief Goal Why Explanation Definition Path Witness
      Attempt Material CounterReading Comparison Review Receipt NextRelation) :
    PacketCurvature Anchor Claim Observation Perspective Belief Goal Why Explanation Definition Path Witness :=
  match P with
  | .path C => C
  | .returned C _ => C

/-- A returned ledger item contains a continued admission; a PATH item does not claim one. -/
def isReturned
    (P : LedgerPacket Anchor Claim Observation Perspective Belief Goal Why Explanation Definition Path Witness
      Attempt Material CounterReading Comparison Review Receipt NextRelation) : Bool :=
  match P with
  | .path _ => false
  | .returned _ _ => true

end LedgerPacket

/-- The roles that a closure packet is permitted to project into the Slearn map. -/
inductive DerivedNode
    (Anchor Observation Perspective Belief Goal Why Explanation Definition Path Attempt Witness Receipt NextRelation : Type u)
  | source (anchor : Anchor)
  | observation (value : Observation)
  | perspective (value : Perspective)
  | beliefLimit (value : Belief)
  | why (value : Why)
  | semanticExplanation (value : Explanation)
  | operativeExplanation (value : Explanation)
  | definition (value : Definition)
  | prospectiveLesson (reason : Why) (meaning : Definition)
  | forwardPath (value : Path)
  | counterPath (value : Path)
  | goal (value : Goal)
  | project (attempt : Attempt)
  | returnedBasis (value : Witness)
  | experience (receipt : Receipt)
  | successorPerspective (value : Perspective)
  | worldContinuation (value : NextRelation)
  | openRemainder (anchor : Anchor)
  deriving Repr

/-- Links name only relations carried by the closure packet; they contain no display coordinates. -/
inductive DerivedLinkKind
  | sourceToObservation
  | situatesPerspective
  | beliefConstrainsWhy
  | semanticExplains
  | operativeExplains
  | definitionMakesLesson
  | whyMakesLesson
  | forwardPathToGoal
  | counterPathToPerspective
  | translationForward
  | translationReturn
  | prospectiveOpen
  | lessonToProject
  | returnedBasis
  | projectExperience
  | experienceFibre
  | successorContinuation
  | continuedOpen
  deriving DecidableEq, Repr

structure DerivedLink
    (Anchor Observation Perspective Belief Goal Why Explanation Definition Path Attempt Witness Receipt NextRelation : Type u) where
  source : DerivedNode Anchor Observation Perspective Belief Goal Why Explanation Definition Path Attempt Witness Receipt NextRelation
  to : DerivedNode Anchor Observation Perspective Belief Goal Why Explanation Definition Path Attempt Witness Receipt NextRelation
  kind : DerivedLinkKind

/-- The retained record projected by a reviewed return. -/
structure ExperienceFibre (Perspective Witness Receipt NextRelation : Type u) where
  receipt : Receipt
  successor : Perspective
  basis : Witness
  nextRelation : NextRelation

namespace ExperienceFibre

variable {Anchor Claim Observation Perspective Belief Goal Why Explanation Definition Path Witness
  Attempt Material CounterReading Comparison Review Receipt NextRelation : Type u}
variable {C : PacketCurvature Anchor Claim Observation Perspective Belief Goal Why Explanation Definition Path Witness}

/-- A continued admission yields an experience fibre with its returned witness basis. -/
def ofAdmission
    (A : ContinuedAdmission C Attempt Material CounterReading Comparison Review Receipt NextRelation) :
    ExperienceFibre Perspective Witness Receipt NextRelation where
  receipt := A.receipt
  successor := A.successor
  basis := C.translation.localWitness A.successor
  nextRelation := A.nextRelation

/-- An experience fibre preserves the exact receipt supplied for the return. -/
theorem receipt_preserved
    (A : ContinuedAdmission C Attempt Material CounterReading Comparison Review Receipt NextRelation) :
    (ofAdmission A).receipt = A.receipt :=
  rfl

end ExperienceFibre

namespace DerivedNode

variable {Anchor Claim Observation Perspective Belief Goal Why Explanation Definition Path Witness
  Attempt Material CounterReading Comparison Review Receipt NextRelation : Type u}

local notation "Node" =>
  DerivedNode Anchor Observation Perspective Belief Goal Why Explanation Definition Path Attempt Witness Receipt NextRelation

local notation "Link" =>
  DerivedLink Anchor Observation Perspective Belief Goal Why Explanation Definition Path Attempt Witness Receipt NextRelation

local notation "Packet" =>
  LedgerPacket Anchor Claim Observation Perspective Belief Goal Why Explanation Definition Path Witness
    Attempt Material CounterReading Comparison Review Receipt NextRelation

local notation "Curvature" =>
  PacketCurvature Anchor Claim Observation Perspective Belief Goal Why Explanation Definition Path Witness

/-- A prospective lesson is derived from the paired presentation/definition primitive. -/
def lessonOf (C : Curvature) : Node :=
  .prospectiveLesson C.why C.definition

/-- The branch present as soon as a source-derived PATH exists. -/
def prospectiveNodes (C : Curvature) : List Node :=
  [ .source C.sourceAnchor,
    .observation C.observation,
    .perspective C.perspective,
    .beliefLimit C.beliefLimit,
    .why C.why,
    .semanticExplanation C.semanticExplanation,
    .operativeExplanation C.operativeExplanation,
    .definition C.definition,
    lessonOf C,
    .forwardPath C.forwardPath,
    .counterPath C.counterPath,
    .goal C.goalLimit,
    .openRemainder C.sourceAnchor ]

/-- The links of a prospective branch, including both translation orientations. -/
def prospectiveLinks (C : Curvature) : List Link :=
  [ ⟨.source C.sourceAnchor, .observation C.observation, .sourceToObservation⟩,
    ⟨.observation C.observation, .perspective C.perspective, .situatesPerspective⟩,
    ⟨.perspective C.perspective, .beliefLimit C.beliefLimit, .situatesPerspective⟩,
    ⟨.beliefLimit C.beliefLimit, .why C.why, .beliefConstrainsWhy⟩,
    ⟨.why C.why, .semanticExplanation C.semanticExplanation, .semanticExplains⟩,
    ⟨.why C.why, .operativeExplanation C.operativeExplanation, .operativeExplains⟩,
    ⟨.semanticExplanation C.semanticExplanation, .definition C.definition, .semanticExplains⟩,
    ⟨.operativeExplanation C.operativeExplanation, .definition C.definition, .operativeExplains⟩,
    ⟨.definition C.definition, lessonOf C, .definitionMakesLesson⟩,
    ⟨.why C.why, lessonOf C, .whyMakesLesson⟩,
    ⟨.perspective C.perspective, .forwardPath C.forwardPath, .translationForward⟩,
    ⟨.forwardPath C.forwardPath, .goal C.goalLimit, .forwardPathToGoal⟩,
    ⟨.goal C.goalLimit, .counterPath C.counterPath, .translationReturn⟩,
    ⟨.counterPath C.counterPath, .perspective C.perspective, .counterPathToPerspective⟩,
    ⟨.counterPath C.counterPath, .openRemainder C.sourceAnchor, .prospectiveOpen⟩ ]

/-- Perspective-to-goal zoom is a derived reading of a packet's own branch. -/
def zoomOut (C : Curvature) : List Node :=
  [ .perspective C.perspective,
    .beliefLimit C.beliefLimit,
    .why C.why,
    lessonOf C,
    .forwardPath C.forwardPath,
    .goal C.goalLimit ]

/-- Goal-to-perspective zoom keeps the counter-path and operative presentation visible. -/
def zoomIn (C : Curvature) : List Node :=
  [ .goal C.goalLimit,
    .counterPath C.counterPath,
    .operativeExplanation C.operativeExplanation,
    .definition C.definition,
    .why C.why,
    .beliefLimit C.beliefLimit,
    .perspective C.perspective ]

/-- The extra map structure created by a reviewed, nonterminal admission. -/
def returnedNodes
    (C : Curvature)
    (A : ContinuedAdmission C Attempt Material CounterReading Comparison Review Receipt NextRelation) : List Node :=
  [ .returnedBasis (C.translation.localWitness A.successor),
    .project A.reviewed.interaction.attempt,
    .experience A.receipt,
    .successorPerspective A.successor,
    .worldContinuation A.nextRelation,
    .openRemainder C.sourceAnchor ]

/-- The returned fibre closes a basis, records an experience, and reopens at its continuation. -/
def returnedLinks
    (C : Curvature)
    (A : ContinuedAdmission C Attempt Material CounterReading Comparison Review Receipt NextRelation) : List Link :=
  [ ⟨.goal C.goalLimit, .returnedBasis (C.translation.localWitness A.successor), .returnedBasis⟩,
    ⟨lessonOf C, .project A.reviewed.interaction.attempt, .lessonToProject⟩,
    ⟨.project A.reviewed.interaction.attempt, .experience A.receipt, .projectExperience⟩,
    ⟨.returnedBasis (C.translation.localWitness A.successor), .experience A.receipt, .experienceFibre⟩,
    ⟨.experience A.receipt, .successorPerspective A.successor, .experienceFibre⟩,
    ⟨.successorPerspective A.successor, .worldContinuation A.nextRelation, .successorContinuation⟩,
    ⟨.worldContinuation A.nextRelation, .openRemainder C.sourceAnchor, .continuedOpen⟩ ]

/-- The map hull is generated by packet cases; it has no separate graph input. -/
def nodesOf : Packet → List Node
  | .path C => prospectiveNodes C
  | .returned C A => prospectiveNodes C ++ returnedNodes C A

/-- The links are generated in parallel from the same packet cases. -/
def linksOf : Packet → List Link
  | .path C => prospectiveLinks C
  | .returned C A => prospectiveLinks C ++ returnedLinks C A

/-- A dynamic Slearn map is the closure hull of its ledger, not an authored graph. -/
def closureHull (ledger : List Packet) : List Node :=
  ledger.flatMap nodesOf

/-- All map relations are likewise a projection of the same ledger. -/
def closureLinks (ledger : List Packet) : List Link :=
  ledger.flatMap linksOf

/-- Successor perspectives are effects of admitted packets, never inputs to a PATH packet. -/
def perspectiveUpdates (ledger : List Packet) : List Perspective :=
  ledger.foldr (fun packet updates =>
    match packet with
    | .path _ => updates
    | .returned _ A => A.successor :: updates) []

/-- A PATH packet projects a prospective branch and an OPEN remainder. -/
theorem path_projects_prospective_lesson
    (C : Curvature) :
    lessonOf C ∈ nodesOf (.path C : Packet) := by
  simp [nodesOf, prospectiveNodes]

/-- A PATH packet has no constructed experience fibre. -/
theorem path_keeps_return_open
    (C : Curvature) :
    .openRemainder C.sourceAnchor ∈ nodesOf (.path C : Packet) := by
  simp [nodesOf, prospectiveNodes]

/-- A returned packet projects the receipt as an experience fibre. -/
theorem returned_projects_experience
    (C : Curvature)
    (A : ContinuedAdmission C Attempt Material CounterReading Comparison Review Receipt NextRelation) :
    .experience A.receipt ∈ nodesOf (.returned C A : Packet) := by
  simp [nodesOf, prospectiveNodes, returnedNodes]

/-- A project appears only with the attempted interaction carried by a returned packet. -/
theorem returned_projects_attempt
    (C : Curvature)
    (A : ContinuedAdmission C Attempt Material CounterReading Comparison Review Receipt NextRelation) :
    .project A.reviewed.interaction.attempt ∈ nodesOf (.returned C A : Packet) := by
  simp [nodesOf, prospectiveNodes, returnedNodes]

/-- A returned packet still ends in an OPEN remainder through its next relation. -/
theorem returned_reopens
    (C : Curvature)
    (A : ContinuedAdmission C Attempt Material CounterReading Comparison Review Receipt NextRelation) :
    .openRemainder C.sourceAnchor ∈ nodesOf (.returned C A : Packet) := by
  simp [nodesOf, prospectiveNodes, returnedNodes]

/-- Equal returned witness bases project to the same basis node and therefore merge structurally. -/
theorem equal_returned_bases_merge
    {C D : Curvature}
    (A : ContinuedAdmission C Attempt Material CounterReading Comparison Review Receipt NextRelation)
    (B : ContinuedAdmission D Attempt Material CounterReading Comparison Review Receipt NextRelation)
    (h : C.translation.localWitness A.successor = D.translation.localWitness B.successor) :
    (DerivedNode.returnedBasis (C.translation.localWitness A.successor) : Node) =
      DerivedNode.returnedBasis (D.translation.localWitness B.successor) := by
  rw [h]

/-- An admitted packet's successor is included in the ledger-derived update stream. -/
theorem returned_projects_successor_update
    (C : Curvature)
    (A : ContinuedAdmission C Attempt Material CounterReading Comparison Review Receipt NextRelation) :
    A.successor ∈ perspectiveUpdates [(.returned C A : Packet)] := by
  simp [perspectiveUpdates]

end DerivedNode

end PerspectivalClosureHull
end Slearn

#print axioms Slearn.PerspectivalClosureHull.ExperienceFibre.receipt_preserved
#print axioms Slearn.PerspectivalClosureHull.DerivedNode.path_projects_prospective_lesson
#print axioms Slearn.PerspectivalClosureHull.DerivedNode.path_keeps_return_open
#print axioms Slearn.PerspectivalClosureHull.DerivedNode.returned_projects_experience
#print axioms Slearn.PerspectivalClosureHull.DerivedNode.returned_projects_attempt
#print axioms Slearn.PerspectivalClosureHull.DerivedNode.returned_reopens
#print axioms Slearn.PerspectivalClosureHull.DerivedNode.equal_returned_bases_merge
#print axioms Slearn.PerspectivalClosureHull.DerivedNode.returned_projects_successor_update
