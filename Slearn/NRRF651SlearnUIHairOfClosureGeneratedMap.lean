import Slearn.ClosedTopologicalTranslation

/-
Witness-generated Slearn UI map and hair contract.

This is a reconstruction of the interface contract described in the primary
Slearn source material and in the supplied NRRF651 summary.  The separately
claimed NRRF651 source file was not available in this checkout, so this module
does not claim to reproduce or audit that unavailable implementation.

The proved direction is deliberately one-way:

    witnessed learner kernel -> generated map.

It does not prove a unique UI, empirical independence of returns, or a
physical reading of the hair transport.  It makes the UI admission boundary
explicit: lessons require all three WHY witnesses, project steps require
attempts, and returned experience requires receipts.
-/

universe u v w x

namespace Slearn

namespace UIHairOfClosure

/--
The learner-side kernel.  It contains relations, witnesses, attempts, and
receipts; it contains no screen position, colour, mesh, card, or drawing.
-/
structure WitnessedKernel (Value : Type u) (Occurrence : Type v) where
  admittedValue : Value → Prop
  inBounds : Occurrence → Prop
  valueOf : Occurrence → Value
  depth : Occurrence → Nat
  domainWhy : Occurrence → Prop
  perspectiveWhy : Occurrence → Prop
  goalWhy : Occurrence → Prop
  attempt : Occurrence → Prop
  returnReceipt : Occurrence → Prop
  bounded_value_admitted : ∀ {o}, inBounds o → admittedValue (valueOf o)
  return_requires_attempt : ∀ {o}, returnReceipt o → attempt o
  attempt_requires_threeWhy : ∀ {o}, attempt o →
    domainWhy o ∧ perspectiveWhy o ∧ goalWhy o

namespace WitnessedKernel

variable {Value : Type u} {Occurrence : Type v}

/-- A lesson has a WHY only when all three witness roles are present. -/
def hasWhy (K : WitnessedKernel Value Occurrence) (o : Occurrence) : Prop :=
  K.domainWhy o ∧ K.perspectiveWhy o ∧ K.goalWhy o

/-- No attempt is admitted without all three WHY witnesses. -/
theorem attempt_requires_why
    (K : WitnessedKernel Value Occurrence) {o : Occurrence}
    (h : K.attempt o) : K.hasWhy o :=
  K.attempt_requires_threeWhy h

/-- No returned experience is admitted without a prior attempt. -/
theorem receipt_requires_attempt
    (K : WitnessedKernel Value Occurrence) {o : Occurrence}
    (h : K.returnReceipt o) : K.attempt o :=
  K.return_requires_attempt h

end WitnessedKernel

/-- The source-derived canonical node family, before any visual coordinates. -/
inductive MapNode (Value : Type u) (Occurrence : Type v)
  | core
  | brain
  | value (v : Value)
  | belief (v : Value)
  | why (o : Occurrence)
  | goal (o : Occurrence)
  | lesson (o : Occurrence)
  | project (o : Occurrence)
  | impact
  | balance
  | slearn
  | dream

/--
The source-derived link family.  `lessonProjectTurn` is the 90-degree turn;
`equalDepthRung` connects a lesson and project only through their common
occurrence/depth carrier.
-/
inductive MapLink (Value : Type u) (Occurrence : Type v)
  | coreBrain
  | brainValue (v : Value)
  | valueBelief (v : Value)
  | beliefWhy (o : Occurrence)
  | whyGoal (o : Occurrence)
  | goalLesson (o : Occurrence)
  | lessonAscent (o : Occurrence)
  | lessonProjectTurn (o : Occurrence)
  | projectDescent (o : Occurrence)
  | projectImpact (o : Occurrence)
  | impactBalance
  | balanceSlearn
  | slearnDream
  | equalDepthRung (o : Occurrence)
  | whyLink (o : Occurrence)

/-- A generated map is only a relation over source-derived nodes and links. -/
structure MapRelation (Value : Type u) (Occurrence : Type v) where
  node : MapNode Value Occurrence → Prop
  link : MapLink Value Occurrence → Prop

namespace MapRelation

variable {Value : Type u} {Occurrence : Type v}

@[ext] theorem ext {M N : MapRelation Value Occurrence}
    (hNode : M.node = N.node) (hLink : M.link = N.link) : M = N := by
  cases M
  cases N
  cases hNode
  cases hLink
  rfl

end MapRelation

namespace WitnessedKernel

variable {Value : Type u} {Occurrence : Type v}
variable (K : WitnessedKernel Value Occurrence)

/-- The intended map before witness/attempt gating, restricted to current bounds. -/
def canonicalNode : MapNode Value Occurrence → Prop
  | .core | .brain | .impact | .balance | .slearn | .dream => True
  | .value v | .belief v => K.admittedValue v
  | .why o | .goal o | .lesson o | .project o => K.inBounds o

/-- The kernel-generated node relation. -/
def genNode : MapNode Value Occurrence → Prop
  | .core | .brain | .impact | .balance | .slearn | .dream => True
  | .value v | .belief v => K.admittedValue v
  | .why o | .goal o | .lesson o => K.inBounds o ∧ K.hasWhy o
  | .project o => K.inBounds o ∧ K.attempt o

/-- The canonical link relation, restricted to the current occurrence bounds. -/
def canonicalLink : MapLink Value Occurrence → Prop
  | .coreBrain | .impactBalance | .balanceSlearn | .slearnDream => True
  | .brainValue v | .valueBelief v => K.admittedValue v
  | .beliefWhy o | .whyGoal o | .goalLesson o | .lessonAscent o | .lessonProjectTurn o
    | .projectDescent o | .projectImpact o | .equalDepthRung o | .whyLink o =>
      K.inBounds o

/-- The generated link relation.  It never inserts an unwitnessed lesson or unattempted step. -/
def genLink : MapLink Value Occurrence → Prop
  | .coreBrain | .impactBalance | .balanceSlearn | .slearnDream => True
  | .brainValue v | .valueBelief v => K.admittedValue v
  | .beliefWhy o | .whyGoal o | .goalLesson o | .lessonAscent o | .whyLink o =>
      K.inBounds o ∧ K.hasWhy o
  | .lessonProjectTurn o | .equalDepthRung o =>
      K.inBounds o ∧ K.hasWhy o ∧ K.attempt o
  | .projectDescent o | .projectImpact o =>
      K.inBounds o ∧ K.attempt o

/-- The visible relation generated from the learner-side kernel. -/
def generatedMap : MapRelation Value Occurrence where
  node := K.genNode
  link := K.genLink

/-- The complete source-derived relation at the current bounds. -/
def canonicalMap : MapRelation Value Occurrence where
  node := K.canonicalNode
  link := K.canonicalLink

/-- Every bounded occurrence has its full WHY and an attempt. -/
def Saturated : Prop :=
  ∀ o, K.inBounds o → K.hasWhy o ∧ K.attempt o

/-- Under saturation, every canonical node is generated and no other node appears. -/
theorem saturated_genNode (h : K.Saturated) :
    ∀ n, K.genNode n ↔ K.canonicalNode n := by
  intro n
  cases n with
  | core | brain | impact | balance | slearn | dream => simp [genNode, canonicalNode]
  | value v | belief v => simp [genNode, canonicalNode]
  | why o | goal o | lesson o =>
      constructor
      · intro hn
        exact hn.1
      · intro hc
        exact ⟨hc, (h o hc).1⟩
  | project o =>
      constructor
      · intro hn
        exact hn.1
      · intro hc
        exact ⟨hc, (h o hc).2⟩

/-- Under saturation, every canonical link is generated and no other link appears. -/
theorem saturated_genLink (h : K.Saturated) :
    ∀ l, K.genLink l ↔ K.canonicalLink l := by
  intro l
  cases l with
  | coreBrain | impactBalance | balanceSlearn | slearnDream =>
      simp [genLink, canonicalLink]
  | brainValue v | valueBelief v => simp [genLink, canonicalLink]
  | beliefWhy o | whyGoal o | goalLesson o | lessonAscent o | whyLink o =>
      constructor
      · intro hl
        exact hl.1
      · intro hc
        exact ⟨hc, (h o hc).1⟩
  | lessonProjectTurn o | equalDepthRung o =>
      constructor
      · intro hl
        exact hl.1
      · intro hc
        exact ⟨hc, (h o hc).1, (h o hc).2⟩
  | projectDescent o | projectImpact o =>
      constructor
      · intro hl
        exact hl.1
      · intro hc
        exact ⟨hc, (h o hc).2⟩

/-- A saturated kernel generates exactly the canonical bounded map. -/
theorem saturated_generatedMap (h : K.Saturated) :
    K.generatedMap = K.canonicalMap := by
  apply MapRelation.ext
  · funext n
    apply propext
    exact K.saturated_genNode h n
  · funext l
    apply propext
    exact K.saturated_genLink h l

/-- An unopened kernel cannot draw an unwitnessed lesson node. -/
theorem no_unwitnessed_lesson
    {o : Occurrence} (_h : K.inBounds o) (hwhy : ¬ K.hasWhy o) :
    ¬ K.genNode (.lesson o) := by
  intro hn
  exact hwhy hn.2

/-- An unresolved WHY cannot silently draw a reason node. -/
theorem no_unwitnessed_why
    {o : Occurrence} (_h : K.inBounds o) (hwhy : ¬ K.hasWhy o) :
    ¬ K.genNode (.why o) := by
  intro hn
  exact hwhy hn.2

/-- A goal is a returned orientation of the three WHY witnesses, not a free map decoration. -/
theorem no_unwitnessed_goal
    {o : Occurrence} (_h : K.inBounds o) (hwhy : ¬ K.hasWhy o) :
    ¬ K.genNode (.goal o) := by
  intro hn
  exact hwhy hn.2

/-- An unopened kernel cannot draw an unattempted project node. -/
theorem no_unattempted_project
    {o : Occurrence} (_h : K.inBounds o) (hattempt : ¬ K.attempt o) :
    ¬ K.genNode (.project o) := by
  intro hn
  exact hattempt hn.2

/-- Under the same bounds, generated lesson nodes reveal their WHY witnesses. -/
theorem same_generatedNodes_sameWhy
    (L : WitnessedKernel Value Occurrence)
    (hBounds : ∀ o, K.inBounds o ↔ L.inBounds o)
    (hNodes : ∀ n, K.genNode n ↔ L.genNode n) :
    ∀ o, K.inBounds o → (K.hasWhy o ↔ L.hasWhy o) := by
  intro o hKo
  constructor
  · intro hWhy
    have hL : L.genNode (.lesson o) :=
      (hNodes (.lesson o)).1 ⟨hKo, hWhy⟩
    exact hL.2
  · intro hWhy
    have hLo : L.inBounds o := (hBounds o).1 hKo
    have hK : K.genNode (.lesson o) :=
      (hNodes (.lesson o)).2 ⟨hLo, hWhy⟩
    exact hK.2

/-- Under the same bounds, generated project nodes reveal their attempts. -/
theorem same_generatedNodes_sameAttempt
    (L : WitnessedKernel Value Occurrence)
    (hBounds : ∀ o, K.inBounds o ↔ L.inBounds o)
    (hNodes : ∀ n, K.genNode n ↔ L.genNode n) :
    ∀ o, K.inBounds o → (K.attempt o ↔ L.attempt o) := by
  intro o hKo
  constructor
  · intro hAttempt
    have hL : L.genNode (.project o) :=
      (hNodes (.project o)).1 ⟨hKo, hAttempt⟩
    exact hL.2
  · intro hAttempt
    have hLo : L.inBounds o := (hBounds o).1 hKo
    have hK : K.genNode (.project o) :=
      (hNodes (.project o)).2 ⟨hLo, hAttempt⟩
    exact hK.2

/-- A lesson is prospective until a return receipt changes its reading. -/
inductive OccurrenceReading
  | prospective
  | returned
  deriving DecidableEq, Repr

/-- The receipt changes reading, not the generated lesson/project topology. -/
noncomputable def reading (K : WitnessedKernel Value Occurrence)
    (o : Occurrence) : OccurrenceReading := by
  classical
  exact if K.returnReceipt o then .returned else .prospective

/-- With no receipts, every occurrence remains prospective. -/
theorem no_receipts_all_prospective
    (h : ∀ o, ¬ K.returnReceipt o) :
    ∀ o, reading K o = OccurrenceReading.prospective := by
  intro o
  simp [reading, h o]

/-- A receipt upgrades its own occurrence. -/
theorem receipt_upgrades_reading {o : Occurrence}
    (h : K.returnReceipt o) : reading K o = OccurrenceReading.returned := by
  simp [reading, h]

/-- If one receipt is the only one admitted, it upgrades exactly that reading. -/
theorem unique_receipt_upgrades_exactly
    {o : Occurrence} (ho : K.returnReceipt o)
  (hOnly : ∀ o', o' ≠ o → ¬ K.returnReceipt o') :
    reading K o = OccurrenceReading.returned ∧
      ∀ o', o' ≠ o → reading K o' = OccurrenceReading.prospective := by
  constructor
  · exact receipt_upgrades_reading (K := K) ho
  · intro o' hne
    simp [reading, hOnly o' hne]

/-- Lesson and project sides of a rung share exactly the same generated depth. -/
def nodeDepth : MapNode Value Occurrence → Option Nat
  | .lesson o | .project o => some (K.depth o)
  | _ => none

/-- The 90-degree turn preserves depth even though it changes map orientation. -/
theorem rung_is_level_preserving (o : Occurrence) :
    K.nodeDepth (.lesson o) = K.nodeDepth (.project o) := by
  rfl

end WitnessedKernel

/-- A Galois reading of one maintained translation at two semantic zooms. -/
structure ZoomReading (Fine : Type u) (Coarse : Type v) where
  fineLe : Fine → Fine → Prop
  coarseLe : Coarse → Coarse → Prop
  zoomOut : Fine → Coarse
  zoomIn : Coarse → Fine
  adjoint : ∀ f c, coarseLe (zoomOut f) c ↔ fineLe f (zoomIn c)

namespace ZoomReading

variable {Fine : Type u} {Coarse : Type v}

/-- The inward reading is the translation selected by this zoom contract. -/
def translation (Z : ZoomReading Fine Coarse) : Coarse → Fine :=
  Z.zoomIn

/-- The selected inward reading determines the recorded translation by definition. -/
theorem inward_determines_translation (Z : ZoomReading Fine Coarse) :
    Z.translation = Z.zoomIn := rfl

end ZoomReading

/-- A small abstract fibre used only to state the non-global-hair obstruction. -/
inductive HairDirection
  | zero
  | east
  | north
  | west
  | south
  deriving DecidableEq, Repr

/-- A stated quarter-turn transport on the fibre, with no physical interpretation. -/
def quarterTurn : HairDirection → HairDirection
  | .zero => .zero
  | .east => .north
  | .north => .west
  | .west => .south
  | .south => .east

/-- Only the zero direction is fixed by this nontrivial transport. -/
theorem quarterTurn_fixed_is_zero {d : HairDirection}
    (h : quarterTurn d = d) : d = .zero := by
  cases d <;> simp [quarterTurn] at h ⊢

/-- Local viewports may carry nonzero directions and explicit transition data. -/
structure HairAtlas (Chart : Type u) where
  localDirection : Chart → HairDirection
  local_nonzero : ∀ chart, localDirection chart ≠ .zero
  transition : Chart → Chart → HairDirection → HairDirection

/-- A globally coherent hair is a direction fixed by the supplied return transport. -/
def GloballyCoherentHair (d : HairDirection) : Prop :=
  quarterTurn d = d

/-- Under the quarter-turn transport, global coherence is informative zero. -/
theorem globallyCoherentHair_is_zero {d : HairDirection}
    (h : GloballyCoherentHair d) : d = .zero :=
  quarterTurn_fixed_is_zero h

/-- The visible maze verdicts; OPEN is a positive runtime state. -/
inductive MapVerdict
  | path
  | obstruction
  | open
  deriving DecidableEq, Repr

/-- No representational support means OPEN, regardless of candidate mechanics. -/
def verdict (hasRepresentation hasPath hasObstruction : Bool) : MapVerdict :=
  if hasRepresentation && hasPath then .path
  else if hasRepresentation && hasObstruction then .obstruction
  else .open

/-- Unsupported material can never be rendered as PATH. -/
theorem unsupported_is_open (hasPath hasObstruction : Bool) :
    verdict false hasPath hasObstruction = .open := by
  simp [verdict]

/-- The natural-rhythm triangle is one downward/upward episode map. -/
structure TriangleEpisode (State : Type u) where
  downward : State → State
  upward : State → State

namespace TriangleEpisode

variable {State : Type u}

/-- Downward prospective and upward returned passes are composed, not separate widgets. -/
def episodeMap (E : TriangleEpisode State) : State → State :=
  E.upward ∘ E.downward

end TriangleEpisode

/--
A learning holonomy can return to the same visible perspective-position while
retaining a changed learner record.  This is a structural state distinction,
not an empirical claim that a specific learner has changed.
-/
structure LearningHolonomy (State : Type u) (Visible : Type v) (Record : Type w)
    (visibleOf : State → Visible) (recordOf : State → Record) where
  start : State
  finish : State
  sameVisible : visibleOf finish = visibleOf start
  changedRecord : recordOf finish ≠ recordOf start

namespace LearningHolonomy

variable {State : Type u} {Visible : Type v} {Record : Type w}
variable {visibleOf : State → Visible} {recordOf : State → Record}

/-- A changed record prevents literal state repetition. -/
theorem not_literal_return
    (H : LearningHolonomy State Visible Record visibleOf recordOf) :
    H.finish ≠ H.start := by
  intro h
  apply H.changedRecord
  simp [h]

end LearningHolonomy

end UIHairOfClosure

end Slearn

#print axioms Slearn.UIHairOfClosure.WitnessedKernel.attempt_requires_why
#print axioms Slearn.UIHairOfClosure.WitnessedKernel.receipt_requires_attempt
#print axioms Slearn.UIHairOfClosure.WitnessedKernel.saturated_generatedMap
#print axioms Slearn.UIHairOfClosure.WitnessedKernel.no_unwitnessed_lesson
#print axioms Slearn.UIHairOfClosure.WitnessedKernel.no_unwitnessed_why
#print axioms Slearn.UIHairOfClosure.WitnessedKernel.no_unwitnessed_goal
#print axioms Slearn.UIHairOfClosure.WitnessedKernel.no_unattempted_project
#print axioms Slearn.UIHairOfClosure.WitnessedKernel.same_generatedNodes_sameWhy
#print axioms Slearn.UIHairOfClosure.WitnessedKernel.same_generatedNodes_sameAttempt
#print axioms Slearn.UIHairOfClosure.quarterTurn_fixed_is_zero
#print axioms Slearn.UIHairOfClosure.globallyCoherentHair_is_zero
#print axioms Slearn.UIHairOfClosure.unsupported_is_open
#print axioms Slearn.UIHairOfClosure.LearningHolonomy.not_literal_return
