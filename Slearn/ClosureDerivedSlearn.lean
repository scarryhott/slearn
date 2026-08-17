import Slearn.ContinualInversionClosure

/-
The typed runtime carrier for the original Slearn perspectival map.

This file does not render an interface or construct a maze from arbitrary data.
It records the common witness discipline that lets perspective, belief, WHY,
goal, lesson, project, and world be rendered as recenterings of one closure
relation.  The natural-rhythm and physical interpretations remain outside the
machine-checked claims below.
-/

universe u

namespace Slearn

/-- The visible resolution of a requested continuation in the current maze. -/
inductive MazeVerdict
  | path
  | wall
  | open
  deriving DecidableEq, Repr

/-- A WHAT remains prospective until a closure-backed receipt returns it. -/
inductive OccurrenceState
  | prospective
  | attempting
  | returned
  deriving DecidableEq, Repr

/--
The closure-derived carrier for the authored Slearn map.

`triangle` is the shared perspective–WHY–goal inversion already formalized in
`ContinualInversion`.  The remaining fields record witness-coherent outward
extensions: belief to goal, WHY to lesson, lesson to project, and project to
world.  These are supplied structure, not claims that every learning system
has a single such path.
-/
structure ClosureDerivedSlearn
    (Perspective Belief Why Goal Lesson Project World Language Definition Witness : Type u) where
  triangle : ContinualInversion Perspective Why Goal Language Definition Witness
  perspectiveToBelief : Perspective → Belief
  beliefToGoal : Belief → Goal
  whyToLesson : Why → Lesson
  lessonToProject : Lesson → Project
  projectToWorld : Project → World
  beliefWitness : Belief → Witness
  whyWitness : Why → Witness
  lessonWitness : Lesson → Witness
  projectWitness : Project → Witness
  worldWitness : World → Witness
  perspective_belief_coherent : ∀ p,
    triangle.translation.localWitness p = beliefWitness (perspectiveToBelief p)
  belief_goal_coherent : ∀ b,
    beliefWitness b = triangle.translation.globalWitness (beliefToGoal b)
  why_goal_coherent : ∀ q,
    whyWitness q = triangle.translation.globalWitness (triangle.whyToGoal q)
  why_lesson_coherent : ∀ q,
    whyWitness q = lessonWitness (whyToLesson q)
  lesson_project_coherent : ∀ l,
    lessonWitness l = projectWitness (lessonToProject l)
  project_world_coherent : ∀ p,
    projectWitness p = worldWitness (projectToWorld p)

namespace ClosureDerivedSlearn

variable {Perspective Belief Why Goal Lesson Project World Language Definition Witness : Type u}
variable (S : ClosureDerivedSlearn Perspective Belief Why Goal Lesson Project World Language Definition Witness)

/-- The belief-goal route is a second rendering of the admitted perspective-goal closure. -/
theorem perspective_belief_goal_closes (p : Perspective) :
    S.triangle.translation.closes p (S.beliefToGoal (S.perspectiveToBelief p)) := by
  unfold AdmittedTranslation.closes
  rw [S.perspective_belief_coherent, S.belief_goal_coherent]

/-- A lesson and its corresponding project rung preserve their common witness. -/
theorem lesson_project_rung_closes (l : Lesson) :
    S.lessonWitness l = S.projectWitness (S.lessonToProject l) :=
  S.lesson_project_coherent l

/-- Project/world extension preserves a common witness without asserting literal identity. -/
theorem project_world_rung_closes (p : Project) :
    S.projectWitness p = S.worldWitness (S.projectToWorld p) :=
  S.project_world_coherent p

/-- The outward WHY route carries one coherent witness through lesson, project, and world. -/
theorem why_lesson_project_world_closes (q : Why) :
    S.whyWitness q = S.worldWitness (S.projectToWorld (S.lessonToProject (S.whyToLesson q))) := by
  rw [S.why_lesson_coherent, S.lesson_project_coherent, S.project_world_coherent]

/--
One rendered learning episode.  A returned occurrence must retain a receipt
from the same perspective–WHY–goal triangle.  This theorem does not determine
whether a receipt is independently grounded; that is a runtime/admission
contract that must be supplied by a concrete implementation.
-/
structure Episode where
  perspective : Perspective
  why : Why
  goal : Goal
  lesson : Lesson
  project : Project
  world : World
  orientation : TranslationOrientation
  verdict : MazeVerdict
  state : OccurrenceState
  receipt : Option S.triangle.Receipt
  returned_has_receipt : state = OccurrenceState.returned → ∃ r, receipt = some r
  receipt_matches_episode : ∀ r, receipt = some r →
    r.triangle.perspective = perspective ∧ r.triangle.goal = goal

/-- A returned experience cannot be displayed without a triangle receipt. -/
theorem Episode.returned_requires_receipt (E : S.Episode) :
    E.state = OccurrenceState.returned → ∃ r, E.receipt = some r :=
  E.returned_has_receipt

/-- A returned receipt is attached to this episode's active perspective and goal. -/
theorem Episode.receipt_replays_active_endpoints (E : S.Episode) (r : S.triangle.Receipt) :
    E.receipt = some r → r.triangle.perspective = E.perspective ∧ r.triangle.goal = E.goal :=
  E.receipt_matches_episode r

end ClosureDerivedSlearn

end Slearn

#print axioms Slearn.ClosureDerivedSlearn.perspective_belief_goal_closes
#print axioms Slearn.ClosureDerivedSlearn.lesson_project_rung_closes
#print axioms Slearn.ClosureDerivedSlearn.why_lesson_project_world_closes
#print axioms Slearn.ClosureDerivedSlearn.Episode.returned_requires_receipt
