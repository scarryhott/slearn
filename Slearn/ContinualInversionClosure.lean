import Slearn.NaturalRhythmClosure

/-
Perspective–WHY–goal continual inversion for Slearn.

The formal object here is deliberately narrower than the project's
interpretation.  It records a selected reduction and inverse expansion through
one admitted translation. The exposed flip may look absolute in an interface,
but the certified result is witness-relative closure, not equality of isolated
presentations. Physical, metaphysical, and ASI claims remain outside this file.
-/

universe u v w x y

namespace Slearn

/-- One typed node in the perspective–WHY–goal triangle. -/
structure PerspectiveWhyGoal
    (Perspective : Type u) (Why : Type v) (Goal : Type w) where
  perspective : Perspective
  why : Why
  goal : Goal

/-- A local definition as read in one currently active language. -/
structure LanguageDefinition (Language : Type u) (Definition : Type v) where
  language : Language
  definition : Definition

/--
The shared closure object behind perspective/goal zooming.

`expand` and `reduce` are selected structural continuations. Their closure
proofs do not assert `reduce (expand p) = p` or `expand (reduce g) = g`.
Instead, the two presentations return through the common witness language of
the admitted translation. `flip` changes the active language-definition
presentation together with the zoom orientation.
-/
structure ContinualInversion
    (Perspective : Type u) (Why : Type v) (Goal : Type w)
    (Language : Type x) (Definition : Type y) (Witness : Type max u v w x y) where
  translation : AdmittedTranslation Perspective Goal Witness
  perspectivePresentation : Perspective → LanguageDefinition Language Definition
  goalPresentation : Goal → LanguageDefinition Language Definition
  flip : LanguageDefinition Language Definition → LanguageDefinition Language Definition
  flip_involutive : ∀ presentation, flip (flip presentation) = presentation
  perspectiveToWhy : Perspective → Why
  whyToGoal : Why → Goal
  goalToWhy : Goal → Why
  whyToPerspective : Why → Perspective
  forward_flip : ∀ p,
    flip (perspectivePresentation p) = goalPresentation (whyToGoal (perspectiveToWhy p))
  backward_flip : ∀ g,
    flip (goalPresentation g) = perspectivePresentation (whyToPerspective (goalToWhy g))
  forward_closes : ∀ p,
    translation.closes p (whyToGoal (perspectiveToWhy p))
  backward_closes : ∀ g,
    translation.closes (whyToPerspective (goalToWhy g)) g

namespace ContinualInversion

variable {Perspective : Type u} {Why : Type v} {Goal : Type w}
variable {Language : Type x} {Definition : Type y} {Witness : Type max u v w x y}
variable (C : ContinualInversion Perspective Why Goal Language Definition Witness)

/-- Zooming out: perspective through WHY into a goal presentation. -/
def expand (p : Perspective) : Goal :=
  C.whyToGoal (C.perspectiveToWhy p)

/-- Zooming in: goal through WHY into a perspective presentation. -/
def reduce (g : Goal) : Perspective :=
  C.whyToPerspective (C.goalToWhy g)

/-- A selected triangle is the common receipt shape for either zoom direction. -/
structure Receipt where
  triangle : PerspectiveWhyGoal Perspective Why Goal
  orientation : TranslationOrientation
  closes : C.translation.closes triangle.perspective triangle.goal

/-- The outward zoom supplies a returned, witness-relative receipt. -/
def expandReceipt (p : Perspective) : C.Receipt where
  triangle := {
    perspective := p
    why := C.perspectiveToWhy p
    goal := C.expand p
  }
  orientation := .localToGlobal
  closes := C.forward_closes p

/-- The inward zoom supplies a returned, witness-relative receipt. -/
def reduceReceipt (g : Goal) : C.Receipt where
  triangle := {
    perspective := C.reduce g
    why := C.goalToWhy g
    goal := g
  }
  orientation := .globalToLocal
  closes := C.backward_closes g

/-- The outward presentation flip is involutive at the selected interface view. -/
theorem expand_flip_returns (p : Perspective) :
    C.flip (C.goalPresentation (C.expand p)) = C.perspectivePresentation p := by
  change C.flip (C.goalPresentation (C.whyToGoal (C.perspectiveToWhy p))) =
    C.perspectivePresentation p
  rw [← C.forward_flip p]
  exact C.flip_involutive _

/-- The inward presentation flip is involutive at the selected interface view. -/
theorem reduce_flip_returns (g : Goal) :
    C.flip (C.perspectivePresentation (C.reduce g)) = C.goalPresentation g := by
  change C.flip (C.perspectivePresentation (C.whyToPerspective (C.goalToWhy g))) =
    C.goalPresentation g
  rw [← C.backward_flip g]
  exact C.flip_involutive _

/--
The formal return relation is closure through a witness, not literal equality of
the two endpoint presentations.
-/
theorem expand_returns_in_closure (p : Perspective) :
    C.translation.closes p (C.expand p) :=
  C.forward_closes p

/-- The same closure reading holds when the goal is the active opening. -/
theorem reduce_returns_in_closure (g : Goal) :
    C.translation.closes (C.reduce g) g :=
  C.backward_closes g

end ContinualInversion

end Slearn

#print axioms Slearn.ContinualInversion.expand_flip_returns
#print axioms Slearn.ContinualInversion.reduce_flip_returns
#print axioms Slearn.ContinualInversion.expand_returns_in_closure
#print axioms Slearn.ContinualInversion.reduce_returns_in_closure
