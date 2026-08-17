import Slearn.UniversalRelativeTranslationalCompletion

/-
Natural-rhythm closure vocabulary for Slearn.

This file deliberately formalizes only the structural vocabulary needed by the
runtime: an admitted translation has two orientations and one return witness;
positions are evaluated within that translation; and a natural-rhythm cone
records a recenterable opening that excludes two named boundary conditions.

It does not formalize physical light cones, curvature tensors, consciousness,
or a normative theory of natural choice.  Those remain interpretations of the
data and the proved return equalities below.
-/

universe u v w

namespace Slearn

/-- The two readings of one admitted translation. -/
inductive TranslationOrientation
  | localToGlobal
  | globalToLocal
  deriving DecidableEq, Repr

/-- Positions are outcomes inside one comparison language, not new operators. -/
inductive RelativePosition
  | natural
  | dual
  | obstructed
  deriving DecidableEq, Repr

/--
One admitted translation, read in inverse orientations through its forward and
return maps.  Equality is required only after projection to `Witness`.
-/
structure AdmittedTranslation (Local : Type u) (Global : Type v) (Witness : Type w) where
  forward : Local → Global
  backward : Global → Local
  localWitness : Local → Witness
  globalWitness : Global → Witness
  forward_coherent : ∀ x, globalWitness (forward x) = localWitness x
  backward_coherent : ∀ y, localWitness (backward y) = globalWitness y

namespace AdmittedTranslation

variable {Local : Type u} {Global : Type v} {Witness : Type w}
variable (T : AdmittedTranslation Local Global Witness)

/-- The local-to-global orientation of the same admitted translation. -/
def orient : TranslationOrientation → Local ⊕ Global → Local ⊕ Global
  | .localToGlobal => fun
      | .inl x => .inr (T.forward x)
      | .inr y => .inr y
  | .globalToLocal => fun
      | .inl x => .inl x
      | .inr y => .inl (T.backward y)

/-- Relative equality in the common returned witness language. -/
def closes (x : Local) (y : Global) : Prop :=
  T.localWitness x = T.globalWitness y

/-- The two orientations return a local presentation to its witness class. -/
theorem local_round_trip_closes (x : Local) :
    T.closes (T.backward (T.forward x)) (T.forward x) := by
  exact T.backward_coherent _

/-- The two orientations return a global presentation to its witness class. -/
theorem global_round_trip_closes (y : Global) :
    T.closes (T.backward y) (T.forward (T.backward y)) := by
  exact (T.forward_coherent _).symm

/-- A position stays attached to its admitted translation and comparison pair. -/
structure TranslationPosition (T : AdmittedTranslation Local Global Witness) where
  localPresentation : Local
  globalPresentation : Global
  kind : RelativePosition

/-- Natural choice is closure evidence for a position in the admitted frame. -/
def TranslationPosition.IsNatural (p : TranslationPosition T) : Prop :=
  p.kind = RelativePosition.natural ∧ T.closes p.localPresentation p.globalPresentation

/-- Dual and obstructed positions remain relative positions in the same frame. -/
def TranslationPosition.IsNonNatural (p : TranslationPosition T) : Prop :=
  p.kind = RelativePosition.dual ∨ p.kind = RelativePosition.obstructed

/-- A non-natural position is still a position of this translation, not another map. -/
theorem TranslationPosition.nonNatural_is_relative (p : TranslationPosition T) :
    p.IsNonNatural → ∃ k : RelativePosition, p.kind = k := by
  intro _
  exact ⟨p.kind, rfl⟩

end AdmittedTranslation

/--
The minimal formal shape of a natural-rhythm cone. `isolatedBoundary` and
`unresolvedBoundary` are caller-supplied predicates: the theorem layer does not
claim that they exhaust physical, temporal, or social degeneracies.
-/
structure NaturalRhythmCone (X : Type u) (F : RelativeFrame X) where
  apex : X
  globalView : F.View
  localView : F.View
  local_refines_global : F.refines globalView localView
  isolatedBoundary : Prop
  unresolvedBoundary : Prop
  not_isolated : ¬ isolatedBoundary
  not_unresolved : ¬ unresolvedBoundary

namespace NaturalRhythmCone

variable {X : Type u} {F : RelativeFrame X}
variable (C : NaturalRhythmCone X F)

/-- The local opening is contained in the global opening at the cone apex. -/
theorem local_opening_subset_global :
    ∀ y, F.opening C.localView C.apex y → F.opening C.globalView C.apex y := by
  intro y hy
  exact F.same_of_refines C.local_refines_global hy

end NaturalRhythmCone

end Slearn

#print axioms Slearn.AdmittedTranslation.local_round_trip_closes
#print axioms Slearn.AdmittedTranslation.global_round_trip_closes
#print axioms Slearn.NaturalRhythmCone.local_opening_subset_global
