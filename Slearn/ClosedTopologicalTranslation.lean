import Slearn.NaturalRhythmClosure

/-
Closed topological translation episodes for Slearn.

This module formalizes a small, deliberately abstract event layer:

* a relation is read in two reciprocal, non-prioritized orientations;
* two selected paths interact while the episode is still open;
* inversion swaps orientations rather than identifying their presentations;
* a return witness recovers the base relation without forcing literal state
  equality;
* a residue is nontrivial only when it distinguishes two successful returns
  with the same recovered base; and
* inheritance keeps the recovered base while changing the continuation field.

The module does not assign a physical, numerical, ethical, or psychological
meaning to a residue.  A ball/hair trajectory, optical route order, learning
revision, and operational ordering are possible interpretations supplied by a
caller.  In particular, it does not identify a residue with Chaitin's halting
probability, physical curvature, or a measure of learner progress.

The imported universal-relative completion theorem remains separate: it proves
uniqueness of a completion operator only after a relative frame and its
admissibility contract have been fixed.  This module records episode-level
return and reopening; it does not introduce another closure operator.
-/

universe u v w x y z

namespace Slearn

/--
Two reciprocal readings of a presentation.  `first` and `second` carry no
local/global priority; their only structural operation is orientation swap.
-/
structure ReciprocalPair (Presentation : Type u) where
  first : Presentation
  second : Presentation

namespace ReciprocalPair

/-- Re-read a reciprocal pair in the opposite orientation. -/
def invert (P : ReciprocalPair Presentation) : ReciprocalPair Presentation where
  first := P.second
  second := P.first

/-- Swapping orientation twice restores the original pair exactly. -/
@[simp] theorem invert_invert (P : ReciprocalPair Presentation) :
    P.invert.invert = P := by
  cases P
  rfl

end ReciprocalPair

namespace AdmittedTranslation

variable {Local : Type u} {Global : Type v} {Witness : Type w}

/--
Present the two differently typed sides of an admitted translation as one
reciprocal pair.  The sum tag preserves the distinction of presentations;
inversion swaps their orientation without coercing either side into the other.
-/
def reciprocalPair (_T : AdmittedTranslation Local Global Witness)
    (x : Local) (y : Global) : ReciprocalPair (Local ⊕ Global) where
  first := .inl x
  second := .inr y

/-- The common witness language for the tagged reciprocal presentation. -/
def reciprocalWitness (T : AdmittedTranslation Local Global Witness) : Local ⊕ Global → Witness
  | .inl x => T.localWitness x
  | .inr y => T.globalWitness y

/--
Closure in the admitted translation is exactly witness agreement of its tagged
reciprocal pair.  This connects the general episode carrier to the existing
local/global translation interface without privileging either orientation.
-/
theorem reciprocalPair_closes (T : AdmittedTranslation Local Global Witness)
    (x : Local) (y : Global) :
    T.closes x y ↔
      T.reciprocalWitness (reciprocalPair T x y).first =
        T.reciprocalWitness (reciprocalPair T x y).second := by
  rfl

end AdmittedTranslation

/-- The explicit runtime states of an episode. -/
inductive TranslationEpisodeStatus
  | open
  | returned
  | closedToNewOpening
  deriving DecidableEq, Repr

/--
The still-open part of a translation episode.  The two path values are retained
as one interaction, so neither is typed as an independently complete topology.
The inversion field says that the returned orientation is a swap of the whole
extended pair, not an equality between its two presentations.
-/
structure OpenTranslationEpisode
    (Presentation : Type u) (Path : Type v) (Interaction : Type w) where
  origin : ReciprocalPair Presentation
  extended : ReciprocalPair Presentation
  firstPath : Path
  secondPath : Path
  interaction : Interaction
  inverted : ReciprocalPair Presentation
  inversion : inverted = extended.invert

namespace OpenTranslationEpisode

variable {Presentation : Type u} {Path : Type v} {Interaction : Type w}

/-- Before an explicit return witness, the episode remains OPEN. -/
def status (_ : OpenTranslationEpisode Presentation Path Interaction) :
    TranslationEpisodeStatus := .open

/-- Inversion reverses orientation but preserves the extended pair on re-read. -/
theorem inversion_returns_extension
    (E : OpenTranslationEpisode Presentation Path Interaction) :
    E.inverted.invert = E.extended := by
  rw [E.inversion]
  exact ReciprocalPair.invert_invert E.extended

end OpenTranslationEpisode

/--
An open episode together with a returned presentation and a witness that its
base relation is recovered.  The witness deliberately does not require the
returned presentation to be literally equal to the origin.
-/
structure ReturnedTranslationEpisode
    (Presentation : Type u) (Path : Type v) (Interaction : Type w)
    (Base : Type x)
    (baseOf : ReciprocalPair Presentation → Base) where
  openEpisode : OpenTranslationEpisode Presentation Path Interaction
  returned : ReciprocalPair Presentation
  returnWitness : baseOf returned = baseOf openEpisode.origin

namespace ReturnedTranslationEpisode

variable {Presentation : Type u} {Path : Type v} {Interaction : Type w}
variable {Base : Type x}
variable {baseOf : ReciprocalPair Presentation → Base}

/-- The base relation recovered by this return. -/
def recoveredBase
    (E : ReturnedTranslationEpisode Presentation Path Interaction Base baseOf) : Base :=
  baseOf E.returned

/-- An explicit returned episode has a returned, not open, status. -/
def status
    (_ : ReturnedTranslationEpisode Presentation Path Interaction Base baseOf) :
    TranslationEpisodeStatus := .returned

/-- A successful return recovers the origin's base relation. -/
theorem recovers_origin
    (E : ReturnedTranslationEpisode Presentation Path Interaction Base baseOf) :
    E.recoveredBase = baseOf E.openEpisode.origin :=
  E.returnWitness

end ReturnedTranslationEpisode

/--
A residue coordinate is nontrivial only relative to another successful return
that recovers the same base but has a different coordinate.  `Residue` is an
arbitrary type: no numerical or physical interpretation is built in.
-/
structure ReturnDistinction
    (Episode : Type u) (Base : Type v) (Residue : Type w)
    (recoveredBase : Episode → Base) (residueOf : Episode → Residue)
    (episode : Episode) where
  alternative : Episode
  sameRecoveredBase : recoveredBase alternative = recoveredBase episode
  residueDiffers : residueOf alternative ≠ residueOf episode

namespace ReturnDistinction

variable {Episode : Type u} {Base : Type v} {Residue : Type w}
variable {recoveredBase : Episode → Base} {residueOf : Episode → Residue}
variable {episode : Episode}

/-- A distinction exposes two successful realizations with one recovered base. -/
theorem has_comparator
    (D : ReturnDistinction Episode Base Residue recoveredBase residueOf episode) :
    ∃ alternative,
      recoveredBase alternative = recoveredBase episode ∧
      residueOf alternative ≠ residueOf episode := by
  exact ⟨D.alternative, D.sameRecoveredBase, D.residueDiffers⟩

/-- A nontrivial residue prevents the coordinate from being constant. -/
theorem residue_not_constant
    (D : ReturnDistinction Episode Base Residue recoveredBase residueOf episode) :
    ¬ ∀ other, residueOf other = residueOf episode := by
  intro h
  exact D.residueDiffers (h D.alternative)

end ReturnDistinction

/--
The inherited successor of a returned episode.  It recovers the same base and
has a changed continuation field.  This is the exact formal criterion for the
runtime label `CLOSED_TO_NEW_OPENING`; it does not follow from a return witness
alone.
-/
structure ClosedToNewOpening
    (Presentation : Type u) (Path : Type v) (Interaction : Type w)
    (Base : Type x) (Residue : Type y) (Continuation : Type z)
    (baseOf : ReciprocalPair Presentation → Base)
    (continuationOf : ReciprocalPair Presentation → Continuation)
    (residueOf : ReturnedTranslationEpisode Presentation Path Interaction Base baseOf → Residue) where
  returnedEpisode : ReturnedTranslationEpisode Presentation Path Interaction Base baseOf
  distinction : ReturnDistinction
    (ReturnedTranslationEpisode Presentation Path Interaction Base baseOf)
    Base
    Residue
    ReturnedTranslationEpisode.recoveredBase
    residueOf
    returnedEpisode
  successor : ReciprocalPair Presentation
  successorReturns : baseOf successor = baseOf returnedEpisode.openEpisode.origin
  continuationChanged :
    continuationOf successor ≠ continuationOf returnedEpisode.openEpisode.origin

namespace ClosedToNewOpening

variable {Presentation : Type u} {Path : Type v} {Interaction : Type w}
variable {Base : Type x} {Residue : Type y} {Continuation : Type z}
variable {baseOf : ReciprocalPair Presentation → Base}
variable {continuationOf : ReciprocalPair Presentation → Continuation}
variable {residueOf : ReturnedTranslationEpisode Presentation Path Interaction Base baseOf → Residue}

/-- The explicit inheritance criterion has the terminal reopening status. -/
def status
    (_ : ClosedToNewOpening Presentation Path Interaction Base Residue Continuation
      baseOf continuationOf residueOf) : TranslationEpisodeStatus :=
  .closedToNewOpening

/-- The inherited opening still returns to the origin's base relation. -/
theorem successor_recovers_origin
    (E : ClosedToNewOpening Presentation Path Interaction Base Residue Continuation
      baseOf continuationOf residueOf) :
    baseOf E.successor = baseOf E.returnedEpisode.openEpisode.origin :=
  E.successorReturns

/-- The inherited opening is not a literal repetition of the old continuation field. -/
theorem successor_is_new_opening
    (E : ClosedToNewOpening Presentation Path Interaction Base Residue Continuation
      baseOf continuationOf residueOf) :
    continuationOf E.successor ≠
      continuationOf E.returnedEpisode.openEpisode.origin :=
  E.continuationChanged

/-- The residue has an alternative successful realization at the recovered base. -/
theorem residue_has_successful_comparator
    (E : ClosedToNewOpening Presentation Path Interaction Base Residue Continuation
      baseOf continuationOf residueOf) :
    ∃ alternative,
      alternative.recoveredBase = E.returnedEpisode.recoveredBase ∧
      residueOf alternative ≠ residueOf E.returnedEpisode :=
  E.distinction.has_comparator

end ClosedToNewOpening

end Slearn

#print axioms Slearn.ReciprocalPair.invert_invert
#print axioms Slearn.AdmittedTranslation.reciprocalPair_closes
#print axioms Slearn.OpenTranslationEpisode.inversion_returns_extension
#print axioms Slearn.ReturnedTranslationEpisode.recovers_origin
#print axioms Slearn.ReturnDistinction.has_comparator
#print axioms Slearn.ReturnDistinction.residue_not_constant
#print axioms Slearn.ClosedToNewOpening.successor_recovers_origin
#print axioms Slearn.ClosedToNewOpening.successor_is_new_opening
#print axioms Slearn.ClosedToNewOpening.residue_has_successful_comparator
