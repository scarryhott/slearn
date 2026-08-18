import Slearn.NRRF654IntegratedFrameworkClosure

/-
Executable perspectival closure episodes for Slearn.

This module is the machine-checked state discipline mirrored by the browser
runtime. It distinguishes evidence present in a record from an operation that
has actually been executed:

  open perspective --contract--> contracted goal --reopen--> re-read local
  --return receipt--> successor perspective + retained residue --continue-->
  next open perspective.

The operations are typed by their predecessor state, so a returned episode
cannot be constructed as an action on an uncontracted or unreopened state.
It does not prove a text receipt true, a person performed an attempt, or that
browser events are extracted from this Lean definition.
-/

universe u v w x

namespace Slearn
namespace FrameworkClosure

inductive ExecutablePhase
  | open
  | contracted
  | reopened
  | returned
  deriving DecidableEq, Repr

variable {Local : Type u} {Global : Type v} {Witness : Type w}
variable {T : AdmittedTranslation Local Global Witness}
variable {Receipt : Type x}

/-- An open local perspective before its forward translation is executed. -/
structure OpenPerspective (T : AdmittedTranslation Local Global Witness) where
  perspective : Local

/-- The concrete result of executing the forward orientation. -/
structure ContractedPerspective (T : AdmittedTranslation Local Global Witness) where
  origin : OpenPerspective T
  goal : Global
  isForward : goal = T.forward origin.perspective

/-- The concrete result of executing the reciprocal return orientation. -/
structure ReopenedPerspective (T : AdmittedTranslation Local Global Witness) where
  contracted : ContractedPerspective T
  perspective : Local
  isBackward : perspective = T.backward contracted.goal

/-- The supplied evidence needed to commit a nonliteral successor. -/
structure ReturnInput (T : AdmittedTranslation Local Global Witness) (Receipt : Type x)
    (R : ReopenedPerspective T) where
  receipt : Receipt
  successor : Local
  successorCloses : T.closes successor R.contracted.goal
  successorChanged : successor ≠ R.contracted.origin.perspective

/-- The retained distinction created by a committed returned episode. -/
structure RetainedResidue (T : AdmittedTranslation Local Global Witness) (Receipt : Type x) where
  receipt : Receipt
  origin : Local
  successor : Local
  changed : successor ≠ origin

/-- A returned episode carries a receipt, a changed successor, and its residue. -/
structure ReturnedPerspective (T : AdmittedTranslation Local Global Witness) (Receipt : Type x) where
  reopened : ReopenedPerspective T
  input : ReturnInput T Receipt reopened
  residue : RetainedResidue T Receipt
  residue_matches : residue.receipt = input.receipt ∧
    residue.origin = reopened.contracted.origin.perspective ∧
    residue.successor = input.successor

namespace OpenPerspective

/-- The browser's `contract` operation executes the forward translation. -/
def contract (O : OpenPerspective T) : ContractedPerspective T where
  origin := O
  goal := T.forward O.perspective
  isForward := rfl

end OpenPerspective

namespace ContractedPerspective

/-- A contracted goal closes with its origin in the admitted witness language. -/
theorem closes_origin (C : ContractedPerspective T) :
    T.closes C.origin.perspective C.goal := by
  rw [C.isForward]
  exact (T.forward_coherent _).symm

/-- The browser's `reopen` operation executes the reciprocal orientation. -/
def reopen (C : ContractedPerspective T) : ReopenedPerspective T where
  contracted := C
  perspective := T.backward C.goal
  isBackward := rfl

end ContractedPerspective

namespace ReopenedPerspective

/-- A re-read local presentation still closes with the contracted goal. -/
theorem closes_goal (R : ReopenedPerspective T) :
    T.closes R.perspective R.contracted.goal := by
  rw [R.isBackward]
  exact T.backward_coherent _

/-- Reopening a contracted local presentation returns its local witness. -/
theorem closes_origin (R : ReopenedPerspective T) :
    T.localWitness R.perspective = T.localWitness R.contracted.origin.perspective := by
  calc
    T.localWitness R.perspective = T.globalWitness R.contracted.goal := R.closes_goal
    _ = T.localWitness R.contracted.origin.perspective := by
      rw [R.contracted.isForward]
      exact T.forward_coherent _

/-- Commit a receipt only after a re-opening has been executed. -/
def commitReturn (R : ReopenedPerspective T) (input : ReturnInput T Receipt R) :
    ReturnedPerspective T Receipt where
  reopened := R
  input := input
  residue := {
    receipt := input.receipt
    origin := R.contracted.origin.perspective
    successor := input.successor
    changed := input.successorChanged
  }
  residue_matches := ⟨rfl, rfl, rfl⟩

end ReopenedPerspective

namespace ReturnedPerspective

/-- The retained residue is a nonliteral difference, not an added display number. -/
theorem residue_changes_origin (R : ReturnedPerspective T Receipt) :
    R.residue.successor ≠ R.residue.origin :=
  R.residue.changed

/-- The successor is closed with the contracted goal through the supplied return input. -/
theorem successor_closes_goal (R : ReturnedPerspective T Receipt) :
    T.closes R.input.successor R.reopened.contracted.goal :=
  R.input.successorCloses

/-- Continuing creates the next open local perspective while retaining the residue as history. -/
structure NextOpening (R : ReturnedPerspective T Receipt) where
  perspective : OpenPerspective T
  inheritedResidue : RetainedResidue T Receipt
  inheritedPerspective : perspective.perspective = R.input.successor
  residue_preserved : inheritedResidue = R.residue

/-- Continuing makes the returned successor the next local opening. -/
def nextOpening (R : ReturnedPerspective T Receipt) : R.NextOpening where
  perspective := ⟨R.input.successor⟩
  inheritedResidue := R.residue
  inheritedPerspective := rfl
  residue_preserved := rfl

/-- Continuation preserves the exact retained residue, not merely its label. -/
theorem continue_preserves_residue (R : ReturnedPerspective T Receipt) :
    (R.nextOpening).inheritedResidue = R.residue :=
  (R.nextOpening).residue_preserved

end ReturnedPerspective

def OpenPerspective.phase (_ : OpenPerspective T) : ExecutablePhase := .open
def ContractedPerspective.phase (_ : ContractedPerspective T) : ExecutablePhase := .contracted
def ReopenedPerspective.phase (_ : ReopenedPerspective T) : ExecutablePhase := .reopened
def ReturnedPerspective.phase (_ : ReturnedPerspective T Receipt) : ExecutablePhase := .returned

/-- A complete executable pass exposes its four necessary predecessor phases. -/
theorem executable_pass_receipt (O : OpenPerspective T)
    (input : ReturnInput T Receipt (O.contract.reopen)) :
    O.phase = .open ∧
      O.contract.phase = .contracted ∧
      O.contract.reopen.phase = .reopened ∧
      (O.contract.reopen.commitReturn input).phase = .returned :=
  ⟨rfl, rfl, rfl, rfl⟩

end FrameworkClosure
end Slearn

#print axioms Slearn.FrameworkClosure.ContractedPerspective.closes_origin
#print axioms Slearn.FrameworkClosure.ReopenedPerspective.closes_goal
#print axioms Slearn.FrameworkClosure.ReopenedPerspective.closes_origin
#print axioms Slearn.FrameworkClosure.ReturnedPerspective.residue_changes_origin
#print axioms Slearn.FrameworkClosure.ReturnedPerspective.successor_closes_goal
#print axioms Slearn.FrameworkClosure.ReturnedPerspective.continue_preserves_residue
#print axioms Slearn.FrameworkClosure.executable_pass_receipt
