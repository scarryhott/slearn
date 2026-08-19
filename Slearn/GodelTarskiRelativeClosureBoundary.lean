import Slearn.RelationalClosureUnification

/-
Gödel/Tarski relative-closure boundary for Slearn.

This is a small formal boundary model, not a formalization of Gödel's first or
second incompleteness theorem, Rosser's theorem, Tarski's undefinability
theorem, Lawvere's theorem in a Cartesian closed category, Chaitin's theorem,
or a complete theory of arithmetic.  It proves only the named abstract
patterns under the definitions below:

* a point-surjective self-evaluation makes every endomap have a fixed point;
* a finite stage in an explicit infinite toy language is incomplete, while a
  selected limit theory is consistent and complete;
* a supplied liar diagonal prevents an internal truth predicate at any one
  theory; and
* certification is bounded inside each supplied basis but unbounded across a
  family of bases.

The point is to locate distinct boundaries without claiming that a limit theory
is effectively axiomatized, physically real, or an escape from Gödel/Tarski.
-/

universe u v

namespace Slearn
namespace GodelTarskiRelativeClosureBoundary

namespace Diagonal

/-- An evaluation names every relation from `A` to `B` only if it is point-surjective. -/
def PointSurjective {A : Type u} {B : Type v}
    (evaluation : A → A → B) : Prop :=
  ∀ relation : A → B, ∃ code, ∀ input, evaluation code input = relation input

/-- The elementary Lawvere diagonal calculation. -/
theorem lawvere_fixed_point {A : Type u} {B : Type v}
    (evaluation : A → A → B) (pointSurjective : PointSurjective evaluation)
    (endomap : B → B) : ∃ value, endomap value = value := by
  let diagonal : A → B := fun code => endomap (evaluation code code)
  obtain ⟨code, hcode⟩ := pointSurjective diagonal
  refine ⟨evaluation code code, ?_⟩
  calc
    endomap (evaluation code code) = diagonal code := rfl
    _ = evaluation code code := (hcode code).symm

/-- Boolean negation has no fixed point. -/
theorem bool_not_has_no_fixed_point (value : Bool) : (!value) ≠ value := by
  cases value <;> decide

/-- Hence no Boolean self-evaluation can name every Boolean relation. -/
theorem encoding_incomplete {A : Type u} (evaluation : A → A → Bool) :
    ¬ PointSurjective evaluation := by
  intro pointSurjective
  obtain ⟨value, fixed⟩ := lawvere_fixed_point evaluation pointSurjective Bool.not
  exact bool_not_has_no_fixed_point value fixed

/-- The Turing-named reading: an evaluator cannot universally encode/evaluate all Boolean relations. -/
theorem no_universal_evaluator {Program : Type u}
    (evaluate : Program → Program → Bool) :
    ¬ PointSurjective evaluate :=
  encoding_incomplete evaluate

end Diagonal

namespace LevelTower

/-- A toy infinite language: an atom and a chosen polarity. -/
inductive Sentence where
  | atom (index : Nat) (positive : Bool)
  deriving DecidableEq, Repr

/-- The explicit negation exchanges the two polarities of one atom. -/
def negate : Sentence → Sentence
  | .atom index positive => .atom index (!positive)

theorem negate_involutive (sentence : Sentence) : negate (negate sentence) = sentence := by
  cases sentence with
  | atom index positive => cases positive <;> rfl

/-- A theory is a set of toy-language sentences. -/
abbrev Theory := Sentence → Prop

/-- Consistency means no atom and its explicit negation are both included. -/
def Consistent (theory : Theory) : Prop :=
  ∀ sentence, ¬ (theory sentence ∧ theory (negate sentence))

/-- Completeness means each atom is decided on one of its two polarities. -/
def Complete (theory : Theory) : Prop :=
  ∀ sentence, theory sentence ∨ theory (negate sentence)

/-- A sentence is decided when it or its explicit negation occurs. -/
def Decides (theory : Theory) (sentence : Sentence) : Prop :=
  theory sentence ∨ theory (negate sentence)

/-- Stage `n` decides only the positive polarity of atoms strictly below `n`. -/
def stage (depth : Nat) : Theory := fun sentence =>
  match sentence with
  | .atom index positive => index < depth ∧ positive = true

/-- The selected closure decides the positive polarity at every depth. -/
def closureTheory : Theory := fun sentence =>
  match sentence with
  | .atom _ positive => positive = true

theorem stage_consistent (depth : Nat) : Consistent (stage depth) := by
  intro sentence
  cases sentence with
  | atom index positive =>
      cases positive <;> simp [stage, negate]

theorem closureTheory_consistent : Consistent closureTheory := by
  intro sentence
  cases sentence with
  | atom index positive =>
      cases positive <;> simp [closureTheory, negate]

theorem closureTheory_complete : Complete closureTheory := by
  intro sentence
  cases sentence with
  | atom index positive =>
      cases positive <;> simp [closureTheory, negate]

/-- No finite stage decides the new atom at its own boundary. -/
theorem stage_incomplete (depth : Nat) : ¬ Complete (stage depth) := by
  intro complete
  have boundary := complete (.atom depth true)
  simp [stage, negate] at boundary

/-- The boundary atom is not decided at the current local level. -/
theorem boundary_undecided (depth : Nat) :
    ¬ Decides (stage depth) (.atom depth true) := by
  simp [Decides, stage, negate]

/-- The same atom is decided at the successor level. -/
theorem boundary_decided_at_successor (depth : Nat) :
    Decides (stage (depth + 1)) (.atom depth true) := by
  left
  simp [stage]

/-- Every fixed sentence is decided at some finite stage of this tower. -/
theorem finite_depth (sentence : Sentence) :
    ∃ depth, Decides (stage depth) sentence := by
  cases sentence with
  | atom index positive =>
      refine ⟨index + 1, ?_⟩
      cases positive <;> simp [Decides, stage, negate]

/-- Every local stage sits inside the selected closure theory. -/
theorem stage_subset_closure (depth : Nat) :
    ∀ sentence, stage depth sentence → closureTheory sentence := by
  intro sentence inStage
  cases sentence with
  | atom index positive =>
      simpa [stage, closureTheory] using inStage.2

/-- An alternative complete closure chooses the opposite polarity. -/
def oppositeClosureTheory : Theory := fun sentence =>
  match sentence with
  | .atom _ positive => positive = false

theorem oppositeClosureTheory_consistent : Consistent oppositeClosureTheory := by
  intro sentence
  cases sentence with
  | atom index positive =>
      cases positive <;> simp [oppositeClosureTheory, negate]

theorem oppositeClosureTheory_complete : Complete oppositeClosureTheory := by
  intro sentence
  cases sentence with
  | atom index positive =>
      cases positive <;> simp [oppositeClosureTheory, negate]

/-- Complete consistent closures can disagree when their selected basis differs. -/
theorem completion_basis_dependent :
    Consistent closureTheory ∧ Complete closureTheory ∧
      Consistent oppositeClosureTheory ∧ Complete oppositeClosureTheory ∧
        closureTheory (.atom 0 true) ≠ oppositeClosureTheory (.atom 0 true) := by
  refine ⟨closureTheory_consistent, closureTheory_complete,
    oppositeClosureTheory_consistent, oppositeClosureTheory_complete, ?_⟩
  simp [closureTheory, oppositeClosureTheory]

/-- A supplied internal truth predicate for one toy theory. -/
structure InternalTruth (theory : Theory) where
  truth : Sentence → Bool
  reflects : ∀ sentence, truth sentence = true ↔ theory sentence

/-- A liar diagonal is an additional datum; it is not generated by this toy language. -/
structure LiarDiagonal {theory : Theory} (truth : InternalTruth theory) where
  sentence : Sentence
  lies : truth.truth sentence = !(truth.truth sentence)

/-- No supplied liar diagonal can coexist with its internal Boolean truth predicate. -/
theorem tarski_global {theory : Theory} (truth : InternalTruth theory)
    (liar : LiarDiagonal truth) : False := by
  have lies := liar.lies
  cases h : truth.truth liar.sentence <;> simp [h] at lies

/-- The obstruction is theory-generic, so merely moving to another supplied theory does not remove it. -/
theorem tarski_not_repairable_by_extension
    {first second : Theory} (_extension : ∀ sentence, first sentence → second sentence)
    (truth : InternalTruth second) (liar : LiarDiagonal truth) : False :=
  tarski_global truth liar

/-- The chosen complete closure also cannot carry a supplied liar diagonal. -/
theorem closureTheory_no_internal_truth (truth : InternalTruth closureTheory)
    (liar : LiarDiagonal truth) : False :=
  tarski_global truth liar

end LevelTower

namespace RelativeDepth

/-- A certification basis has a finite declared capacity. -/
structure BoundedBasis where
  capacity : Nat
  certifies : Nat → Prop
  bounded : ∀ depth, certifies depth → depth ≤ capacity

/-- Every finite basis leaves one explicit deeper request uncertified. -/
theorem basis_has_open_depth (basis : BoundedBasis) :
    ¬ basis.certifies (basis.capacity + 1) := by
  intro certified
  have impossible := basis.bounded (basis.capacity + 1) certified
  omega

/-- One simple basis that certifies every depth up to its selected capacity. -/
def basisAt (capacity : Nat) : BoundedBasis where
  capacity := capacity
  certifies := fun depth => depth ≤ capacity
  bounded := by
    intro depth certified
    exact certified

/-- Any selected finite depth is certified by some basis in the family. -/
theorem depth_reopens (depth : Nat) : (basisAt depth).certifies depth :=
  Nat.le_refl depth

/-- Depth is bounded within a basis but unbounded across the supplied family of bases. -/
theorem relative_depth_of_completion :
    (∀ basis : BoundedBasis, ∃ depth, ¬ basis.certifies depth) ∧
      (∀ depth, ∃ basis : BoundedBasis, basis.certifies depth) := by
  constructor
  · intro basis
    exact ⟨basis.capacity + 1, basis_has_open_depth basis⟩
  · intro depth
    exact ⟨basisAt depth, depth_reopens depth⟩

end RelativeDepth

end GodelTarskiRelativeClosureBoundary
end Slearn

#print axioms Slearn.GodelTarskiRelativeClosureBoundary.Diagonal.lawvere_fixed_point
#print axioms Slearn.GodelTarskiRelativeClosureBoundary.Diagonal.encoding_incomplete
#print axioms Slearn.GodelTarskiRelativeClosureBoundary.LevelTower.stage_incomplete
#print axioms Slearn.GodelTarskiRelativeClosureBoundary.LevelTower.boundary_decided_at_successor
#print axioms Slearn.GodelTarskiRelativeClosureBoundary.LevelTower.closureTheory_complete
#print axioms Slearn.GodelTarskiRelativeClosureBoundary.LevelTower.tarski_global
#print axioms Slearn.GodelTarskiRelativeClosureBoundary.RelativeDepth.relative_depth_of_completion
