import Slearn.RecalculationAgainstTranslatedTruthAnswers

/-
Partition aggregate closure for Slearn.

This is a deliberately finite, non-physical re-derivation of the closure
relevant part of the reported partition-wave scenario.  A four-form
presentation has an aggregate at the current scalar reading.  Two distinct
phase arrangements can have the same aggregate, so the scalar reading closes
them together.  A retained phase question then separates them at the next
reading.  The theorem does not interpret the four forms as quantum states,
curvature, matter, time, or a continuous orbit.
-/

namespace Slearn
namespace PartitionAggregateClosure

open RecalculationAgainstTranslatedTruthAnswers

/-- The four finite orientations used by the model. -/
inductive Phase
  | zero
  | quarter
  | half
  | threeQuarter
  deriving DecidableEq, Repr

namespace Phase

/-- A quarter-turn in the finite orientation model. -/
def turn : Phase → Phase
  | zero => quarter
  | quarter => half
  | half => threeQuarter
  | threeQuarter => zero

theorem turn_four (phase : Phase) :
    turn (turn (turn (turn phase))) = phase := by
  cases phase <;> rfl

/-- Integer coordinates are only a finite aggregate readout, not physical amplitudes. -/
def vector : Phase → Int × Int
  | zero => (1, 0)
  | quarter => (0, 1)
  | half => (-1, 0)
  | threeQuarter => (0, -1)

end Phase

/-- A four-block presentation retains the placement of its four orientations. -/
abbrev Partition := Fin 4 → Phase

private def index0 : Fin 4 := ⟨0, by decide⟩
private def index1 : Fin 4 := ⟨1, by decide⟩
private def index2 : Fin 4 := ⟨2, by decide⟩
private def index3 : Fin 4 := ⟨3, by decide⟩

/-- The canonical four-part cancellation: (1 + i - 1 - i = 0). -/
def quadrature : Partition
  | ⟨0, _⟩ => .zero
  | ⟨1, _⟩ => .quarter
  | ⟨2, _⟩ => .half
  | ⟨3, _⟩ => .threeQuarter

/-- A different phase placement with the same scalar aggregate. -/
def rearranged : Partition
  | ⟨0, _⟩ => .quarter
  | ⟨1, _⟩ => .zero
  | ⟨2, _⟩ => .threeQuarter
  | ⟨3, _⟩ => .half

private def add (left right : Int × Int) : Int × Int :=
  (left.1 + right.1, left.2 + right.2)

/-- The current scalar closure reads only the aggregate of the four positions. -/
def aggregate (partition : Partition) : Int × Int :=
  add
    (add (add (Phase.vector (partition index0)) (Phase.vector (partition index1)))
      (Phase.vector (partition index2)))
    (Phase.vector (partition index3))

theorem quadrature_aggregate_zero : aggregate quadrature = (0, 0) := by
  decide

theorem rearranged_aggregate_zero : aggregate rearranged = (0, 0) := by
  decide

theorem same_scalar_aggregate : aggregate quadrature = aggregate rearranged := by
  rw [quadrature_aggregate_zero, rearranged_aggregate_zero]

/-- The retained local form at the first block is a possible successor question. -/
def firstPhase (partition : Partition) : Phase := partition index0

theorem first_phase_separates : firstPhase quadrature ≠ firstPhase rearranged := by
  decide

theorem presentations_are_distinct : quadrature ≠ rearranged := by
  intro equal
  exact first_phase_separates (congrArg firstPhase equal)

/-- Applying the finite turn to every retained form. -/
def fold (partition : Partition) : Partition := fun index => Phase.turn (partition index)

theorem fold_four (partition : Partition) :
    fold (fold (fold (fold partition))) = partition := by
  funext index
  exact Phase.turn_four (partition index)

theorem fold_moves_quadrature : fold quadrature ≠ quadrature := by
  intro equal
  have atFirst := congrFun equal index0
  change Phase.quarter = Phase.zero at atFirst
  exact Phase.quarter.noConfusion atFirst

/-- A scalar result or a retained phase result are different observable readings. -/
inductive Observation
  | scalar (value : Int × Int)
  | phase (value : Phase)
  deriving DecidableEq, Repr

/-- At the current level only the scalar aggregate is in the question-language. -/
def scalarLanguage :
    FrozenQuestionLanguage Partition Observation where
  Question := Unit
  translate := id
  answer := fun _ partition => .scalar (aggregate partition)

/-- The scalar aggregate is a genuine current-level translated truth equality. -/
theorem scalar_truth_equal : scalarLanguage.TruthEq quadrature rearranged := by
  intro question
  cases question
  simpa [scalarLanguage] using congrArg Observation.scalar same_scalar_aggregate

/-- The aggregate equality is admitted through the existing transaction adapter. -/
theorem scalar_truth_closes_in_transaction :
    (scalarLanguage.transactionOf scalar_truth_equal).admitted.closes () () :=
  scalarLanguage.truthEq_closes_in_transaction scalar_truth_equal

/-- The phase placement is retained as a supplied, rather than invented, next question. -/
def phaseAsymmetry : scalarLanguage.PerspectiveAsymmetry quadrature rearranged where
  discriminator := fun partition => .phase (firstPhase partition)
  separates := by
    intro equal
    apply first_phase_separates
    simpa using congrArg (fun observation =>
      match observation with
      | .phase phase => phase
      | .scalar _ => Phase.zero) equal

/-- A closed scalar relation reopens when the retained phase question is admitted. -/
theorem scalar_closure_reopens :
    scalarLanguage.TruthEq quadrature rearranged ∧
      ¬ (scalarLanguage.extend phaseAsymmetry.discriminator).TruthEq quadrature rearranged :=
  scalarLanguage.successor_reopens scalar_truth_equal phaseAsymmetry

/-- A continuation is aggregate-determined only when it factors through the scalar readout. -/
def DeterminedByAggregate (continuation : Partition → Phase) : Prop :=
  ∃ summary : Int × Int → Phase, ∀ partition, continuation partition = summary (aggregate partition)

/-- The next phase question cannot be reconstructed from this scalar aggregate alone. -/
theorem continuation_not_determined_by_aggregate :
    ¬ DeterminedByAggregate firstPhase := by
  rintro ⟨summary, determined⟩
  apply first_phase_separates
  calc
    firstPhase quadrature = summary (aggregate quadrature) := determined quadrature
    _ = summary (aggregate rearranged) := by rw [same_scalar_aggregate]
    _ = firstPhase rearranged := (determined rearranged).symm

/-- A zero aggregate is not an empty retained presentation in this finite model. -/
theorem aggregate_zero_retains_four_forms :
    aggregate quadrature = (0, 0) ∧
      quadrature index0 = .zero ∧
        quadrature index1 = .quarter ∧
          quadrature index2 = .half ∧ quadrature index3 = .threeQuarter := by
  decide

/-- The finite scenario's closure result, restricted to the stated representations. -/
theorem partition_aggregate_closure_scenario :
    scalarLanguage.TruthEq quadrature rearranged ∧
      quadrature ≠ rearranged ∧
        ¬ (scalarLanguage.extend phaseAsymmetry.discriminator).TruthEq quadrature rearranged ∧
          ¬ DeterminedByAggregate firstPhase ∧
            fold (fold (fold (fold quadrature))) = quadrature := by
  exact ⟨scalar_truth_equal, presentations_are_distinct, scalar_closure_reopens.2,
    continuation_not_determined_by_aggregate, fold_four quadrature⟩

end PartitionAggregateClosure
end Slearn

#print axioms Slearn.PartitionAggregateClosure.Phase.turn_four
#print axioms Slearn.PartitionAggregateClosure.scalar_truth_equal
#print axioms Slearn.PartitionAggregateClosure.scalar_truth_closes_in_transaction
#print axioms Slearn.PartitionAggregateClosure.scalar_closure_reopens
#print axioms Slearn.PartitionAggregateClosure.continuation_not_determined_by_aggregate
#print axioms Slearn.PartitionAggregateClosure.partition_aggregate_closure_scenario
