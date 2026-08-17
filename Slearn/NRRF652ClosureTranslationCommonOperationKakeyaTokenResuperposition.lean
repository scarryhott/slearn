import Slearn.ChaitinKakeyaTokenResuperposition

/-
The common closure operation for Slearn.

`ClosureOp` is deliberately small:

    plurality --Ch--> contracted reading --Ka--> reopened plurality
                                      \-- compare --> residue

It records the relation in which a return is judged separately from literal
equality.  Thus relational recovery may coexist with a nonzero retained
difference, and a vanishing residue need not determine every local route.

The finite "Kakeya", token, and four-phase pieces below are structural models
of resolution, ordered contribution, and quarter-turn transport.  They do not
claim a mathematical Kakeya construction, Chaitin's halting probability,
quantum dynamics, or a physical/cosmological light-matter theory.
-/

universe u v w x y

namespace Slearn

namespace CommonClosureOperation

/--
One reusable closure level: contraction, reopening, the maintained relational
comparison, and a caller-selected residue coordinate.
-/
structure ClosureOp (Plurality : Type u) (Contracted : Type v) (Difference : Type w) where
  contract : Plurality → Contracted
  reopen : Contracted → Plurality
  related : Plurality → Plurality → Prop
  diff : Plurality → Plurality → Difference

namespace ClosureOp

variable {Plurality : Type u} {Contracted : Type v} {Difference : Type w}

/-- The many-one-many return at this closure level. -/
def round (C : ClosureOp Plurality Contracted Difference) : Plurality → Plurality :=
  C.reopen ∘ C.contract

/-- Recovery is judged in the admitted relation, not by literal equality. -/
def Recovers (C : ClosureOp Plurality Contracted Difference) (Γ : Plurality) : Prop :=
  C.related Γ (C.round Γ)

/-- The retained difference between a plurality and its reopened return. -/
def residue (C : ClosureOp Plurality Contracted Difference) (Γ : Plurality) : Difference :=
  C.diff Γ (C.round Γ)

/-- Literal return is a stronger, separately named condition. -/
def LiterallyReturns (C : ClosureOp Plurality Contracted Difference) (Γ : Plurality) : Prop :=
  C.round Γ = Γ

/--
A contraction that identifies two distinct pluralities cannot, by itself, use
one ordinary reopening function to return both of them literally.
-/
theorem contraction_alone_not_closure
    (C : ClosureOp Plurality Contracted Difference) {Γ₁ Γ₂ : Plurality}
    (hMerged : C.contract Γ₁ = C.contract Γ₂) (hDistinct : Γ₁ ≠ Γ₂) :
    ¬ ∃ reopen : Contracted → Plurality,
      reopen (C.contract Γ₁) = Γ₁ ∧ reopen (C.contract Γ₂) = Γ₂ := by
  intro h
  obtain ⟨reopen, h₁, h₂⟩ := h
  apply hDistinct
  calc
    Γ₁ = reopen (C.contract Γ₁) := h₁.symm
    _ = reopen (C.contract Γ₂) := congrArg reopen hMerged
    _ = Γ₂ := h₂

/-- Reciprocal closure supplies relational recovery, while retaining literal novelty as data. -/
structure ReciprocalClosure (C : ClosureOp Plurality Contracted Difference) where
  relationalRecovery : ∀ Γ, C.Recovers Γ
  literalFailure : ∃ Γ, ¬ C.LiterallyReturns Γ

namespace ReciprocalClosure

/-- Reciprocal reopening returns every plurality in the maintained relation. -/
theorem relational_recovery
    {C : ClosureOp Plurality Contracted Difference}
    (R : ReciprocalClosure C) (Γ : Plurality) : C.Recovers Γ :=
  R.relationalRecovery Γ

/-- A reciprocal relation does not collapse into literal endpoint identity. -/
theorem literal_return_still_fails
    {C : ClosureOp Plurality Contracted Difference}
    (R : ReciprocalClosure C) : ∃ Γ, ¬ C.LiterallyReturns Γ :=
  R.literalFailure

/-- The common operation is genuinely many-one-many: relational return and literal novelty coexist. -/
theorem many_one_many
    {C : ClosureOp Plurality Contracted Difference}
    (R : ReciprocalClosure C) :
    (∀ Γ, C.Recovers Γ) ∧ ∃ Γ, ¬ C.LiterallyReturns Γ :=
  ⟨R.relationalRecovery, R.literalFailure⟩

end ReciprocalClosure

end ClosureOp

/-- The three possible residue readings.  Vanishing may still branch structurally. -/
inductive DifferenceReading (Difference : Type u)
  | vanishing (value : Difference)
  | retained (value : Difference)
  | unresolved
  deriving Repr

/-- Extra structure distinguishes ordinary current closure from a collapse. -/
inductive ReturnStructure
  | supported
  | degenerate
  deriving DecidableEq, Repr

/-- The four runtime verdicts shared by the closure-derived map. -/
inductive ClosureVerdict
  | currentClosure
  | newOpening
  | open
  | collapse
  deriving DecidableEq, Repr

/--
The four-way classifier.  The apparent three/four mismatch is intentional:
the vanishing residue reading branches by the structural support of its return.
-/
def verdictOf {Difference : Type u} :
    DifferenceReading Difference → ReturnStructure → ClosureVerdict
  | .vanishing _, .supported => .currentClosure
  | .vanishing _, .degenerate => .collapse
  | .retained _, _ => .newOpening
  | .unresolved, _ => .open

/-- The vanishing, supported case is a current closure. -/
theorem verdictOf_vanishing_supported {Difference : Type u} (Ω : Difference) :
    verdictOf (.vanishing Ω) .supported = .currentClosure :=
  rfl

/-- A vanishing scalar readout with degenerate structure is collapse, not completion. -/
theorem verdictOf_vanishing_degenerate {Difference : Type u} (Ω : Difference) :
    verdictOf (.vanishing Ω) .degenerate = .collapse :=
  rfl

/-- A retained difference is a return-compatible new opening. -/
theorem verdictOf_retained {Difference : Type u}
    (Ω : Difference) (S : ReturnStructure) :
    verdictOf (.retained Ω) S = .newOpening := by
  cases S <;> rfl

/-- An unresolved comparison remains OPEN regardless of display structure. -/
theorem verdictOf_unresolved {Difference : Type u} (S : ReturnStructure) :
    verdictOf (.unresolved : DifferenceReading Difference) S = .open := by
  cases S <;> rfl

/-- The classifier is exhaustive over its three residue readings and two structural states. -/
theorem verdictOf_exhaustive {Difference : Type u}
    (reading : DifferenceReading Difference) (S : ReturnStructure) :
    verdictOf reading S = .currentClosure ∨
      verdictOf reading S = .newOpening ∨
      verdictOf reading S = .open ∨
      verdictOf reading S = .collapse := by
  cases reading <;> cases S <;> simp [verdictOf]

/--
A finite two-route model of the ball/hair lesson: the return is relational,
the selected route retains residue two, and literal endpoint identity fails.
It is an abstract two-cell witness, not a geometric ball construction.
-/
def ballHairOp : ClosureOp Bool Unit Nat where
  contract := fun _ => ()
  reopen := fun _ => false
  related := fun _ _ => True
  diff := fun Γ _ => if Γ then 2 else 0

/-- The selected ball/hair route returns in the maintained relation. -/
theorem ball_hair_relational_recovery : ballHairOp.Recovers true :=
  trivial

/-- The selected ball/hair route retains the archived two-cell residue. -/
theorem ball_hair_residue_two : ballHairOp.residue true = 2 :=
  rfl

/-- Relational recovery here does not entail literal return. -/
theorem ball_hair_not_literal_return : ¬ ballHairOp.LiterallyReturns true := by
  simp [ClosureOp.LiterallyReturns, ClosureOp.round, ballHairOp]

/--
A mirror/collapse witness: its parent residue reads as zero even though the
two input routes are identified by contraction and one is not literally
recovered.  Thus zero residue is level-relative, never absolute completion.
-/
def mirrorParentOp : ClosureOp Bool Unit Nat where
  contract := fun _ => ()
  reopen := fun _ => false
  related := fun _ _ => True
  diff := fun _ _ => 0

theorem mirror_parent_residue_zero : mirrorParentOp.residue true = 0 :=
  rfl

theorem mirror_parent_still_not_literal : ¬ mirrorParentOp.LiterallyReturns true := by
  simp [ClosureOp.LiterallyReturns, ClosureOp.round, mirrorParentOp]

theorem mirror_contraction_identifies_children :
    mirrorParentOp.contract false = mirrorParentOp.contract true :=
  rfl

/--
Finite readout resolutions are the formal role of the proposed Kakeya grain.
They need not be mathematical Kakeya sets: a positive readout may identify
directions, while the entire family of readouts can still determine them.
-/
structure KakeyaResolution (Direction : Type u) (Readout : Type v) where
  read : Nat → Direction → Readout
  finiteCollapses : ∀ n, 0 < n → ∃ d₁ d₂,
    d₁ ≠ d₂ ∧ read n d₁ = read n d₂
  allGrainsDetermine : ∀ {d₁ d₂}, (∀ n, read n d₁ = read n d₂) → d₁ = d₂

namespace KakeyaResolution

variable {Direction : Type u} {Readout : Type v}

/-- Every positive finite grain has a genuine unresolved directional identification. -/
theorem finite_grain_not_injective
    (K : KakeyaResolution Direction Readout) {n : Nat} (hn : 0 < n) :
    ¬ Function.Injective (K.read n) := by
  intro hInjective
  obtain ⟨d₁, d₂, hDistinct, hSame⟩ := K.finiteCollapses n hn
  exact hDistinct (hInjective hSame)

/-- Equality at every grain, rather than equality at one chosen zoom, determines a direction. -/
theorem all_grains_determine_direction
    (K : KakeyaResolution Direction Readout) {d₁ d₂ : Direction}
    (h : ∀ n, K.read n d₁ = K.read n d₂) : d₁ = d₂ :=
  K.allGrainsDetermine h

end KakeyaResolution

/--
An aggregate can be order-blind while a separate residue retains route order.
This is the formal minimum of the tip-to-tail / holonomy distinction.
-/
structure OrderedResuperposition
    (Token : Type u) (Aggregate : Type v) (RouteResidue : Type w) where
  aggregate : List Token → Aggregate
  routeResidue : List Token → RouteResidue
  pairAggregateCommutes : ∀ x y, aggregate [x, y] = aggregate [y, x]

namespace OrderedResuperposition

variable {Token : Type u} {Aggregate : Type v} {RouteResidue : Type w}

/-- An order-blind aggregate cannot by itself determine a route that its residue distinguishes. -/
theorem aggregate_not_route_determining
    (O : OrderedResuperposition Token Aggregate RouteResidue) (x y : Token)
    (hRoute : O.routeResidue [x, y] ≠ O.routeResidue [y, x]) :
    ∃ first second,
      O.aggregate first = O.aggregate second ∧
      O.routeResidue first ≠ O.routeResidue second := by
  exact ⟨[x, y], [y, x], O.pairAggregateCommutes x y, hRoute⟩

end OrderedResuperposition

/-- A finite integer-coordinate presentation of the complex pair \((a,b)\). -/
structure ComplexCoordinate where
  real : Int
  imaginary : Int
  deriving DecidableEq, Repr

namespace ComplexCoordinate

/-- The zero coordinate. -/
def zero : ComplexCoordinate := ⟨0, 0⟩

/-- Multiplication by \(i\) in the stated integer-coordinate complex model. -/
def iShift (z : ComplexCoordinate) : ComplexCoordinate :=
  ⟨-z.imaginary, z.real⟩

/-- Real and imaginary coordinates are the local resonance/dissonance readouts. -/
def resonance (z : ComplexCoordinate) : Int := z.real
def dissonance (z : ComplexCoordinate) : Int := z.imaginary

/-- The two named sectors are coordinate subspaces, not physical substances. -/
def lightOnly (z : ComplexCoordinate) : Prop := z.imaginary = 0
def darkOnly (z : ComplexCoordinate) : Prop := z.real = 0

/-- The i-shift exchanges the real and imaginary readouts with the expected sign. -/
theorem iShift_exchanges_readouts (z : ComplexCoordinate) :
    (iShift z).resonance = -z.dissonance ∧
      (iShift z).dissonance = z.resonance :=
  ⟨rfl, rfl⟩

/-- Four i-shifts visibly return the same coordinate. -/
theorem iShift_four (z : ComplexCoordinate) :
    iShift (iShift (iShift (iShift z))) = z := by
  cases z
  simp [iShift]

/-- The two coordinate sectors meet only at the zero coordinate. -/
theorem sectors_meet_only_zero {z : ComplexCoordinate}
    (hLight : z.lightOnly) (hDark : z.darkOnly) : z = zero := by
  cases z with
  | mk real imaginary =>
      simp [lightOnly, darkOnly] at hLight hDark
      subst real
      subst imaginary
      rfl

/-- The i-shift sends the light-named coordinate sector into the dark-named sector. -/
theorem iShift_light_to_dark {z : ComplexCoordinate}
    (h : z.lightOnly) : (iShift z).darkOnly := by
  cases z with
  | mk real imaginary =>
      simpa [lightOnly, darkOnly, iShift] using h

/-- The i-shift sends the dark-named coordinate sector into the light-named sector. -/
theorem iShift_dark_to_light {z : ComplexCoordinate}
    (h : z.darkOnly) : (iShift z).lightOnly := by
  cases z with
  | mk real imaginary =>
      simpa [lightOnly, darkOnly, iShift] using h

/-- Shift exactly one selected dimension of a dimension-indexed metavector net. -/
def metavec_shiftDim {Dimension : Type u} [DecidableEq Dimension]
    (d : Dimension) (net : Dimension → ComplexCoordinate) :
    Dimension → ComplexCoordinate :=
  fun e => if e = d then iShift (net e) else net e

/-- The selected dimension is the only component turned by `metavec_shiftDim`. -/
theorem metavec_shiftDim_target {Dimension : Type u} [DecidableEq Dimension]
    (d : Dimension) (net : Dimension → ComplexCoordinate) :
    metavec_shiftDim d net d = iShift (net d) := by
  simp [metavec_shiftDim]

/-- Every unselected dimension is preserved by the local turn. -/
theorem metavec_shiftDim_other {Dimension : Type u} [DecidableEq Dimension]
    {d e : Dimension} (h : e ≠ d) (net : Dimension → ComplexCoordinate) :
    metavec_shiftDim d net e = net e := by
  simp [metavec_shiftDim, h]

/-- Four local turns restore the whole visible dimension net. -/
theorem metavec_shiftDim_four {Dimension : Type u} [DecidableEq Dimension]
    (d : Dimension) (net : Dimension → ComplexCoordinate) :
    metavec_shiftDim d
      (metavec_shiftDim d
        (metavec_shiftDim d
          (metavec_shiftDim d net))) = net := by
  funext e
  by_cases h : e = d
  · subst e
    simp [metavec_shiftDim, iShift_four]
  · simp [metavec_shiftDim, h]

/--
A four-phase return can retain a nonzero caller-recorded holonomy even though
the visible net returns exactly.  The record is structural history, not a
claim about physical time.
-/
structure FourPhaseHolonomy (Dimension : Type u) [DecidableEq Dimension] where
  dimension : Dimension
  net : Dimension → ComplexCoordinate
  accumulatedTurns : Nat
  nonzeroHolonomy : accumulatedTurns ≠ 0

theorem four_phase_visible_return {Dimension : Type u} [DecidableEq Dimension]
    (H : FourPhaseHolonomy Dimension) :
    metavec_shiftDim H.dimension
      (metavec_shiftDim H.dimension
        (metavec_shiftDim H.dimension
          (metavec_shiftDim H.dimension H.net))) = H.net :=
  metavec_shiftDim_four H.dimension H.net

end ComplexCoordinate

/--
The Slearn binding: zoom out and zoom in are the two arrows of `ClosureOp`,
not an independent display navigation mechanism.
-/
structure SlearnClosureRuntime
    (PerspectivePath : Type u) (Goal : Type v) (Difference : Type w) where
  operation : ClosureOp PerspectivePath Goal Difference

namespace SlearnClosureRuntime

variable {PerspectivePath : Type u} {Goal : Type v} {Difference : Type w}

/-- Perspective-to-goal semantic zoom is contraction. -/
def zoomOut (R : SlearnClosureRuntime PerspectivePath Goal Difference) :
    PerspectivePath → Goal :=
  R.operation.contract

/-- Goal-to-perspective semantic expansion is reopening. -/
def zoomIn (R : SlearnClosureRuntime PerspectivePath Goal Difference) :
    Goal → PerspectivePath :=
  R.operation.reopen

/-- Every admitted semantic zoom executes the shared closure round. -/
def executeZoom (R : SlearnClosureRuntime PerspectivePath Goal Difference) :
    PerspectivePath → PerspectivePath :=
  R.zoomIn ∘ R.zoomOut

/-- The runtime zoom is definitionally the common operation's round. -/
theorem executeZoom_is_round
    (R : SlearnClosureRuntime PerspectivePath Goal Difference) :
    R.executeZoom = R.operation.round :=
  rfl

/-- The learner-facing residue is the common closure residue, not merely the goal summary. -/
def zoomResidue (R : SlearnClosureRuntime PerspectivePath Goal Difference)
    (path : PerspectivePath) : Difference :=
  R.operation.residue path

end SlearnClosureRuntime

end CommonClosureOperation

end Slearn

#print axioms Slearn.CommonClosureOperation.ClosureOp.contraction_alone_not_closure
#print axioms Slearn.CommonClosureOperation.ClosureOp.ReciprocalClosure.relational_recovery
#print axioms Slearn.CommonClosureOperation.verdictOf_exhaustive
#print axioms Slearn.CommonClosureOperation.KakeyaResolution.finite_grain_not_injective
#print axioms Slearn.CommonClosureOperation.OrderedResuperposition.aggregate_not_route_determining
#print axioms Slearn.CommonClosureOperation.ComplexCoordinate.iShift_four
#print axioms Slearn.CommonClosureOperation.ComplexCoordinate.sectors_meet_only_zero
#print axioms Slearn.CommonClosureOperation.ComplexCoordinate.metavec_shiftDim_four
#print axioms Slearn.CommonClosureOperation.SlearnClosureRuntime.executeZoom_is_round
