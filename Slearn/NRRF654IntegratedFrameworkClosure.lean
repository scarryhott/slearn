import Slearn.NRRF651SlearnUIHairOfClosureGeneratedMap
import Slearn.NRRF652ClosureTranslationCommonOperationKakeyaTokenResuperposition
import Slearn.InteractiveTranslationalOpenFoundation

/-
Integrated framework closure for Slearn.

This file is an adapter layer, not a new claim that the imported models are
definitionally identical.  It makes their shared contract explicit where the
types genuinely line up:

* an admitted local/global translation supplies the contraction and reopening
  of the common closure operation;
* Slearn semantic zoom executes that same operation;
* the natural-rhythm cone supplies the relative local/global view discipline;
* universal-relative completion remains the unique completion operator only
  under its own admissibility contract;
* the generated learning map presents a supplied translation through tagged
  local/global occurrences; and
* interactive verification and resolution-aware receipts are optional, typed
  evidence gates rather than facts manufactured by the browser.

No theorem here establishes a physical UI, validates a learner receipt,
identifies a source text with a formal theorem, or turns a metaphorical
Topos/Turing, token, or Kakeya reading into an empirical claim.
-/

universe u v w x y z

namespace Slearn

namespace RelativeToposTuring

variable {Turing : Type u} {Topos : Type v} {Witness : Type w}

/-- The existing Topos/Turing interface is one instance of admitted translation. -/
def admittedTranslation (R : RelativeToposTuring Turing Topos Witness) :
    AdmittedTranslation Turing Topos Witness where
  forward := R.encode
  backward := R.evaluate
  localWitness := R.turingWitness
  globalWitness := R.toposWitness
  forward_coherent := R.encode_coherent
  backward_coherent := R.evaluate_coherent

/-- Cross-language equality is exactly closure in its admitted-translation reading. -/
theorem crossEq_iff_admitted_closes
    (R : RelativeToposTuring Turing Topos Witness) (t : Turing) (p : Topos) :
    R.crossEq t p ↔ R.admittedTranslation.closes t p := by
  rfl

end RelativeToposTuring

namespace FrameworkClosure

open CommonClosureOperation

/--
One whole-framework closure pass.  The equality fields are the required
bridges: the shared operation cannot be silently substituted for an admitted
translation or a Slearn zoom implementation.
-/
structure IntegratedFramework
    (Perspective : Type u) (Goal : Type v) (Witness : Type w) (Difference : Type x) where
  frame : RelativeFrame.{u, u} Perspective
  rhythm : NaturalRhythmCone Perspective frame
  translation : AdmittedTranslation Perspective Goal Witness
  operation : ClosureOp Perspective Goal Difference
  runtime : SlearnClosureRuntime Perspective Goal Difference
  contract_is_forward : operation.contract = translation.forward
  reopen_is_backward : operation.reopen = translation.backward
  related_iff_witness : ∀ p q,
    operation.related p q ↔ translation.localWitness p = translation.localWitness q
  runtime_is_operation : runtime.operation = operation
  literalNovelty : ∃ p, operation.round p ≠ p

namespace IntegratedFramework

variable {Perspective : Type u} {Goal : Type v} {Witness : Type w} {Difference : Type x}

/-- The common round is exactly forward translation followed by its admitted return. -/
theorem round_is_translation_return
    (I : IntegratedFramework Perspective Goal Witness Difference) :
    I.operation.round = I.translation.backward ∘ I.translation.forward := by
  funext p
  change I.operation.reopen (I.operation.contract p) =
    I.translation.backward (I.translation.forward p)
  rw [I.contract_is_forward, I.reopen_is_backward]

/-- The operation's return is closed in the translation witness language. -/
theorem round_closes
    (I : IntegratedFramework Perspective Goal Witness Difference) (p : Perspective) :
    I.translation.localWitness (I.operation.round p) = I.translation.localWitness p := by
  have hround : I.operation.round p =
      I.translation.backward (I.translation.forward p) := by
    change I.operation.reopen (I.operation.contract p) =
      I.translation.backward (I.translation.forward p)
    rw [I.contract_is_forward, I.reopen_is_backward]
  calc
    I.translation.localWitness (I.operation.round p) =
        I.translation.localWitness (I.translation.backward (I.translation.forward p)) :=
      congrArg I.translation.localWitness hround
    _ = I.translation.globalWitness (I.translation.forward p) :=
      I.translation.backward_coherent _
    _ = I.translation.localWitness p := I.translation.forward_coherent p

/-- Each common-operation round returns in its declared closure relation. -/
theorem operation_recovers
    (I : IntegratedFramework Perspective Goal Witness Difference) (p : Perspective) :
    I.operation.Recovers p := by
  apply (I.related_iff_witness p (I.operation.round p)).2
  exact (I.round_closes p).symm

/-- The shared operation satisfies the common reciprocal-closure interface. -/
theorem reciprocalClosure
    (I : IntegratedFramework Perspective Goal Witness Difference) :
    ClosureOp.ReciprocalClosure I.operation where
  relationalRecovery := I.operation_recovers
  literalFailure := by
    obtain ⟨p, hp⟩ := I.literalNovelty
    exact ⟨p, hp⟩

/-- The framework retains relational return without reducing it to endpoint identity. -/
theorem many_one_many
    (I : IntegratedFramework Perspective Goal Witness Difference) :
    (∀ p, I.operation.Recovers p) ∧ ∃ p, ¬ I.operation.LiterallyReturns p :=
  I.reciprocalClosure.many_one_many

/-- Browser-level semantic zoom is the same forward/return translation round. -/
theorem runtime_zoom_is_translation_return
    (I : IntegratedFramework Perspective Goal Witness Difference) :
    I.runtime.executeZoom = I.translation.backward ∘ I.translation.forward := by
  calc
    I.runtime.executeZoom = I.runtime.operation.round :=
      SlearnClosureRuntime.executeZoom_is_round I.runtime
    _ = I.operation.round := by rw [I.runtime_is_operation]
    _ = I.translation.backward ∘ I.translation.forward := I.round_is_translation_return

/-- The source-frame theorem remains available as the unique admissible completion. -/
theorem universal_completion_unique
    (I : IntegratedFramework Perspective Goal Witness Difference)
    {C : (Perspective → Prop) → Perspective → Prop}
    (hC : I.frame.UniversalRelativeAdmissible C) :
    C = I.frame.completion :=
  I.frame.admissible_eq_completion hC

/-- The natural-rhythm local opening remains within its declared global opening. -/
theorem local_opening_within_global
    (I : IntegratedFramework Perspective Goal Witness Difference) :
    ∀ p, I.frame.opening I.rhythm.localView I.rhythm.apex p →
      I.frame.opening I.rhythm.globalView I.rhythm.apex p :=
  I.rhythm.local_opening_subset_global

end IntegratedFramework

/--
An explicit witness that a generated map is a presentation of one admitted
translation.  Sum tags preserve the distinction between local and global
presentations instead of coercing one into the other.
-/
structure TranslationGeneratedMapWitness
    {Local : Type u} {Global : Type v} {Witness : Type w}
    {Trace : Type x} {Receipt : Type y}
    (T : AdmittedTranslation Local Global Witness)
    (F : UIHairOfClosure.InteractionField (Local ⊕ Global) Trace Receipt) where
  localOf : Trace → Local
  globalOf : Trace → Global
  source_is_local : ∀ t, F.source t = .inl (localOf t)
  target_is_global : ∀ t, F.target t = .inr (globalOf t)
  natural_bridge_closes : ∀ t,
    F.Bridge t → F.position t = UIHairOfClosure.RelativePosition.natural →
      T.closes (localOf t) (globalOf t)

namespace TranslationGeneratedMapWitness

variable {Local : Type u} {Global : Type v} {Witness : Type w}
variable {Trace : Type x} {Receipt : Type y}
variable {T : AdmittedTranslation Local Global Witness}
variable {F : UIHairOfClosure.InteractionField (Local ⊕ Global) Trace Receipt}

/-- A natural bridged map trace closes in the same witness language as its translation. -/
theorem bridge_closes
    (M : TranslationGeneratedMapWitness T F) (t : Trace)
    (hbridge : F.Bridge t)
    (hposition : F.position t = UIHairOfClosure.RelativePosition.natural) :
    T.closes (M.localOf t) (M.globalOf t) :=
  M.natural_bridge_closes t hbridge hposition

/-- The source occurrence preserves its explicit local presentation tag. -/
theorem source_has_local_tag
    (M : TranslationGeneratedMapWitness T F) (t : Trace) :
    F.source t = .inl (M.localOf t) :=
  M.source_is_local t

/-- The target occurrence preserves its explicit global presentation tag. -/
theorem target_has_global_tag
    (M : TranslationGeneratedMapWitness T F) (t : Trace) :
    F.target t = .inr (M.globalOf t) :=
  M.target_is_global t

end TranslationGeneratedMapWitness

/--
The whole-framework form of the Slearn map adapter.  It is intentionally
optional data: browser strings are not presumed to satisfy it automatically.
-/
structure IntegratedSlearnProjection
    {Perspective : Type u} {Goal : Type v} {Witness : Type w} {Difference : Type x}
    {Trace : Type y} {Receipt : Type z}
    (I : IntegratedFramework Perspective Goal Witness Difference)
    (F : UIHairOfClosure.InteractionField (Perspective ⊕ Goal) Trace Receipt) where
  mapWitness : TranslationGeneratedMapWitness I.translation F

namespace IntegratedSlearnProjection

variable {Perspective : Type u} {Goal : Type v} {Witness : Type w} {Difference : Type x}
variable {Trace : Type y} {Receipt : Type z}
variable {I : IntegratedFramework Perspective Goal Witness Difference}
variable {F : UIHairOfClosure.InteractionField (Perspective ⊕ Goal) Trace Receipt}

/-- A natural bridged UI trace is a closure of the framework's admitted translation. -/
theorem natural_bridge_closes
    (P : IntegratedSlearnProjection I F) (t : Trace)
    (hbridge : F.Bridge t)
    (hposition : F.position t = UIHairOfClosure.RelativePosition.natural) :
    I.translation.closes (P.mapWitness.localOf t) (P.mapWitness.globalOf t) :=
  P.mapWitness.bridge_closes t hbridge hposition

end IntegratedSlearnProjection

/--
An optional interactive-proof gate for receipts.  A runtime must supply this
data; it is not inferred from a text field or a successful-looking UI action.
-/
structure InteractiveReceiptGate (Receipt : Type u) where
  transcript : Receipt → InteractiveOpenFoundation.Transcript
  continuouslyChecked : ∀ receipt,
    InteractiveOpenFoundation.ContinuousCompletion (transcript receipt)

namespace InteractiveReceiptGate

variable {Receipt : Type u}

/-- A continuously checked receipt is closed in the finite-prefix translation frame. -/
theorem receipt_has_translational_completion
    (G : InteractiveReceiptGate Receipt) (receipt : Receipt) :
    InteractiveOpenFoundation.transcriptFrame.completion InteractiveOpenFoundation.Sound
      (G.transcript receipt) :=
  (InteractiveOpenFoundation.continuousCompletion_eq_translationalClosure
    (G.transcript receipt)).1 (G.continuouslyChecked receipt)

end InteractiveReceiptGate

/--
An optional resolution-aware reading of receipts.  It links a returned receipt
to the existing Kakeya-grain interface without claiming that every receipt has
such a reading or that a finite grain settles an open question.
-/
structure ResolutionAwareReceipt
    (Receipt : Type u) (Direction : Type v) (Readout : Type w) where
  direction : Receipt → Direction
  resolution : KakeyaResolution Direction Readout

namespace ResolutionAwareReceipt

variable {Receipt : Type u} {Direction : Type v} {Readout : Type w}

/-- Agreement at every available grain determines the supplied receipt directions. -/
theorem all_grains_determine_direction
    (R : ResolutionAwareReceipt Receipt Direction Readout) {first second : Receipt}
    (h : ∀ n, R.resolution.read n (R.direction first) =
      R.resolution.read n (R.direction second)) :
    R.direction first = R.direction second :=
  KakeyaResolution.all_grains_determine_direction R.resolution h

end ResolutionAwareReceipt

end FrameworkClosure

end Slearn

#print axioms Slearn.RelativeToposTuring.crossEq_iff_admitted_closes
#print axioms Slearn.FrameworkClosure.IntegratedFramework.round_closes
#print axioms Slearn.FrameworkClosure.IntegratedFramework.operation_recovers
#print axioms Slearn.FrameworkClosure.IntegratedFramework.many_one_many
#print axioms Slearn.FrameworkClosure.IntegratedFramework.runtime_zoom_is_translation_return
#print axioms Slearn.FrameworkClosure.IntegratedFramework.universal_completion_unique
#print axioms Slearn.FrameworkClosure.TranslationGeneratedMapWitness.bridge_closes
#print axioms Slearn.FrameworkClosure.IntegratedSlearnProjection.natural_bridge_closes
#print axioms Slearn.FrameworkClosure.InteractiveReceiptGate.receipt_has_translational_completion
#print axioms Slearn.FrameworkClosure.ResolutionAwareReceipt.all_grains_determine_direction
