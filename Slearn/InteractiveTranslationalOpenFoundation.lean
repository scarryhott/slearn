import Slearn.UniversalRelativeTranslationalCompletion

/-
Interactive translational openness for Slearn.

This module joins the universal-relative completion operator to a finite-prefix
model of interactive verification, an inverse-limit presentation, a returned
Topos/Turing translation interface, and concrete relative-gluing examples.

The scope is deliberately exact:
* finite-stage incompleteness is caused by finite-prefix locality;
* continuous completion is identified with translational closure in that model;
* Topos/Turing names designate two translated presentations, not a theorem that
  an arbitrary topos is definitionally or categorically equal to a Turing
  machine;
* translational completion is unique only under the universal-relative
  admissibility contract already formalized in the imported module;
* translation maps remain choices and may close or obstruct a local gluing.
-/

universe u v w

namespace Slearn

namespace InteractiveOpenFoundation

/-- An interaction transcript: `true` records a defect at that exchange. -/
abbrev Transcript := Nat → Bool

/-- The stage-`n` local language: the first `n` exchanges. -/
def finitePrefix (n : Nat) (x : Transcript) : Fin n → Bool :=
  fun i => x i.val

/-- The globally sound transcript. -/
def zeros : Transcript :=
  fun _ => false

/-- A transcript whose first defect is placed immediately beyond stage `n`. -/
def delayedDefect (n : Nat) : Transcript :=
  fun i => if i = n then true else false

/-- Global soundness is absence of defects at every exchange. -/
def Sound (x : Transcript) : Prop :=
  ∀ i, x i = false

/-- A stage verifier is arbitrary, but it can read only the stage prefix. -/
def StageVerifier (n : Nat) : Type :=
  (Fin n → Bool) → Bool

/-- Apply a stage verifier to the only information admitted at that stage. -/
def stageVerdict {n : Nat} (V : StageVerifier n) (x : Transcript) : Bool :=
  V (finitePrefix n x)

/-- The zero transcript is sound. -/
theorem zeros_sound : Sound zeros := by
  intro i
  rfl

/-- A delayed defect makes the transcript globally unsound. -/
theorem delayedDefect_not_sound (n : Nat) : ¬ Sound (delayedDefect n) := by
  intro h
  have hfalse : true = false := by
    simpa [delayedDefect] using h n
  cases hfalse

/-- No stage-`n` prefix distinguishes zero from a defect first appearing at `n`. -/
theorem finitePrefix_delayedDefect (n : Nat) :
    finitePrefix n zeros = finitePrefix n (delayedDefect n) := by
  funext i
  have hne : i.val ≠ n := Nat.ne_of_lt i.isLt
  simp [finitePrefix, zeros, delayedDefect, hne]

/--
Every finite-prefix verifier is incomplete for global soundness, independently
of computability: two transcripts with the same admitted input have different
global soundness values.
-/
theorem no_finite_stage_decides (n : Nat) (V : StageVerifier n) :
    ¬ ∀ x, (stageVerdict V x = true ↔ Sound x) := by
  intro hdecides
  have hz : stageVerdict V zeros = true :=
    (hdecides zeros).2 zeros_sound
  have hd : stageVerdict V (delayedDefect n) = true := by
    unfold stageVerdict at hz ⊢
    rw [← finitePrefix_delayedDefect n]
    exact hz
  exact delayedDefect_not_sound n
    ((hdecides (delayedDefect n)).1 hd)

/-- Passing the canonical stage test means that every visible exchange is clear. -/
def StagePass (n : Nat) (x : Transcript) : Prop :=
  ∀ i : Fin n, finitePrefix n x i = false

/-- Continuous completion means passing every finite stage. -/
def ContinuousCompletion (x : Transcript) : Prop :=
  ∀ n, StagePass n x

/-- Passing every finite stage is exactly global soundness. -/
theorem continuousCompletion_iff_sound (x : Transcript) :
    ContinuousCompletion x ↔ Sound x := by
  constructor
  · intro h i
    exact h (i + 1) ⟨i, Nat.lt_succ_self i⟩
  · intro h n i
    exact h i.val

/-- Lift an index from a coarser prefix into a refining prefix. -/
def liftFin {n m : Nat} (h : n ≤ m) (i : Fin n) : Fin m :=
  ⟨i.val, Nat.lt_of_lt_of_le i.isLt h⟩

/--
The finite-prefix relative frame. A larger natural number is a more refined
language, and equality is equality of the visible prefix.
-/
def transcriptFrame : RelativeFrame Transcript where
  View := Nat
  same n x y := finitePrefix n x = finitePrefix n y
  same_refl := by
    intro n x
    rfl
  same_symm := by
    intro n x y h
    exact h.symm
  same_trans := by
    intro n x y z hxy hyz
    exact hxy.trans hyz
  refines n m := n ≤ m
  refines_refl := by
    intro n
    exact Nat.le_refl n
  refines_trans := by
    intro a b c hab hbc
    exact Nat.le_trans hab hbc
  directed := by
    intro a b
    exact ⟨Nat.max a b, Nat.le_max_left a b, Nat.le_max_right a b⟩
  same_of_refines := by
    intro a b x y hab hxy
    funext i
    exact congrFun hxy (liftFin hab i)

/-- The global sound set is a fixed point of finite-prefix translational closure. -/
theorem completion_sound_iff (x : Transcript) :
    transcriptFrame.completion Sound x ↔ Sound x := by
  constructor
  · intro hx i
    obtain ⟨y, hy, hxy⟩ := hx (i + 1)
    have hAt := congrFun hxy (⟨i, Nat.lt_succ_self i⟩ : Fin (i + 1))
    calc
      x i = y i := hAt
      _ = false := hy i
  · intro hx
    exact RelativeFrame.completion_extensive transcriptFrame Sound x hx

/-- In this model, soundness is closed under universal-relative completion. -/
theorem sound_is_closed : transcriptFrame.IsComplete Sound := by
  funext x
  apply propext
  exact completion_sound_iff x

/--
Continuous interactive completion and the translational closure operator are
the same acceptance condition in the finite-prefix frame.
-/
theorem continuousCompletion_eq_translationalClosure (x : Transcript) :
    ContinuousCompletion x ↔ transcriptFrame.completion Sound x := by
  exact (continuousCompletion_iff_sound x).trans
    (completion_sound_iff x).symm

/-- A compact receipt for finite openness and globally closed completion. -/
theorem interactive_open_foundation_receipt
    (n : Nat) (V : StageVerifier n) :
    (¬ ∀ x, (stageVerdict V x = true ↔ Sound x)) ∧
    (∀ x, ContinuousCompletion x ↔ transcriptFrame.completion Sound x) ∧
    transcriptFrame.IsComplete Sound := by
  exact ⟨no_finite_stage_decides n V,
    continuousCompletion_eq_translationalClosure,
    sound_is_closed⟩

/--
A compatible family of all finite prefixes: the elementary inverse-limit
object for the refinement tower.
-/
structure PrefixInverseLimit where
  component : (n : Nat) → Fin n → Bool
  compatible :
    ∀ {n m} (h : n ≤ m) (i : Fin n),
      component m (liftFin h i) = component n i

/-- Every complete transcript determines a compatible prefix family. -/
def transcriptToLimit (x : Transcript) : PrefixInverseLimit where
  component := fun n => finitePrefix n x
  compatible := by
    intro n m h i
    rfl

/-- Every compatible prefix family determines a complete transcript. -/
def PrefixInverseLimit.toTranscript (C : PrefixInverseLimit) : Transcript :=
  fun i => C.component (i + 1) ⟨i, Nat.lt_succ_self i⟩

/-- Reconstructing a transcript from its prefix family returns it exactly. -/
theorem transcript_limit_return (x : Transcript) :
    (transcriptToLimit x).toTranscript = x := by
  funext i
  rfl

/-- Reconstructing from a compatible family returns every one of its prefixes. -/
theorem limit_prefix_return (C : PrefixInverseLimit) (n : Nat) :
    finitePrefix n C.toTranscript = C.component n := by
  funext i
  let j : Fin (i.val + 1) := ⟨i.val, Nat.lt_succ_self i.val⟩
  have hle : i.val + 1 ≤ n := Nat.succ_le_of_lt i.isLt
  have hlift : liftFin hle j = i := by
    apply Fin.ext
    rfl
  have hc := C.compatible hle j
  change C.component (i.val + 1) j = C.component n i
  rw [← hlift]
  exact hc.symm

/-- A compatible prefix family is determined by its reconstructed transcript. -/
theorem inverseLimit_extensional
    (C D : PrefixInverseLimit)
    (h : C.toTranscript = D.toTranscript) :
    ∀ n, C.component n = D.component n := by
  intro n
  rw [← limit_prefix_return C n, ← limit_prefix_return D n, h]

end InteractiveOpenFoundation

/--
Two asymmetric presentations joined only through a returned witness language.
The maps need not be inverse as functions; their composites return the same
closure witness.
-/
structure RelativeToposTuring
    (Turing : Type u) (Topos : Type v) (Witness : Type w) where
  encode : Turing → Topos
  evaluate : Topos → Turing
  turingWitness : Turing → Witness
  toposWitness : Topos → Witness
  encode_coherent :
    ∀ t, toposWitness (encode t) = turingWitness t
  evaluate_coherent :
    ∀ p, turingWitness (evaluate p) = toposWitness p

namespace RelativeToposTuring

variable {Turing : Type u} {Topos : Type v} {Witness : Type w}
variable (R : RelativeToposTuring Turing Topos Witness)

/-- Relative equality inside the Turing presentation. -/
def turingEq (x y : Turing) : Prop :=
  R.turingWitness x = R.turingWitness y

/-- Relative equality inside the Topos presentation. -/
def toposEq (x y : Topos) : Prop :=
  R.toposWitness x = R.toposWitness y

/-- Cross-language equality through the common returned witness. -/
def crossEq (t : Turing) (p : Topos) : Prop :=
  R.turingWitness t = R.toposWitness p

/-- Turing encoded through Topos and evaluated back returns in closure. -/
theorem turing_return (t : Turing) :
    R.turingEq (R.evaluate (R.encode t)) t := by
  calc
    R.turingWitness (R.evaluate (R.encode t))
        = R.toposWitness (R.encode t) := R.evaluate_coherent _
    _ = R.turingWitness t := R.encode_coherent _

/-- Topos evaluated through Turing and encoded back returns in closure. -/
theorem topos_return (p : Topos) :
    R.toposEq (R.encode (R.evaluate p)) p := by
  calc
    R.toposWitness (R.encode (R.evaluate p))
        = R.turingWitness (R.evaluate p) := R.encode_coherent _
    _ = R.toposWitness p := R.evaluate_coherent _

/--
A two-sided choice is admitted by evidence of cross-language closure, not by a
preinstalled assertion that one side is the globally natural presentation.
-/
structure TranslatedChoice where
  turing : Turing
  topos : Topos
  closes : R.crossEq turing topos

/-- A choice generated internally from the Turing presentation. -/
def internalChoice (t : Turing) : R.TranslatedChoice where
  turing := t
  topos := R.encode t
  closes := (R.encode_coherent t).symm

/-- A choice generated externally from the Topos presentation. -/
def externalChoice (p : Topos) : R.TranslatedChoice where
  turing := R.evaluate p
  topos := p
  closes := R.evaluate_coherent p

end RelativeToposTuring

namespace RelativeGluing

/-- The finite interval `[0,2]`. -/
inductive LeftPoint
  | p0
  | p1
  | p2
  deriving DecidableEq

/-- The finite interval `[1,3]`. -/
inductive RightPoint
  | p1
  | p2
  | p3
  deriving DecidableEq

/-- The overlap `[1,2]`. -/
inductive OverlapPoint
  | p1
  | p2
  deriving DecidableEq

/-- Include an overlap point into the left interval. -/
def leftOfOverlap : OverlapPoint → LeftPoint
  | .p1 => .p1
  | .p2 => .p2

/-- Include an overlap point into the right interval. -/
def rightOfOverlap : OverlapPoint → RightPoint
  | .p1 => .p1
  | .p2 => .p2

/-- Ordinary gluing: native values agree on the overlap. -/
def Glues {A : Type u}
    (f : LeftPoint → A) (g : RightPoint → A) : Prop :=
  ∀ o, f (leftOfOverlap o) = g (rightOfOverlap o)

/-- A selected translation of two local value languages into one witness language. -/
structure Comparison (A : Type u) (B : Type v) (W : Type w) where
  left : A → W
  right : B → W

/-- Relative gluing: translated values agree on the overlap. -/
def RelativelyGlues {A : Type u} {B : Type v} {W : Type w}
    (C : Comparison A B W)
    (f : LeftPoint → A) (g : RightPoint → B) : Prop :=
  ∀ o,
    C.left (f (leftOfOverlap o)) =
    C.right (g (rightOfOverlap o))

/-- A translation choice has a concrete obstruction when some overlap point disagrees. -/
def ChoiceObstruction {A : Type u} {B : Type v} {W : Type w}
    (C : Comparison A B W)
    (f : LeftPoint → A) (g : RightPoint → B) : Prop :=
  ∃ o,
    C.left (f (leftOfOverlap o)) ≠
    C.right (g (rightOfOverlap o))

/-- Relative gluing excludes a translation obstruction. -/
theorem no_obstruction_of_relativelyGlues
    {A : Type u} {B : Type v} {W : Type w}
    {C : Comparison A B W}
    {f : LeftPoint → A} {g : RightPoint → B}
    (h : RelativelyGlues C f g) :
    ¬ ChoiceObstruction C f g := by
  intro hobstruction
  obtain ⟨o, ho⟩ := hobstruction
  exact ho (h o)

/-- `x ↦ x` on `[0,2]`. -/
def leftLine : LeftPoint → Nat
  | .p0 => 0
  | .p1 => 1
  | .p2 => 2

/-- `x ↦ x` on `[1,3]`. -/
def rightLine : RightPoint → Nat
  | .p1 => 1
  | .p2 => 2
  | .p3 => 3

/-- `x ↦ x+1` on `[1,3]`. -/
def shiftedRight : RightPoint → Nat
  | .p1 => 2
  | .p2 => 3
  | .p3 => 4

/-- The two identity lines glue in their native value language. -/
theorem line_pair_glues : Glues leftLine rightLine := by
  intro o
  cases o <;> rfl

/-- The shifted right line does not glue natively to the left line. -/
theorem shifted_pair_does_not_glue : ¬ Glues leftLine shiftedRight := by
  intro h
  have impossible : (1 : Nat) = 2 := h .p1
  cases impossible

/-- Translate the shifted language back by one on the concrete image. -/
def shiftBack : Nat → Nat
  | 2 => 1
  | 3 => 2
  | 4 => 3
  | n => n

/-- Translation that makes the natively unglued pair relatively agree. -/
def shiftedComparison : Comparison Nat Nat Nat where
  left := id
  right := shiftBack

/-- A natively unglued pair can glue relative to a selected translation. -/
theorem shifted_pair_relatively_glues :
    RelativelyGlues shiftedComparison leftLine shiftedRight := by
  intro o
  cases o <;> rfl

/-- A comparison that reverses the overlap labels `1` and `2` on the right. -/
def flipOneTwo : Nat → Nat
  | 1 => 2
  | 2 => 1
  | n => n

/-- Translation that obstructs the natively glued pair. -/
def obstructingComparison : Comparison Nat Nat Nat where
  left := id
  right := flipOneTwo

/-- A natively glued pair can have a relative obstruction under another translation. -/
theorem line_pair_has_relative_obstruction :
    ChoiceObstruction obstructingComparison leftLine rightLine := by
  refine ⟨.p1, ?_⟩
  intro impossible
  cases impossible

/-- Therefore that selected translation does not relatively glue the native pair. -/
theorem line_pair_not_relatively_glues :
    ¬ RelativelyGlues obstructingComparison leftLine rightLine := by
  intro h
  exact no_obstruction_of_relativelyGlues h
    line_pair_has_relative_obstruction

end RelativeGluing

end Slearn

#print axioms Slearn.InteractiveOpenFoundation.no_finite_stage_decides
#print axioms Slearn.InteractiveOpenFoundation.interactive_open_foundation_receipt
#print axioms Slearn.InteractiveOpenFoundation.limit_prefix_return
#print axioms Slearn.RelativeToposTuring.turing_return
#print axioms Slearn.RelativeToposTuring.topos_return
#print axioms Slearn.RelativeGluing.shifted_pair_relatively_glues
#print axioms Slearn.RelativeGluing.line_pair_has_relative_obstruction
