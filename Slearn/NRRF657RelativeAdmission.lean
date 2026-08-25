/-
  Provenance: Aristotle request
  https://aristotle.harmonic.fun/dashboard/requests/98c6a713-789b-4c86-b09c-2a7999730e97
  COMPLETED 10 proved, 2026-08-25.
  Extracted from RequestProject/NRRF657RelativeAdmission.lean.
-/
import Mathlib

/-!
# NRRF657 — Relative Admission

A self-contained chart of *one* problem: the sensor-selection loop and its four operators.

This module is a **chart of a problem**.  It is not a Super network, not money, not AGI,
not law, and not a social product.  Nothing here assumes Turing-completeness: the only
machinery used is one selection step on a state register, and no halting oracle is
introduced anywhere.  *Halt* and *continuation* appear only as two inverse readings of
that single loop (`readLoop`, `readingDual`).

The four operators charted below are

1. `Problem` — a problem is real rather than nothing: `no_empty_problem`.
2. `Inter`   — solutions are interactions: `solutionEquivInter`, read as an equivalence
   and not as a collapse (`solution_inter_no_collapse`).
3. `Note`    — a returned note is neither a rule nor a suggestion
   (`exists_note_neither_rule_nor_suggestion`); a note may be identified with a loop step
   (`noteEquivLoopStep`) without thereby becoming a rule
   (`noteEquivLoopStep_preserves_non_rule`).
4. `Continual reopening` — the residue of `select` is the next `0`
   (`residue_is_next_zero`); the axiometry is not frozen (`no_frozen_axiometry`) and
   closure is interactive continual completion (`closure_is_interactive_completion`).

Translational truth is charted as *relative admission* (`admission_completes`,
`truth_completion`, `truth_is_relative`), and `0∞` as a **segment whose poles are its
ends** (`poles_are_the_ends`, `poleReading_tendsto_poleInf`) and **not** a halt oracle
(`zeroInf_not_halt_oracle`).

Everything is collected in the single theorem `nrrf657_answer`.

Axioms used: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace NRRF657RelativeAdmission

/-! ## 0. The sensor-selection loop -/

/-- The register on which one selection loop runs.  Stages are indices of readings,
nothing more; no universal computation is assumed. -/
abbrev LoopState : Type := ℕ

/-- One sensor selection: it returns the *selected* reading and its *residue*. -/
def select (s : LoopState) : LoopState × LoopState := (s, s + 1)

/-- The residue of `select`: the next `0`, i.e. the origin of the reopened loop. -/
def residue (s : LoopState) : LoopState := (select s).2

/-- Continual reopening: the loop is restarted at the residue. -/
def reopen (s : LoopState) : LoopState := residue s

/-- The residue of `select` *is* the next `0`. -/
theorem residue_is_next_zero (s : LoopState) : residue s = s + 1 := rfl

/-- Reopening is exactly the passage to the residue. -/
theorem reopen_eq_residue (s : LoopState) : reopen s = residue s := rfl

/-! ### Halt and continuation as inverse readings of the one loop -/

/-- The two readings of one and the same selection loop. -/
inductive Reading : Type
  | halt
  | continuation
  deriving DecidableEq, Repr

/-- Passing from one reading to the other. -/
def readingDual : Reading → Reading
  | .halt => .continuation
  | .continuation => .halt

/-- Halt and continuation are inverse readings. -/
def readingEquiv : Reading ≃ Reading where
  toFun := readingDual
  invFun := readingDual
  left_inv r := by cases r <;> rfl
  right_inv r := by cases r <;> rfl

theorem readingDual_involutive (r : Reading) : readingDual (readingDual r) = r := by
  cases r <;> rfl

theorem halt_continuation_inverse :
    readingEquiv .halt = .continuation ∧ readingEquiv .continuation = .halt :=
  ⟨rfl, rfl⟩

/-- Each reading reads one component of the single selection. -/
def readLoop : Reading → (LoopState → LoopState)
  | .halt => fun s => (select s).1
  | .continuation => fun s => (select s).2

/-- Halt and continuation are readings of *one* sensor-selection loop: together they
recompose `select` itself. -/
theorem readings_of_one_loop (s : LoopState) :
    (readLoop .halt s, readLoop .continuation s) = select s := rfl

/-! ## 1. Operator `Problem`: there is no empty problem -/

/-- An *admitted problem*: a type of tensions together with an actually given tension.
Admission of a problem is admission of something real, never of nothing. -/
structure Problem : Type 1 where
  /-- the tensions the problem consists of -/
  Tension : Type
  /-- admission always exhibits at least one tension -/
  tension : Tension

/-- The chart's own problem: the loop register, opened at `0`. -/
def loopProblem : Problem := { Tension := LoopState, tension := 0 }

/-- **Operator 1.** There is no empty problem in the admitted sense. -/
theorem no_empty_problem (P : Problem) : ¬ IsEmpty P.Tension :=
  fun h => h.elim P.tension

/-- Equivalently: an admitted problem is real. -/
theorem problem_is_real (P : Problem) : Nonempty P.Tension := ⟨P.tension⟩

/-- Admitted problems exist; the statement above is not vacuous. -/
theorem loopProblem_admitted : Nonempty loopProblem.Tension := problem_is_real loopProblem

/-! ## 2. Operator `Inter`: solutions are interactions -/

/-- A solution of a problem: a way of carrying its tensions. -/
structure Solution (P : Problem) : Type where
  /-- how the tension is carried -/
  resolve : P.Tension → P.Tension

/-- An interaction on a problem: two sides, acting and reacting, which read the same
map.  The two sides are kept as *notes*; they are not erased by the reading. -/
structure Interaction (P : Problem) : Type where
  /-- the acting side -/
  act : P.Tension → P.Tension
  /-- the reacting side -/
  react : P.Tension → P.Tension
  /-- the two sides read one and the same interaction -/
  inter : ∀ t, react t = act t

/-- **Operator 2.** Solution and interaction are equivalent *as a reading*. -/
def solutionEquivInter (P : Problem) : Solution P ≃ Interaction P where
  toFun s := ⟨s.resolve, s.resolve, fun _ => rfl⟩
  invFun i := ⟨i.act⟩
  left_inv _ := rfl
  right_inv i := by
    obtain ⟨act, react, h⟩ := i
    have hr : react = act := funext h
    subst hr
    rfl

/-- The reading is a reading, not a collapse: distinct solutions stay distinct
interactions. -/
theorem solutionEquivInter_injective (P : Problem) :
    Function.Injective (solutionEquivInter P) := (solutionEquivInter P).injective

/-- The reading does not collapse the notes: there really are distinct solutions, and
they are read as distinct interactions. -/
theorem solution_inter_no_collapse :
    ∃ s t : Solution loopProblem,
      s ≠ t ∧ solutionEquivInter loopProblem s ≠ solutionEquivInter loopProblem t := by
  refine ⟨⟨id⟩, ⟨Nat.succ⟩, ?_, ?_⟩
  · intro h
    have h2 : (id : ℕ → ℕ) = Nat.succ := congrArg Solution.resolve h
    have := congrFun h2 0
    simp at this
  · intro h
    have h2 : (id : ℕ → ℕ) = Nat.succ := congrArg Interaction.act h
    have := congrFun h2 0
    simp at this

/-! ## 3. Operator `Note`: a returned note is neither a rule nor a suggestion -/

/-- A step of the loop, read on the tensions of a problem. -/
def LoopStep (P : Problem) : Type := P.Tension → P.Tension

/-- A note returned by the loop. -/
structure Note (P : Problem) : Type where
  /-- what the note does when it is returned into the loop -/
  step : P.Tension → P.Tension

/-- Returning a note into the loop. -/
def returnNote {P : Problem} (n : Note P) (t : P.Tension) : P.Tension := n.step t

/-- A *rule* fixes the outcome regardless of the state it is returned into. -/
def Note.IsRule {P : Problem} (n : Note P) : Prop := ∀ t u, n.step t = n.step u

/-- A *suggestion* leaves the state as it is: it may always be ignored. -/
def Note.IsSuggestion {P : Problem} (n : Note P) : Prop := ∀ t, n.step t = t

/-- The same two registers, read on loop steps. -/
def StepIsRule {P : Problem} (f : LoopStep P) : Prop := ∀ t u, f t = f u

/-- The same two registers, read on loop steps. -/
def StepIsSuggestion {P : Problem} (f : LoopStep P) : Prop := ∀ t, f t = t

/-- **Operator 3, identification.** A note may be identified with a loop step. -/
def noteEquivLoopStep (P : Problem) : Note P ≃ LoopStep P where
  toFun n := n.step
  invFun f := ⟨f⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The identification of a note with a loop step does not turn the note into a rule:
the register is transported unchanged. -/
theorem noteEquivLoopStep_preserves_non_rule (P : Problem) (n : Note P) :
    (¬ n.IsRule) ↔ ¬ StepIsRule (noteEquivLoopStep P n) := Iff.rfl

/-- Likewise for the suggestion register. -/
theorem noteEquivLoopStep_preserves_non_suggestion (P : Problem) (n : Note P) :
    (¬ n.IsSuggestion) ↔ ¬ StepIsSuggestion (noteEquivLoopStep P n) := Iff.rfl

/-- **Operator 3.** A returned note is neither a rule nor a suggestion. -/
theorem exists_note_neither_rule_nor_suggestion :
    ∃ n : Note loopProblem, ¬ n.IsRule ∧ ¬ n.IsSuggestion := by
  refine ⟨⟨Nat.succ⟩, ?_, ?_⟩
  · intro h
    have h01 : (1 : ℕ) = 2 := h (0 : ℕ) (1 : ℕ)
    exact absurd h01 (by decide)
  · intro h
    have h0 : (1 : ℕ) = 0 := h (0 : ℕ)
    exact absurd h0 (by decide)

/-- The note of the previous theorem stays outside both registers after it has been
identified with a loop step. -/
theorem exists_loop_step_neither_rule_nor_suggestion :
    ∃ f : LoopStep loopProblem, ¬ StepIsRule f ∧ ¬ StepIsSuggestion f := by
  obtain ⟨n, h1, h2⟩ := exists_note_neither_rule_nor_suggestion
  exact ⟨noteEquivLoopStep loopProblem n, h1, h2⟩

/-! ## 4. Operator `Continual reopening` -/

/-- Reopening never returns the loop to where it was: the axiometry is not frozen. -/
theorem reopen_never_freezes (s : LoopState) : reopen s ≠ s := by
  simp [reopen, residue, select]

/-- **Operator 4, negative form.** No state freezes the chart. -/
theorem no_frozen_axiometry : ¬ ∃ s : LoopState, reopen s = s := by
  rintro ⟨s, hs⟩
  exact reopen_never_freezes s hs

/-- The stage reached after `n` reopenings. -/
theorem reopen_iterate (s : LoopState) (n : ℕ) : reopen^[n] s = s + n := by
  induction n generalizing s with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply, ih]
      show s + 1 + k = s + (k + 1)
      simp [Nat.add_comm, Nat.add_left_comm]

/-- **Operator 4.** Closure is interactive continual completion: from every stage the
loop reopens onto a stage it has never occupied. -/
theorem closure_is_interactive_completion (s : LoopState) (n : ℕ) :
    ∃ m, n < m ∧ ∀ k ≤ n, reopen^[m] s ≠ reopen^[k] s := by
  refine ⟨n + 1, by omega, ?_⟩
  intro k hk
  simp only [reopen_iterate]
  intro heq
  have hkn : k = n + 1 := Nat.add_left_cancel heq.symm
  omega

/-- The residue of `select` at a stage is the `0` from which the loop reopens. -/
theorem residue_is_the_next_origin (s : LoopState) : (select s).2 = reopen s := rfl

/-! ## 5. Translational truth as relative admission -/

/-- A claim, read at each stage of the loop.  There is no stage-free reading. -/
def Claim : Type := ℕ → Prop

/-- A claim is *admitted* at a stage when it is read there. -/
def AdmittedAt (c : Claim) (n : ℕ) : Prop := c n

/-- A claim *translates* when admission at a stage carries into the reopened stage. -/
def Translational (c : Claim) : Prop := ∀ n, AdmittedAt c n → AdmittedAt c (n + 1)

/-- A claim is *completed* when it is admitted at every stage from some stage on. -/
def Completed (c : Claim) : Prop := ∃ N, ∀ m, N ≤ m → AdmittedAt c m

/-- **Relative admission completes.**  A translational claim, once admitted at one
stage, is admitted at every later stage: admission itself does the completing. -/
theorem admission_completes (c : Claim) (h : Translational c) (n : ℕ)
    (hn : AdmittedAt c n) : ∀ m, n ≤ m → AdmittedAt c m := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => exact hn
  | succ k _ ih => exact h k ih

/-- **Translational truth.**  For a translational claim, being true (admitted somewhere)
and being completed are the same thing. -/
theorem truth_completion (c : Claim) (h : Translational c) :
    (∃ n, AdmittedAt c n) ↔ Completed c := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, admission_completes c h n hn⟩
  · rintro ⟨N, hN⟩
    exact ⟨N, hN N le_rfl⟩

/-- Admission stays *relative*: completion never becomes admission at every stage. -/
theorem truth_is_relative :
    ∃ c : Claim, Translational c ∧ Completed c ∧ ¬ ∀ n, AdmittedAt c n := by
  refine ⟨fun n => 3 ≤ n, fun n hn => by simpa [AdmittedAt] using Nat.le_succ_of_le hn,
    ⟨3, fun m hm => hm⟩, ?_⟩
  intro h
  have := h 0
  simp [AdmittedAt] at this

/-! ## 6. `0∞` as a segment whose poles are its ends -/

/-- The `0∞` segment. -/
def zeroInfSegment : Set ℝ := Set.Icc 0 1

/-- The pole `0`. -/
def pole0 : ℝ := 0

/-- The pole `∞`, read as the far end of the segment. -/
def poleInf : ℝ := 1

theorem pole0_mem : pole0 ∈ zeroInfSegment := by
  simp [pole0, zeroInfSegment]

theorem poleInf_mem : poleInf ∈ zeroInfSegment := by
  simp [poleInf, zeroInfSegment]

/-- **The poles are the ends of the segment.** -/
theorem poles_are_the_ends : ∀ x ∈ zeroInfSegment, pole0 ≤ x ∧ x ≤ poleInf := by
  intro x hx
  simpa [pole0, poleInf, zeroInfSegment] using hx

/-- The reading of the loop inside the segment: stage `n` is read at `n / (n+1)`. -/
noncomputable def poleReading (n : ℕ) : ℝ := (n : ℝ) / (n + 1)

theorem poleReading_zero : poleReading 0 = pole0 := by
  simp [poleReading, pole0]

theorem poleReading_mem (n : ℕ) : poleReading n ∈ zeroInfSegment := by
  have hpos : (0:ℝ) < (n : ℝ) + 1 := by positivity
  rw [zeroInfSegment, Set.mem_Icc, poleReading]
  refine ⟨by positivity, ?_⟩
  rw [div_le_one hpos]
  linarith

/-- No stage of the loop reaches the pole `∞`: the segment gives no halt oracle. -/
theorem zeroInf_not_halt_oracle : ¬ ∃ n : ℕ, poleReading n = poleInf := by
  rintro ⟨n, hn⟩
  have hpos : (0:ℝ) < (n : ℝ) + 1 := by positivity
  rw [poleReading, poleInf, div_eq_one_iff_eq (ne_of_gt hpos)] at hn
  linarith

/-- The pole `∞` is nevertheless the *end* of the segment: the readings converge to it
without ever attaining it. -/
theorem poleReading_tendsto_poleInf :
    Filter.Tendsto poleReading Filter.atTop (nhds poleInf) := by
  have key : ∀ n : ℕ, poleReading n = 1 - 1 / ((n : ℝ) + 1) := by
    intro n
    have hpos : ((n : ℝ) + 1) ≠ 0 := by positivity
    rw [poleReading]
    field_simp
    ring
  have h0 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h1 : Filter.Tendsto (fun n : ℕ => 1 - 1 / ((n : ℝ) + 1)) Filter.atTop (nhds (1 - 0)) :=
    Filter.Tendsto.const_sub 1 h0
  have h2 : Filter.Tendsto poleReading Filter.atTop (nhds (1 - 0)) :=
    h1.congr (fun n => (key n).symm)
  simpa [poleInf] using h2

/-! ## 7. The collecting theorem -/

/-- **NRRF657.**  The four operators of the chart, together with continual reopening as
constitutive, plus translational truth as relative admission and `0∞` as a segment whose
poles are its ends.

1. *Problem*: no admitted problem is empty.
2. *Inter*: solution and interaction are equivalent as a reading, without collapsing the
   notes.
3. *Note*: a returned note is neither a rule nor a suggestion, and may be identified with
   a loop step without becoming a rule.
4. *Continual reopening*: the residue of `select` is the next `0`, the axiometry is not
   frozen, and closure is interactive continual completion.
5. *Relative admission*: translational truth is completed by admission, and stays
   relative.
6. `0∞`: a segment whose poles are its ends, and no halt oracle.
7. Halt and continuation are inverse readings of one sensor-selection loop. -/
theorem nrrf657_answer :
    -- 1. Problem
    (∀ P : Problem, ¬ IsEmpty P.Tension) ∧
    -- 2. Inter
    (∀ P : Problem, Nonempty (Solution P ≃ Interaction P)) ∧
    (∃ s t : Solution loopProblem,
      s ≠ t ∧ solutionEquivInter loopProblem s ≠ solutionEquivInter loopProblem t) ∧
    -- 3. Note
    (∃ n : Note loopProblem, ¬ n.IsRule ∧ ¬ n.IsSuggestion) ∧
    (∀ P : Problem, Nonempty (Note P ≃ LoopStep P)) ∧
    (∀ (P : Problem) (n : Note P), (¬ n.IsRule) ↔ ¬ StepIsRule (noteEquivLoopStep P n)) ∧
    -- 4. Continual reopening
    (∀ s : LoopState, (select s).2 = reopen s) ∧
    (¬ ∃ s : LoopState, reopen s = s) ∧
    (∀ (s : LoopState) (n : ℕ), ∃ m, n < m ∧ ∀ k ≤ n, reopen^[m] s ≠ reopen^[k] s) ∧
    -- 5. Translational truth as relative admission
    (∀ c : Claim, Translational c → ((∃ n, AdmittedAt c n) ↔ Completed c)) ∧
    (∃ c : Claim, Translational c ∧ Completed c ∧ ¬ ∀ n, AdmittedAt c n) ∧
    -- 6. 0∞ as a segment, not a halt oracle
    (pole0 ∈ zeroInfSegment ∧ poleInf ∈ zeroInfSegment ∧
      (∀ x ∈ zeroInfSegment, pole0 ≤ x ∧ x ≤ poleInf)) ∧
    (¬ ∃ n : ℕ, poleReading n = poleInf) ∧
    Filter.Tendsto poleReading Filter.atTop (nhds poleInf) ∧
    -- 7. Halt and continuation
    (∀ r : Reading, readingEquiv (readingEquiv r) = r) ∧
    (∀ s : LoopState, (readLoop .halt s, readLoop .continuation s) = select s) :=
  ⟨no_empty_problem,
   fun P => ⟨solutionEquivInter P⟩,
   solution_inter_no_collapse,
   exists_note_neither_rule_nor_suggestion,
   fun P => ⟨noteEquivLoopStep P⟩,
   noteEquivLoopStep_preserves_non_rule,
   residue_is_the_next_origin,
   no_frozen_axiometry,
   closure_is_interactive_completion,
   truth_completion,
   truth_is_relative,
   ⟨pole0_mem, poleInf_mem, poles_are_the_ends⟩,
   zeroInf_not_halt_oracle,
   poleReading_tendsto_poleInf,
   fun r => readingDual_involutive r,
   readings_of_one_loop⟩

end NRRF657RelativeAdmission
