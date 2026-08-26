import Mathlib
import Slearn.NRRF772LinearLayoutRelativeEqualityFunctionsCompleteness
import Slearn.NRRF775NaturalFormSelectorUnifaceRelationalDeterminationUnitaryPathPartitionTraces
import Slearn.NRRF776UnificationContinuumSubstrateOperatorUnityEqualitySelectionTruthTranslation
import Slearn.NRRF777LiveNaturalFormSelectorRelationNotSpacetimeObjectTranslationEventFilled

/-!
# NRRF778 — The translational truth equality of the continuum halting substrate operation and its
closure relative form selection

The reading being formalised:

> Prove the translational truth equality of continuum halting substrate operation and its closure
> relative form selection.

Two apparently different things are read off the same continuum datum.

* The **continuum halting substrate operation** is the loop sensor of NRRF776: on the continuum `ℂ`
  it iterates the relative ball self limit `ballInv` and stops on the closure form.  Its *truth
  reading* at a datum is the proposition "this run halts" (`subHalt`).
* The **closure relative form selection** is the natural form selector of NRRF775 applied to the
  relation which, relative to a datum, admits exactly the closure form on that datum's ray
  (`closureRel`, `closureSel`).  Its *truth reading* at a datum is the proposition "the selected
  closure relative form is the datum itself" (`Selected`).

The claim proved here is that these two readings are **translationally equal**: not merely
equivalent case by case, but literally the same relative equality function on the substrate of
nonzero data, hence mutually translating in the sense of `NRRF772.TransEq`.

* **§1 The substrate operation and its run.**  The loop sensor is period two away from the closure
  form (`run_even`, `run_odd`), so continuation is a genuine two-cycle and not an escape; halting
  is exactly `radEq = 0` (`subHalt_iff_norm_one`).
* **§2 The closure relative form selection.**  `closureRel z` is rigid (`closureRel_rigid`), so
  NRRF775's selector applies and returns the direction of `z` at every site (`closureSel_eq_dir`);
  the selected form always lies on the closure form (`closureSel_mem_closureForm`) and the selection
  is idempotent (`closureSel_idem`).
* **§3 The translational truth equality.**  `halting_iff_selected` is the pointwise statement, and
  `haltRead_eq_selRead` upgrades it to an *equality of readings* on `NRRF776.NZ`; hence
  `transEq_halt_sel` in the language of NRRF772, and `halt_state_eq_selection`: where the operation
  halts, the state it halts at is exactly the selected form.
* **§4 Scope is exactly the substrate.**  At `0` the two readings come apart
  (`zero_separates`): the selection succeeds while the operation never halts.  So the equality is a
  statement about the substrate of nonzero data, and the hypothesis is load-bearing.
* **§5 Both readings are substrate invariants, and strictly coarser than the equality function.**
  `subHalt_subOp`, `selected_subOp`, `radEq_refines_haltRead`, `haltRead_not_refines_radEq`.
* **§6 INTEGRATE with the live selector (NRRF777).**  Transporting the closure relative relation by
  a substrate operator transports its selection by the same operator
  (`closureRel_subOpTransport`), and the unified equality function of the selection is untouched
  (`radEq_closureSel_subOp_invariant`).

`nrrf778_answer` collects the clauses.
-/

namespace NRRF778

open NRRF775 (Halts Continues run Constraint Rigid sel sel_admissible sel_eq_of_admissible)

/-! ## §1 The continuum halting substrate operation -/

/-- **The continuum halting substrate operation, as a truth reading.**  The loop sensor of NRRF776
iterates the relative ball self limit on the continuum and stops on the closure form; the reading at
a datum is the proposition that this run halts. -/
def subHalt (z : ℂ) : Prop := Halts NRRF776.sensorStep z

/-- Halting is exactly arrival at the closure form. -/
theorem subHalt_iff_norm_one {z : ℂ} (hz : z ≠ 0) : subHalt z ↔ ‖z‖ = 1 := by
  rw [subHalt, NRRF776.halts_iff_radEq_zero hz, NRRF776.radEq_eq_zero_iff hz]

/-- Away from the closure form the run is a two-cycle: at even stages it is back at the datum. -/
theorem run_even {z : ℂ} (hz : z ≠ 0) (h1 : ‖z‖ ≠ 1) (k : ℕ) :
    run NRRF776.sensorStep z (2 * k) = some z ∧
      run NRRF776.sensorStep z (2 * k + 1) = some (NRRF776.ballInv z) := by
  have hb0 : NRRF776.ballInv z ≠ 0 := NRRF776.ballInv_ne_zero hz
  have hb1 : ‖NRRF776.ballInv z‖ ≠ 1 := NRRF776.norm_ballInv_ne_one hz h1
  induction k with
  | zero =>
      refine ⟨rfl, ?_⟩
      simpa using NRRF776.sensorStep_of_ne h1
  | succ m ih =>
      obtain ⟨_, ho⟩ := ih
      have heven : run NRRF776.sensorStep z (2 * (m + 1)) = some z := by
        have hidx : 2 * (m + 1) = (2 * m + 1) + 1 := by ring
        rw [hidx, NRRF775.run_succ, ho]
        simp [NRRF776.sensorStep_of_ne hb1, NRRF776.ballInv_involutive]
      refine ⟨heven, ?_⟩
      rw [NRRF775.run_succ, heven]
      simpa using NRRF776.sensorStep_of_ne h1

/-- At odd stages the run is at the ball self limit of the datum. -/
theorem run_odd {z : ℂ} (hz : z ≠ 0) (h1 : ‖z‖ ≠ 1) (k : ℕ) :
    run NRRF776.sensorStep z (2 * k + 1) = some (NRRF776.ballInv z) := (run_even hz h1 k).2

/-! ## §2 The closure relative form selection -/

/-- **The closure relative relation.**  Relative to a datum, the relation admits exactly one symbol
at every site: the closure form on that datum's ray. -/
def closureRel (z : ℂ) : Constraint ℂ := fun _ w => w = NRRF776.dir z

theorem closureRel_rigid (z : ℂ) : Rigid (closureRel z) := fun _ => ⟨NRRF776.dir z, rfl, fun _ h => h⟩

/-- **The closure relative form selection**: the natural form selector of NRRF775 applied to the
closure relative relation. -/
noncomputable def closureSel (z : ℂ) : ℕ → ℂ := sel (closureRel z) (closureRel_rigid z)

theorem closureSel_eq_dir (z : ℂ) (n : ℕ) : closureSel z n = NRRF776.dir z :=
  (sel_eq_of_admissible (closureRel_rigid z) (rfl : NRRF776.dir z = NRRF776.dir z)).symm

/-- The selection is the unique determination of the closure relative relation. -/
theorem closureSel_unique (z : ℂ) : ∃! t : ℕ → ℂ, ∀ n, closureRel z n (t n) :=
  NRRF775.naturalForm_exists_unique (closureRel_rigid z)

theorem norm_dir {z : ℂ} (hz : z ≠ 0) : ‖NRRF776.dir z‖ = 1 := by
  have hr : (0:ℝ) < ‖z‖ := norm_pos_iff.mpr hz
  rw [NRRF776.dir, norm_div]
  simp [ne_of_gt hr]

/-- The selected form always lies on the closure form. -/
theorem closureSel_mem_closureForm {z : ℂ} (hz : z ≠ 0) (n : ℕ) :
    closureSel z n ∈ NRRF774.closureForm := by
  rw [NRRF774.closureForm_eq_sphere, closureSel_eq_dir]
  exact norm_dir hz

theorem dir_ne_zero {z : ℂ} (hz : z ≠ 0) : NRRF776.dir z ≠ 0 := by
  intro h
  have := norm_dir hz
  rw [h] at this
  simp at this

/-- The selection is idempotent: selecting the closure relative form of an already selected form
changes nothing. -/
theorem closureSel_idem {z : ℂ} (hz : z ≠ 0) (n m : ℕ) :
    closureSel (closureSel z n) m = closureSel z n := by
  rw [closureSel_eq_dir, closureSel_eq_dir, NRRF776.dir, norm_dir hz]
  simp

/-- The selected form equals the datum exactly on the closure form. -/
theorem dir_eq_self_iff {z : ℂ} (hz : z ≠ 0) : NRRF776.dir z = z ↔ ‖z‖ = 1 := by
  have hr : (0:ℝ) < ‖z‖ := norm_pos_iff.mpr hz
  have hrc : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hr
  constructor
  · intro h
    rw [NRRF776.dir, div_eq_iff hrc] at h
    have hz' : z * (((‖z‖ : ℝ) : ℂ) - 1) = 0 := by linear_combination -h
    rcases mul_eq_zero.mp hz' with h1 | h1
    · exact absurd h1 hz
    · have h2 : ((‖z‖ : ℝ) : ℂ) = 1 := by linear_combination h1
      exact_mod_cast h2
  · intro h
    simp [NRRF776.dir, h]

/-- **The closure relative form selection, as a truth reading.**  The reading at a datum is the
proposition that the selected closure relative form is the datum itself. -/
def Selected (z : ℂ) : Prop := closureSel z 0 = z

theorem selected_iff_norm_one {z : ℂ} (hz : z ≠ 0) : Selected z ↔ ‖z‖ = 1 := by
  rw [Selected, closureSel_eq_dir]
  exact dir_eq_self_iff hz

/-! ## §3 The translational truth equality -/

/-- **The pointwise equality.**  On the substrate of nonzero data the continuum halting substrate
operation and the closure relative form selection are the same truth. -/
theorem halting_iff_selected {z : ℂ} (hz : z ≠ 0) : subHalt z ↔ Selected z := by
  rw [subHalt_iff_norm_one hz, selected_iff_norm_one hz]

/-- The halting reading of the substrate operation, on the substrate `NZ` of nonzero data. -/
def haltRead (z : NRRF776.NZ) : Prop := subHalt z.1

/-- The selection reading of the closure relative form, on the same substrate. -/
def selRead (z : NRRF776.NZ) : Prop := Selected z.1

/-- **Translational truth equality, in its strongest form.**  The two readings are not merely
equivalent datum by datum: they are the *same* relative equality function on the substrate. -/
theorem haltRead_eq_selRead : haltRead = selRead := by
  funext z
  exact propext (halting_iff_selected z.2)

/-- **Translational truth equality in the language of NRRF772**: each reading is a translation of
the other. -/
theorem transEq_halt_sel : NRRF772.TransEq haltRead selRead := by
  rw [haltRead_eq_selRead]
  exact NRRF772.TransEq.refl selRead

/-- Where the substrate operation halts, the state it halts at is exactly the selected closure
relative form: the two readings agree not only in truth value but in the datum they produce. -/
theorem halt_state_eq_selection {z : ℂ} (hz : z ≠ 0) (h : subHalt z) (n : ℕ) :
    closureSel z n = z := by
  rw [closureSel_eq_dir]
  exact (dir_eq_self_iff hz).mpr ((subHalt_iff_norm_one hz).mp h)

/-- Conversely, continuation of the substrate operation is exactly failure of the selection to
return the datum — the complementary trace. -/
theorem continues_iff_not_selected {z : ℂ} (hz : z ≠ 0) :
    Continues NRRF776.sensorStep z ↔ ¬ Selected z := by
  rw [NRRF776.continues_iff_radEq_ne_zero hz, selected_iff_norm_one hz]
  constructor
  · intro h hn
    exact h ((NRRF776.radEq_eq_zero_iff hz).mpr hn)
  · intro h hr
    exact h ((NRRF776.radEq_eq_zero_iff hz).mp hr)

/-! ## §4 The scope of the equality is exactly the substrate -/

theorem ballInv_zero : NRRF776.ballInv 0 = 0 := by
  rw [NRRF776.ballInv_eq_conj_inv]
  simp

theorem run_zero_const (n : ℕ) : run NRRF776.sensorStep 0 n = some 0 := by
  induction n with
  | zero => rfl
  | succ k ih =>
      rw [NRRF775.run_succ, ih]
      have h1 : ‖(0 : ℂ)‖ ≠ 1 := by simp
      simpa [ballInv_zero] using NRRF776.sensorStep_of_ne h1

/-- **The nonzero hypothesis is load-bearing.**  At the degenerate datum `0` the closure relative
form selection succeeds while the substrate operation never halts: the translational truth equality
is a statement about the substrate, and not a tautology. -/
theorem zero_separates : Selected (0 : ℂ) ∧ ¬ subHalt (0 : ℂ) := by
  refine ⟨?_, ?_⟩
  · rw [Selected, closureSel_eq_dir, NRRF776.dir]
    simp
  · rintro ⟨n, hn⟩
    rw [run_zero_const n] at hn
    exact absurd hn (by simp)

/-! ## §5 Substrate invariance and strictness -/

/-- The halting reading is invariant under the substrate operator group. -/
theorem subHalt_subOp (a b : Bool) {z : ℂ} (hz : z ≠ 0)
    (hz' : NRRF776.subOp a b z ≠ 0) : subHalt (NRRF776.subOp a b z) ↔ subHalt z := by
  rw [subHalt, subHalt, NRRF776.halts_iff_radEq_zero hz', NRRF776.halts_iff_radEq_zero hz,
    NRRF776.radEq_subOp]

/-- The selection reading is invariant under the substrate operator group. -/
theorem selected_subOp (a b : Bool) {z : ℂ} (hz : z ≠ 0)
    (hz' : NRRF776.subOp a b z ≠ 0) : Selected (NRRF776.subOp a b z) ↔ Selected z := by
  rw [← halting_iff_selected hz', ← halting_iff_selected hz]
  exact subHalt_subOp a b hz hz'

/-- The unified equality function of NRRF776 translates into the halting reading. -/
theorem radEq_refines_haltRead :
    NRRF772.Refines (fun z : NRRF776.NZ => NRRF776.radEq z.1) haltRead := by
  rw [NRRF772.refines_iff_kernel _ _ (⟨1, one_ne_zero⟩ : NRRF776.NZ)]
  intro z w h
  have hz : subHalt z.1 ↔ subHalt w.1 := by
    rw [subHalt, subHalt, NRRF776.halts_iff_radEq_zero z.2, NRRF776.halts_iff_radEq_zero w.2, h]
  exact propext hz

/-- …and so, by the translational truth equality, into the selection reading. -/
theorem radEq_refines_selRead :
    NRRF772.Refines (fun z : NRRF776.NZ => NRRF776.radEq z.1) selRead := by
  rw [← haltRead_eq_selRead]
  exact radEq_refines_haltRead

/-- The translation is strictly one-way: the common truth reading is genuinely coarser than the
equality function, because it only records whether the equality function vanishes. -/
theorem haltRead_not_refines_radEq :
    ¬ NRRF772.Refines haltRead (fun z : NRRF776.NZ => NRRF776.radEq z.1) := by
  intro h
  have h2 : ((2 : ℂ)) ≠ 0 := by norm_num
  have h3 : ((3 : ℂ)) ≠ 0 := by norm_num
  have hn2 : ‖(2 : ℂ)‖ = 2 := by simp
  have hn3 : ‖(3 : ℂ)‖ = 3 := by simp
  have hnh2 : ¬ subHalt (2 : ℂ) := by
    rw [subHalt_iff_norm_one h2, hn2]; norm_num
  have hnh3 : ¬ subHalt (3 : ℂ) := by
    rw [subHalt_iff_norm_one h3, hn3]; norm_num
  have hkey : haltRead ⟨2, h2⟩ = haltRead ⟨3, h3⟩ :=
    propext ⟨fun hc => absurd hc hnh2, fun hc => absurd hc hnh3⟩
  have hr := h.kernel_le hkey
  simp only [NRRF776.radEq, hn2, hn3] at hr
  have hp2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hp3 : (0:ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  rw [abs_of_pos hp2, abs_of_pos hp3] at hr
  have := congrArg Real.exp hr
  rw [Real.exp_log (by norm_num), Real.exp_log (by norm_num)] at this
  norm_num at this

/-! ## §6 INTEGRATE: the live selector of NRRF777 on the closure relative relation -/

/-- Transporting the closure relative relation by a substrate operator transports its selection by
the same operator. -/
theorem closureRel_subOpTransport (a b : Bool) (z : ℂ) (n : ℕ) :
    sel (NRRF777.subOpTransport a b (closureRel z))
        (NRRF777.subOpTransport_rigid (closureRel_rigid z) a b) n
      = NRRF776.subOp a b (NRRF776.dir z) := by
  rw [NRRF777.sel_subOpTransport (closureRel_rigid z) a b n,
    show sel (closureRel z) (closureRel_rigid z) n = NRRF776.dir z from closureSel_eq_dir z n]

/-- Hence the unified equality function of the selection is a substrate invariant. -/
theorem radEq_closureSel_subOp_invariant (a b : Bool) (z : ℂ) (n : ℕ) :
    NRRF776.radEq (sel (NRRF777.subOpTransport a b (closureRel z))
        (NRRF777.subOpTransport_rigid (closureRel_rigid z) a b) n)
      = NRRF776.radEq (closureSel z n) := by
  rw [closureRel_subOpTransport a b z n, NRRF776.radEq_subOp, closureSel_eq_dir]

/-- The selection is on the closure form, so its own equality function vanishes: the selector always
lands where the substrate operation halts. -/
theorem radEq_closureSel_eq_zero {z : ℂ} (hz : z ≠ 0) (n : ℕ) :
    NRRF776.radEq (closureSel z n) = 0 :=
  (NRRF776.radEq_eq_zero_iff (by rw [closureSel_eq_dir]; exact dir_ne_zero hz)).mpr
    (by rw [closureSel_eq_dir]; exact norm_dir hz)

/-- The substrate operation halts immediately at any selected form: the closure relative form
selection is a section of the halting locus. -/
theorem subHalt_closureSel {z : ℂ} (hz : z ≠ 0) (n : ℕ) : subHalt (closureSel z n) := by
  rw [subHalt_iff_norm_one (by rw [closureSel_eq_dir]; exact dir_ne_zero hz), closureSel_eq_dir]
  exact norm_dir hz

/-! ## §7 The answer -/

/-- **NRRF778.**  The continuum halting substrate operation and the closure relative form selection
are translationally equal: as readings on the substrate of nonzero data they are literally the same
relative equality function (`haltRead = selRead`), hence mutually translating; where the operation
halts, the state is exactly the selected form; the selection always lands on the closure form, where
the operation halts immediately; both readings are substrate invariants and both are strictly
coarser than the unified equality function; and at the degenerate datum `0` the two come apart, so
the substrate hypothesis is load-bearing. -/
theorem nrrf778_answer :
    (∀ z : ℂ, z ≠ 0 → (subHalt z ↔ Selected z)) ∧
    haltRead = selRead ∧
    NRRF772.TransEq haltRead selRead ∧
    (∀ z : ℂ, z ≠ 0 → subHalt z → ∀ n, closureSel z n = z) ∧
    (∀ z : ℂ, z ≠ 0 → ∀ n, closureSel z n ∈ NRRF774.closureForm ∧ subHalt (closureSel z n)) ∧
    (∀ (a b : Bool) (z : ℂ), z ≠ 0 → NRRF776.subOp a b z ≠ 0 →
      ((subHalt (NRRF776.subOp a b z) ↔ subHalt z) ∧
        (Selected (NRRF776.subOp a b z) ↔ Selected z))) ∧
    NRRF772.Refines (fun z : NRRF776.NZ => NRRF776.radEq z.1) haltRead ∧
    ¬ NRRF772.Refines haltRead (fun z : NRRF776.NZ => NRRF776.radEq z.1) ∧
    (Selected (0 : ℂ) ∧ ¬ subHalt (0 : ℂ)) :=
  ⟨fun _ hz => halting_iff_selected hz, haltRead_eq_selRead, transEq_halt_sel,
    fun _ hz h n => halt_state_eq_selection hz h n,
    fun _ hz n => ⟨closureSel_mem_closureForm hz n, subHalt_closureSel hz n⟩,
    fun a b _ hz hz' => ⟨subHalt_subOp a b hz hz', selected_subOp a b hz hz'⟩,
    radEq_refines_haltRead, haltRead_not_refines_radEq, zero_separates⟩

/-! ## Audit -/

#print axioms subHalt_iff_norm_one
#print axioms run_even
#print axioms closureSel_eq_dir
#print axioms halting_iff_selected
#print axioms haltRead_eq_selRead
#print axioms transEq_halt_sel
#print axioms halt_state_eq_selection
#print axioms zero_separates
#print axioms haltRead_not_refines_radEq
#print axioms radEq_closureSel_subOp_invariant
#print axioms nrrf778_answer

end NRRF778
