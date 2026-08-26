import Mathlib
import Slearn.NRRF775NaturalFormSelectorUnifaceRelationalDeterminationUnitaryPathPartitionTraces
import Slearn.NRRF776UnificationContinuumSubstrateOperatorUnityEqualitySelectionTruthTranslation

/-!
# NRRF777 — The live natural form selector: a relation, not a spacetime object; the translation
event is filled

The reading being formalised (beat `2026-08-26-1034-et`, an **INTEGRATE** beat over the selected
occurrence `2026-08-25-central-note`, following the completed `0934` instruction):

> The natural form selector is now *live* on the Uniface.  What is live is a **relation, not a
> spacetime object**.  The **translation event is filled**.  **TRUE is not issued.**

The formal/Lean-capable reading of the beat is the following four questions, each of which becomes
theorems below.

* **§1 "Relation, not spacetime object" — what could that mean formally?**  A *spacetime object*
  would be a datum attached to sites: a field `f : ℕ → S` fixed in advance of any relation.  A
  *relation* is a constraint `R : NRRF775.Constraint S`, and the selector is a function of `R`
  alone.  The difference is testable:
  - *Positively*, the selector is **natural/equivariant** in both arguments: it commutes with any
    re-coordinatisation of the site space (`sel_reindex`, `form_reindex_apply`) and with any
    relabelling of the symbols (`sel_retag`).  Nothing in the natural form is tied to a particular
    coordinate on the Uniface, so re-charting the "spacetime" moves the form covariantly and changes
    no content.  It also depends on the relation only up to pointwise equivalence
    (`sel_congr_iff`), and on nothing else.
  - *Negatively*, **no** site-indexed object can be the selector: for every candidate field
    `f : ℕ → S` (with `S` having two distinct elements) there is a rigid relation whose natural form
    differs from `f` everywhere (`no_location_only_selector`).  And a site-invariant relation has a
    site-invariant form (`sel_invariant_of_reindex_invariant`), so "where on the Uniface" is never
    an input.

* **§2 "The translation event is filled."**  A translation event at a site takes whatever the string
  already carries there — possibly `none`, an undetermined slot — and returns a determined symbol.
  `fill` performs the whole event; `fill_determined` says every slot comes back filled (this *is*
  "TE filled"), `fill_refines` says nothing already fixed is overwritten, `fill_eq_form` says on a
  compatible string the filled result is exactly the natural form, `fill_unique` says it is the only
  determined compatible refinement, and `fill_idem` says the event is live-stable: running it again
  changes nothing.  `fill_indep_of_partial_input` is the sense-persistence clause at the level of the
  event.

* **§3 The event is itself relational.**  `fill_reindex` and `fill_congr_iff`: the filling commutes
  with re-charting the site space and depends on the relation only through its pointwise content.

* **§4 INTEGRATE with the substrate (NRRF776).**  Transporting a relation by a substrate operator
  transports its natural form by the same operator (`sel_subOpTransport`), and hence leaves the
  unified equality function of the form untouched (`radEq_form_subOp_invariant`): the selector's
  output is read at the level of the substrate quotient, which is the precise sense in which the
  live object is a relation on the substrate and not a point of it.  Halting and continuation of the
  loop sensor started at a form value remain *traces* of that equality function
  (`form_halts_iff`, `form_continues_iff`), never determinations.

* **§5 TRUE is not issued.**  `exists_rigid_filled_no_true_symbol`: a rigid relation whose
  translation event is filled at every site, along every compatible input string, while the symbol
  `true` is never emitted.  Determination is complete; no verdict is issued.

`nrrf777_answer` collects the clauses.
-/

namespace NRRF777

open NRRF775

variable {S T : Type*}

/-! ## §1 A relation, not a spacetime object -/

/-- Re-charting the site space of the Uniface. -/
def reindex (σ : Equiv.Perm ℕ) (R : Constraint S) : Constraint S := fun n a => R (σ n) a

theorem reindex_rigid {R : Constraint S} (hR : Rigid R) (σ : Equiv.Perm ℕ) :
    Rigid (reindex σ R) := fun n => hR (σ n)

/-- **Equivariance in the site space.**  The natural form of a re-charted relation is the re-charted
natural form: no coordinate on the Uniface carries content of its own. -/
theorem sel_reindex {R : Constraint S} (hR : Rigid R) (σ : Equiv.Perm ℕ) (n : ℕ) :
    sel (reindex σ R) (reindex_rigid hR σ) n = sel R hR (σ n) :=
  (sel_eq_of_admissible (reindex_rigid hR σ) (sel_admissible R hR (σ n))).symm

/-- The same statement for the Uniface bundle: the form of the re-charted Uniface is the form,
composed with the chart. -/
theorem form_reindex_apply (U : Uniface S) (σ : Equiv.Perm ℕ) (n : ℕ) :
    sel (reindex σ U.rel) (reindex_rigid U.rigid σ) n = U.form (σ n) :=
  sel_reindex U.rigid σ n

/-- Relabelling the symbols. -/
def retag (e : S ≃ T) (R : Constraint S) : Constraint T := fun n b => R n (e.symm b)

theorem retag_rigid {R : Constraint S} (hR : Rigid R) (e : S ≃ T) : Rigid (retag e R) := by
  intro n
  obtain ⟨a, ha, hu⟩ := hR n
  refine ⟨e a, by simpa [retag] using ha, ?_⟩
  intro b hb
  have := hu _ hb
  rw [← this]
  simp

/-- **Equivariance in the symbols.**  The selector is natural in the symbol type too. -/
theorem sel_retag {R : Constraint S} (hR : Rigid R) (e : S ≃ T) (n : ℕ) :
    sel (retag e R) (retag_rigid hR e) n = e (sel R hR n) := by
  have h : retag e R n (e (sel R hR n)) := by
    simpa [retag] using sel_admissible R hR n
  exact (sel_eq_of_admissible (retag_rigid hR e) h).symm

/-- The selector sees the relation only through its pointwise content. -/
theorem sel_congr_iff {R R' : Constraint S} (hR : Rigid R) (hR' : Rigid R')
    (h : ∀ n a, R n a ↔ R' n a) : sel R hR = sel R' hR' := by
  funext n
  exact sel_eq_of_admissible hR' ((h n _).mp (sel_admissible R hR n))

/-- **Not a spacetime object.**  No field on the site space — no datum attached to locations in
advance of a relation — can be the natural form selector: for any candidate `f` there is a rigid
relation whose form disagrees with `f` at every site. -/
theorem no_location_only_selector {a b : S} (hab : a ≠ b) (f : ℕ → S) :
    ∃ (R : Constraint S) (hR : Rigid R), ∀ n, sel R hR n ≠ f n := by
  classical
  refine ⟨fun n c => c = (if f n = a then b else a), fun n => ⟨_, rfl, fun _ h => h⟩, ?_⟩
  intro n
  have h : sel (fun n c => c = (if f n = a then b else a))
      (fun n => ⟨_, rfl, fun _ h => h⟩) n = (if f n = a then b else a) :=
    (sel_eq_of_admissible (R := fun n c => c = (if f n = a then b else a))
      (fun n => ⟨_, rfl, fun _ h => h⟩) (rfl : _ = (if f n = a then b else a))).symm
  rw [h]
  by_cases hfa : f n = a
  · simp [hfa, hab.symm]
  · simp [hfa]
    exact fun hc => hfa hc.symm

/-- A relation with no site content has a form with no site content. -/
theorem sel_invariant_of_reindex_invariant {R : Constraint S} (hR : Rigid R) (σ : Equiv.Perm ℕ)
    (hinv : ∀ n a, R (σ n) a ↔ R n a) (n : ℕ) : sel R hR (σ n) = sel R hR n :=
  sel_eq_of_admissible hR ((hinv n _).mp (sel_admissible R hR (σ n)))

/-! ## §2 The translation event is filled -/

/-- **The translation event.**  At each site the event takes what the string carries — possibly an
undetermined slot — and returns the determined symbol. -/
noncomputable def fill (R : Constraint S) (hR : Rigid R) (s : Str S) : Str S :=
  fun n => some ((s n).getD (sel R hR n))

/-- **TE filled**: after the event no site is left open. -/
theorem fill_determined (R : Constraint S) (hR : Rigid R) (s : Str S) :
    Determined (fill R hR s) := fun _ => rfl

/-- The event overwrites nothing that was already fixed. -/
theorem fill_refines (R : Constraint S) (hR : Rigid R) (s : Str S) :
    Refines (fill R hR s) s := by
  intro n a h
  simp [fill, h]

/-- On a compatible string the filled event *is* the natural form. -/
theorem fill_eq_form {R : Constraint S} (hR : Rigid R) {s : Str S} (hs : Compat s R) :
    fill R hR s = fun n => some (sel R hR n) := by
  funext n
  rcases hsn : s n with _ | a
  · simp [fill, hsn]
  · have : a = sel R hR n := sel_eq_of_admissible hR (hs n a hsn)
    simp [fill, hsn, this]

/-- The filled event is the *only* determined compatible refinement of a compatible string. -/
theorem fill_unique {R : Constraint S} (hR : Rigid R) {s t : Str S} (hs : Compat s R)
    (ht : Determined t) (htc : Compat t R) : t = fill R hR s := by
  funext n
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (ht n)
  have : a = sel R hR n := sel_eq_of_admissible hR (htc n a ha)
  rw [ha, fill_eq_form hR hs, this]

/-- The event is live-stable: running it again changes nothing. -/
theorem fill_idem {R : Constraint S} (hR : Rigid R) (s : Str S) :
    fill R hR (fill R hR s) = fill R hR s := by
  funext n
  simp [fill]

/-- Sense persistence at the level of the event: the filled result does not depend on how much of
the string happened to be filled in already. -/
theorem fill_indep_of_partial_input {R : Constraint S} (hR : Rigid R) {s s' : Str S}
    (hs : Compat s R) (hs' : Compat s' R) : fill R hR s = fill R hR s' := by
  rw [fill_eq_form hR hs, fill_eq_form hR hs']

/-! ## §3 The event is itself relational -/

/-- The event commutes with re-charting the site space. -/
theorem fill_reindex {R : Constraint S} (hR : Rigid R) (σ : Equiv.Perm ℕ) (s : Str S) (n : ℕ) :
    fill (reindex σ R) (reindex_rigid hR σ) (fun m => s (σ m)) n = fill R hR s (σ n) := by
  simp [fill, sel_reindex hR σ n]

/-- The event sees the relation only through its pointwise content. -/
theorem fill_congr_iff {R R' : Constraint S} (hR : Rigid R) (hR' : Rigid R')
    (h : ∀ n a, R n a ↔ R' n a) (s : Str S) : fill R hR s = fill R' hR' s := by
  have hsel : sel R hR = sel R' hR' := sel_congr_iff hR hR' h
  funext n
  show some ((s n).getD (sel R hR n)) = some ((s n).getD (sel R' hR' n))
  rw [hsel]

/-! ## §4 INTEGRATE: the live selector on the substrate of NRRF776 -/

/-- Transport of a relation by a substrate operator. -/
def subOpTransport (a b : Bool) (R : Constraint ℂ) : Constraint ℂ :=
  fun n z => R n (NRRF776.subOp a b z)

theorem subOpTransport_rigid {R : Constraint ℂ} (hR : Rigid R) (a b : Bool) :
    Rigid (subOpTransport a b R) := by
  intro n
  obtain ⟨w, hw, hu⟩ := hR n
  refine ⟨NRRF776.subOp a b w, ?_, ?_⟩
  · simpa [subOpTransport, NRRF776.subOp_involutive] using hw
  · intro z hz
    have hzw : NRRF776.subOp a b z = w := hu _ hz
    calc z = NRRF776.subOp a b (NRRF776.subOp a b z) := (NRRF776.subOp_involutive a b z).symm
      _ = NRRF776.subOp a b w := by rw [hzw]

/-- **The selector commutes with the substrate operators.** -/
theorem sel_subOpTransport {R : Constraint ℂ} (hR : Rigid R) (a b : Bool) (n : ℕ) :
    sel (subOpTransport a b R) (subOpTransport_rigid hR a b) n
      = NRRF776.subOp a b (sel R hR n) := by
  have h : subOpTransport a b R n (NRRF776.subOp a b (sel R hR n)) := by
    simpa [subOpTransport, NRRF776.subOp_involutive] using sel_admissible R hR n
  exact (sel_eq_of_admissible (subOpTransport_rigid hR a b) h).symm

/-- **The unified equality function of the natural form is a substrate invariant.**  This is the
integration clause: what the live selector determines is read at the level of the substrate
quotient, not at the level of a point. -/
theorem radEq_form_subOp_invariant {R : Constraint ℂ} (hR : Rigid R) (a b : Bool) (n : ℕ) :
    NRRF776.radEq (sel (subOpTransport a b R) (subOpTransport_rigid hR a b) n)
      = NRRF776.radEq (sel R hR n) := by
  rw [sel_subOpTransport hR a b n, NRRF776.radEq_subOp]

/-- Halting of the loop sensor at a form value is a trace of the equality function. -/
theorem form_halts_iff {R : Constraint ℂ} (hR : Rigid R) {n : ℕ} (hz : sel R hR n ≠ 0) :
    Halts NRRF776.sensorStep (sel R hR n) ↔ NRRF776.radEq (sel R hR n) = 0 :=
  NRRF776.halts_iff_radEq_zero hz

/-- Continuation is the complementary trace. -/
theorem form_continues_iff {R : Constraint ℂ} (hR : Rigid R) {n : ℕ} (hz : sel R hR n ≠ 0) :
    Continues NRRF776.sensorStep (sel R hR n) ↔ NRRF776.radEq (sel R hR n) ≠ 0 :=
  NRRF776.continues_iff_radEq_ne_zero hz

/-- Transporting the relation by a substrate operator does not change which trace occurs: halting is
determined by the relation's substrate class, not by the representative. -/
theorem halts_iff_halts_subOpTransport {R : Constraint ℂ} (hR : Rigid R) (a b : Bool) {n : ℕ}
    (hz : sel R hR n ≠ 0)
    (hz' : sel (subOpTransport a b R) (subOpTransport_rigid hR a b) n ≠ 0) :
    Halts NRRF776.sensorStep (sel (subOpTransport a b R) (subOpTransport_rigid hR a b) n)
      ↔ Halts NRRF776.sensorStep (sel R hR n) := by
  rw [NRRF776.halts_iff_radEq_zero hz', NRRF776.halts_iff_radEq_zero hz,
    radEq_form_subOp_invariant hR a b n]

/-! ## §5 TRUE is not issued -/

/-- **No verdict.**  There is a rigid relation whose translation event is filled at every site, for
every compatible input string, and which never emits the symbol `true`. -/
theorem exists_rigid_filled_no_true_symbol :
    ∃ (R : Constraint Bool) (hR : Rigid R),
      (∀ s : Str Bool, Determined (fill R hR s)) ∧
      (∀ s : Str Bool, Compat s R → ∀ n, fill R hR s n = some false) := by
  refine ⟨falseOnly, falseOnly_rigid, fun s => fill_determined _ _ s, ?_⟩
  intro s hs n
  rw [fill_eq_form falseOnly_rigid hs]
  simp [sel_falseOnly]

/-- The event is a function of the relation, so no valuation of the symbols can influence it. -/
theorem fill_indep_of_valuation {R R' : Constraint S} (hR : Rigid R) (hR' : Rigid R')
    (h : ∀ n a, R n a ↔ R' n a) (v : S → Bool) (s : Str S) :
    (fill R hR s n).map v = (fill R' hR' s n).map v := by
  rw [fill_congr_iff hR hR' h]

/-! ## §6 The answer -/

/-- **NRRF777.**  The live natural form selector, formally: it is equivariant under re-charting the
site space and relabelling the symbols and depends on nothing but the relation's pointwise content,
while no site-indexed field can be it (relation, not spacetime object); its translation event fills
every site, refines the input, is the unique determined compatible refinement and is stable under
repetition (TE filled); it commutes with the substrate operators of NRRF776 so that the unified
equality function of the form — and hence which of halting/continuation is traced — is a substrate
invariant (INTEGRATE); and it can determine everything while issuing no verdict (TRUE not
issued). -/
theorem nrrf777_answer :
    (∀ {S : Type} (R : Constraint S) (hR : Rigid R) (σ : Equiv.Perm ℕ) (n : ℕ),
        sel (reindex σ R) (reindex_rigid hR σ) n = sel R hR (σ n)) ∧
    (∀ {S T : Type} (R : Constraint S) (hR : Rigid R) (e : S ≃ T) (n : ℕ),
        sel (retag e R) (retag_rigid hR e) n = e (sel R hR n)) ∧
    (∀ (f : ℕ → Bool), ∃ (R : Constraint Bool) (hR : Rigid R), ∀ n, sel R hR n ≠ f n) ∧
    (∀ {S : Type} (R : Constraint S) (hR : Rigid R) (s : Str S),
        Determined (fill R hR s) ∧ Refines (fill R hR s) s ∧
        fill R hR (fill R hR s) = fill R hR s) ∧
    (∀ {S : Type} (R : Constraint S) (hR : Rigid R) (s t : Str S), Compat s R → Determined t →
        Compat t R → t = fill R hR s) ∧
    (∀ (R : Constraint ℂ) (hR : Rigid R) (a b : Bool) (n : ℕ),
        sel (subOpTransport a b R) (subOpTransport_rigid hR a b) n
          = NRRF776.subOp a b (sel R hR n) ∧
        NRRF776.radEq (sel (subOpTransport a b R) (subOpTransport_rigid hR a b) n)
          = NRRF776.radEq (sel R hR n)) ∧
    (∀ (R : Constraint ℂ) (hR : Rigid R) (n : ℕ), sel R hR n ≠ 0 →
        (Halts NRRF776.sensorStep (sel R hR n) ↔ NRRF776.radEq (sel R hR n) = 0) ∧
        (Continues NRRF776.sensorStep (sel R hR n) ↔ NRRF776.radEq (sel R hR n) ≠ 0)) ∧
    (∃ (R : Constraint Bool) (hR : Rigid R),
        (∀ s : Str Bool, Determined (fill R hR s)) ∧
        (∀ s : Str Bool, Compat s R → ∀ n, fill R hR s n = some false)) :=
  ⟨fun R hR σ n => sel_reindex hR σ n,
   fun R hR e n => sel_retag hR e n,
   fun f => no_location_only_selector (a := false) (b := true) (by simp) f,
   fun R hR s => ⟨fill_determined R hR s, fill_refines R hR s, fill_idem hR s⟩,
   fun R hR s t hs ht htc => fill_unique hR hs ht htc,
   fun R hR a b n => ⟨sel_subOpTransport hR a b n, radEq_form_subOp_invariant hR a b n⟩,
   fun R hR n hz => ⟨form_halts_iff hR hz, form_continues_iff hR hz⟩,
   exists_rigid_filled_no_true_symbol⟩

/-! ## Audit -/

#print axioms sel_reindex
#print axioms sel_retag
#print axioms no_location_only_selector
#print axioms fill_unique
#print axioms fill_idem
#print axioms sel_subOpTransport
#print axioms radEq_form_subOp_invariant
#print axioms exists_rigid_filled_no_true_symbol
#print axioms nrrf777_answer

end NRRF777
