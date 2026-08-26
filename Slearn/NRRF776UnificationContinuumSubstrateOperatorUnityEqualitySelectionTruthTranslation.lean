import Mathlib
import Slearn.NRRF772LinearLayoutRelativeEqualityFunctionsCompleteness
import Slearn.NRRF774SelfTensorInversionClosureFormAIHardwareLoopGlobalConstraint
import Slearn.NRRF775NaturalFormSelectorUnifaceRelationalDeterminationUnitaryPathPartitionTraces

/-!
# NRRF776 — The unification continuum: substrate operator unity, equality selection, truth
translation, halting/continuation

The reading being formalised:

> The alternative multiplication has `|·|²` and `Γ` as *one* equality function of relative
> translational truth; one operator is the relative hair inversion and one is the relative ball self
> limit, both read off the same data.  How does organising translational truth into relative
> equality functions approach a *complete* theory?  The unification continuum problem is that the
> natural form selector required for closure has not been formalised through relative translation of
> truth as continuous equality completion.  Substrate operator unity, halting continuation, equality
> selection, truth translation.

Everything below is proved from ordinary Mathlib together with the earlier modules NRRF771/772/774/775.

* **§1 Substrate operator unity.**  The relative hair inversion `hairInv = conj` and the relative
  ball self limit `ballInv = z ↦ z/‖z‖²` (the self tensor inversion of NRRF774) are both involutions
  of the same datum, they commute, and their composite is ordinary inversion `z ↦ z⁻¹`
  (`hairInv_ballInv`, `ballInv_hairInv`, `hairInv_ballInv_comm`).  So the two operators are not two
  theories: they generate a single Klein four-group of substrate operators, `subOp`, with
  composition law `subOp_comp` — *substrate operator unity* as a group law, not a slogan.

* **§2 One equality function.**  `radEq z = |log ‖z‖|` is invariant under the whole substrate group
  (`radEq_subOp`), vanishes exactly on the closure form (`radEq_eq_zero_iff`,
  `closureForm_eq_radEq_zero`), and *every* NRRF771 translational-truth reading `tsq f` translates
  into it (`tsq_refines_radEq`) — in particular the `|·|²` reading and the `Γ` reading translate
  into the *same* equality function (`absSq_refines_radEq`, `gamma_refines_radEq`).  The translation
  is strictly one-way (`radEq_not_refines_tsq`), which is why `radEq` is the equality function of the
  *quotient* level and not a re-encoding of the data.

* **§3 Equality selection: what completeness is.**  The ball self limit's orbit relation
  `BallOrbit` is an equivalence, and the two relative equality functions `dir` (direction) and
  `radEq` determine *exactly* it (`ballOrbit_iff`).  Hence the pair is a complete family for the
  substrate quotient (`pairRead_complete`, `pairLift_injective`), while `radEq` alone is not
  (`radEq_alone_not_complete`).  Completeness is therefore selection: a family is complete when its
  joint kernel has been driven down to the equality the substrate operator already imposes.

* **§4 Halting and continuation are traces of the equality function.**  The loop sensor
  `sensorStep` iterates the ball self limit and stops on the closure form.  The equality function is
  constant along the whole run (`radEq_invariant_run`), and the run halts exactly when the equality
  function is `0` (`halts_iff_radEq_zero`), continues exactly when it is not
  (`continues_iff_radEq_ne_zero`).  Halting and continuation are two traces of one determination, and
  which trace occurs is *read off* the equality function rather than decided externally.

* **§5 Truth translation as continuous equality completion.**  `completion_universal` is the
  universal property the earlier modules were missing: for any family of relative equality functions,
  the translational quotient is the universal receptacle — every reading that respects the family's
  equality factors through it *uniquely*.  `complete_iff_quotientMk_injective` says a family is
  complete exactly when that completion is already the substrate.  This is the closure form of the
  organisation: not an external equation, but the unique factorisation of every further reading
  through the equality the family determines.

`nrrf776_answer` collects the clauses.
-/

open Complex

namespace NRRF776

/-! ## §1 Substrate operator unity -/

/-- The **relative hair inversion**: reflection of the datum in its own real axis. -/
noncomputable def hairInv (z : ℂ) : ℂ := (starRingEnd ℂ) z

/-- The **relative ball self limit**: the self tensor inversion of NRRF774, `z ↦ z / ‖z‖²`. -/
noncomputable def ballInv (z : ℂ) : ℂ := NRRF774.selfInv z

theorem ballInv_eq_conj_inv (z : ℂ) : ballInv z = (starRingEnd ℂ) z⁻¹ :=
  NRRF774.selfInv_eq_conj_inv z

theorem hairInv_involutive (z : ℂ) : hairInv (hairInv z) = z := Complex.conj_conj z

theorem ballInv_involutive (z : ℂ) : ballInv (ballInv z) = z := NRRF774.selfInv_involutive z

theorem norm_hairInv (z : ℂ) : ‖hairInv z‖ = ‖z‖ := RCLike.norm_conj z

theorem norm_ballInv (z : ℂ) : ‖ballInv z‖ = ‖z‖⁻¹ := NRRF774.norm_selfInv z

/-- Hair inversion after the ball self limit is ordinary inversion. -/
theorem hairInv_ballInv (z : ℂ) : hairInv (ballInv z) = z⁻¹ := by
  rw [hairInv, ballInv_eq_conj_inv, Complex.conj_conj]

/-- And in the other order — the two operators commute. -/
theorem ballInv_hairInv (z : ℂ) : ballInv (hairInv z) = z⁻¹ := by
  rw [hairInv, ballInv_eq_conj_inv, map_inv₀, Complex.conj_conj]

theorem hairInv_ballInv_comm (z : ℂ) : hairInv (ballInv z) = ballInv (hairInv z) := by
  rw [hairInv_ballInv, ballInv_hairInv]

/-- The **substrate operator group**: the four operators generated by the hair inversion and the
ball self limit. -/
noncomputable def subOp : Bool → Bool → ℂ → ℂ
  | false, false => id
  | true, false => hairInv
  | false, true => ballInv
  | true, true => fun z => z⁻¹

@[simp] theorem subOp_ff (z : ℂ) : subOp false false z = z := rfl
@[simp] theorem subOp_tf (z : ℂ) : subOp true false z = hairInv z := rfl
@[simp] theorem subOp_ft (z : ℂ) : subOp false true z = ballInv z := rfl
@[simp] theorem subOp_tt (z : ℂ) : subOp true true z = z⁻¹ := rfl

/-- **Substrate operator unity.**  The four operators compose by the Klein four-group law: the hair
inversion and the ball self limit are two coordinates of one substrate symmetry. -/
theorem subOp_comp (a b c d : Bool) (z : ℂ) :
    subOp a b (subOp c d z) = subOp (xor a c) (xor b d) z := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [hairInv, ballInv_eq_conj_inv, map_inv₀]

theorem subOp_involutive (a b : Bool) (z : ℂ) : subOp a b (subOp a b z) = z := by
  simpa using subOp_comp a b a b z

/-! ## §2 The one equality function of relative translational truth -/

/-- The **unified equality function**: the radial magnitude read symmetrically about the closure
form. -/
noncomputable def radEq (z : ℂ) : ℝ := |Real.log ‖z‖|

@[simp] theorem radEq_hairInv (z : ℂ) : radEq (hairInv z) = radEq z := by
  rw [radEq, radEq, norm_hairInv]

@[simp] theorem radEq_ballInv (z : ℂ) : radEq (ballInv z) = radEq z := by
  rw [radEq, radEq, norm_ballInv, Real.log_inv, abs_neg]

theorem radEq_inv (z : ℂ) : radEq z⁻¹ = radEq z := by
  rw [radEq, radEq, norm_inv, Real.log_inv, abs_neg]

/-- The equality function is invariant under the whole substrate operator group. -/
theorem radEq_subOp (a b : Bool) (z : ℂ) : radEq (subOp a b z) = radEq z := by
  cases a <;> cases b <;> simp [radEq_inv]

/-- It vanishes exactly on the closure form. -/
theorem radEq_eq_zero_iff {z : ℂ} (hz : z ≠ 0) : radEq z = 0 ↔ ‖z‖ = 1 := by
  have hpos : (0:ℝ) < ‖z‖ := norm_pos_iff.mpr hz
  constructor
  · intro h
    have hlog : Real.log ‖z‖ = 0 := abs_eq_zero.mp h
    rcases Real.log_eq_zero.mp hlog with h1 | h1 | h1
    · exact absurd h1 (ne_of_gt hpos)
    · exact h1
    · linarith [hpos, h1]
  · intro h
    simp [radEq, h]

/-- The closure form of NRRF774 is the zero locus of the unified equality function. -/
theorem closureForm_eq_radEq_zero :
    NRRF774.closureForm = {z : ℂ | z ≠ 0 ∧ radEq z = 0} := by
  rw [NRRF774.closureForm_eq_sphere]
  ext z
  constructor
  · intro (hz : ‖z‖ = 1)
    have hz0 : z ≠ 0 := by
      intro h; rw [h] at hz; simp at hz
    exact ⟨hz0, (radEq_eq_zero_iff hz0).mpr hz⟩
  · rintro ⟨hz0, h⟩
    exact (radEq_eq_zero_iff hz0).mp h

/-- **`|·|²` and `Γ` are one equality function.**  Every translational-truth reading of NRRF771
translates into `radEq`: the alternative multiplication's self value determines the unified equality
function. -/
theorem tsq_refines_radEq {f : ℂ → ℂ} (hf : NRRF771.TranslationalTruth f) :
    NRRF772.Refines (fun z : ℂ => NRRF771.tsq f z) (fun z : ℂ => radEq (f z)) := by
  rw [NRRF772.refines_iff_kernel _ _ (0 : ℂ)]
  intro z w h
  rw [NRRF771.tsq_eq_normSq hf, NRRF771.tsq_eq_normSq hf] at h
  have h' : (‖f z‖ : ℝ) ^ 2 = (‖f w‖ : ℝ) ^ 2 := by exact_mod_cast h
  have : ‖f z‖ = ‖f w‖ := by
    have := congrArg Real.sqrt h'
    simpa [Real.sqrt_sq (norm_nonneg _)] using this
  rw [radEq, radEq, this]

/-- The `|·|²` reading. -/
theorem absSq_refines_radEq :
    NRRF772.Refines (fun z : ℂ => NRRF771.tsq id z) (fun z : ℂ => radEq z) :=
  tsq_refines_radEq NRRF771.translationalTruth_id

/-- The `Γ` reading — the *same* equality function, at the `Γ`-translated datum. -/
theorem gamma_refines_radEq :
    NRRF772.Refines (fun z : ℂ => NRRF771.tsq Complex.Gamma z)
      (fun z : ℂ => radEq (Complex.Gamma z)) :=
  tsq_refines_radEq NRRF771.translationalTruth_Gamma

/-- The translation is strictly one-way: the unified equality function is genuinely coarser than the
self value, because it identifies a datum with its ball self limit. -/
theorem radEq_not_refines_tsq :
    ¬ NRRF772.Refines (fun z : ℂ => radEq z) (fun z : ℂ => NRRF771.tsq id z) := by
  intro h
  have hker := h.kernel_le (d := (2 : ℂ)) (d' := ballInv 2) (by simp)
  rw [NRRF771.tsq_eq_normSq NRRF771.translationalTruth_id,
    NRRF771.tsq_eq_normSq NRRF771.translationalTruth_id] at hker
  simp only [id_eq] at hker
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  have hb : ‖ballInv (2 : ℂ)‖ = (2 : ℝ)⁻¹ := by rw [norm_ballInv, h2]
  rw [h2, hb] at hker
  norm_num at hker

/-! ## §3 Equality selection: completeness for the substrate operator -/

/-- The direction reading. -/
noncomputable def dir (z : ℂ) : ℂ := z / ((‖z‖ : ℝ) : ℂ)

/-- The orbit relation of the relative ball self limit. -/
def BallOrbit (z w : ℂ) : Prop := w = z ∨ w = ballInv z

theorem ballOrbit_refl (z : ℂ) : BallOrbit z z := Or.inl rfl

theorem ballOrbit_symm {z w : ℂ} (h : BallOrbit z w) : BallOrbit w z := by
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (ballInv_involutive z).symm

theorem ballOrbit_trans {z w u : ℂ} (h₁ : BallOrbit z w) (h₂ : BallOrbit w u) : BallOrbit z u := by
  rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inl (ballInv_involutive z)

theorem ballOrbit_equivalence : Equivalence BallOrbit :=
  ⟨ballOrbit_refl, ballOrbit_symm, ballOrbit_trans⟩

theorem dir_ballInv {z : ℂ} (hz : z ≠ 0) : dir (ballInv z) = dir z := by
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hnc : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn
  have hb : ballInv z = z / ((‖z‖ : ℝ) : ℂ) ^ 2 := by
    rw [ballInv, NRRF774.selfInv, NRRF774.selfT_eq_normSq]
  rw [dir, dir, norm_ballInv, hb]
  have hcast : ((‖z‖⁻¹ : ℝ) : ℂ) = (((‖z‖ : ℝ) : ℂ))⁻¹ := by push_cast; ring
  rw [hcast]
  field_simp

/-- **The two relative equality functions determine exactly the substrate orbit.** -/
theorem ballOrbit_iff {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0) :
    BallOrbit z w ↔ (dir z = dir w ∧ radEq z = radEq w) := by
  constructor
  · rintro (rfl | rfl)
    · exact ⟨rfl, rfl⟩
    · exact ⟨(dir_ballInv hz).symm, (radEq_ballInv z).symm⟩
  · rintro ⟨hd, hr⟩
    have hzp : (0:ℝ) < ‖z‖ := norm_pos_iff.mpr hz
    have hwp : (0:ℝ) < ‖w‖ := norm_pos_iff.mpr hw
    have hnorm : ‖w‖ = ‖z‖ ∨ ‖w‖ = ‖z‖⁻¹ := by
      rcases abs_eq_abs.mp hr.symm with h | h
      · left
        have := congrArg Real.exp h
        rwa [Real.exp_log hwp, Real.exp_log hzp] at this
      · right
        have := congrArg Real.exp h
        rwa [Real.exp_log hwp, ← Real.log_inv, Real.exp_log (by positivity)] at this
    have hzc : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hzp
    have hwc : ((‖w‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hwp
    have hzw : w = (((‖w‖ : ℝ) : ℂ) / ((‖z‖ : ℝ) : ℂ)) * z := by
      rw [dir, dir] at hd
      field_simp at hd
      field_simp
      linear_combination -hd
    rcases hnorm with h | h
    · left
      rw [hzw, h]
      field_simp
    · right
      have hb : ballInv z = z / ((‖z‖ : ℝ) : ℂ) ^ 2 := by
        rw [ballInv, NRRF774.selfInv, NRRF774.selfT_eq_normSq]
      rw [hzw, hb, h]
      push_cast
      field_simp

/-- Nonzero data — the substrate the operators act on. -/
abbrev NZ := {z : ℂ // z ≠ 0}

/-- The substrate equality: identification along the ball self limit. -/
def nzSetoid : Setoid NZ where
  r z w := BallOrbit z.1 w.1
  iseqv :=
    ⟨fun z => ballOrbit_refl z.1, fun h => ballOrbit_symm h, fun h₁ h₂ => ballOrbit_trans h₁ h₂⟩

/-- The joint relative reading: direction together with the unified equality function. -/
noncomputable def pairRead (z : NZ) : ℂ × ℝ := (dir z.1, radEq z.1)

theorem radEq_respects {z w : NZ} (h : nzSetoid.r z w) : radEq z.1 = radEq w.1 :=
  ((ballOrbit_iff z.2 w.2).mp h).2

theorem pairRead_respects {z w : NZ} (h : nzSetoid.r z w) : pairRead z = pairRead w := by
  rcases (ballOrbit_iff z.2 w.2).mp h with ⟨h1, h2⟩
  simp [pairRead, h1, h2]

/-- The reading, transported to the level of data it determines. -/
noncomputable def pairLift : Quotient nzSetoid → ℂ × ℝ :=
  Quotient.lift pairRead fun _ _ h => pairRead_respects h

/-- **Equality selection.**  On the substrate quotient the pair (direction, unified equality
function) is injective: the family is complete exactly at the level the substrate operator selects. -/
theorem pairLift_injective : Function.Injective pairLift := by
  intro q q'
  induction q using Quotient.inductionOn with
  | h z =>
    induction q' using Quotient.inductionOn with
    | h w =>
      intro h
      have h' : dir z.1 = dir w.1 ∧ radEq z.1 = radEq w.1 := by
        have h1 := congrArg Prod.fst h
        have h2 := congrArg Prod.snd h
        exact ⟨h1, h2⟩
      exact Quotient.sound ((ballOrbit_iff z.2 w.2).mpr h')

/-- The same statement in the completeness language of NRRF772. -/
theorem pairRead_complete :
    NRRF772.Complete (fun (_ : Unit) (q : Quotient nzSetoid) => pairLift q) := by
  intro q q' h
  exact pairLift_injective (congrFun h ())

/-- The unified equality function *alone* is not complete: `1` and `i` share it but are not in one
substrate orbit.  Completeness needs the direction too — this is why the organisation into several
relative equality functions is the right move. -/
theorem radEq_alone_not_complete :
    ¬ Function.Injective (Quotient.lift (fun z : NZ => radEq z.1)
      fun _ _ h => radEq_respects h) := by
  intro hinj
  have h1 : (1 : ℂ) ≠ 0 := one_ne_zero
  have hI : (Complex.I) ≠ 0 := Complex.I_ne_zero
  have hIne : Complex.I ≠ (1 : ℂ) := by
    simp [Complex.ext_iff]
  have hval : radEq (1 : ℂ) = radEq Complex.I := by
    simp [radEq]
  have hq := hinj (a₁ := Quotient.mk nzSetoid ⟨1, h1⟩)
    (a₂ := Quotient.mk nzSetoid ⟨Complex.I, hI⟩) hval
  have horb : BallOrbit (1 : ℂ) Complex.I := Quotient.exact hq
  rcases horb with h | h
  · exact hIne h
  · rw [ballInv_eq_conj_inv] at h
    simp at h
    exact hIne h

/-! ## §4 Halting and continuation as traces of the equality function -/

/-- The **loop sensor**: iterate the relative ball self limit, stopping on the closure form. -/
noncomputable def sensorStep (z : ℂ) : Option ℂ :=
  if ‖z‖ = 1 then none else some (ballInv z)

theorem sensorStep_of_ne {z : ℂ} (h : ‖z‖ ≠ 1) : sensorStep z = some (ballInv z) := by
  simp [sensorStep, h]

theorem sensorStep_of_eq {z : ℂ} (h : ‖z‖ = 1) : sensorStep z = none := by
  simp [sensorStep, h]

theorem ballInv_ne_zero {z : ℂ} (hz : z ≠ 0) : ballInv z ≠ 0 := by
  intro h
  have : ‖ballInv z‖ = 0 := by rw [h]; simp
  rw [norm_ballInv] at this
  exact hz (norm_eq_zero.mp (by simpa using inv_eq_zero.mp this))

theorem norm_ballInv_ne_one {z : ℂ} (hz : z ≠ 0) (h : ‖z‖ ≠ 1) : ‖ballInv z‖ ≠ 1 := by
  rw [norm_ballInv]
  intro hcon
  have hzp : (0:ℝ) < ‖z‖ := norm_pos_iff.mpr hz
  have : ‖z‖ = 1 := by
    field_simp at hcon
    linarith [hcon]
  exact h this

/-- **The equality function is constant along the whole run.** -/
theorem radEq_invariant_run (z : ℂ) (n : ℕ) (y : ℂ) (h : NRRF775.run sensorStep z n = some y) :
    radEq y = radEq z := by
  induction n generalizing y with
  | zero => rw [NRRF775.run_zero] at h; rw [Option.some_inj.mp h]
  | succ k ih =>
      rw [NRRF775.run_succ] at h
      rcases hk : NRRF775.run sensorStep z k with _ | x
      · rw [hk] at h; simp at h
      · rw [hk] at h
        simp only [Option.bind_some] at h
        by_cases hx : ‖x‖ = 1
        · rw [sensorStep_of_eq hx] at h; simp at h
        · rw [sensorStep_of_ne hx] at h
          rw [← Option.some_inj.mp h, radEq_ballInv]
          exact ih x hk

theorem run_some_of_ne_one {z : ℂ} (hz : z ≠ 0) (h : ‖z‖ ≠ 1) (n : ℕ) :
    ∃ y : ℂ, NRRF775.run sensorStep z n = some y ∧ y ≠ 0 ∧ ‖y‖ ≠ 1 := by
  induction n with
  | zero => exact ⟨z, rfl, hz, h⟩
  | succ k ih =>
      obtain ⟨y, hy, hy0, hy1⟩ := ih
      refine ⟨ballInv y, ?_, ballInv_ne_zero hy0, norm_ballInv_ne_one hy0 hy1⟩
      rw [NRRF775.run_succ, hy]
      simpa using sensorStep_of_ne hy1

/-- **Halting is a trace of the equality function.**  The loop sensor halts exactly on the closure
form, i.e. exactly where the unified equality function vanishes. -/
theorem halts_iff_radEq_zero {z : ℂ} (hz : z ≠ 0) :
    NRRF775.Halts sensorStep z ↔ radEq z = 0 := by
  constructor
  · intro ⟨n, hn⟩
    by_contra hcon
    have h1 : ‖z‖ ≠ 1 := fun h => hcon ((radEq_eq_zero_iff hz).mpr h)
    obtain ⟨y, hy, _, _⟩ := run_some_of_ne_one hz h1 n
    rw [hy] at hn
    exact absurd hn (by simp)
  · intro h
    have h1 : ‖z‖ = 1 := (radEq_eq_zero_iff hz).mp h
    exact ⟨1, by rw [NRRF775.run_succ, NRRF775.run_zero]; simpa using sensorStep_of_eq h1⟩

/-- **Continuation is the complementary trace.** -/
theorem continues_iff_radEq_ne_zero {z : ℂ} (hz : z ≠ 0) :
    NRRF775.Continues sensorStep z ↔ radEq z ≠ 0 := by
  constructor
  · intro hc hr
    exact NRRF775.not_halts_and_continues ⟨(halts_iff_radEq_zero hz).mpr hr, hc⟩
  · intro hr
    rcases NRRF775.halts_or_continues sensorStep z with h | h
    · exact absurd ((halts_iff_radEq_zero hz).mp h) hr
    · exact h

/-! ## §5 Truth translation as continuous equality completion -/

section Completion

variable {D : Type u}

/-- **The completion is universal.**  Every reading that respects the equality a family of relative
equality functions determines factors through the translational quotient — and does so uniquely.
This is the closure form of the organisation: no external equation, just unique factorisation. -/
theorem completion_universal {ι : Type*} {V : ι → Type v} (r : ∀ i, D → V i) {W : Type w}
    (s : D → W) (h : ∀ d d', (∀ i, r i d = r i d') → s d = s d') :
    ∃! t : Quotient (NRRF772.kerSetoid r) → W, ∀ d, t (Quotient.mk _ d) = s d := by
  refine ⟨Quotient.lift s (fun a b hab => h a b fun i => congrFun hab i), fun _ => rfl, ?_⟩
  intro t ht
  funext q
  induction q using Quotient.inductionOn with
  | h d => exact ht d

/-- A family is complete exactly when its completion is already the substrate. -/
theorem complete_iff_quotientMk_injective {ι : Type*} {V : ι → Type v} (r : ∀ i, D → V i) :
    NRRF772.Complete r ↔
      Function.Injective (fun d : D => Quotient.mk (NRRF772.kerSetoid r) d) := by
  rw [NRRF772.complete_iff]
  constructor
  · intro hcomp d d' hd
    exact hcomp d d' fun i => congrFun (Quotient.exact hd) i
  · intro hinj d d' hd
    exact hinj (Quotient.sound (funext hd))

/-- Truth translation is transitive along completions: a reading refined by a family is refined by
the family's completion, so completing never loses translational reach. -/
theorem refines_of_completion {ι : Type*} {V : ι → Type v} (r : ∀ i, D → V i) {W : Type w}
    (s : D → W) (h : NRRF772.Refines (NRRF772.joint r) s) :
    ∃ t : Quotient (NRRF772.kerSetoid r) → W, ∀ d, t (Quotient.mk _ d) = s d := by
  have hker : ∀ d d', (∀ i, r i d = r i d') → s d = s d' := by
    intro d d' hd
    exact h.kernel_le (funext hd)
  obtain ⟨t, ht, _⟩ := completion_universal r s hker
  exact ⟨t, ht⟩

end Completion

/-! ## §6 The answer -/

/-- **NRRF776.**  The unification continuum, in one statement: the hair inversion and the ball self
limit are one substrate group; `|·|²` and `Γ` translate into one equality function invariant under
it; direction plus that equality function is a complete family for exactly the substrate's own
equality; halting and continuation are the two traces of the equality function's value; and every
reading factors uniquely through the translational completion. -/
theorem nrrf776_answer :
    (∀ a b c d : Bool, ∀ z : ℂ, subOp a b (subOp c d z) = subOp (xor a c) (xor b d) z) ∧
    (∀ a b : Bool, ∀ z : ℂ, radEq (subOp a b z) = radEq z) ∧
    NRRF772.Refines (fun z : ℂ => NRRF771.tsq id z) (fun z : ℂ => radEq z) ∧
    NRRF772.Refines (fun z : ℂ => NRRF771.tsq Complex.Gamma z)
      (fun z : ℂ => radEq (Complex.Gamma z)) ∧
    (∀ z w : ℂ, z ≠ 0 → w ≠ 0 → (BallOrbit z w ↔ (dir z = dir w ∧ radEq z = radEq w))) ∧
    Function.Injective pairLift ∧
    (∀ z : ℂ, z ≠ 0 → (NRRF775.Halts sensorStep z ↔ radEq z = 0)) ∧
    (∀ z : ℂ, z ≠ 0 → (NRRF775.Continues sensorStep z ↔ radEq z ≠ 0)) ∧
    NRRF774.closureForm = {z : ℂ | z ≠ 0 ∧ radEq z = 0} :=
  ⟨subOp_comp, radEq_subOp, absSq_refines_radEq, gamma_refines_radEq,
    fun _ _ hz hw => ballOrbit_iff hz hw, pairLift_injective,
    fun _ hz => halts_iff_radEq_zero hz, fun _ hz => continues_iff_radEq_ne_zero hz,
    closureForm_eq_radEq_zero⟩

/-! ## Audit -/

#print axioms subOp_comp
#print axioms radEq_subOp
#print axioms tsq_refines_radEq
#print axioms ballOrbit_iff
#print axioms pairLift_injective
#print axioms radEq_alone_not_complete
#print axioms halts_iff_radEq_zero
#print axioms completion_universal
#print axioms nrrf776_answer

end NRRF776
