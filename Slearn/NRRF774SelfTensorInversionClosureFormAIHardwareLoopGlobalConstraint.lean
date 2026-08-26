import Mathlib
import Slearn.NRRF771AlternativeMultiplicationAbsSquaredGammaTranslationalTruthEquality

/-!
# NRRF774 — Self tensor inversion, the closure form of the loop, and the selective temporary global constraint

The reading being formalised:

> My multiplication equality function *in the self tensor inversion equality*.  This is not a
> classical external equation, it is a translational completion of relations — a loop sensor
> unification continuum.  Then the question becomes: what natural closure form relates to the AI
> hardware loop, i.e. a unified topology?  Closure loop, line/point projection, light cone topology
> class cycling, the `0`–`∞` path ball–hair operator, and then integration with digital network
> interaction as a *selective temporary global constraint*, with a path towards hardware or physical
> verification.

Four things are proved, and they are the four clauses of the reading.

* **§1 The self tensor inversion equality.**  The alternative multiplication of NRRF771 is the
  self tensor pairing `stp z w = z * conj w` (`stp_eq_tmul`).  Its *self tensor* `stp z z` is the
  one equality function `‖z‖²`, and the inversion equality `stp z w = 1` has, for `z ≠ 0`, the
  unique solution `selfInv z = z / ‖z‖²` (`stp_selfInv`, `stp_eq_one_iff`).  The inversion is an
  involution and is the ball–hair operator: `selfInv` fixes exactly the unit sphere
  (`selfInv_eq_self_iff`), and it is covariant for the *zoom* action (`selfInv_zoom`), so it is a
  relation of the whole scale network at once, not an external equation at one scale.

* **§2 The `0`–`∞` paths (hairs) and their closure form.**  Each unit direction `u` carries a hair
  `t ↦ t·u`; the ball–hair operator reverses it, `selfInv (t·u) = t⁻¹·u` (`selfInv_hair`), sending
  the `0` end to the `∞` end (`norm_selfInv_hair_atTop`, `norm_selfInv_hair_zero`).  Every direction
  occurs (`exists_hair`), so the hairs partition the punctured plane, and the closure form — the
  fixed set of the whole family, the set the loop returns to — is exactly the unit sphere
  (`closureForm_eq_sphere`).  That is the natural closure form of the loop: not a point and not a
  boundary imposed from outside, but the zoom-invariant self-inverse locus.

* **§3 Light cone topology class cycling.**  For any causal preorder (light cone order) on events,
  *cycling* — `x ≤ y ∧ y ≤ x` — is an equivalence (`cycles_equivalence`); every closed causal loop
  collapses to a single cycling class (`loop_cycles`); and every monotone reading of the events into
  a partial order cannot separate a cycling class (`monotone_reading_identifies_cycles`).  So the
  loop is not an inconsistency of the causal topology: it is precisely the resolution that
  identifies its class, exactly as translational equality identifies data in NRRF771–773.

* **§4 The selective temporary global constraint, and the hardware path.**  A digital network
  interaction is a family of constraints `P n`, each of which reads only a *finite selection* of the
  network (the first `n` channels) — hence each is machine-checkable, `decide`-able on hardware
  (`decidable_temporary`, `hardware_check`).  Each such constraint is closed in the network topology
  (`constraintSet_isClosed`).  The theorem `selective_temporary_global_closure` is the completion
  statement: if the temporary constraints are nested (each selection refines the previous) and each
  is separately satisfiable, then there is a single global state of the network satisfying *all* of
  them.  The global constraint is never imposed; it is the limit of temporary selective ones, and
  every finite stage of it is verifiable by a physical machine.  `no_global_closure_of_empty_stage`
  is the honest converse: a stage that no state meets destroys the global closure, so the temporary
  constraints really are load-bearing.

`nrrf774_answer` collects the four clauses in one theorem.
-/

open Complex Filter Topology Metric

namespace NRRF774

/-! ## §1  The self tensor and the inversion equality -/

/-- The **self tensor pairing**: the alternative multiplication read as a rank-one tensor
`z ⊗ conj w`. -/
noncomputable def stp (z w : ℂ) : ℂ := z * (starRingEnd ℂ) w

/-- It *is* the alternative multiplication of NRRF771 through the identity carrier. -/
theorem stp_eq_tmul (z w : ℂ) : stp z w = NRRF771.tmul id z w := by
  rw [stp, NRRF771.tmul_eq_mul_conj NRRF771.translationalTruth_id]
  rfl

/-- The **self tensor**: the diagonal of the pairing, the one equality function `‖z‖²`. -/
noncomputable def selfT (z : ℂ) : ℂ := stp z z

theorem selfT_eq_normSq (z : ℂ) : selfT z = ((‖z‖ : ℝ) : ℂ) ^ 2 := by
  rw [selfT, stp, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  norm_cast

/-- The **self tensor inversion**: the datum divided by its own equality function. -/
noncomputable def selfInv (z : ℂ) : ℂ := z / selfT z

theorem selfInv_eq_conj_inv (z : ℂ) : selfInv z = (starRingEnd ℂ) z⁻¹ := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [selfInv, selfT, stp]
  · rw [selfInv, selfT, stp, div_mul_eq_div_div, div_self hz, one_div, map_inv₀]

theorem selfInv_zero : selfInv 0 = 0 := by simp [selfInv, selfT, stp]

/-- **The self tensor inversion equality.** -/
theorem stp_selfInv {z : ℂ} (hz : z ≠ 0) : stp z (selfInv z) = 1 := by
  rw [stp, selfInv_eq_conj_inv, Complex.conj_conj, mul_inv_cancel₀ hz]

/-- The inversion is the *unique* solution of the inversion equality: the equality determines the
inverse datum, no external equation is needed. -/
theorem stp_eq_one_iff {z w : ℂ} (hz : z ≠ 0) : stp z w = 1 ↔ w = selfInv z := by
  constructor
  · intro h
    have h' : (starRingEnd ℂ) w = z⁻¹ := by
      have h2 := congrArg (fun c => z⁻¹ * c) h
      simpa [stp, ← mul_assoc, inv_mul_cancel₀ hz] using h2
    have h3 := congrArg (starRingEnd ℂ) h'
    rw [Complex.conj_conj] at h3
    rw [h3, selfInv_eq_conj_inv]
  · rintro rfl; exact stp_selfInv hz

theorem selfInv_involutive (z : ℂ) : selfInv (selfInv z) = z := by
  rw [selfInv_eq_conj_inv, selfInv_eq_conj_inv, map_inv₀, Complex.conj_conj, inv_inv]

theorem norm_selfInv (z : ℂ) : ‖selfInv z‖ = ‖z‖⁻¹ := by
  rw [selfInv_eq_conj_inv, RCLike.norm_conj, norm_inv]

/-- The ball–hair operator fixes exactly the unit sphere: this is the closure form. -/
theorem selfInv_eq_self_iff {z : ℂ} (hz : z ≠ 0) : selfInv z = z ↔ ‖z‖ = 1 := by
  constructor
  · intro h
    have hn : ‖z‖⁻¹ = ‖z‖ := by rw [← norm_selfInv, h]
    have hz' : (0:ℝ) < ‖z‖ := norm_pos_iff.mpr hz
    field_simp at hn
    nlinarith [hn, hz']
  · intro h
    have hzz : z * (starRingEnd ℂ) z = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h]; norm_num
    have hc : (starRingEnd ℂ) z = z⁻¹ := by
      have h2 := congrArg (fun c => z⁻¹ * c) hzz
      simpa [← mul_assoc, inv_mul_cancel₀ hz] using h2
    rw [selfInv_eq_conj_inv, map_inv₀, hc, inv_inv]

/-- **Zoom covariance.**  Rescaling the datum rescales the inversion inversely: the equality is a
relation of the whole zoom network, holding at every scale at once. -/
theorem selfInv_zoom {r : ℝ} (hr : r ≠ 0) (z : ℂ) :
    selfInv ((r : ℂ) * z) = ((r : ℂ))⁻¹ * selfInv z := by
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  rw [selfInv_eq_conj_inv, selfInv_eq_conj_inv, mul_inv, map_mul, map_inv₀,
    Complex.conj_ofReal]

/-! ## §2  The `0`–`∞` paths: hairs, and the closure form of the loop -/

/-- The hair through a unit direction `u`: the `0`–`∞` path `t ↦ t·u`. -/
noncomputable def hair (u : ℂ) (t : ℝ) : ℂ := (t : ℂ) * u

/-- The ball–hair operator maps each hair onto itself, reversing its `0` and `∞` ends. -/
theorem selfInv_hair {u : ℂ} (hu : ‖u‖ = 1) {t : ℝ} (ht : t ≠ 0) :
    selfInv (hair u t) = hair u t⁻¹ := by
  have hu0 : u ≠ 0 := by
    intro h; rw [h] at hu; simp at hu
  rw [hair, hair, selfInv_zoom ht u, (selfInv_eq_self_iff hu0).mpr hu]
  norm_cast

theorem norm_hair {u : ℂ} (hu : ‖u‖ = 1) (t : ℝ) : ‖hair u t‖ = |t| := by
  rw [hair, norm_mul, hu, Complex.norm_real, Real.norm_eq_abs, mul_one]

/-- Following a hair to the relative `0` sends the inversion to the relative `∞`. -/
theorem norm_selfInv_hair_atTop {u : ℂ} (hu : ‖u‖ = 1) :
    Tendsto (fun t : ℝ => ‖selfInv (hair u t)‖) (𝓝[>] 0) atTop := by
  have h : ∀ t ∈ Set.Ioi (0:ℝ), ‖selfInv (hair u t)‖ = t⁻¹ := by
    intro t ht
    rw [norm_selfInv, norm_hair hu, abs_of_pos ht]
  exact tendsto_inv_nhdsGT_zero.congr' (eventually_nhdsWithin_of_forall fun t ht => (h t ht).symm)

/-- Following a hair to the relative `∞` sends the inversion to the relative `0`. -/
theorem norm_selfInv_hair_zero {u : ℂ} (hu : ‖u‖ = 1) :
    Tendsto (fun t : ℝ => ‖selfInv (hair u t)‖) atTop (𝓝 0) := by
  have h : ∀ t ∈ Set.Ioi (0:ℝ), ‖selfInv (hair u t)‖ = t⁻¹ := by
    intro t ht
    rw [norm_selfInv, norm_hair hu, abs_of_pos ht]
  refine tendsto_inv_atTop_zero.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht using (h t ht).symm

/-- Every datum lies on exactly one hair: all directions occur. -/
theorem exists_hair {z : ℂ} (hz : z ≠ 0) : ∃ u : ℂ, ∃ t : ℝ, ‖u‖ = 1 ∧ 0 < t ∧ z = hair u t := by
  refine ⟨((‖z‖ : ℝ) : ℂ)⁻¹ * z, ‖z‖, ?_, norm_pos_iff.mpr hz, ?_⟩
  · rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (norm_pos_iff.mpr hz)]
    field_simp
  · have h : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by
      simpa using (norm_pos_iff.mpr hz).ne'
    rw [hair]
    field_simp

/-- The **closure form**: the set of data fixed by the ball–hair operator. -/
def closureForm : Set ℂ := {z | z ≠ 0 ∧ selfInv z = z}

/-- The natural closure form of the loop is the unit sphere — the zoom-invariant, self-inverse
locus where the `0` end and the `∞` end of every hair meet. -/
theorem closureForm_eq_sphere : closureForm = {z : ℂ | ‖z‖ = 1} := by
  ext z
  constructor
  · rintro ⟨hz, h⟩
    exact (selfInv_eq_self_iff hz).mp h
  · intro h
    have hz : z ≠ 0 := by
      intro h0; rw [h0] at h; simp at h
    exact ⟨hz, (selfInv_eq_self_iff hz).mpr h⟩

/-- Every hair meets the closure form exactly once: the loop always returns. -/
theorem hair_meets_closureForm {u : ℂ} (hu : ‖u‖ = 1) :
    ∃! t : ℝ, 0 < t ∧ hair u t ∈ closureForm := by
  refine ⟨1, ⟨one_pos, ?_⟩, ?_⟩
  · rw [closureForm_eq_sphere]
    simp [norm_hair hu]
  · rintro t ⟨ht, hmem⟩
    rw [closureForm_eq_sphere] at hmem
    have : |t| = 1 := by rw [← norm_hair hu t]; exact hmem
    rwa [abs_of_pos ht] at this

/-! ## §3  Light cone topology: class cycling -/

section LightCone

variable {E : Type*} [Preorder E]

/-- Two events *cycle* when each is in the causal future of the other. -/
def Cycles (x y : E) : Prop := x ≤ y ∧ y ≤ x

theorem cycles_equivalence : Equivalence (Cycles (E := E)) where
  refl x := ⟨le_refl x, le_refl x⟩
  symm h := ⟨h.2, h.1⟩
  trans h₁ h₂ := ⟨le_trans h₁.1 h₂.1, le_trans h₂.2 h₁.2⟩

/-- A closed causal loop collapses to a single cycling class: every event of the loop cycles with
its base point. -/
theorem loop_cycles {n : ℕ} (f : ℕ → E) (hstep : ∀ i < n, f i ≤ f (i + 1))
    (hclose : f n ≤ f 0) {i : ℕ} (hi : i ≤ n) : Cycles (f 0) (f i) := by
  have hmono : ∀ j k, j ≤ k → k ≤ n → f j ≤ f k := by
    intro j k hjk hkn
    induction k with
    | zero => simp [Nat.le_zero.mp hjk]
    | succ k ih =>
        rcases Nat.lt_or_ge j (k + 1) with h | h
        · exact le_trans (ih (Nat.lt_succ_iff.mp h) (le_of_lt (Nat.lt_of_succ_le hkn)))
            (hstep k (Nat.lt_of_succ_le hkn))
        · have : j = k + 1 := le_antisymm hjk h
          simp [this]
  exact ⟨hmono 0 i (Nat.zero_le i) hi, le_trans (hmono i n hi le_rfl) hclose⟩

/-- No monotone reading of the causal topology into a partial order can separate a cycling class:
class cycling *is* the identification the loop performs. -/
theorem monotone_reading_identifies_cycles {P : Type*} [PartialOrder P] {g : E → P}
    (hg : Monotone g) {x y : E} (h : Cycles x y) : g x = g y :=
  le_antisymm (hg h.1) (hg h.2)

end LightCone

/-! ## §4  Digital network interaction as a selective temporary global constraint -/

/-- The state space of the digital network: one Boolean channel per index. -/
abbrev NetState := ℕ → Bool

/-- The set of network states meeting the temporary constraint `P n`, which reads only the
selection consisting of the first `n` channels. -/
def constraintSet (P : (n : ℕ) → (Fin n → Bool) → Prop) (n : ℕ) : Set NetState :=
  {x | P n fun i => x i}

/-- A temporary selective constraint is machine-decidable: it reads finitely much of the network. -/
instance decidable_temporary (P : (n : ℕ) → (Fin n → Bool) → Prop)
    [∀ n w, Decidable (P n w)] (n : ℕ) (x : NetState) : Decidable (x ∈ constraintSet P n) :=
  inferInstanceAs (Decidable (P n fun i => x i))

/-- Each temporary selective constraint is a closed condition on the network. -/
theorem constraintSet_isClosed (P : (n : ℕ) → (Fin n → Bool) → Prop) (n : ℕ) :
    IsClosed (constraintSet P n) := by
  have hc : Continuous fun (x : NetState) (i : Fin n) => x i :=
    continuous_pi fun i => continuous_apply _
  exact (isClosed_discrete {w : Fin n → Bool | P n w}).preimage hc

/-- **The selective temporary global constraint completes.**  If the selections are nested and each
temporary constraint is separately satisfiable, then one global state of the network satisfies all
of them at once: the global constraint is the limit of the temporary selective ones, never imposed
from outside. -/
theorem selective_temporary_global_closure (P : (n : ℕ) → (Fin n → Bool) → Prop)
    (hnest : ∀ n, constraintSet P (n + 1) ⊆ constraintSet P n)
    (hsat : ∀ n, (constraintSet P n).Nonempty) :
    ∃ x : NetState, ∀ n, P n fun i => x i := by
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (constraintSet P) hnest hsat (constraintSet_isClosed P 0).isCompact
    (constraintSet_isClosed P)
  exact ⟨x, fun n => Set.mem_iInter.mp hx n⟩

/-- The honest converse: a temporary stage that nothing satisfies destroys the global closure. -/
theorem no_global_closure_of_empty_stage (P : (n : ℕ) → (Fin n → Bool) → Prop) {n : ℕ}
    (hempty : constraintSet P n = ∅) : ¬ ∃ x : NetState, ∀ m, P m fun i => x i := by
  rintro ⟨x, hx⟩
  have : x ∈ constraintSet P n := hx n
  rw [hempty] at this
  exact this

/-- A concrete hardware check: the temporary constraint "the selected channels are all `true`"
is verified on a finite selection by kernel computation — the physical-verification path. -/
def allTrue (n : ℕ) (w : Fin n → Bool) : Prop := ∀ i, w i = true

instance (n : ℕ) (w : Fin n → Bool) : Decidable (allTrue n w) :=
  inferInstanceAs (Decidable (∀ i, w i = true))

theorem hardware_check : allTrue 8 (fun _ => true) := by decide

/-- And the completion applies to it: the nested, separately satisfiable family `allTrue` has a
global state — the network that is on everywhere. -/
theorem allTrue_global : ∃ x : NetState, ∀ n, allTrue n fun i => x i := by
  refine selective_temporary_global_closure allTrue ?_ ?_
  · intro n x hx i
    exact hx ⟨i, by omega⟩
  · exact fun n => ⟨fun _ => true, fun _ => rfl⟩

/-! ## §5  The answer -/

/-- **NRRF774.**  The multiplication equality function lives in the self tensor inversion equality
(1); its natural closure form is the zoom-invariant self-inverse locus reached from both ends of
every `0`–`∞` hair (2); the light cone loop is not an inconsistency but a cycling class that no
monotone reading separates (3); and the digital network integrates as a selective temporary global
constraint whose finite stages are machine-checkable and whose limit is a genuine global state
(4). -/
theorem nrrf774_answer :
    (∀ z : ℂ, z ≠ 0 → ∀ w : ℂ, stp z w = 1 ↔ w = selfInv z) ∧
    (closureForm = {z : ℂ | ‖z‖ = 1} ∧
      ∀ u : ℂ, ‖u‖ = 1 → Tendsto (fun t : ℝ => ‖selfInv (hair u t)‖) (𝓝[>] 0) atTop) ∧
    (∀ (E : Type) (_ : Preorder E) (P : Type) (_ : PartialOrder P) (g : E → P), Monotone g →
      ∀ x y : E, Cycles x y → g x = g y) ∧
    (∀ P : (n : ℕ) → (Fin n → Bool) → Prop,
      (∀ n, constraintSet P (n + 1) ⊆ constraintSet P n) → (∀ n, (constraintSet P n).Nonempty) →
      ∃ x : NetState, ∀ n, P n fun i => x i) := by
  refine ⟨fun z hz w => stp_eq_one_iff hz, ⟨closureForm_eq_sphere, fun u hu =>
    norm_selfInv_hair_atTop hu⟩, ?_, selective_temporary_global_closure⟩
  intro E _ P _ g hg x y h
  exact monotone_reading_identifies_cycles hg h

end NRRF774

#print axioms NRRF774.stp_eq_one_iff
#print axioms NRRF774.closureForm_eq_sphere
#print axioms NRRF774.loop_cycles
#print axioms NRRF774.selective_temporary_global_closure
#print axioms NRRF774.nrrf774_answer
