import Mathlib
import Slearn.NRRF764ConsciousCulturalMoralitySuperNetwork
import Slearn.NRRF766PublicInterfaceFullyInteractiveCollectiveArchitecture
import Slearn.NRRF767ForgottenAssumptionsReorderedSharedMoralConnection

/-!
# NRRF768 — Admissible reopening families, dependency order, and iterated reopening

`NRRF767` reopened inherited assumptions **one at a time**: its `remaining c S = ⋂ a ∈ S, cl (S \ {a})`
is a first-order robustness notion.  Three closures were left open there, and this module supplies
them.

## §1  Admissible reopening families

A `Reopening` assigns to each body of assumptions `S` a nonempty family `R.fam S` of *admissible
reopenings* of it: whole families of assumptions suspended at once, reordered, translated, or
jointly replaced.  The structure that survives all of them is

`remainingStar c R S = ⋂ T ∈ R.fam S, c.cl T`.

`remainingStar_singleRemoval` shows that NRRF767's single-assumption suspension is exactly the
special case `R = singleRemoval`, so nothing is lost; `remainingStar_anti_family` shows that
allowing more reopenings can only shrink the residue, `remainingStar_trivial` that reopening
nothing returns the whole body of lessons, and `remainingStar_powerset` that reopening *everything*
leaves only what needs no assumption at all.  `singleRemoval_subset_joint` places the joint
suspensions of `NRRF768` below NRRF767's single ones.

## §2  Content-preserving permutation versus meaning-changing dependency reorder

In NRRF767 reordering is free because closure sees only membership.  A `Reading` is an order-*aware*
reading of a held list of assumptions.  `membershipReading_orderFree` recovers the NRRF767 situation
(order is mere presentation); `exists_meaning_changing_reorder` shows that an order-aware reading
genuinely exists for which some permutation changes the cultural reading; and
`orderFree_iff_no_meaning_change` says the two notions exhaust each other: a reading is order-free
exactly when no permutation of assumptions is meaning-changing for it.

## §3  Iterated reopening — continual closure, not a final moral fixed point

The core produced by one round is itself a body of assumptions, and can be reopened again:
`iterate c R S n`.  On a closed body of assumptions and a relaxing family, the rounds form a
decreasing chain of closed cores (`iterate_antitone`).  `no_final_core` exhibits a culture in which
*every* round strictly reopens further — there is no final moral fixed point — while
`finite_stabilizes` shows that a finite culture must eventually come to rest.  `core_of_reopenings`
and `star_moral_connect` carry NRRF767's `core_of_suspensions` / `moral_connect_iff` over to the
general families, and `iterated_moral_connect` states that the moral connection is available at
every round of the iteration.
-/

namespace NRRF768

open NRRF764 NRRF766 NRRF767

universe u v

variable {α : Type u}

/-! ## §1  Admissible reopening families -/

/-- An **admissible reopening family**: for each body of assumptions `S`, the bodies `T ∈ fam S`
that may legitimately be put in its place — whole families of assumptions suspended at once,
reordered, translated, or jointly replaced.  Only nonemptiness is demanded: there is always at least
one admissible way to read the assumptions. -/
structure Reopening (α : Type u) where
  /-- The admissible reopenings of a body of assumptions. -/
  fam : Set α → Set (Set α)
  /-- Some reading is always admissible. -/
  fam_nonempty : ∀ S, (fam S).Nonempty

/-- A reopening is **relaxing** when every admissible reopening only suspends assumptions, never
adds new ones. -/
def Relaxing (R : Reopening α) : Prop := ∀ {S T : Set α}, T ∈ R.fam S → T ⊆ S

/-- The **inherent structure remaining** after all admissible reopenings:
`remaining* (S) = ⋂_{T ∈ R(S)} cl T`. -/
def remainingStar (c : Clo (Set α)) (R : Reopening α) (S : Set α) : Set α :=
  ⋂ T ∈ R.fam S, c.cl T

theorem mem_remainingStar {c : Clo (Set α)} {R : Reopening α} {S : Set α} {x : α} :
    x ∈ remainingStar c R S ↔ ∀ T ∈ R.fam S, x ∈ c.cl T := by
  simp [remainingStar]

/-- What remains survives each single admissible reopening. -/
theorem remainingStar_subset_cl {c : Clo (Set α)} {R : Reopening α} {S T : Set α}
    (hT : T ∈ R.fam S) : remainingStar c R S ⊆ c.cl T := fun _ hx => mem_remainingStar.mp hx T hT

/-- The residue is itself closed: it is a body of lessons, hence available as a new body of
assumptions for the next round. -/
theorem remainingStar_closed (c : Clo (Set α)) (R : Reopening α) (S : Set α) :
    c.Closed (remainingStar c R S) := by
  refine le_antisymm ?_ (c.le_cl _)
  refine Set.subset_iInter fun T => Set.subset_iInter fun hT => ?_
  have := c.mono (remainingStar_subset_cl (c := c) (R := R) (S := S) hT)
  simpa [c.idem] using this

/-- Everything derivable from the assumptions common to all admissible reopenings survives them. -/
theorem cl_iInter_subset_remainingStar (c : Clo (Set α)) (R : Reopening α) (S : Set α) :
    c.cl (⋂ T ∈ R.fam S, T) ⊆ remainingStar c R S :=
  Set.subset_iInter fun _ => Set.subset_iInter fun hT =>
    c.mono (Set.biInter_subset_of_mem hT)

/-- Enlarging the family of admissible reopenings can only shrink the residue: the more ways the
inherited assumptions may be reopened, the less survives. -/
theorem remainingStar_anti_family (c : Clo (Set α)) (R R' : Reopening α) (S : Set α)
    (h : R.fam S ⊆ R'.fam S) : remainingStar c R' S ⊆ remainingStar c R S :=
  Set.subset_iInter fun _ => Set.subset_iInter fun hT =>
    remainingStar_subset_cl (c := c) (R := R') (h hT)

/-- **Single-assumption suspension** (NRRF767) as a reopening family. -/
def singleRemoval (α : Type u) : Reopening α where
  fam S := insert S {T | ∃ a ∈ S, T = S \ {a}}
  fam_nonempty S := ⟨S, Set.mem_insert _ _⟩

/-- **NRRF767 is the special case.**  On a nonempty body of assumptions, the residue of the
single-removal family is exactly `NRRF767.remaining`. -/
theorem remainingStar_singleRemoval (c : Clo (Set α)) {S : Set α} (hS : S.Nonempty) :
    remainingStar c (singleRemoval α) S = NRRF767.remaining c S := by
  apply Set.Subset.antisymm
  · intro x hx
    refine NRRF767.mem_remaining.mpr fun a ha => ?_
    exact mem_remainingStar.mp hx (S \ {a}) (Set.mem_insert_of_mem _ ⟨a, ha, rfl⟩)
  · intro x hx
    refine mem_remainingStar.mpr fun T hT => ?_
    rcases hT with hT | ⟨a, ha, rfl⟩
    · subst hT
      exact NRRF767.remaining_subset_cl c hS hx
    · exact NRRF767.mem_remaining.mp hx a ha

/-- **Reopening nothing.**  If the only admissible reading of the assumptions is the inherited one,
the residue is the whole body of lessons: no reopening, no discovery. -/
def trivialReopening (α : Type u) : Reopening α where
  fam S := {S}
  fam_nonempty S := ⟨S, rfl⟩

theorem remainingStar_trivial (c : Clo (Set α)) (S : Set α) :
    remainingStar c (trivialReopening α) S = c.cl S := by
  simp [remainingStar, trivialReopening]

/-- **Reopening everything.**  If every subfamily of the inherited assumptions may be suspended at
once, all that remains is what needs no assumption at all. -/
def powersetReopening (α : Type u) : Reopening α where
  fam S := {T | T ⊆ S}
  fam_nonempty S := ⟨S, Set.Subset.rfl⟩

theorem remainingStar_powerset (c : Clo (Set α)) (S : Set α) :
    remainingStar c (powersetReopening α) S = c.cl ∅ := by
  apply Set.Subset.antisymm
  · exact remainingStar_subset_cl (c := c) (R := powersetReopening α)
      (S := S) (Set.empty_subset S)
  · exact Set.subset_iInter fun T => Set.subset_iInter fun _ => c.mono (Set.empty_subset T)

/-- **Joint suspension**: whole families `A` of assumptions, drawn from an admissible catalogue `F`
of suspensions, are reopened at once. -/
def jointSuspension (F : Set (Set α)) : Reopening α where
  fam S := insert S {T | ∃ A ∈ F, T = S \ A}
  fam_nonempty S := ⟨S, Set.mem_insert _ _⟩

theorem jointSuspension_relaxing (F : Set (Set α)) : Relaxing (jointSuspension F) := by
  rintro S T (rfl | ⟨A, -, rfl⟩)
  · exact Set.Subset.rfl
  · exact Set.diff_subset

/-- **Single removal is a special case of joint suspension**, so the joint residue is contained in
the NRRF767 one: suspending families jointly is at least as demanding as suspending one at a
time. -/
theorem singleRemoval_subset_joint (c : Clo (Set α)) (F : Set (Set α)) {S : Set α}
    (hS : S.Nonempty) (hF : ∀ a ∈ S, ({a} : Set α) ∈ F) :
    remainingStar c (jointSuspension F) S ⊆ NRRF767.remaining c S := by
  rw [← remainingStar_singleRemoval c hS]
  refine remainingStar_anti_family c (singleRemoval α) (jointSuspension F) S ?_
  rintro T (rfl | ⟨a, ha, rfl⟩)
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ ⟨{a}, hF a ha, rfl⟩

/-! ## §2  Content-preserving permutation versus meaning-changing dependency reorder -/

/-- An **order-aware reading** of a held list of assumptions: it must admit the assumptions it
reads, but it may depend on the order in which they are held (causal or interpretive dependency). -/
structure Reading (α : Type u) where
  /-- The cultural reading of a held, ordered list of assumptions. -/
  read : List α → Set α
  /-- A reading admits the assumptions it reads. -/
  le_read : ∀ l, NRRF767.base l ⊆ read l

/-- A reading is **order-free** when order is mere presentation. -/
def OrderFree (d : Reading α) : Prop := ∀ {l l' : List α}, l.Perm l' → d.read l = d.read l'

/-- A permutation is **content-preserving** for a reading when it leaves the reading unchanged. -/
def ContentPreserving (d : Reading α) (l l' : List α) : Prop := l.Perm l' ∧ d.read l = d.read l'

/-- A permutation is a **meaning-changing dependency reorder** when the same assumptions, held in a
different order, are read differently. -/
def MeaningChanging (d : Reading α) (l l' : List α) : Prop := l.Perm l' ∧ d.read l ≠ d.read l'

/-- No permutation is both. -/
theorem not_both (d : Reading α) (l l' : List α) :
    ¬ (ContentPreserving d l l' ∧ MeaningChanging d l l') := by
  rintro ⟨⟨-, h⟩, ⟨-, h'⟩⟩; exact h' h

/-- Every permutation is one or the other. -/
theorem contentPreserving_or_meaningChanging (d : Reading α) {l l' : List α} (h : l.Perm l') :
    ContentPreserving d l l' ∨ MeaningChanging d l l' := by
  by_cases hd : d.read l = d.read l'
  · exact Or.inl ⟨h, hd⟩
  · exact Or.inr ⟨h, hd⟩

/-- The **NRRF767 situation**: a reading that closes the mere membership of the list is order-free —
there, reordering was free precisely because closure depends only on membership. -/
def membershipReading (c : Clo (Set α)) : Reading α where
  read l := c.cl (NRRF767.base l)
  le_read _ := c.le_cl _

theorem membershipReading_orderFree (c : Clo (Set α)) : OrderFree (membershipReading c) := by
  intro l l' h
  simp [membershipReading, NRRF767.base_perm h]

/-- **Order can genuinely create a new cultural reading.**  There is an order-aware reading and a
permutation of the very same assumptions under which the reading changes: with interpretive
dependency, the assumption held first governs how the rest are read. -/
theorem exists_meaning_changing_reorder :
    ∃ (d : Reading ℕ) (l l' : List ℕ), MeaningChanging d l l' := by
  refine ⟨⟨fun l => if l.head? = some 0 then Set.univ else NRRF767.base l, ?_⟩,
    [0, 1], [1, 0], List.Perm.swap _ _ _, ?_⟩
  · intro l a ha
    by_cases h : l.head? = some 0 <;> simp [h, ha]
  · intro h
    have hmem := congrArg (fun s : Set ℕ => (2 : ℕ) ∈ s) h
    simp [NRRF767.base] at hmem

/-- **The dichotomy is exact**: a reading is order-free exactly when it admits no meaning-changing
dependency reorder. -/
theorem orderFree_iff_no_meaning_change (d : Reading α) :
    OrderFree d ↔ ∀ l l', ¬ MeaningChanging d l l' := by
  constructor
  · rintro hd l l' ⟨hp, hne⟩; exact hne (hd hp)
  · intro h l l' hp
    rcases contentPreserving_or_meaningChanging d hp with ⟨-, hc⟩ | hm
    · exact hc
    · exact absurd hm (h l l')

/-- For an order-free reading, every permutation is content-preserving. -/
theorem orderFree_contentPreserving {d : Reading α} (hd : OrderFree d) {l l' : List α}
    (h : l.Perm l') : ContentPreserving d l l' := ⟨h, hd h⟩

/-! ## §3  Iterated reopening -/

/-- One **round of reopening**: the inherited assumptions are replaced by what survives all their
admissible reopenings. -/
def reopenStep (c : Clo (Set α)) (R : Reopening α) (S : Set α) : Set α := remainingStar c R S

/-- **Iterated reopening**: the core produced by one round is itself an assumption structure,
subject to reopening in the next. -/
def iterate (c : Clo (Set α)) (R : Reopening α) (S : Set α) : ℕ → Set α
  | 0 => S
  | n + 1 => reopenStep c R (iterate c R S n)

@[simp] theorem iterate_zero (c : Clo (Set α)) (R : Reopening α) (S : Set α) :
    iterate c R S 0 = S := rfl

@[simp] theorem iterate_succ (c : Clo (Set α)) (R : Reopening α) (S : Set α) (n : ℕ) :
    iterate c R S (n + 1) = reopenStep c R (iterate c R S n) := rfl

/-- Every round after the first produces a closed core. -/
theorem iterate_closed (c : Clo (Set α)) (R : Reopening α) (S : Set α) (n : ℕ) :
    c.Closed (iterate c R S (n + 1)) := remainingStar_closed c R _

/-- A round of a relaxing reopening never adds to a closed body of assumptions. -/
theorem reopenStep_subset (c : Clo (Set α)) {R : Reopening α} (hR : Relaxing R) {S : Set α}
    (hS : c.Closed S) : reopenStep c R S ⊆ S := by
  obtain ⟨T, hT⟩ := R.fam_nonempty S
  have h1 : reopenStep c R S ⊆ c.cl T := remainingStar_subset_cl hT
  have h2 : c.cl T ⊆ c.cl S := c.mono (hR hT)
  exact fun x hx => hS ▸ h2 (h1 hx)

/-- **The rounds form a decreasing chain**: continual reopening never recovers what an earlier
round has already let go. -/
theorem iterate_succ_subset (c : Clo (Set α)) {R : Reopening α} (hR : Relaxing R) {S : Set α}
    (hS : c.Closed S) (n : ℕ) : iterate c R S (n + 1) ⊆ iterate c R S n := by
  induction n with
  | zero => exact reopenStep_subset c hR hS
  | succ n _ => exact reopenStep_subset c hR (iterate_closed c R S n)

theorem iterate_antitone (c : Clo (Set α)) {R : Reopening α} (hR : Relaxing R) {S : Set α}
    (hS : c.Closed S) : Antitone (iterate c R S) := by
  refine antitone_nat_of_succ_le fun n => ?_
  exact iterate_succ_subset c hR hS n

/-- A **final moral fixed point** of the reopening: a core that reopening no longer changes. -/
def FinalCore (c : Clo (Set α)) (R : Reopening α) (S : Set α) : Prop := reopenStep c R S = S

/-- Reopening nothing makes every closed body of lessons a final core — a culture that never
reopens has already finished. -/
theorem finalCore_trivial (c : Clo (Set α)) {S : Set α} (hS : c.Closed S) :
    FinalCore c (trivialReopening α) S := by
  simpa [FinalCore, reopenStep, remainingStar_trivial] using hS

/-- The reopening that always suspends the least assumption still in play. -/
def leastSuspension : Reopening ℕ where
  fam S := {S \ {sInf S}}
  fam_nonempty _ := ⟨_, rfl⟩

theorem leastSuspension_relaxing : Relaxing leastSuspension := by
  rintro S T rfl; exact Set.diff_subset

theorem sInf_Ici (n : ℕ) : sInf (Set.Ici n) = n :=
  le_antisymm (Nat.sInf_le Set.self_mem_Ici) (Nat.sInf_mem ⟨n, Set.self_mem_Ici⟩)

/-- The residue of a reopening family with a single admissible reading. -/
theorem remainingStar_of_fam_singleton (c : Clo (Set α)) (R : Reopening α) {S X : Set α}
    (h : R.fam S = {X}) : remainingStar c R S = c.cl X := by
  rw [remainingStar, h]; simp

theorem iterate_leastSuspension (n : ℕ) :
    iterate (NRRF767.idClo ℕ) leastSuspension Set.univ n = Set.Ici n := by
  induction n with
  | zero => ext k; simp
  | succ n ih =>
      have hstep : iterate (NRRF767.idClo ℕ) leastSuspension Set.univ (n + 1)
          = Set.Ici n \ {sInf (Set.Ici n)} := by
        rw [iterate_succ, ih]
        simpa [reopenStep] using
          remainingStar_of_fam_singleton (NRRF767.idClo ℕ) leastSuspension
            (S := Set.Ici n) (X := Set.Ici n \ {sInf (Set.Ici n)}) rfl
      rw [hstep, sInf_Ici]
      ext k
      simp [Set.mem_Ici]

/-- **There need be no final moral fixed point.**  There is a culture, and an admissible relaxing
reopening of it, in which every single round strictly reopens further: the shared core produced by
one round becomes, in the next, an assumption structure that is itself reopened.  Cultural closure
is continual, not terminal. -/
theorem no_final_core :
    ∃ (c : Clo (Set ℕ)) (R : Reopening ℕ) (S : Set ℕ), Relaxing R ∧ c.Closed S ∧
      ∀ n, iterate c R S (n + 1) ⊂ iterate c R S n := by
  refine ⟨NRRF767.idClo ℕ, leastSuspension, Set.univ, leastSuspension_relaxing, rfl, fun n => ?_⟩
  rw [iterate_leastSuspension, iterate_leastSuspension]
  constructor
  · intro k hk; exact le_of_lt (Nat.lt_of_succ_le hk)
  · intro h
    have : n ∈ Set.Ici (n + 1) := h Set.self_mem_Ici
    simp at this

/-- **A finite culture must come to rest.**  When there are only finitely many possible assumptions,
the chain of reopenings stabilises: some round is already a final core. -/
theorem finite_stabilizes [Finite α] (c : Clo (Set α)) {R : Reopening α} (hR : Relaxing R)
    {S : Set α} (hS : c.Closed S) : ∃ n, iterate c R S (n + 1) = iterate c R S n := by
  by_contra hcon
  push_neg at hcon
  have hstrict : ∀ n, (iterate c R S (n + 1)).ncard < (iterate c R S n).ncard := by
    intro n
    exact Set.ncard_lt_ncard ⟨iterate_succ_subset c hR hS n, fun h =>
      hcon n (Set.Subset.antisymm (iterate_succ_subset c hR hS n) h)⟩ (Set.toFinite _)
  have hdec : ∀ n, (iterate c R S n).ncard + n ≤ (iterate c R S 0).ncard := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => have := hstrict n; omega
  have := hdec ((iterate c R S 0).ncard + 1)
  omega

/-! ### The moral connection, across general reopenings and across rounds -/

/-- **The shared core of the admissible reopenings.**  Generalising NRRF767's `core_of_suspensions`:
the understanding shared by all the admissible reopenings of `S` is exactly `remainingStar`.  The
shared core is not imposed in advance — it is discovered by allowing the assumptions to be reopened
and observing what stays derivable. -/
theorem core_of_reopenings (c : Clo (Set α)) (R : Reopening α) (S : Set α) :
    NRRF767.coreUnderstanding c (fun T : R.fam S => (T : Set α)) = remainingStar c R S := by
  ext x
  simp only [NRRF767.coreUnderstanding, Set.mem_iInter, mem_remainingStar, Subtype.forall]

/-- **Moral connection on the general residue.**  Two participants who read the culture through
admissible reopenings are connected exactly when their understandings agree on the residue
`remainingStar` — not when their whole understandings coincide. -/
theorem star_moral_connect_iff (c : Clo (Set α)) (R : Reopening α) (S : Set α) (x y : Set α) :
    (NRRF767.moralNet c (fun T : R.fam S => (T : Set α))).admits x y ↔
      x ∩ remainingStar c R S = y ∩ remainingStar c R S := by
  rw [NRRF767.moral_connect_iff, core_of_reopenings]

/-- Any two admissible reopenings do connect there. -/
theorem star_moral_connect (c : Clo (Set α)) (R : Reopening α) (S : Set α) (T T' : R.fam S) :
    c.cl (T : Set α) ∩ remainingStar c R S = c.cl (T' : Set α) ∩ remainingStar c R S := by
  have h := NRRF767.moral_connect c (fun T : R.fam S => (T : Set α)) T T'
  rwa [NRRF767.moral_connect_iff, core_of_reopenings] at h

/-- **The connection is available at every round.**  Iterated reopening does not exhaust the moral
field: at each stage the participants of that stage still connect on the residue that stage
leaves. -/
theorem iterated_moral_connect (c : Clo (Set α)) (R : Reopening α) (S : Set α) (n : ℕ)
    (T T' : R.fam (iterate c R S n)) :
    c.cl (T : Set α) ∩ iterate c R S (n + 1) = c.cl (T' : Set α) ∩ iterate c R S (n + 1) := by
  simpa [iterate_succ, reopenStep] using star_moral_connect c R (iterate c R S n) T T'

/-! ## The reading, in one theorem -/

/-- **Reopening the inherited assumptions in whole admissible families, distinguishing free
reordering from dependency reorder, and iterating the reopening so that each shared core becomes,
in turn, the assumptions of the next round.** -/
theorem nrrf768_answer (c : Clo (Set α)) (R : Reopening α) (hR : Relaxing R) (S : Set α)
    (hS : S.Nonempty) (hSc : c.Closed S) (F : Set (Set α)) (hF : ∀ a ∈ S, ({a} : Set α) ∈ F)
    (n : ℕ) (T T' : R.fam S) :
    -- §1  general admissible reopening families, with NRRF767 as the special case
    remainingStar c (singleRemoval α) S = NRRF767.remaining c S ∧
    remainingStar c (trivialReopening α) S = c.cl S ∧
    remainingStar c (powersetReopening α) S = c.cl ∅ ∧
    remainingStar c (jointSuspension F) S ⊆ NRRF767.remaining c S ∧
    c.Closed (remainingStar c R S) ∧
    -- §2  free reordering versus meaning-changing dependency reorder
    OrderFree (membershipReading c) ∧
    (∃ (d : Reading ℕ) (l l' : List ℕ), MeaningChanging d l l') ∧
    (∀ d : Reading α, OrderFree d ↔ ∀ l l', ¬ MeaningChanging d l l') ∧
    -- §3  iterated reopening: a decreasing chain, with no final fixed point in general
    Antitone (iterate c R S) ∧
    (∃ (d : Clo (Set ℕ)) (R' : Reopening ℕ) (T : Set ℕ), Relaxing R' ∧ d.Closed T ∧
      ∀ m, iterate d R' T (m + 1) ⊂ iterate d R' T m) ∧
    -- §4  the shared core is what survives the reopenings, and the moral connection lives there
    NRRF767.coreUnderstanding c (fun T : R.fam S => (T : Set α)) = remainingStar c R S ∧
    (∀ x y : Set α, (NRRF767.moralNet c (fun T : R.fam S => (T : Set α))).admits x y ↔
      x ∩ remainingStar c R S = y ∩ remainingStar c R S) ∧
    c.cl (T : Set α) ∩ remainingStar c R S = c.cl (T' : Set α) ∩ remainingStar c R S ∧
    (∀ U U' : R.fam (iterate c R S n),
      c.cl (U : Set α) ∩ iterate c R S (n + 1) = c.cl (U' : Set α) ∩ iterate c R S (n + 1)) :=
  ⟨remainingStar_singleRemoval c hS, remainingStar_trivial c S, remainingStar_powerset c S,
    singleRemoval_subset_joint c F hS hF, remainingStar_closed c R S,
    membershipReading_orderFree c, exists_meaning_changing_reorder,
    fun d => orderFree_iff_no_meaning_change d, iterate_antitone c hR hSc, no_final_core,
    core_of_reopenings c R S, star_moral_connect_iff c R S, star_moral_connect c R S T T',
    iterated_moral_connect c R S n⟩

/-! ## Axiom audit -/

#print axioms remainingStar_singleRemoval
#print axioms remainingStar_powerset
#print axioms singleRemoval_subset_joint
#print axioms membershipReading_orderFree
#print axioms exists_meaning_changing_reorder
#print axioms orderFree_iff_no_meaning_change
#print axioms iterate_antitone
#print axioms no_final_core
#print axioms finite_stabilizes
#print axioms core_of_reopenings
#print axioms star_moral_connect_iff
#print axioms iterated_moral_connect
#print axioms nrrf768_answer

end NRRF768
