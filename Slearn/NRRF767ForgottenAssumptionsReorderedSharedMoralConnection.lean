import Mathlib
import Slearn.NRRF764ConsciousCulturalMoralitySuperNetwork
import Slearn.NRRF766PublicInterfaceFullyInteractiveCollectiveArchitecture

/-!
# NRRF767 — Forgotten lessons, temporarily removed or reordered assumptions, and the shared
inherent structure in which we connect morally

The reading being formalised:

> When we forget the learned lessons of basic assumptions we may need to remove or reorder them
> temporarily, giving freedom to a shared understanding of the inherent structures remaining of our
> cultural force; only then can we connect in moral meaning.

The module continues `NRRF764ConsciousCulturalMoralitySuperNetwork` (its `Network` — the shared
interactive field of culture, morality and consciousness) and
`NRRF766PublicInterfaceFullyInteractiveCollectiveArchitecture` (its closure `Clo`), reusing them
rather than restating them.

Throughout, a **basic assumption** is an element of a type `α`, a set of assumptions carries the
**learned lessons** that close over it (`Clo.cl`, the consequence operator), and a *held* list of
assumptions carries, besides its content, an **order** in which they are held.

## §1  Forgetting the learned lessons

`Forgets` says the lessons actually in view fall strictly short of the lessons the assumptions
carry.  `forgetting_not_self_repairing` shows that forgetting is not repaired from inside what is
still seen: closing the seen lessons need not recover the forgotten ones.  So one has to go back to
the assumptions themselves — which is what §2 does.

## §2  Removing or reordering them, temporarily

`lessons_perm`: **reordering is free** — the lessons depend on the assumptions, not on the order in
which they are held, so any reordering (`lessons_reverse` in particular) may be performed at no
cost.  `understandings_subset_remove`: **removing gives freedom** — suspending an assumption can
only enlarge the space of understandings compatible with what is left, and
`exists_strictly_freer_removal` shows the enlargement can be strict.  `restore_removed` and
`restore_reordered`: both moves are **temporary** — putting the assumption back, or putting the
order back, returns exactly the lessons one started from, so nothing is destroyed by the
manoeuvre.

## §3  The inherent structure remaining — our cultural force

`remaining c S = ⋂ a ∈ S, c.cl (S \ {a})` is what still follows however any single assumption is
suspended.  `remaining_subset_cl`: it is part of the lessons; `remaining_subset_cl_erase`: it
survives every single suspension, so (`remaining_not_forced_by_one`) it is the force of no single
assumption — it is carried by the culture as a whole.  `remaining_perm` records again that it does
not depend on the order, and `exists_remaining_ssubset` that it is in general strictly less than
the whole body of lessons: what is dropped is exactly what hung on one assumption alone.

## §4  A shared understanding

Participants hold assumptions (`hold : P → Set α`).  `coreUnderstanding` is what every participant
still derives; `cl_common_subset_core` places the closure of the assumptions they all share inside
it, `core_subset_read` places it inside each participant's own understanding.
`core_of_suspensions` is the junction with §3: when the participants are exactly the temporary
suspensions of the single assumptions of `S`, their shared understanding **is** the inherent
structure remaining.

## §5  Only then can we connect in moral meaning

`moralNet` is a `NRRF764.Network` — a shared interactive field — whose readings are the
participants' understandings and whose admissibility is agreement on the shared core.
`moral_connect` is the connection: any two participants' understandings are admissible for one
another.  `moral_connect_iff` says exactly what the connection consists in: agreement on the
inherent structure remaining.  `rigid_disconnect` is the "only then": while participants who
demand agreement on the whole of their understandings need not connect at all, on the remaining
shared structure the very same participants do connect.  `suspension_moral_connect` reads this on
the suspension family of §3.

`nrrf767_answer` collects the reading in one theorem, and `nrrf767_answer_bool` instantiates it
concretely.
-/

namespace NRRF767

open NRRF764 NRRF766

universe u v

variable {α : Type u}

/-! ## §0  Assumptions, their order, and their learned lessons -/

/-- The assumptions a held list contains, forgetting the order in which they are held. -/
def base (l : List α) : Set α := {a | a ∈ l}

@[simp] theorem mem_base {l : List α} {a : α} : a ∈ base l ↔ a ∈ l := Iff.rfl

/-- Reordering the assumptions does not change which assumptions they are. -/
theorem base_perm {l l' : List α} (h : l.Perm l') : base l = base l' := by
  ext a; exact h.mem_iff

/-- The **learned lessons** of a body of assumptions: everything that follows from them. -/
def lessons (c : Clo (Set α)) (S : Set α) : Set α := c.cl S

/-- The assumptions are among their own lessons. -/
theorem subset_lessons (c : Clo (Set α)) (S : Set α) : S ⊆ lessons c S := c.le_cl S

theorem lessons_mono (c : Clo (Set α)) {S T : Set α} (h : S ⊆ T) : lessons c S ⊆ lessons c T :=
  c.mono h

/-- The lessons are already learned: closing them again adds nothing. -/
theorem lessons_idem (c : Clo (Set α)) (S : Set α) : lessons c (lessons c S) = lessons c S :=
  c.idem S

/-! ## §1  When we forget the learned lessons -/

/-- **Forgetting**: the lessons still in view fall strictly short of the lessons the assumptions
carry. -/
def Forgets (c : Clo (Set α)) (seen S : Set α) : Prop := seen ⊂ lessons c S

/-- The identity closure: every set is its own body of lessons.  A culture in which nothing is
derived beyond what is assumed — enough to exhibit the phenomena below. -/
def idClo (β : Type u) : Clo (Set β) where
  cl := id
  le_cl _ := le_rfl
  mono := monotone_id
  idem _ := rfl

@[simp] theorem idClo_cl (β : Type u) (S : Set β) : (idClo β).cl S = S := rfl

/-- **Forgetting is not repaired from inside what is still seen.**  There are assumptions and a
partial view of their lessons such that closing the seen lessons still does not recover the
forgotten ones: to get them back one has to return to the basic assumptions themselves. -/
theorem forgetting_not_self_repairing :
    ∃ (c : Clo (Set Bool)) (seen S : Set Bool),
      Forgets c seen S ∧ lessons c seen ⊂ lessons c S := by
  have h : ({true} : Set Bool) ⊂ ({true, false} : Set Bool) := by
    constructor
    · intro x hx; simp at hx; simp [hx]
    · intro hsub
      have : (false : Bool) ∈ ({true} : Set Bool) := hsub (by simp)
      simp at this
  exact ⟨idClo Bool, {true}, {true, false}, h, h⟩

/-! ## §2  Remove or reorder them, temporarily -/

/-- **Reordering is free.**  The lessons of a held list of assumptions depend only on which
assumptions are held, never on the order in which they are held. -/
theorem lessons_perm (c : Clo (Set α)) {l l' : List α} (h : l.Perm l') :
    lessons c (base l) = lessons c (base l') := by rw [base_perm h]

/-- In particular, holding the assumptions in the opposite order changes nothing. -/
theorem lessons_reverse (c : Clo (Set α)) (l : List α) :
    lessons c (base l.reverse) = lessons c (base l) :=
  lessons_perm c l.reverse_perm

/-- An **understanding** compatible with a body of assumptions: a closed body of lessons that
admits them all. -/
def understandings (c : Clo (Set α)) (S : Set α) : Set (Set α) := {U | c.Closed U ∧ S ⊆ U}

/-- The lessons themselves form an understanding. -/
theorem lessons_mem_understandings (c : Clo (Set α)) (S : Set α) :
    lessons c S ∈ understandings c S := ⟨c.closed_cl S, c.le_cl S⟩

/-- **Fewer assumptions, more freedom.** -/
theorem understandings_anti (c : Clo (Set α)) {S T : Set α} (h : S ⊆ T) :
    understandings c T ⊆ understandings c S := fun _ hU => ⟨hU.1, h.trans hU.2⟩

/-- **Removing an assumption gives freedom**: every understanding compatible with the assumptions
is still compatible once one of them is suspended, and there may be more. -/
theorem understandings_subset_remove (c : Clo (Set α)) (S : Set α) (a : α) :
    understandings c S ⊆ understandings c (S \ {a}) :=
  understandings_anti c Set.diff_subset

/-- The freedom gained can be strict: suspending an assumption really does open understandings
that were not available before. -/
theorem exists_strictly_freer_removal :
    ∃ (c : Clo (Set Bool)) (S : Set Bool) (a : Bool),
      understandings c S ⊂ understandings c (S \ {a}) := by
  refine ⟨idClo Bool, {true}, true, understandings_subset_remove _ _ _, ?_⟩
  intro h
  have hmem : (∅ : Set Bool) ∈ understandings (idClo Bool) ({true} \ {true}) := by
    refine ⟨rfl, ?_⟩
    intro x hx
    simp at hx
  have := (h hmem).2 (show (true : Bool) ∈ ({true} : Set Bool) by simp)
  simp at this

/-- **The removal is temporary.**  Putting the suspended assumption back returns exactly the
lessons one started from: nothing was destroyed by the suspension. -/
theorem restore_removed (c : Clo (Set α)) {S : Set α} {a : α} (ha : a ∈ S) :
    lessons c (insert a (S \ {a})) = lessons c S := by
  rw [lessons, lessons, Set.insert_diff_singleton, Set.insert_eq_of_mem ha]

/-- **The reordering is temporary too.**  Whatever order the assumptions are put through, putting
them back gives back the same lessons — indeed they never changed. -/
theorem restore_reordered (c : Clo (Set α)) {l l' : List α} (h : l.Perm l') :
    lessons c (base l') = lessons c (base l) := (lessons_perm c h).symm

/-! ## §3  The inherent structures remaining — our cultural force -/

/-- The **inherent structure remaining**: what still follows however any single basic assumption is
temporarily suspended. -/
def remaining (c : Clo (Set α)) (S : Set α) : Set α := ⋂ a ∈ S, c.cl (S \ {a})

theorem mem_remaining {c : Clo (Set α)} {S : Set α} {x : α} :
    x ∈ remaining c S ↔ ∀ a ∈ S, x ∈ c.cl (S \ {a}) := by
  simp [remaining]

/-- **It survives every single suspension.** -/
theorem remaining_subset_cl_erase (c : Clo (Set α)) {S : Set α} {a : α} (ha : a ∈ S) :
    remaining c S ⊆ c.cl (S \ {a}) := fun _ hx => mem_remaining.mp hx a ha

/-- What remains is part of what was learned. -/
theorem remaining_subset_cl (c : Clo (Set α)) {S : Set α} (h : S.Nonempty) :
    remaining c S ⊆ lessons c S := by
  obtain ⟨a, ha⟩ := h
  exact (remaining_subset_cl_erase c ha).trans (c.mono Set.diff_subset)

/-- **It is the force of no single assumption.**  No basic assumption is such that suspending it
takes the remaining structure away — that is what makes it *cultural* force rather than the weight
of any one thing assumed. -/
theorem remaining_not_forced_by_one (c : Clo (Set α)) (S : Set α) (a : α) (ha : a ∈ S)
    {x : α} (hx : x ∈ remaining c S) : x ∈ lessons c (S \ {a}) :=
  remaining_subset_cl_erase c ha hx

/-- The remaining structure does not depend on the order in which the assumptions are held. -/
theorem remaining_perm (c : Clo (Set α)) {l l' : List α} (h : l.Perm l') :
    remaining c (base l) = remaining c (base l') := by rw [base_perm h]

/-- What remains is in general strictly less than the whole body of lessons: whatever hung on a
single assumption alone does not survive its suspension. -/
theorem exists_remaining_ssubset :
    ∃ (c : Clo (Set Bool)) (S : Set Bool), remaining c S ⊂ lessons c S := by
  refine ⟨idClo Bool, Set.univ, ?_, ?_⟩
  · intro x _
    simp [lessons]
  · intro h
    have hx : (true : Bool) ∈ remaining (idClo Bool) Set.univ := h (by simp [lessons])
    have := mem_remaining.mp hx true (Set.mem_univ _)
    simp at this

/-! ## §4  A shared understanding -/

variable {P : Type v}

/-- The assumptions every participant holds. -/
def common (hold : P → Set α) : Set α := ⋂ p, hold p

/-- The **shared understanding**: the lessons every participant still derives, whatever else each
of them holds. -/
def coreUnderstanding (c : Clo (Set α)) (hold : P → Set α) : Set α := ⋂ p, c.cl (hold p)

theorem core_subset_read (c : Clo (Set α)) (hold : P → Set α) (p : P) :
    coreUnderstanding c hold ⊆ lessons c (hold p) := Set.iInter_subset _ p

/-- Everything derived from the assumptions everyone shares belongs to the shared understanding. -/
theorem cl_common_subset_core (c : Clo (Set α)) (hold : P → Set α) :
    lessons c (common hold) ⊆ coreUnderstanding c hold :=
  Set.subset_iInter fun p => c.mono (Set.iInter_subset _ p)

/-- **The junction with §3.**  When the participants are exactly the temporary suspensions of the
single basic assumptions, their shared understanding *is* the inherent structure remaining: the
freedom taken by removing assumptions one at a time is what makes the remaining structure
shared. -/
theorem core_of_suspensions (c : Clo (Set α)) (S : Set α) :
    coreUnderstanding c (fun a : S => S \ {(a : α)}) = remaining c S := by
  ext x
  simp only [coreUnderstanding, Set.mem_iInter, mem_remaining, Subtype.forall]

/-! ## §5  Only then can we connect in moral meaning -/

/-- The **moral field** of a body of participants: their understandings, read as one shared
interactive field in the sense of `NRRF764.Network`, in which two understandings are admissible for
one another exactly when they agree on the shared inherent structure. -/
def moralNet (c : Clo (Set α)) (hold : P → Set α) : Network P (Set α) where
  read p := lessons c (hold p)
  admits x y := x ∩ coreUnderstanding c hold = y ∩ coreUnderstanding c hold
  admits_refl _ := rfl
  admits_symm h := h.symm
  admits_trans h h' := h.trans h'
  shared p q := by
    rw [Set.inter_eq_self_of_subset_right (core_subset_read c hold p),
      Set.inter_eq_self_of_subset_right (core_subset_read c hold q)]

@[simp] theorem moralNet_read (c : Clo (Set α)) (hold : P → Set α) (p : P) :
    (moralNet c hold).read p = lessons c (hold p) := rfl

/-- **What the connection consists in**: agreement on the inherent structure remaining. -/
theorem moral_connect_iff (c : Clo (Set α)) (hold : P → Set α) (x y : Set α) :
    (moralNet c hold).admits x y ↔
      x ∩ coreUnderstanding c hold = y ∩ coreUnderstanding c hold := Iff.rfl

/-- **Then we connect in moral meaning.**  However differently the participants understand, their
understandings are admissible for one another in the moral field. -/
theorem moral_connect (c : Clo (Set α)) (hold : P → Set α) (p q : P) :
    (moralNet c hold).admits ((moralNet c hold).read p) ((moralNet c hold).read q) :=
  (moralNet c hold).shared p q

/-- On the suspension family of §3, the moral connection is agreement on `remaining c S`. -/
theorem suspension_moral_connect (c : Clo (Set α)) (S : Set α) (a b : S) :
    lessons c (S \ {(a : α)}) ∩ remaining c S = lessons c (S \ {(b : α)}) ∩ remaining c S := by
  have h := moral_connect c (fun a : S => S \ {(a : α)}) a b
  rwa [moral_connect_iff, core_of_suspensions] at h

/-- **Only then.**  Participants who demand agreement on the whole of their understandings need not
connect at all — their readings can differ; on the shared inherent structure that remains, those
very same participants do connect. -/
theorem rigid_disconnect :
    ∃ (c : Clo (Set Bool)) (hold : Bool → Set Bool),
      lessons c (hold true) ≠ lessons c (hold false) ∧
      ∀ p q, (moralNet c hold).admits ((moralNet c hold).read p) ((moralNet c hold).read q) := by
  refine ⟨idClo Bool, fun p => {p}, ?_, moral_connect _ _⟩
  intro h
  have hmem := congrArg (fun s : Set Bool => (true : Bool) ∈ s) h
  simp [lessons] at hmem

/-! ## The reading, in one theorem -/

/-- **When we forget the learned lessons of basic assumptions we may need to remove or reorder them
temporarily, giving freedom to a shared understanding of the inherent structures remaining of our
cultural force; only then can we connect in moral meaning.** -/
theorem nrrf767_answer (c : Clo (Set α)) (S : Set α) (hS : S.Nonempty) {a : α} (ha : a ∈ S)
    {l l' : List α} (hl : l.Perm l') (hold : P → Set α) (p q : P) :
    -- §1  forgetting the lessons is not repaired from inside what is still seen
    (∃ (d : Clo (Set Bool)) (seen T : Set Bool), Forgets d seen T ∧ lessons d seen ⊂ lessons d T) ∧
    -- §2  reordering is free, removing gives freedom, and both are temporary
    lessons c (base l) = lessons c (base l') ∧
    understandings c S ⊆ understandings c (S \ {a}) ∧
    (∃ (d : Clo (Set Bool)) (T : Set Bool) (b : Bool),
      understandings d T ⊂ understandings d (T \ {b})) ∧
    lessons c (insert a (S \ {a})) = lessons c S ∧
    lessons c (base l') = lessons c (base l) ∧
    -- §3  the inherent structure remaining is the force of no single assumption
    remaining c S ⊆ lessons c (S \ {a}) ∧
    remaining c S ⊆ lessons c S ∧
    remaining c (base l) = remaining c (base l') ∧
    -- §4  it is exactly the understanding shared by the temporary suspensions
    coreUnderstanding c (fun b : S => S \ {(b : α)}) = remaining c S ∧
    lessons c (common hold) ⊆ coreUnderstanding c hold ∧
    -- §5  and only there do we connect in moral meaning
    (moralNet c hold).admits ((moralNet c hold).read p) ((moralNet c hold).read q) ∧
    ((moralNet c hold).admits ((moralNet c hold).read p) ((moralNet c hold).read q) ↔
      lessons c (hold p) ∩ coreUnderstanding c hold =
        lessons c (hold q) ∩ coreUnderstanding c hold) ∧
    (∃ (d : Clo (Set Bool)) (h : Bool → Set Bool),
      lessons d (h true) ≠ lessons d (h false) ∧
      ∀ r s, (moralNet d h).admits ((moralNet d h).read r) ((moralNet d h).read s)) :=
  ⟨forgetting_not_self_repairing, lessons_perm c hl, understandings_subset_remove c S a,
    exists_strictly_freer_removal, restore_removed c ha, restore_reordered c hl,
    remaining_subset_cl_erase c ha, remaining_subset_cl c hS, remaining_perm c hl,
    core_of_suspensions c S, cl_common_subset_core c hold, moral_connect c hold p q,
    moral_connect_iff c hold _ _, rigid_disconnect⟩

/-- The reading, instantiated concretely: the assumptions are the booleans, the culture derives
nothing beyond what it assumes, and the participants hold one assumption each. -/
theorem nrrf767_answer_bool :
    (∃ (d : Clo (Set Bool)) (seen T : Set Bool), Forgets d seen T ∧ lessons d seen ⊂ lessons d T) ∧
    lessons (idClo Bool) (base [true, false]) = lessons (idClo Bool) (base [false, true]) ∧
    understandings (idClo Bool) Set.univ ⊆ understandings (idClo Bool) (Set.univ \ {true}) ∧
    (∃ (d : Clo (Set Bool)) (T : Set Bool) (b : Bool),
      understandings d T ⊂ understandings d (T \ {b})) ∧
    lessons (idClo Bool) (insert true (Set.univ \ {true})) = lessons (idClo Bool) Set.univ ∧
    lessons (idClo Bool) (base [false, true]) = lessons (idClo Bool) (base [true, false]) ∧
    remaining (idClo Bool) Set.univ ⊆ lessons (idClo Bool) (Set.univ \ {true}) ∧
    remaining (idClo Bool) Set.univ ⊆ lessons (idClo Bool) Set.univ ∧
    remaining (idClo Bool) (base [true, false]) = remaining (idClo Bool) (base [false, true]) ∧
    coreUnderstanding (idClo Bool) (fun b : (Set.univ : Set Bool) => Set.univ \ {(b : Bool)}) =
      remaining (idClo Bool) Set.univ ∧
    lessons (idClo Bool) (common (fun p : Bool => ({p} : Set Bool))) ⊆
      coreUnderstanding (idClo Bool) (fun p : Bool => ({p} : Set Bool)) ∧
    (moralNet (idClo Bool) (fun p : Bool => ({p} : Set Bool))).admits
      (lessons (idClo Bool) ({true} : Set Bool)) (lessons (idClo Bool) ({false} : Set Bool)) ∧
    ((moralNet (idClo Bool) (fun p : Bool => ({p} : Set Bool))).admits
        (lessons (idClo Bool) ({true} : Set Bool)) (lessons (idClo Bool) ({false} : Set Bool)) ↔
      lessons (idClo Bool) ({true} : Set Bool) ∩
          coreUnderstanding (idClo Bool) (fun p : Bool => ({p} : Set Bool)) =
        lessons (idClo Bool) ({false} : Set Bool) ∩
          coreUnderstanding (idClo Bool) (fun p : Bool => ({p} : Set Bool))) ∧
    (∃ (d : Clo (Set Bool)) (h : Bool → Set Bool),
      lessons d (h true) ≠ lessons d (h false) ∧
      ∀ r s, (moralNet d h).admits ((moralNet d h).read r) ((moralNet d h).read s)) :=
  nrrf767_answer (idClo Bool) Set.univ ⟨true, trivial⟩ (Set.mem_univ true)
    (l := [true, false]) (l' := [false, true]) (List.Perm.swap _ _ _)
    (fun p : Bool => ({p} : Set Bool)) true false

end NRRF767

/-! ## Axiom audit -/

#print axioms NRRF767.forgetting_not_self_repairing
#print axioms NRRF767.lessons_perm
#print axioms NRRF767.understandings_subset_remove
#print axioms NRRF767.exists_strictly_freer_removal
#print axioms NRRF767.restore_removed
#print axioms NRRF767.remaining_subset_cl
#print axioms NRRF767.remaining_not_forced_by_one
#print axioms NRRF767.exists_remaining_ssubset
#print axioms NRRF767.core_of_suspensions
#print axioms NRRF767.moral_connect
#print axioms NRRF767.rigid_disconnect
#print axioms NRRF767.nrrf767_answer
#print axioms NRRF767.nrrf767_answer_bool
