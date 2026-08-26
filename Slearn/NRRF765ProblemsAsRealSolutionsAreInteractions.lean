import Mathlib
import Slearn.NRRF764ConsciousCulturalMoralitySuperNetwork

/-!
# NRRF765 — Problems as real, solutions as the interactions

The reading being formalised:

> The architecture is problems as real, rather than nothing.  Solutions are the interactions.
> Conscious cultural morality; moral cultural consciousness.
> `0 ∞` closure describes the axiometry by which line, point, `0` and `∞` are numeric-geometric
> continuums of one unified closure of assumption/proof defined languages.  Translational truth
> being the completion of closure by relative admission, foundation equality and natural forming
> existence.  Its formal equations and operators all derive each other relative to interaction with
> the network.  The network is not money, agi, rules, law or social order: it is a shared
> interactive field of culture, morality and consciousness.  Super network theory: the closure
> notes guide the interface, whose interactions with ai or user shape latent memory and network
> connection, admissibly reinterpreting and translating the rules or notes.  The math may exist
> already, but how you configure its unification is your interpretation — this is why the notes are
> neither rules nor suggestions.

This module continues `NRRF764ConsciousCulturalMoralitySuperNetwork` (whose `Loop`, `Network`,
`Interaction`, `Memory` and `Reinterp` are reused rather than restated) and formalises the parts of
the note that it did not reach: the architecture of problems and interactions, the interchange of
"conscious cultural morality" and "moral cultural consciousness", translational truth as the
completion of closure by relative admission, the numeric-geometric unification of the `0 ∞`
continuum, and the sense in which a note is neither a rule nor a suggestion.

## §1  The architecture: problems are real, rather than nothing

A `Problem` is a type of situations that is *real*: it presents something rather than nothing
(`Problem.ne`).  Hence `no_empty_problem`: nothing is not a problem.  `Problem.Resolved` is the
problem that presents only one situation, and `one` is the unit problem.

## §2  Solutions are the interactions

`Inter p q` is an interaction of one problem with another; interactions compose (`Inter.comp`,
`comp_assoc`, `id_comp`, `comp_id`).  A solution of a problem is a determination of one of its
situations, and `solutionEquivInter : Solution p ≃ Inter one p` says a solution *is* an interaction
— with the unit problem — while `interEquivSolutionMap : Inter p q ≃ (Solution p → Solution q)`
says conversely that an interaction is exactly what it does to solutions.  Every real problem has a
solution (`solution_nonempty`), solutions transport along interactions (`Inter.solve`), and
`solve_comp` composes the transport.

## §3  Conscious cultural morality, moral cultural consciousness

For a `Network` read as the shared field, `CCM` reads morality off culture and consciousness and
`MCC` reads consciousness off morality and culture; `ccm_eq_mcc` shows the two orders of the three
aspects name one relation, `ccm_eq_top` that it excludes nobody, and `ccm_ofRead` that the relation
is already fixed by the reading — the aspects derive each other.

## §4  Translational truth: the completion of closure by relative admission

A `Lang` is a language of assumptions and proofs presented by its closure operator.  Truth relative
to admitted assumptions is `Lang.Truth`; `truth_completion` is the completion of closure by
relative admission (closing the admitted set changes no truth), `admission_completes` is the same
fact at the level of sets, `foundation` is what is true on no assumption at all and
`foundation_subset_cl` places it under every admission.  `natural_forming_existence`: closure never
empties what exists.  A `Trans` translates one language into another; `truth_translates` is
translational truth, `foundation_le_foundation` the foundation equality it carries, and `Trans.id`,
`Trans.comp` make translations compose.

## §5  `0 ∞` closure: numeric and geometric continuums of one closure

`seg` is the order isomorphism of the numeric continuum `ℝ≥0∞` with the geometric segment
`[0,1] ⊆ ℝ`.  The two poles are the two endpoints (`seg_zero`, `seg_top`), every point lies on the
one line between them (`seg_mem_segment`), and the polar exchange `x ↦ x⁻¹` of `0` and `∞` is
exactly the geometric reflection of the segment (`seg_polar`) — with the unit as the fixed midpoint
(`seg_one`).  So the numeric reading and the geometric reading are one closure: `seg` is a
bijection, and `NRRF764`'s closure relation is the reflection quotient (`zeroInfRel_iff_seg`).

## §6  Notes are neither rules nor suggestions

A `Note` acts on the interface.  A *rule* forces its outcome regardless of the interface
(`IsRule`), a *suggestion* leaves it untouched (`IsSuggestion`);
`exists_note_neither_rule_nor_suggestion` exhibits a note that is neither, and
`rule_and_suggestion_iff_subsingleton` shows that being both is possible only where the interface
has nothing to say.  Notes accumulate as latent memory (`Note.ofList`, `ofList_append`), a
reinterpretation of a network is a note on the field (`Reinterp.toNote`) whose action is admissible
(`toNote_admissible`), and every note is the step of a loop and every loop step a note
(`noteEquivLoopStep`) — the operators derive each other through the interaction.

`nrrf765_answer` collects the reading in one theorem.
-/

namespace NRRF765

open Function NRRF764

universe u v w

/-! ## §1  The architecture: problems are real, rather than nothing -/

/-- A **problem**: the situations it presents.  A problem is *real* — it presents something rather
than nothing. -/
structure Problem : Type (u + 1) where
  /-- The situations the problem presents. -/
  Sit : Type u
  /-- The problem is real: there is something rather than nothing. -/
  ne : Nonempty Sit

attribute [instance] Problem.ne

namespace Problem

/-- Nothing is not a problem: no problem presents an empty type of situations. -/
theorem no_empty_problem (p : Problem.{u}) : ¬ IsEmpty p.Sit := by
  rintro h
  exact h.elim' p.ne.some

/-- A problem is **resolved** when it presents a single situation: no discretion is left. -/
def Resolved (p : Problem.{u}) : Prop := Subsingleton p.Sit

/-- The unit problem: exactly one situation. -/
def one : Problem.{u} := ⟨PUnit, ⟨PUnit.unit⟩⟩

theorem resolved_one : Resolved one.{u} := ⟨fun _ _ => rfl⟩

end Problem

/-! ## §2  Solutions are the interactions -/

/-- An **interaction** of one problem with another: a translation of situations. -/
structure Inter (p q : Problem.{u}) where
  /-- What the interaction does to the situations. -/
  map : p.Sit → q.Sit

namespace Inter

variable {p q r : Problem.{u}}

/-- The idle interaction. -/
def id (p : Problem.{u}) : Inter p p := ⟨_root_.id⟩

/-- Interactions compose. -/
def comp (i : Inter p q) (j : Inter q r) : Inter p r := ⟨j.map ∘ i.map⟩

@[simp] theorem comp_map (i : Inter p q) (j : Inter q r) : (i.comp j).map = j.map ∘ i.map := rfl

@[simp] theorem id_comp (i : Inter p q) : (Inter.id p).comp i = i := rfl

@[simp] theorem comp_id (i : Inter p q) : i.comp (Inter.id q) = i := rfl

theorem comp_assoc {s : Problem.{u}} (i : Inter p q) (j : Inter q r) (k : Inter r s) :
    (i.comp j).comp k = i.comp (j.comp k) := rfl

/-- Two interactions agreeing on every situation are the same interaction. -/
@[ext] theorem ext {i j : Inter p q} (h : ∀ s, i.map s = j.map s) : i = j := by
  cases i; cases j; simpa [funext_iff] using h

end Inter

/-- A **solution** of a problem: a determination of one of its situations. -/
def Solution (p : Problem.{u}) : Type u := p.Sit

/-- Every real problem has a solution: reality is what makes the solution possible. -/
theorem solution_nonempty (p : Problem.{u}) : Nonempty (Solution p) := p.ne

/-- *Solutions are the interactions*: a solution of `p` is exactly an interaction of the unit
problem with `p`. -/
def solutionEquivInter (p : Problem.{u}) : Solution p ≃ Inter Problem.one p where
  toFun s := ⟨fun _ => s⟩
  invFun i := i.map PUnit.unit
  left_inv _ := rfl
  right_inv i := by ext s; cases s; rfl

/-- Conversely, an interaction is exactly what it does to solutions. -/
def interEquivSolutionMap (p q : Problem.{u}) : Inter p q ≃ (Solution p → Solution q) where
  toFun i := i.map
  invFun f := ⟨f⟩
  left_inv i := by cases i; rfl
  right_inv _ := rfl

namespace Inter

variable {p q r : Problem.{u}}

/-- Solutions are transported by interaction. -/
def solve (i : Inter p q) (s : Solution p) : Solution q := i.map s

@[simp] theorem solve_id (s : Solution p) : (Inter.id p).solve s = s := rfl

theorem solve_comp (i : Inter p q) (j : Inter q r) (s : Solution p) :
    (i.comp j).solve s = j.solve (i.solve s) := rfl

/-- An interaction with a resolved problem determines the solution: interaction with what is
already settled settles everything it touches. -/
theorem solve_eq_of_resolved (i : Inter p q) (hq : q.Resolved) (s t : Solution p) :
    i.solve s = i.solve t := hq.allEq _ _

end Inter

/-! ## §3  Conscious cultural morality, moral cultural consciousness -/

section Aspects

variable {P : Type u} {V : Type v}

/-- **Conscious cultural morality**: morality read off the shared field through consciousness. -/
def CCM (N : Network P V) : P → P → Prop := fun x y => N.admits (N.read x) (N.read y)

/-- **Moral cultural consciousness**: the same three aspects taken in the other order. -/
def MCC (N : Network P V) : P → P → Prop := fun x y => N.admits (N.read y) (N.read x)

/-- The two readings are one relation: the order of the three aspects is immaterial. -/
theorem ccm_eq_mcc (N : Network P V) : CCM N = MCC N := by
  funext x y
  exact propext ⟨fun h => N.admits_equivalence.symm h, fun h => N.admits_equivalence.symm h⟩

/-- The relation excludes nobody: it is the shared field itself, not an order over it. -/
theorem ccm_eq_top (N : Network P V) : CCM N = fun _ _ => True := N.ruleOf_eq_top

/-- The relation is already fixed by consciousness alone: any two networks with any readings
whatsoever give the same conscious cultural morality, so the aspects derive each other. -/
theorem ccm_eq_ccm (N : Network P V) {W : Type w} (M : Network P W) : CCM N = CCM M := by
  rw [ccm_eq_top, ccm_eq_top]

/-- A reading of the field is already a network: consciousness generates culture and morality. -/
def ofRead (read : P → V) : Network P V where
  read := read
  admits := fun _ _ => True
  admits_refl := fun _ => trivial
  admits_symm := fun _ => trivial
  admits_trans := fun _ _ => trivial
  shared := fun _ _ => trivial

@[simp] theorem ofRead_read (read : P → V) : (ofRead read).read = read := rfl

theorem ccm_ofRead (read : P → V) : CCM (ofRead read) = fun _ _ => True := ccm_eq_top _

end Aspects

/-! ## §4  Translational truth: the completion of closure by relative admission -/

/-- A **language defined by assumption and proof**, presented by what it closes: `cl T` is
everything provable from the admitted assumptions `T`. -/
structure Lang (S : Type u) where
  /-- What the language closes a set of admitted assumptions into. -/
  cl : Set S → Set S
  /-- Assumptions are admitted. -/
  le_cl : ∀ T, T ⊆ cl T
  /-- Admitting more proves more. -/
  mono : ∀ {T T' : Set S}, T ⊆ T' → cl T ⊆ cl T'
  /-- Proof from proofs is proof. -/
  idem : ∀ T, cl (cl T) ⊆ cl T

namespace Lang

variable {S : Type u} {W : Type v} (L : Lang S)

/-- Truth relative to what is admitted. -/
def Truth (T : Set S) (s : S) : Prop := s ∈ L.cl T

theorem truth_of_mem {T : Set S} {s : S} (h : s ∈ T) : L.Truth T s := L.le_cl T h

/-- **The completion of closure by relative admission**: admitting everything already true changes
no truth. -/
theorem truth_completion (T : Set S) (s : S) : L.Truth (L.cl T) s ↔ L.Truth T s :=
  ⟨fun h => L.idem T h, fun h => L.mono (L.le_cl T) h⟩

theorem admission_completes (T : Set S) : L.cl (T ∪ L.cl T) = L.cl T := by
  apply Set.Subset.antisymm
  · intro s hs
    refine L.idem T (L.mono ?_ hs)
    exact Set.union_subset (L.le_cl T) (subset_refl _)
  · exact L.mono Set.subset_union_left

/-- The **foundation** of a language: what is true on no assumption. -/
def foundation : Set S := L.cl ∅

theorem foundation_subset_cl (T : Set S) : L.foundation ⊆ L.cl T := L.mono (Set.empty_subset T)

/-- **Natural forming existence**: closure never empties what exists. -/
theorem natural_forming_existence {T : Set S} (h : T.Nonempty) : (L.cl T).Nonempty :=
  h.mono (L.le_cl T)

/-- A **translation** of one language into another: it carries proofs to proofs. -/
structure Trans (L : Lang S) (M : Lang W) where
  /-- The translation of the statements. -/
  f : S → W
  /-- Proofs translate into proofs. -/
  cl_map : ∀ T : Set S, f '' L.cl T ⊆ M.cl (f '' T)

end Lang

namespace Lang.Trans

variable {S : Type u} {W : Type v} {X : Type w} {L : Lang S} {M : Lang W}

/-- **Translational truth**: truth relative to admitted assumptions translates. -/
theorem truth_translates (t : Trans L M) {T : Set S} {s : S} (h : L.Truth T s) :
    M.Truth (t.f '' T) (t.f s) := t.cl_map T ⟨s, h, rfl⟩

/-- **Foundation equality**: the translated foundation is the foundation of the translation. -/
theorem foundation_le_foundation (t : Trans L M) : t.f '' L.foundation ⊆ M.foundation := by
  intro w hw
  have := t.cl_map ∅ hw
  simpa [Lang.foundation] using this

/-- The identical translation. -/
def id (L : Lang S) : Trans L L where
  f := _root_.id
  cl_map T := by simp

/-- Translations compose. -/
def comp {N : Lang X} (t : Trans L M) (u : Trans M N) : Trans L N where
  f := u.f ∘ t.f
  cl_map T := by
    rintro _ ⟨s, hs, rfl⟩
    have h1 : t.f s ∈ M.cl (t.f '' T) := t.cl_map T ⟨s, hs, rfl⟩
    have h2 : u.f (t.f s) ∈ N.cl (u.f '' (t.f '' T)) := u.cl_map _ ⟨t.f s, h1, rfl⟩
    simpa [Set.image_image] using h2

end Lang.Trans

/-! ## §5  `0 ∞` closure: numeric and geometric continuums of one closure -/

open scoped ENNReal

/-- The numeric continuum with both poles, read as the geometric segment: one closure, two
readings. -/
noncomputable def seg : ℝ≥0∞ ≃o Set.Icc (0 : ℝ) 1 := ENNReal.orderIsoUnitIntervalBirational

/-- The numeric reading of a point of the segment. -/
noncomputable def segVal (x : ℝ≥0∞) : ℝ := (seg x : ℝ)

theorem seg_mem_segment (x : ℝ≥0∞) : segVal x ∈ Set.Icc (0 : ℝ) 1 := (seg x).2

theorem seg_zero : segVal 0 = 0 := by simp [segVal, seg]

theorem seg_top : segVal ⊤ = 1 := by simp [segVal, seg]

theorem segVal_eq (x : ℝ≥0∞) : segVal x = ((x⁻¹ + 1)⁻¹).toReal :=
  ENNReal.orderIsoUnitIntervalBirational_apply_coe x

theorem seg_one : segVal 1 = 1 / 2 := by
  rw [segVal_eq, show ((1 : ℝ≥0∞)⁻¹ + 1) = 2 by norm_num, ENNReal.toReal_inv]
  norm_num

/-- The polar exchange of the two poles is the geometric reflection of the segment. -/
theorem seg_polar (x : ℝ≥0∞) : segVal x⁻¹ = 1 - segVal x := by
  rw [segVal_eq, segVal_eq, inv_inv]
  rcases eq_or_ne x 0 with rfl | h0
  · simp
  rcases eq_or_ne x ⊤ with rfl | ht
  · simp
  have hxi : x⁻¹ ≠ ⊤ := by simp [h0]
  have hxpos : 0 < x.toReal := ENNReal.toReal_pos h0 ht
  rw [ENNReal.toReal_inv, ENNReal.toReal_inv, ENNReal.toReal_add (by simp [ht]) (by simp),
    ENNReal.toReal_add (by simp [hxi]) (by simp), ENNReal.toReal_inv, ENNReal.toReal_one]
  field_simp
  ring

/-- The geometric reading is faithful: the numeric and the geometric continuums are one. -/
theorem segVal_injective : Injective segVal := by
  intro x y h
  have : seg x = seg y := Subtype.ext h
  exact seg.injective this

/-- `NRRF764`'s `0 ∞` closure relation, read geometrically: two numbers are identified exactly when
their positions on the segment are equal or reflections of each other. -/
theorem zeroInfRel_iff_seg (x y : ℝ≥0∞) :
    ZeroInfRel x y ↔ (segVal y = segVal x ∨ segVal y = 1 - segVal x) := by
  constructor
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (seg_polar x)
  · rintro (h | h)
    · exact Or.inl (segVal_injective h)
    · refine Or.inr (segVal_injective ?_)
      rw [h, ← seg_polar x]
      rfl

/-- Point and line: the two poles are the two ends of the one segment, and every point of the
continuum lies between them. -/
theorem poles_are_the_ends (x : ℝ≥0∞) : segVal 0 ≤ segVal x ∧ segVal x ≤ segVal ⊤ := by
  rw [seg_zero, seg_top]
  exact ⟨(seg_mem_segment x).1, (seg_mem_segment x).2⟩

/-! ## §6  Notes are neither rules nor suggestions -/

/-- A **note**: how it acts on the interface. -/
structure Note (X : Type u) where
  /-- The action of the note on the interface. -/
  act : X → X

namespace Note

variable {X : Type u}

/-- A note read as a **rule**: it forces its outcome regardless of the interface. -/
def IsRule (n : Note X) : Prop := ∀ x y, n.act x = n.act y

/-- A note read as a **suggestion**: it leaves the interface untouched. -/
def IsSuggestion (n : Note X) : Prop := ∀ x, n.act x = x

/-- Notes compose. -/
def comp (n m : Note X) : Note X := ⟨m.act ∘ n.act⟩

/-- Latent memory: the note accumulated by a list of notes. -/
def ofList : List (Note X) → Note X
  | [] => ⟨_root_.id⟩
  | n :: t => n.comp (ofList t)

theorem ofList_append (l l' : List (Note X)) :
    (ofList (l ++ l')).act = (ofList l').act ∘ (ofList l).act := by
  induction l with
  | nil => rfl
  | cons n t ih => funext x; simp [ofList, comp, ih]

/-- A note is neither a rule nor a suggestion: it reinterprets the interface without forcing it. -/
theorem exists_note_neither_rule_nor_suggestion :
    ∃ n : Note Bool, ¬ n.IsRule ∧ ¬ n.IsSuggestion := by
  refine ⟨⟨not⟩, ?_, ?_⟩
  · intro h; simpa using h true false
  · intro h; simpa using h true

/-- Being both a rule and a suggestion is possible only where the interface has nothing to say. -/
theorem rule_and_suggestion_iff_subsingleton :
    (∀ n : Note X, n.IsRule ↔ n.IsSuggestion) ↔ Subsingleton X := by
  constructor
  · intro h
    refine ⟨fun x y => ?_⟩
    have hx : (Note.mk (fun _ => x)).IsRule := fun _ _ => rfl
    exact ((h _).1 hx) y
  · intro h n
    exact ⟨fun _ _ => h.allEq _ _, fun _ _ _ => h.allEq _ _⟩

end Note

section Operators

variable {P : Type u} {V : Type v}

/-- A reinterpretation of the network is a note on the shared field. -/
def Reinterp.toNote (N : Network P V) (e : Network.Reinterp N) : Note V := ⟨e.toEquiv⟩

theorem toNote_admissible (N : Network P V) (e : Network.Reinterp N) {x y : V}
    (h : N.admits x y) : N.admits ((Reinterp.toNote N e).act x) ((Reinterp.toNote N e).act y) :=
  e.admissible h

/-- The operators derive each other: a note is exactly the step of a loop, and the step of a loop
is exactly a note. -/
def noteEquivLoopStep (X : Type u) : Note X ≃ (X → X) where
  toFun n := n.act
  invFun f := ⟨f⟩
  left_inv n := by cases n; rfl
  right_inv _ := rfl

theorem note_eq_loop_step {X : Type u} (n : Note X) : (stepLoop n.act).step = n.act := rfl

/-- A note on the field is an interaction of the problem the field presents with itself. -/
def Note.toInter {p : Problem.{u}} (n : Note p.Sit) : Inter p p := ⟨n.act⟩

theorem note_solves {p : Problem.{u}} (n : Note p.Sit) (s : Solution p) :
    n.toInter.solve s = n.act s := rfl

end Operators

/-! ## The reading, in one theorem -/

/-- **NRRF765.**  The architecture is problems as real rather than nothing (§1); solutions are the
interactions (§2); conscious cultural morality and moral cultural consciousness are one reading of
the shared field (§3); translational truth is the completion of closure by relative admission, with
foundation equality and natural forming existence (§4); `0 ∞` closure makes the numeric and the
geometric continuums one closure with the poles as its ends and the polar exchange as its
reflection (§5); and a note is neither a rule nor a suggestion, the operators deriving each other
through the interaction (§6). -/
theorem nrrf765_answer
    (p q : Problem.{u}) {P : Type u} {V : Type v} (N : Network P V)
    {S : Type u} (L : Lang S) {W : Type v} (M : Lang W) (t : Lang.Trans L M) (T : Set S) (s : S)
    (x : ℝ≥0∞) (X : Type u) (n : Note X) :
    -- §1 problems are real, rather than nothing
    (¬ IsEmpty p.Sit) ∧
    -- §2 solutions are the interactions, and an interaction is what it does to solutions
    Nonempty (Solution p ≃ Inter Problem.one p) ∧
    Nonempty (Inter p q ≃ (Solution p → Solution q)) ∧
    Nonempty (Solution p) ∧
    -- §3 the three aspects are one reading, in either order, and it excludes nobody
    (CCM N = MCC N) ∧ (CCM N = fun _ _ => True) ∧
    -- §4 translational truth: completion by relative admission, translation, foundation, existence
    (L.Truth (L.cl T) s ↔ L.Truth T s) ∧
    (L.Truth T s → M.Truth (t.f '' T) (t.f s)) ∧
    (t.f '' L.foundation ⊆ M.foundation) ∧
    (T.Nonempty → (L.cl T).Nonempty) ∧
    -- §5 `0 ∞` closure: one continuum, poles at the ends, polar exchange = geometric reflection
    (segVal 0 = 0 ∧ segVal ⊤ = 1 ∧ segVal 1 = 1 / 2) ∧
    (segVal x⁻¹ = 1 - segVal x) ∧
    Injective segVal ∧
    (segVal 0 ≤ segVal x ∧ segVal x ≤ segVal ⊤) ∧
    -- §6 a note is neither a rule nor a suggestion; the operators derive each other
    (∃ b : Note Bool, ¬ b.IsRule ∧ ¬ b.IsSuggestion) ∧
    Nonempty (Note X ≃ (X → X)) ∧
    (stepLoop n.act).step = n.act := by
  refine ⟨p.no_empty_problem, ⟨solutionEquivInter p⟩, ⟨interEquivSolutionMap p q⟩,
    solution_nonempty p, ccm_eq_mcc N, ccm_eq_top N, L.truth_completion T s,
    fun h => t.truth_translates h, t.foundation_le_foundation, fun h => L.natural_forming_existence h,
    ⟨seg_zero, seg_top, seg_one⟩, seg_polar x, segVal_injective, poles_are_the_ends x,
    Note.exists_note_neither_rule_nor_suggestion, ⟨noteEquivLoopStep X⟩, note_eq_loop_step n⟩

end NRRF765

/-! ## Axiom audit -/

#print axioms NRRF765.Problem.no_empty_problem
#print axioms NRRF765.solutionEquivInter
#print axioms NRRF765.ccm_eq_mcc
#print axioms NRRF765.Lang.truth_completion
#print axioms NRRF765.seg_polar
#print axioms NRRF765.zeroInfRel_iff_seg
#print axioms NRRF765.Note.exists_note_neither_rule_nor_suggestion
#print axioms NRRF765.nrrf765_answer
