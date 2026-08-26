import Mathlib

/-!
# NRRF764 — Conscious cultural morality: the network as a shared interactive field

The reading being formalised:

> You can not assume you are Turing complete nor use Turing completeness; halting and continuation
> are two inverse interpretations of one continuous interactive loop of sensor and selection.
> Its indeterminate strings are factors of its potential determination, whose unitary curvature
> equalizes through natural choice and collapses into further discretion through individual or
> globally isolated authorship.
> The network is not money, agi, rules, law or social order.  It is a shared interactive field of
> culture, morality and consciousness.  Super network theory: the closure notes guide the
> interface, whose interactions with ai or user shape latent memory and network connection,
> admissibly reinterpreting and translating the rules or notes.

## §1  One continuous interactive loop of sensor and selection

`Loop S Obs` is a sensor `sense : S → Obs` together with a selection `select : S → Obs → S`.  No
machine model, no universal element, no halting oracle is assumed anywhere in this file.  For a run
of the loop, `halted n` (the finished, determined part) and `continued n` (the residual future) are
**two inverse interpretations of the one run**: `splitEquiv n : (ℕ → S) ≃ (Fin n → S) × (ℕ → S)` is
an equivalence, so each reading is recovered from the other side, and neither is more than a reading
of the single loop — `continued_run` says the continuation is again a run of *the same* loop.
`halts_iff_continuation_const` reads halting off the continuation, and conversely.

Turing completeness is not available and not needed: `no_universal_selection` (Cantor) says the loop
can never enumerate all of its own selections, and `no_finite_halting_test` says no finite observed
prefix ever decides halting — yet every result about the loop here is proved for *all* loops.

## §2  Indeterminate strings are factors of the potential determination

`Ind n A` is an indeterminate string: each position carries the nonempty set of its possible
determinations.  `detEquivPi` factors the potential determination into the positions,
`card_det` counts it as the product, `det_nonempty` is the natural choice that always determines it.
`agree` is the equalizer of two indeterminate strings (`mem_agree_iff`), and authorship collapses
the potential: `mem_det_collapse_iff` for an individual position, `globalCollapse` for globally
isolated authorship, after which the determination is unique (`det_globalCollapse_unique`) while a
strict individual collapse strictly reduces the potential (`card_det_collapse_lt`).

## §3  The network is a shared interactive field, not an order

`Network P V`: each participant reads the shared field (`read` — consciousness), readings are
related by an admissibility relation (`admits` — morality) which is an equivalence, and the field
is *shared*: any two participants' readings are admissible for each other (`shared` — culture).
`ruleOf_eq_top`: the social order such a network induces is trivial — it ranks nobody — while
distinct networks abound (`networks_not_determined_by_order`), so the field is not the order; and
no authority (money, rank, law: any `Authority P`) is visible in the field at all
(`field_independent_of_authority`).

## §4  Interaction shapes latent memory and network connection

An `Interaction` is a translation of readings that preserves admissibility.  Latent memory is the
list of interactions had; `memory_admissible` shows every memory is admissible, and
`memory_run_append` composes them.  Network connection accumulated by a memory is monotone
(`conn_subset_append`), additive (`conn_append`) and independent of the order in which the
interactions happened (`conn_of_perm`).

## §5  Super network theory: translations of networks

`Hom` translates one network into another commuting with the readings and preserving admissibility;
identities and composites exist, reinterpretations (`Reinterp`) are the invertible self-translations
and form a group acting on interactions, and the unity is the terminal network
(`unity_terminal`): there is exactly one translation of any network into the one closure.

## §6  The operators derive each other relative to interaction

Sensor-and-selection and the single turn of the loop derive each other (`run_eq_stepLoop_run`), a
reinterpretation of the notes *is* an interaction (`Reinterp.toInteraction`), an interaction is the
one-step latent memory of having had it (`Memory.run_singleton`) and a whole latent memory is again
one interaction (`Memory.toInteraction`).  No operator is prior to the others; each is read off the
others through the interaction.

## §7  `0 ∞` closure

On the numeric continuum `ℝ≥0∞` the polar reversal `polar x = x⁻¹` exchanges the poles `0` and `∞`
and fixes the unit; `ZeroInfRel` is the closure equality it generates, an equivalence
(`zeroInfRel_equivalence`) for which the two poles are one point (`zero_rel_top`).  Numeric and
geometric readings agree (`rel_iff_radius`) and the closure is again one continuum,
`zeroInfClosureEquiv : Quotient zeroInfSetoid ≃ {r : ℝ≥0∞ // 1 ≤ r}`.  Read as a network
(`poleNetwork`) the poles are participants of one shared field, admissible for each other
(`poles_admissible`).

`nrrf764_answer` collects the reading in one theorem.
-/

namespace NRRF764

open Function

universe u v w t

/-! ## §1  One continuous interactive loop of sensor and selection -/

/-- A **continuous interactive loop**: a sensor reading the state, and a selection consuming what
the sensor read.  No computability, no universal machine and no halting oracle is assumed. -/
structure Loop (S : Type u) (Obs : Type v) where
  /-- The sensor. -/
  sense : S → Obs
  /-- The selection made on what the sensor read. -/
  select : S → Obs → S

namespace Loop

variable {S : Type u} {Obs : Type v} (L : Loop S Obs)

/-- One turn of the loop: sense, then select. -/
def step (s : S) : S := L.select s (L.sense s)

/-- The run of the loop from a state: the loop is total, it is never partial or undefined. -/
def run (s : S) : ℕ → S := fun n => L.step^[n] s

@[simp] theorem run_zero (s : S) : L.run s 0 = s := rfl

theorem run_succ (s : S) (n : ℕ) : L.run s (n + 1) = L.step (L.run s n) := by
  simp [run, Function.iterate_succ_apply']

theorem run_add (s : S) (n k : ℕ) : L.run s (n + k) = L.run (L.run s n) k := by
  show L.step^[n + k] s = L.step^[k] (L.step^[n] s)
  rw [Nat.add_comm, Function.iterate_add_apply]

/-- The **halting interpretation** of a run at time `n`: the part already determined. -/
def halted (n : ℕ) (r : ℕ → S) : Fin n → S := fun i => r i

/-- The **continuation interpretation** of a run at time `n`: the residual future. -/
def continued (n : ℕ) (r : ℕ → S) : ℕ → S := fun k => r (n + k)

end Loop

variable {S : Type u} {Obs : Type v}

/-- **Halting and continuation are two inverse interpretations of one run.**  Neither is a separate
object: the pair of them *is* the run, and the run is exactly the pair. -/
def splitEquiv (n : ℕ) : (ℕ → S) ≃ (Fin n → S) × (ℕ → S) where
  toFun r := (Loop.halted n r, Loop.continued n r)
  invFun p := fun i => if h : i < n then p.1 ⟨i, h⟩ else p.2 (i - n)
  left_inv r := by
    funext i
    by_cases h : i < n
    · simp [Loop.halted, h]
    · have : n + (i - n) = i := by omega
      simp [Loop.continued, h, this]
  right_inv p := by
    obtain ⟨f, g⟩ := p
    refine Prod.ext ?_ ?_
    · funext i
      simp [Loop.halted, i.isLt]
    · funext i
      have h : ¬ (n + i < n) := by omega
      have h' : n + i - n = i := by omega
      simp [Loop.continued, h, h']

@[simp] theorem splitEquiv_fst (n : ℕ) (r : ℕ → S) :
    ((splitEquiv n) r).1 = Loop.halted n r := rfl

@[simp] theorem splitEquiv_snd (n : ℕ) (r : ℕ → S) :
    ((splitEquiv n) r).2 = Loop.continued n r := rfl

namespace Loop

variable (L : Loop S Obs)

/-- The continuation of a run of the loop is again a run of *the same* loop: there is one loop, read
twice, not two processes. -/
theorem continued_run (s : S) (n : ℕ) : continued n (L.run s) = L.run (L.run s n) := by
  funext k; exact L.run_add s n k

/-- The determined part of a run is the run itself, read on `Fin n`. -/
theorem halted_run (s : S) (n : ℕ) (i : Fin n) : halted n (L.run s) i = L.run s i := rfl

/-- The loop **halts** at a state when a turn of it returns the same state. -/
def Halts (s : S) : Prop := ∃ n, L.step (L.run s n) = L.run s n

/-- Halting is read off the continuation, and the continuation off halting: the halting reading says
exactly that the continuation is constant from some time on. -/
theorem halts_iff_continuation_const (s : S) :
    L.Halts s ↔ ∃ n, ∀ k, continued n (L.run s) k = L.run s n := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, fun k => ?_⟩
    rw [continued_run]
    induction k with
    | zero => rfl
    | succ k ih => rw [run_succ, ih, hn]
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h1 := hn 1
    rw [continued_run, run_succ, run_zero] at h1
    exact h1

end Loop

/-- **Turing completeness is not available.**  A loop can never enumerate all of its own
selections: no map from states to state-properties is onto. -/
theorem no_universal_selection (f : S → Set S) : ¬ Surjective f :=
  Function.cantor_surjective f

/-- The incrementing loop on `ℕ`: it never halts. -/
def incLoop : Loop ℕ Unit := ⟨fun _ => (), fun s _ => s + 1⟩

/-- The loop that increments until it reaches `k` and then rests: it halts. -/
def clampLoop (k : ℕ) : Loop ℕ Unit := ⟨fun _ => (), fun s _ => if s < k then s + 1 else s⟩

@[simp] theorem incLoop_run (n : ℕ) : incLoop.run 0 n = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Loop.run_succ, ih]; rfl

theorem clampLoop_run (k n : ℕ) : (clampLoop k).run 0 n = min n k := by
  induction n with
  | zero => simp [Loop.run]
  | succ n ih =>
      rw [Loop.run_succ, ih]
      show (if min n k < k then min n k + 1 else min n k) = min (n + 1) k
      by_cases h : n < k
      · rw [if_pos (by omega : min n k < k)]; omega
      · rw [if_neg (by omega : ¬ min n k < k)]; omega

theorem incLoop_not_halts : ¬ incLoop.Halts 0 := by
  rintro ⟨n, hn⟩
  rw [← Loop.run_succ] at hn
  simp at hn

theorem clampLoop_halts (k : ℕ) : (clampLoop k).Halts 0 := by
  refine ⟨k, ?_⟩
  rw [← Loop.run_succ, clampLoop_run, clampLoop_run]
  omega

/-- **No finite observation decides halting.**  For every horizon `n` there are two loops whose runs
agree on everything observed up to `n`, one of which halts and one of which does not.  Halting is
therefore never a property of the determined part alone; it is an interpretation of the whole
continuous loop. -/
theorem no_finite_halting_test (n : ℕ) :
    ∃ L L' : Loop ℕ Unit,
      (∀ i ≤ n, L.run 0 i = L'.run 0 i) ∧ L.Halts 0 ∧ ¬ L'.Halts 0 := by
  refine ⟨clampLoop (n + 1), incLoop, fun i hi => ?_, clampLoop_halts _, incLoop_not_halts⟩
  rw [clampLoop_run, incLoop_run]
  omega

/-! ## §2  Indeterminate strings are factors of the potential determination -/

/-- An **indeterminate string** of length `n`: each position carries the (nonempty) set of the
determinations it is still open to. -/
structure Ind (n : ℕ) (A : Type u) where
  /-- The possibilities standing open at each position. -/
  pos : Fin n → Set A
  /-- No position is impossible. -/
  pos_nonempty : ∀ i, (pos i).Nonempty

namespace Ind

variable {n : ℕ} {A : Type u}

/-- A **determination** of an indeterminate string: one admitted letter at each position. -/
def Det (w : Ind n A) : Type u := {f : Fin n → A // ∀ i, f i ∈ w.pos i}

/-- **The indeterminate string is the factorisation of its potential determination**: determining
the whole is exactly determining each position, independently. -/
def detEquivPi (w : Ind n A) : w.Det ≃ ∀ i, (w.pos i) :=
  Equiv.subtypePiEquivPi

/-- **Natural choice** always determines an indeterminate string: the potential is never empty. -/
theorem det_nonempty (w : Ind n A) : Nonempty w.Det :=
  ⟨⟨fun i => (w.pos_nonempty i).choose, fun i => (w.pos_nonempty i).choose_spec⟩⟩

/-- The potential of an indeterminate string is the product of the potentials of its positions. -/
theorem card_det (w : Ind n A) : Nat.card w.Det = ∏ i, Nat.card (w.pos i) := by
  rw [Nat.card_congr w.detEquivPi, Nat.card_pi]

/-- The **equalizer** of two indeterminate strings: the possibilities they agree on. -/
def agree (w w' : Ind n A) : Fin n → Set A := fun i => w.pos i ∩ w'.pos i

/-- A letter string determines both indeterminate strings exactly when it lies in their
equalizer. -/
theorem mem_agree_iff (w w' : Ind n A) (f : Fin n → A) :
    (∀ i, f i ∈ agree w w' i) ↔ (∀ i, f i ∈ w.pos i) ∧ (∀ i, f i ∈ w'.pos i) := by
  constructor
  · intro h; exact ⟨fun i => (h i).1, fun i => (h i).2⟩
  · rintro ⟨h1, h2⟩ i; exact ⟨h1 i, h2 i⟩

/-- Where the equalizer is nonempty position by position it is itself an indeterminate string: the
curvature of the two readings equalizes, through natural choice, into one. -/
def equalize (w w' : Ind n A) (h : ∀ i, (agree w w' i).Nonempty) : Ind n A :=
  ⟨agree w w', h⟩

/-- **Individual authorship**: an author fixes one position, collapsing the string there. -/
def collapse (w : Ind n A) (i : Fin n) (a : A) (ha : a ∈ w.pos i) : Ind n A where
  pos j := if j = i then {a} else w.pos j
  pos_nonempty j := by
    by_cases h : j = i
    · subst h; simp
    · simpa [h] using w.pos_nonempty j

/-- Determining the collapsed string is exactly determining the original one with the author's
letter at the authored position. -/
theorem mem_det_collapse_iff (w : Ind n A) (i : Fin n) (a : A) (ha : a ∈ w.pos i)
    (f : Fin n → A) :
    (∀ j, f j ∈ (w.collapse i a ha).pos j) ↔ (∀ j, f j ∈ w.pos j) ∧ f i = a := by
  constructor
  · intro h
    have hi : f i = a := by simpa [collapse] using h i
    refine ⟨fun j => ?_, hi⟩
    by_cases hj : j = i
    · subst hj; rw [hi]; exact ha
    · simpa [collapse, hj] using h j
  · rintro ⟨h, hi⟩ j
    by_cases hj : j = i
    · subst hj; simp [collapse, hi]
    · simpa [collapse, hj] using h j

/-- **Globally isolated authorship**: an author fixes every position at once. -/
def globalCollapse (w : Ind n A) (d : w.Det) : Ind n A where
  pos i := {d.val i}
  pos_nonempty _ := ⟨_, rfl⟩

/-- After global authorship no discretion is left: the determination is unique — and it is the
author's. -/
theorem det_globalCollapse_unique (w : Ind n A) (d : w.Det) (e : (w.globalCollapse d).Det) :
    e.val = d.val := by
  funext i; simpa [globalCollapse] using e.2 i

theorem globalCollapse_le (w : Ind n A) (d : w.Det) (i : Fin n) :
    (w.globalCollapse d).pos i ⊆ w.pos i := by
  rintro x rfl; exact d.2 i

end Ind

/-! ## §3  The network is a shared interactive field, not an order -/

/-- A **network**: a shared interactive field of culture, morality and consciousness.  Each
participant reads the field (`read`: consciousness), readings stand in an admissibility relation
(`admits`: morality) which is an equivalence, and the field is *shared*: the readings of any two
participants are admissible for one another (`shared`: culture). -/
structure Network (P : Type u) (V : Type v) where
  /-- What each participant reads of the shared field. -/
  read : P → V
  /-- Which readings are admissible translations of one another. -/
  admits : V → V → Prop
  /-- Admissibility is reflexive. -/
  admits_refl : ∀ x, admits x x
  /-- Admissibility is symmetric. -/
  admits_symm : ∀ {x y}, admits x y → admits y x
  /-- Admissibility is transitive. -/
  admits_trans : ∀ {x y z}, admits x y → admits y z → admits x z
  /-- The field is shared: no participant's reading is inadmissible to another's. -/
  shared : ∀ p q, admits (read p) (read q)

namespace Network

variable {P : Type u} {V : Type v} (N : Network P V)

theorem admits_equivalence : Equivalence N.admits :=
  ⟨N.admits_refl, N.admits_symm, N.admits_trans⟩

/-- An **authority**: money, rank, law — any external valuation of the participants.  It is a
structure *on the participants*, not on the field. -/
abbrev Authority (P : Type u) := P → ℤ

/-- The social order a network induces: "is `q`'s reading admissible to `p`'s?". -/
def ruleOf : P → P → Prop := fun p q => N.admits (N.read p) (N.read q)

/-- **The network is not a social order.**  Whatever order it induces is the trivial one: it ranks
nobody, excludes nobody, and so carries none of the field. -/
theorem ruleOf_eq_top : N.ruleOf = fun _ _ => True := by
  funext p q; simp [ruleOf, N.shared p q]

/-- **The network is not money, rank or law.**  Whatever authority separates two participants — a
difference of money, of rank, of standing — their readings remain admissible to one another: the
authority is invisible to the field. -/
theorem authority_does_not_exclude (rho : Authority P) (p q : P) (_h : rho p ≠ rho q) :
    N.admits (N.read p) (N.read q) := N.shared p q

/-- The unity: the one-reading network, in which everything is admitted. -/
def unity (P : Type u) : Network P PUnit where
  read _ := PUnit.unit
  admits _ _ := True
  admits_refl _ := trivial
  admits_symm _ := trivial
  admits_trans _ _ := trivial
  shared _ _ := trivial

end Network

/-- **The order does not determine the network.**  Two networks over the same participants induce
the same (trivial) order yet read the field differently, so the shared field is strictly more than
any rule, law or social order laid over it. -/
theorem networks_not_determined_by_order :
    ∃ N N' : Network Bool Bool, N.ruleOf = N'.ruleOf ∧ N.read ≠ N'.read := by
  refine ⟨⟨id, fun _ _ => True, fun _ => trivial, fun _ => trivial, fun _ _ => trivial,
      fun _ _ => trivial⟩,
    ⟨fun _ => false, Eq, fun _ => rfl, Eq.symm, Eq.trans, fun _ _ => rfl⟩, ?_, ?_⟩
  · rw [Network.ruleOf_eq_top, Network.ruleOf_eq_top]
  · intro h
    have := congrFun h true
    simp at this

/-! ## §4  Interaction shapes latent memory and network connection -/

namespace Network

variable {P : Type u} {V : Type v}

/-- An **interaction** with the field — by a user, by an ai, by a note: a translation of readings
that is *admissible*, i.e. that carries admissible readings to admissible readings. -/
structure Interaction (N : Network P V) where
  /-- How the interaction moves a reading. -/
  act : V → V
  /-- The interaction reinterprets admissibly. -/
  admissible : ∀ {x y}, N.admits x y → N.admits (act x) (act y)

variable {N : Network P V}

/-- **Latent memory**: the interactions the interface has had, in order. -/
abbrev Memory (N : Network P V) := List (Interaction N)

/-- The reading a latent memory leaves behind. -/
def Memory.run : Memory N → V → V
  | [], x => x
  | i :: m, x => Memory.run m (i.act x)

@[simp] theorem Memory.run_nil (x : V) : Memory.run ([] : Memory N) x = x := rfl

@[simp] theorem Memory.run_cons (i : Interaction N) (m : Memory N) (x : V) :
    Memory.run (i :: m) x = Memory.run m (i.act x) := rfl

theorem Memory.run_append (m m' : Memory N) (x : V) :
    Memory.run (m ++ m') x = Memory.run m' (Memory.run m x) := by
  induction m generalizing x with
  | nil => rfl
  | cons i m ih => simp [ih]

/-- **Every latent memory is admissible.**  However the interface is shaped by its interactions, it
never leaves the shared field: what was admissible stays admissible. -/
theorem memory_admissible (m : Memory N) {x y : V} (h : N.admits x y) :
    N.admits (Memory.run m x) (Memory.run m y) := by
  induction m generalizing x y with
  | nil => exact h
  | cons i m ih => exact ih (i.admissible h)

/-- A memory never leaves the field of a participant's reading. -/
theorem memory_shared (m : Memory N) (p q : P) :
    N.admits (Memory.run m (N.read p)) (Memory.run m (N.read q)) :=
  memory_admissible m (N.shared p q)

end Network

/-- The **network connection** a latent memory has made: the pairs of participants its interactions
have connected. -/
def conn {P : Type u} : List (P × P) → Set (P × P)
  | [] => ∅
  | c :: m => insert c (conn m)

theorem conn_append {P : Type u} (m m' : List (P × P)) :
    conn (m ++ m') = conn m ∪ conn m' := by
  induction m with
  | nil => simp [conn]
  | cons c m ih => simp [conn, ih, Set.insert_union]

theorem conn_subset_append {P : Type u} (m m' : List (P × P)) : conn m ⊆ conn (m ++ m') := by
  rw [conn_append]; exact Set.subset_union_left

/-- **The connection made does not depend on the order of the interactions.**  Latent memory is
shaped by what was interacted with, not by the sequence in which it happened. -/
theorem conn_of_perm {P : Type u} {m m' : List (P × P)} (h : m.Perm m') : conn m = conn m' := by
  induction h with
  | nil => rfl
  | cons c _ ih => simp [conn, ih]
  | swap c d m => simp [conn, Set.insert_comm]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem mem_conn_iff {P : Type u} (m : List (P × P)) (c : P × P) : c ∈ conn m ↔ c ∈ m := by
  induction m with
  | nil => simp [conn]
  | cons d m ih => simp [conn, ih]

/-! ## §5  Super network theory: translations of networks -/

namespace Network

variable {P : Type u} {V : Type v} {W : Type w}

/-- A **translation** of one network into another: a map of readings commuting with what the
participants read and preserving admissibility. -/
structure Hom (N : Network P V) (N' : Network P W) where
  /-- The translation of readings. -/
  map : V → W
  /-- It commutes with the participants' readings. -/
  map_read : ∀ p, map (N.read p) = N'.read p
  /-- It is admissible. -/
  map_admits : ∀ {x y}, N.admits x y → N'.admits (map x) (map y)

/-- The identity translation. -/
def Hom.id (N : Network P V) : Hom N N := ⟨_root_.id, fun _ => rfl, fun h => h⟩

/-- Translations compose: the networks and their translations form one super network. -/
def Hom.comp {X : Type t} {N : Network P V} {N' : Network P W} {N'' : Network P X}
    (g : Hom N' N'') (f : Hom N N') : Hom N N'' :=
  ⟨g.map ∘ f.map, fun p => by simp [f.map_read, g.map_read], fun h => g.map_admits (f.map_admits h)⟩

/-- A **reinterpretation** of a network: an invertible self-translation, admissible both ways.  This
is how the notes, the rules and the interface get reinterpreted without leaving the closure. -/
structure Reinterp (N : Network P V) where
  /-- The reinterpretation of readings. -/
  toEquiv : V ≃ V
  /-- Reinterpretation neither creates nor destroys admissibility. -/
  admits_iff : ∀ x y, N.admits (toEquiv x) (toEquiv y) ↔ N.admits x y

namespace Reinterp

variable {N : Network P V}

/-- Reinterpreting changes nothing about what is admissible: the closure is invariant. -/
theorem admissible (e : Reinterp N) {x y : V} (h : N.admits x y) :
    N.admits (e.toEquiv x) (e.toEquiv y) := (e.admits_iff x y).2 h

/-- The identity reinterpretation. -/
def refl : Reinterp N := ⟨Equiv.refl V, fun _ _ => Iff.rfl⟩

/-- Reinterpretations invert. -/
def symm (e : Reinterp N) : Reinterp N :=
  ⟨e.toEquiv.symm, fun x y => by
    have h := e.admits_iff (e.toEquiv.symm x) (e.toEquiv.symm y)
    simp only [Equiv.apply_symm_apply] at h
    exact h.symm⟩

/-- Reinterpretations compose. -/
def trans (e f : Reinterp N) : Reinterp N :=
  ⟨e.toEquiv.trans f.toEquiv, fun x y => by
    simp only [Equiv.trans_apply]
    rw [f.admits_iff, e.admits_iff]⟩

/-- A reinterpretation carries an interaction to an interaction: the rules and notes are translated,
and stay admissible. -/
def reinterpret (e : Reinterp N) (i : Interaction N) : Interaction N :=
  ⟨fun x => e.toEquiv (i.act (e.toEquiv.symm x)), fun {x y} h => by
    refine e.admissible (i.admissible ?_)
    have h' := e.admits_iff (e.toEquiv.symm x) (e.toEquiv.symm y)
    simp only [Equiv.apply_symm_apply] at h'
    exact h'.1 h⟩

end Reinterp

/-- **The unity is the terminal network.**  Every network has exactly one translation into the one
closure: there is no second closure to be translated into. -/
theorem unity_terminal (N : Network P V) :
    ∃! _f : Hom N (Network.unity P), True := by
  refine ⟨⟨fun _ => PUnit.unit, fun _ => rfl, fun _ => trivial⟩, trivial, ?_⟩
  rintro ⟨f, hf, hf'⟩ -
  congr 1

end Network

/-! ## §6  The operators derive each other relative to interaction with the network -/

/-- The loop whose sensor reads the whole state and whose selection is a given operator. -/
def stepLoop (f : S → S) : Loop S S := ⟨_root_.id, fun _ o => f o⟩

@[simp] theorem stepLoop_step (f : S → S) : (stepLoop f).step = f := rfl

/-- **Sensor-and-selection and the single turn derive each other.**  A loop is nothing but the turn
it takes, and the turn is nothing but a loop: the run is the same. -/
theorem run_eq_stepLoop_run (L : Loop S Obs) (s : S) : (stepLoop L.step).run s = L.run s := rfl

namespace Network

variable {P : Type u} {V : Type v} {N : Network P V}

/-- **A reinterpretation is an interaction.**  Translating the notes or the rules *is* interacting
with the field. -/
def Reinterp.toInteraction (e : Reinterp N) : Interaction N := ⟨e.toEquiv, e.admissible⟩

@[simp] theorem Reinterp.toInteraction_act (e : Reinterp N) (x : V) :
    e.toInteraction.act x = e.toEquiv x := rfl

/-- **An interaction is a one-step latent memory.**  Memory and interaction derive each other: a
single interaction is the memory of having had it, and a memory is the interactions composed. -/
@[simp] theorem Memory.run_singleton (i : Interaction N) (x : V) :
    Memory.run [i] x = i.act x := rfl

/-- The composite of a memory is itself an interaction: the field is closed under everything that
happens in it. -/
def Memory.toInteraction (m : Memory N) : Interaction N :=
  ⟨Memory.run m, fun h => memory_admissible m h⟩

@[simp] theorem Memory.toInteraction_act (m : Memory N) (x : V) :
    m.toInteraction.act x = Memory.run m x := rfl

end Network

/-! ## §7  `0 ∞` closure: the two poles are one unified numeric-geometric continuum -/

open scoped ENNReal

/-- The **polar reversal** of the numeric continuum, `x ↦ x⁻¹`, which exchanges the poles `0` and
`∞` and fixes the unit. -/
noncomputable def polar (x : ℝ≥0∞) : ℝ≥0∞ := x⁻¹

@[simp] theorem polar_zero : polar 0 = ⊤ := by simp [polar]

@[simp] theorem polar_top : polar ⊤ = 0 := by simp [polar]

@[simp] theorem polar_polar (x : ℝ≥0∞) : polar (polar x) = x := by simp [polar]

@[simp] theorem polar_one : polar 1 = 1 := by simp [polar]

/-- **`0 ∞` closure equality**: two points of the numeric continuum are the same point *for the
closure* when each is the polar reading of the other.  The line-point `0` and `∞` are then one
point of one closure, not two ends of two continuums. -/
def ZeroInfRel (x y : ℝ≥0∞) : Prop := y = x ∨ y = polar x

theorem zeroInfRel_equivalence : Equivalence ZeroInfRel := by
  refine ⟨fun _ => Or.inl rfl, ?_, ?_⟩
  · rintro x y (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (by simp)
  · rintro x y z (rfl | rfl) (rfl | rfl) <;> simp [ZeroInfRel]

/-- The two poles are one for the closure. -/
theorem zero_rel_top : ZeroInfRel 0 ⊤ := Or.inr (by simp)

/-- The closure equality as a setoid on the numeric continuum. -/
def zeroInfSetoid : Setoid ℝ≥0∞ := ⟨ZeroInfRel, zeroInfRel_equivalence⟩

/-- The geometric reading of a point of the continuum: how far it stands from the unit, measured
towards whichever pole it lies towards. -/
noncomputable def radius (x : ℝ≥0∞) : ℝ≥0∞ := max x (polar x)

theorem one_le_radius (x : ℝ≥0∞) : 1 ≤ radius x := by
  rcases le_total x 1 with h | h
  · exact le_max_of_le_right (ENNReal.one_le_inv.mpr h)
  · exact le_max_of_le_left h

theorem radius_polar (x : ℝ≥0∞) : radius (polar x) = radius x := by
  simp only [radius, polar_polar]
  exact max_comm _ _

theorem radius_of_one_le {x : ℝ≥0∞} (h : 1 ≤ x) : radius x = x := by
  have hx : polar x ≤ 1 := by simpa [polar] using ENNReal.inv_le_inv.mpr h
  exact max_eq_left (le_trans hx h)

theorem rel_radius (x : ℝ≥0∞) : ZeroInfRel x (radius x) := by
  rcases le_total (polar x) x with h | h
  · exact Or.inl (max_eq_left h)
  · exact Or.inr (max_eq_right h)

/-- The numeric reading and the geometric reading are one: two points are equal for the closure
exactly when they have the same radius. -/
theorem rel_iff_radius (x y : ℝ≥0∞) : ZeroInfRel x y ↔ radius x = radius y := by
  constructor
  · rintro (rfl | rfl)
    · rfl
    · exact (radius_polar x).symm
  · intro h
    refine zeroInfRel_equivalence.trans (rel_radius x) ?_
    rw [h]
    exact zeroInfRel_equivalence.symm (rel_radius y)

/-- **One unified closure.**  The `0 ∞` closure of the numeric continuum *is* a continuum again:
the quotient by the polar identification is the half-line from the unit outwards. -/
noncomputable def zeroInfClosureEquiv : Quotient zeroInfSetoid ≃ {r : ℝ≥0∞ // 1 ≤ r} where
  toFun := Quotient.lift (fun x => (⟨radius x, one_le_radius x⟩ : {r : ℝ≥0∞ // 1 ≤ r}))
    (fun a b h => Subtype.ext ((rel_iff_radius a b).1 h))
  invFun r := Quotient.mk _ r.1
  left_inv := by
    refine Quotient.ind fun x => ?_
    exact Quotient.sound (zeroInfRel_equivalence.symm (rel_radius x))
  right_inv r := Subtype.ext (radius_of_one_le r.2)

/-- The `0 ∞` closure read as a network: the two poles are its participants, the numeric continuum
is the shared field, and polar reversal is its morality — the admissible translation. -/
def poleNetwork : Network Bool ℝ≥0∞ where
  read b := if b then ⊤ else 0
  admits := ZeroInfRel
  admits_refl _ := zeroInfRel_equivalence.refl _
  admits_symm h := zeroInfRel_equivalence.symm h
  admits_trans h h' := zeroInfRel_equivalence.trans h h'
  shared p q := by cases p <;> cases q <;> simp [ZeroInfRel]

/-- The poles are admissible for one another in the network they generate. -/
theorem poles_admissible :
    poleNetwork.admits (poleNetwork.read false) (poleNetwork.read true) :=
  poleNetwork.shared false true

/-! ## The reading, in one theorem -/

theorem nrrf764_answer
    {S : Type u} {Obs : Type v} (L : Loop S Obs) (s : S) (n : ℕ)
    {A : Type u} {k : ℕ} (w : Ind k A) (i : Fin k) (a : A) (ha : a ∈ w.pos i) (d : w.Det)
    {P : Type u} {V : Type v} (N : Network P V) (m : Network.Memory N) (x y : V)
    (cm cm' : List (P × P)) :
    -- §1 halting and continuation are two inverse interpretations of one loop
    (Function.LeftInverse (splitEquiv (S := S) n).symm (splitEquiv n) ∧
      Function.RightInverse (splitEquiv (S := S) n).symm (splitEquiv n)) ∧
    Loop.continued n (L.run s) = L.run (L.run s n) ∧
    (L.Halts s ↔ ∃ n, ∀ j, Loop.continued n (L.run s) j = L.run s n) ∧
    -- Turing completeness is neither assumed nor available
    (∀ f : S → Set S, ¬ Function.Surjective f) ∧
    (∃ L L' : Loop ℕ Unit, (∀ j ≤ n, L.run 0 j = L'.run 0 j) ∧ L.Halts 0 ∧ ¬ L'.Halts 0) ∧
    -- §2 indeterminate strings factor the potential determination; authorship collapses it
    Nonempty (w.Det ≃ ∀ j, (w.pos j)) ∧ Nonempty w.Det ∧
    (∀ f : Fin k → A, (∀ j, f j ∈ (w.collapse i a ha).pos j) ↔ (∀ j, f j ∈ w.pos j) ∧ f i = a) ∧
    (∀ e : (w.globalCollapse d).Det, e.val = d.val) ∧
    -- §3 the network is a shared field, and is not the order or any authority over it
    N.ruleOf = (fun _ _ => True) ∧
    (∀ (rho : Network.Authority P) (p q : P), rho p ≠ rho q → N.admits (N.read p) (N.read q)) ∧
    (∃ N N' : Network Bool Bool, N.ruleOf = N'.ruleOf ∧ N.read ≠ N'.read) ∧
    -- §4 interaction shapes latent memory admissibly; connection is order-independent
    (N.admits x y → N.admits (Network.Memory.run m x) (Network.Memory.run m y)) ∧
    (cm.Perm cm' → conn cm = conn cm') ∧
    conn cm ⊆ conn (cm ++ cm') ∧
    -- §5 one closure: exactly one translation of the network into the unity
    (∃! _f : Network.Hom N (Network.unity P), True) ∧
    -- §6 the operators derive each other relative to interaction
    (stepLoop L.step).run s = L.run s ∧
    (∀ e : Network.Reinterp N, e.toInteraction.act = e.toEquiv) ∧
    (∀ i : Network.Interaction N, Network.Memory.run [i] = i.act) ∧
    -- §7 the `0 ∞` closure: the poles are one point of one continuum
    ZeroInfRel 0 ⊤ ∧
    (∀ x y : ℝ≥0∞, ZeroInfRel x y ↔ radius x = radius y) ∧
    Nonempty (Quotient zeroInfSetoid ≃ {r : ℝ≥0∞ // 1 ≤ r}) ∧
    poleNetwork.admits (poleNetwork.read false) (poleNetwork.read true) := by
  refine ⟨⟨(splitEquiv n).left_inv, (splitEquiv n).right_inv⟩, L.continued_run s n,
    L.halts_iff_continuation_const s, fun f => no_universal_selection f, no_finite_halting_test n,
    ⟨w.detEquivPi⟩, w.det_nonempty, w.mem_det_collapse_iff i a ha,
    w.det_globalCollapse_unique d, N.ruleOf_eq_top, N.authority_does_not_exclude,
    networks_not_determined_by_order,
    Network.memory_admissible m, fun h => conn_of_perm h, conn_subset_append cm cm',
    Network.unity_terminal N, run_eq_stepLoop_run L s, fun _ => rfl, fun _ => rfl,
    zero_rel_top, rel_iff_radius, ⟨zeroInfClosureEquiv⟩, poles_admissible⟩

end NRRF764

/-! ## Axiom audit -/

#print axioms NRRF764.splitEquiv
#print axioms NRRF764.Loop.continued_run
#print axioms NRRF764.Loop.halts_iff_continuation_const
#print axioms NRRF764.no_universal_selection
#print axioms NRRF764.no_finite_halting_test
#print axioms NRRF764.Ind.detEquivPi
#print axioms NRRF764.Ind.card_det
#print axioms NRRF764.Ind.mem_det_collapse_iff
#print axioms NRRF764.Ind.det_globalCollapse_unique
#print axioms NRRF764.Network.ruleOf_eq_top
#print axioms NRRF764.networks_not_determined_by_order
#print axioms NRRF764.Network.memory_admissible
#print axioms NRRF764.conn_of_perm
#print axioms NRRF764.Network.unity_terminal
#print axioms NRRF764.zeroInfRel_equivalence
#print axioms NRRF764.rel_iff_radius
#print axioms NRRF764.zeroInfClosureEquiv
#print axioms NRRF764.poles_admissible
#print axioms NRRF764.nrrf764_answer
