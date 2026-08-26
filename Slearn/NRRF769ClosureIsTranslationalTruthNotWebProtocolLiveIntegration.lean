import Mathlib
import Slearn.NRRF764ConsciousCulturalMoralitySuperNetwork
import Slearn.NRRF766PublicInterfaceFullyInteractiveCollectiveArchitecture
import Slearn.NRRF767ForgottenAssumptionsReorderedSharedMoralConnection

/-!
# NRRF769 — Closure is not a web protocol but a translational truth, live-integrated

The principle to be made precise: *ultimately closure is not a web protocol but a translational
truth*, and the running architecture is to be integrated **live** with that principle.

A *web protocol* is an endpoint-level convention: contents are encoded onto a wire and two
endpoints exchange a handshake verdict.  A *translational truth* is a relation on contents that is
reflexive, symmetric and transitive — an admissibility of readings of one another, in the sense of
`NRRF764.Network.admits`.  The three sections separate the two notions, show which one is the
invariant, and integrate a live stream of interactions with it.

## §1  Protocol verdicts versus translational truth

`Protocol α W` carries `encode : α → W` and `handshake : W → W → Prop`, and its `verdict` is the
induced relation on contents.  `exists_verdict_without_truth` and `exists_truth_without_verdict`
show a handshake can succeed where nothing is translationally true and fail where it is;
`exists_verdict_not_transitive` shows a protocol verdict need not even be an equivalence, so it is
not in general a translational truth at all.  Conversely `Faithful` protocols are *disciplined by*
the truth: `verdict_equivalence_of_faithful` makes their verdict an equivalence, and
`verdicts_agree_of_faithful` shows any two faithful protocols — over different wire types, with
different encodings — return exactly the same verdicts.  So the protocol is a carrier, never the
content: `closure_is_not_the_protocol` collects the separation, and
`network_verdict_of_faithful` says a faithful protocol can only certify the sharing that the
network already has.

## §2  Translational truth as a closure invariant

A `Rendering` is a family of translations `map i : α → α` (the frames the same content may be
re-read in).  It is `Contractive` for a closure `c` when translating a closure lands inside the
closure of the translate — translations do not manufacture structure.  `Invariant` sets are those
closed under all renderings, and `invariant_cl` shows the closure of an invariant body is again
invariant: **closure transports along translation**.  `invariant_iUnion`, `invariant_iInter` and
`invariant_univ` make the invariant bodies a complete sublattice-like family, and
`exists_verdict_not_invariant` shows the protocol-level verdict enjoys no such stability.

## §3  Live integration

A live stream `ev : ℕ → Set α` of interactions is integrated stage by stage:
`live c ev n = c.cl (upto ev n)` against the batch reading `batch c ev = c.cl (⋃ k, ev k)`.
`live_mono`, `live_closed`, `live_subset_batch` and `cl_iUnion_live_eq_batch` say the live
integration is a monotone chain of closed stages whose limit *is* the batch truth — integrating
live is not a different truth from integrating at once.  `batch_reindex` and
`live_limit_reindex` say the limit does not depend on delivery order (the protocol), while
`exists_stage_order_dependent` shows an individual stage does: what the wire delivers first is
protocol, what it converges to is truth.  `live_invariant` and `live_limit_invariant` carry §2
through the stream, and `live_network_certification` integrates the current architecture: at every
stage of the live run, every participant's reading is admissible to every other's, and any faithful
protocol returns that verdict.

`nrrf769_answer` collects the reading, and `nrrf769_answer_bool` instantiates it concretely.
-/

namespace NRRF769

open NRRF764 NRRF766 NRRF767

universe u v w

variable {α : Type u}

/-! ## §1  Protocol verdicts versus translational truth -/

/-- A **web protocol**: contents are encoded onto a wire type `W`, and two endpoints exchange a
handshake verdict about the wire values they hold.  Nothing is assumed about the handshake — that
is the point. -/
structure Protocol (α : Type u) (W : Type v) where
  /-- Encoding of a content onto the wire. -/
  encode : α → W
  /-- The endpoint-level handshake on wire values. -/
  handshake : W → W → Prop

/-- The relation on *contents* induced by a protocol: the handshake of their encodings. -/
def Protocol.verdict {W : Type v} (p : Protocol α W) (x y : α) : Prop :=
  p.handshake (p.encode x) (p.encode y)

/-- A protocol is **faithful** to a relation `R` when its verdict is exactly `R`: the protocol
reports the truth and adds nothing of its own. -/
def Protocol.Faithful {W : Type v} (p : Protocol α W) (R : α → α → Prop) : Prop :=
  ∀ x y, p.verdict x y ↔ R x y

/-- A **translational truth** on contents: an admissibility of readings of one another. -/
structure TransTruth (α : Type u) where
  /-- Which contents are admissible translations of one another. -/
  rel : α → α → Prop
  /-- Every content reads as itself. -/
  refl : ∀ x, rel x x
  /-- Admissibility is symmetric. -/
  symm : ∀ {x y}, rel x y → rel y x
  /-- Admissibility is transitive. -/
  trans : ∀ {x y z}, rel x y → rel y z → rel x z

/-- The translational truth carried by a shared network of readings. -/
def ofNetwork {P : Type v} {V : Type w} (net : Network P V) : TransTruth V where
  rel := net.admits
  refl := net.admits_refl
  symm := net.admits_symm
  trans := net.admits_trans

@[simp] theorem ofNetwork_rel {P : Type v} {V : Type w} (net : Network P V) (x y : V) :
    (ofNetwork net).rel x y ↔ net.admits x y := Iff.rfl

/-- **A handshake can succeed where nothing is true.**  There is a protocol whose verdict holds of
two contents that are not translations of one another. -/
theorem exists_verdict_without_truth :
    ∃ (p : Protocol Bool Unit) (t : TransTruth Bool) (x y : Bool),
      p.verdict x y ∧ ¬ t.rel x y := by
  refine ⟨⟨fun _ => (), fun _ _ => True⟩, ⟨Eq, fun _ => rfl, fun h => h.symm,
    fun h h' => h.trans h'⟩, true, false, trivial, by simp⟩

/-- **A handshake can fail where the truth holds.**  There is a protocol whose verdict fails of a
content and itself, though every content is a translation of itself. -/
theorem exists_truth_without_verdict :
    ∃ (p : Protocol Bool Unit) (t : TransTruth Bool) (x : Bool),
      t.rel x x ∧ ¬ p.verdict x x := by
  refine ⟨⟨fun _ => (), fun _ _ => False⟩, ⟨Eq, fun _ => rfl, fun h => h.symm,
    fun h h' => h.trans h'⟩, true, rfl, id⟩

/-- **A protocol verdict need not be a translational truth at all.**  There is a protocol whose
verdict is not transitive, hence is not the relation of any `TransTruth`. -/
theorem exists_verdict_not_transitive :
    ∃ p : Protocol Bool Bool,
      (∀ t : TransTruth Bool, ∃ x y, ¬ (p.verdict x y ↔ t.rel x y)) := by
  refine ⟨⟨id, fun x y => x ≠ y⟩, ?_⟩
  intro t
  by_contra hcon
  push_neg at hcon
  have h₁ : t.rel true false := (hcon true false).1 (by simp [Protocol.verdict])
  have h₂ : t.rel false true := (hcon false true).1 (by simp [Protocol.verdict])
  have h₃ : t.rel true true := t.trans h₁ h₂
  have : (true : Bool) ≠ true := (hcon true true).2 h₃
  exact this rfl

/-- A faithful protocol's verdict inherits the equivalence discipline of the truth it reports: the
protocol is governed by the truth, not the truth by the protocol. -/
theorem verdict_equivalence_of_faithful {W : Type v} {p : Protocol α W} {t : TransTruth α}
    (h : p.Faithful t.rel) :
    (∀ x, p.verdict x x) ∧ (∀ {x y}, p.verdict x y → p.verdict y x) ∧
      (∀ {x y z}, p.verdict x y → p.verdict y z → p.verdict x z) :=
  ⟨fun x => (h x x).2 (t.refl x),
   fun {x y} hxy => (h y x).2 (t.symm ((h x y).1 hxy)),
   fun {x y z} hxy hyz => (h x z).2 (t.trans ((h x y).1 hxy) ((h y z).1 hyz))⟩

/-- **The truth is protocol-invariant.**  Any two faithful protocols — over different wire types,
with different encodings and different handshakes — return exactly the same verdicts.  Whatever
distinguishes protocols is therefore not the closure. -/
theorem verdicts_agree_of_faithful {W : Type v} {W' : Type w}
    {p : Protocol α W} {q : Protocol α W'} {R : α → α → Prop}
    (hp : p.Faithful R) (hq : q.Faithful R) (x y : α) :
    p.verdict x y ↔ q.verdict x y :=
  (hp x y).trans (hq x y).symm

/-- **A faithful protocol only certifies the sharing the network already has.**  In a shared
network, every participant's reading is admissible to every other's, so a faithful protocol's
handshake succeeds between any two participants — it discovers nothing the field did not hold. -/
theorem network_verdict_of_faithful {P : Type v} {V : Type w} {W : Type w}
    (net : Network P V) {p : Protocol V W} (h : p.Faithful net.admits) (a b : P) :
    p.verdict (net.read a) (net.read b) :=
  (h _ _).2 (net.shared a b)

/-- **Closure is not the protocol.**  Protocol verdicts can hold without truth, fail with truth,
and fail to be equivalences; while faithful protocols are interchangeable.  The invariant content
of a closure is therefore the translational relation, not any protocol implementing it. -/
theorem closure_is_not_the_protocol :
    (∃ (p : Protocol Bool Unit) (t : TransTruth Bool) (x y : Bool),
        p.verdict x y ∧ ¬ t.rel x y) ∧
      (∃ (p : Protocol Bool Unit) (t : TransTruth Bool) (x : Bool),
        t.rel x x ∧ ¬ p.verdict x x) ∧
      (∃ p : Protocol Bool Bool, ∀ t : TransTruth Bool, ∃ x y, ¬ (p.verdict x y ↔ t.rel x y)) ∧
      (∀ {W : Type} {W' : Type} (p : Protocol Bool W) (q : Protocol Bool W')
        (R : Bool → Bool → Prop), p.Faithful R → q.Faithful R →
          ∀ x y, (p.verdict x y ↔ q.verdict x y)) :=
  ⟨exists_verdict_without_truth, exists_truth_without_verdict, exists_verdict_not_transitive,
    fun _p _q _R hp hq x y => verdicts_agree_of_faithful hp hq x y⟩

/-! ## §2  Translational truth as a closure invariant -/

/-- A **rendering family**: the translations `map i : α → α` under which the same content may be
re-read in another frame. -/
structure Rendering (α : Type u) (I : Type v) where
  /-- The translation belonging to frame `i`. -/
  map : I → α → α

variable {I : Type v}

/-- A body of content is **invariant** when every rendering of it stays inside it. -/
def Rendering.Invariant (r : Rendering α I) (S : Set α) : Prop :=
  ∀ i, r.map i '' S ⊆ S

/-- A rendering family is **contractive** for a closure when translating a closure lands inside the
closure of the translate: translations carry structure, they do not manufacture it. -/
def Contractive (c : Clo (Set α)) (r : Rendering α I) : Prop :=
  ∀ (i : I) (S : Set α), r.map i '' c.cl S ⊆ c.cl (r.map i '' S)

/-- **Closure transports along translation.**  For a contractive rendering family, the closure of an
invariant body is again invariant: the truth a closure states survives being re-read in any
frame. -/
theorem invariant_cl {c : Clo (Set α)} {r : Rendering α I} (hc : Contractive c r) {S : Set α}
    (hS : r.Invariant S) : r.Invariant (c.cl S) := by
  intro i
  refine (hc i S).trans ?_
  exact c.mono (hS i)

/-- Invariance is preserved by unions of invariant bodies. -/
theorem invariant_iUnion {r : Rendering α I} {J : Type w} {S : J → Set α}
    (hS : ∀ j, r.Invariant (S j)) : r.Invariant (⋃ j, S j) := by
  rintro i _ ⟨x, hx, rfl⟩
  rw [Set.mem_iUnion] at hx
  obtain ⟨j, hj⟩ := hx
  exact Set.mem_iUnion.2 ⟨j, hS j i ⟨x, hj, rfl⟩⟩

/-- Invariance is preserved by intersections of invariant bodies, provided each rendering maps the
whole intersection into each member. -/
theorem invariant_iInter {r : Rendering α I} {J : Type w} {S : J → Set α}
    (hS : ∀ j i, r.map i '' (⋂ j', S j') ⊆ S j) : r.Invariant (⋂ j, S j) := by
  intro i _ hx
  exact Set.mem_iInter.2 fun j => hS j i hx

/-- The whole content type is invariant. -/
theorem invariant_univ (r : Rendering α I) : r.Invariant (Set.univ : Set α) := by
  rintro i _ ⟨x, _, rfl⟩; trivial

/-- **A protocol verdict enjoys no such stability.**  There is a rendering family and a protocol
whose verdict holds of a pair but fails of its translation — a protocol-level agreement is not
carried along translation, whereas by `invariant_cl` a closure is. -/
theorem exists_verdict_not_invariant :
    ∃ (r : Rendering Bool Unit) (p : Protocol Bool Bool) (x y : Bool),
      p.verdict x y ∧ ¬ p.verdict (r.map () x) (r.map () y) := by
  refine ⟨⟨fun _ b => !b⟩, ⟨id, fun a b => a = true ∧ b = false⟩, true, false, ⟨rfl, rfl⟩, ?_⟩
  simp [Protocol.verdict]

/-! ## §3  Live integration -/

/-- What a live stream of interactions has delivered before stage `n`. -/
def upto (ev : ℕ → Set α) (n : ℕ) : Set α := ⋃ k, ⋃ _ : k < n, ev k

@[simp] theorem mem_upto {ev : ℕ → Set α} {n : ℕ} {x : α} :
    x ∈ upto ev n ↔ ∃ k < n, x ∈ ev k := by
  simp [upto]

theorem upto_mono (ev : ℕ → Set α) {n m : ℕ} (h : n ≤ m) : upto ev n ⊆ upto ev m := by
  intro x hx
  rw [mem_upto] at hx ⊢
  obtain ⟨k, hk, hx⟩ := hx
  exact ⟨k, lt_of_lt_of_le hk h, hx⟩

theorem ev_subset_upto (ev : ℕ → Set α) (k : ℕ) : ev k ⊆ upto ev (k + 1) := by
  intro x hx
  exact mem_upto.2 ⟨k, Nat.lt_succ_self k, hx⟩

theorem upto_subset_iUnion (ev : ℕ → Set α) (n : ℕ) : upto ev n ⊆ ⋃ k, ev k := by
  intro x hx
  obtain ⟨k, _, hx⟩ := mem_upto.1 hx
  exact Set.mem_iUnion.2 ⟨k, hx⟩

/-- The **live** reading of the stream at stage `n`: the closure of what has arrived so far. -/
def live (c : Clo (Set α)) (ev : ℕ → Set α) (n : ℕ) : Set α := c.cl (upto ev n)

/-- The **batch** reading of the stream: the closure of everything it will ever deliver. -/
def batch (c : Clo (Set α)) (ev : ℕ → Set α) : Set α := c.cl (⋃ k, ev k)

/-- Two bodies with the same closure-reach have the same closure. -/
theorem cl_eq_of_subset_cl {c : Clo (Set α)} {A B : Set α} (hA : A ⊆ c.cl B) (hB : B ⊆ c.cl A) :
    c.cl A = c.cl B :=
  le_antisymm (by simpa [c.idem] using c.mono hA) (by simpa [c.idem] using c.mono hB)

/-- Every live stage is closed. -/
theorem live_closed (c : Clo (Set α)) (ev : ℕ → Set α) (n : ℕ) : c.Closed (live c ev n) :=
  c.closed_cl _

/-- The live integration is a monotone chain: nothing already integrated is lost. -/
theorem live_mono (c : Clo (Set α)) (ev : ℕ → Set α) : Monotone (live c ev) :=
  fun _ _ h => c.mono (upto_mono ev h)

/-- Every live stage sits inside the batch truth. -/
theorem live_subset_batch (c : Clo (Set α)) (ev : ℕ → Set α) (n : ℕ) :
    live c ev n ⊆ batch c ev :=
  c.mono (upto_subset_iUnion ev n)

/-- **Live integration is the same truth as integration at once.**  The closure of everything the
live run ever produces is exactly the batch closure of the stream. -/
theorem cl_iUnion_live_eq_batch (c : Clo (Set α)) (ev : ℕ → Set α) :
    c.cl (⋃ n, live c ev n) = batch c ev := by
  refine cl_eq_of_subset_cl ?_ ?_
  · rintro x hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hx
    exact live_subset_batch c ev n hn
  · intro x hx
    obtain ⟨k, hx⟩ := Set.mem_iUnion.1 hx
    have : x ∈ live c ev (k + 1) := c.le_cl _ (ev_subset_upto ev k hx)
    exact c.le_cl _ (Set.mem_iUnion.2 ⟨k + 1, this⟩)

/-- The limit of the live run. -/
def liveLimit (c : Clo (Set α)) (ev : ℕ → Set α) : Set α := c.cl (⋃ n, live c ev n)

theorem liveLimit_eq_batch (c : Clo (Set α)) (ev : ℕ → Set α) :
    liveLimit c ev = batch c ev := cl_iUnion_live_eq_batch c ev

theorem liveLimit_closed (c : Clo (Set α)) (ev : ℕ → Set α) : c.Closed (liveLimit c ev) :=
  c.closed_cl _

/-- **Delivery order is protocol, not truth.**  Reindexing the stream by any permutation of stages
leaves the batch truth unchanged. -/
theorem batch_reindex (c : Clo (Set α)) (ev : ℕ → Set α) (σ : Equiv.Perm ℕ) :
    batch c (ev ∘ σ) = batch c ev := by
  have h : (⋃ k, (ev ∘ σ) k) = ⋃ k, ev k := by
    ext x
    simp only [Set.mem_iUnion, Function.comp_apply]
    constructor
    · rintro ⟨k, hk⟩; exact ⟨σ k, hk⟩
    · rintro ⟨k, hk⟩; exact ⟨σ.symm k, by simpa using hk⟩
  rw [batch, batch, h]

/-- The live limit, too, is independent of delivery order. -/
theorem live_limit_reindex (c : Clo (Set α)) (ev : ℕ → Set α) (σ : Equiv.Perm ℕ) :
    liveLimit c (ev ∘ σ) = liveLimit c ev := by
  rw [liveLimit_eq_batch, liveLimit_eq_batch, batch_reindex]

/-- **But an individual stage is protocol-dependent.**  There is a stream and a reordering of it
with the same limit whose stage-one readings differ: what arrives first is a fact about the wire,
what it converges to is the truth. -/
theorem exists_stage_order_dependent :
    ∃ (c : Clo (Set ℕ)) (ev : ℕ → Set ℕ) (σ : Equiv.Perm ℕ),
      batch c (ev ∘ σ) = batch c ev ∧ live c (ev ∘ σ) 1 ≠ live c ev 1 := by
  refine ⟨idClo ℕ, fun k => {k}, Equiv.swap 0 1, batch_reindex _ _ _, ?_⟩
  intro h
  have h0 : (0 : ℕ) ∈ live (idClo ℕ) (fun k => ({k} : Set ℕ)) 1 := by
    simp [live, idClo_cl, mem_upto]
  rw [← h] at h0
  simp [live, idClo_cl, mem_upto, Equiv.swap_apply_left] at h0

/-- The live run of an invariant stream is invariant at every stage. -/
theorem live_invariant {c : Clo (Set α)} {r : Rendering α I} (hc : Contractive c r)
    {ev : ℕ → Set α} (hev : ∀ k, r.Invariant (ev k)) (n : ℕ) : r.Invariant (live c ev n) := by
  refine invariant_cl hc ?_
  intro i _ hx
  obtain ⟨x, hx, rfl⟩ := hx
  obtain ⟨k, hk, hx⟩ := mem_upto.1 hx
  exact mem_upto.2 ⟨k, hk, hev k i ⟨x, hx, rfl⟩⟩

/-- And so is its limit: the live integration never leaves the translational truth. -/
theorem live_limit_invariant {c : Clo (Set α)} {r : Rendering α I} (hc : Contractive c r)
    {ev : ℕ → Set α} (hev : ∀ k, r.Invariant (ev k)) : r.Invariant (liveLimit c ev) :=
  invariant_cl hc (invariant_iUnion fun n => live_invariant hc hev n)

/-- **Live integration of the current architecture.**  At every stage of a live run over a shared
network, every participant's reading is admissible to every other's, any faithful protocol returns
that verdict, the stage is a closed body, and the limit is the batch truth — independent of the
order in which the wire delivered the interactions. -/
theorem live_network_certification {P : Type v} {V : Type w} {W : Type w}
    (net : Network P V) {p : Protocol V W} (hp : p.Faithful net.admits)
    (c : Clo (Set V)) (ev : ℕ → Set V) (σ : Equiv.Perm ℕ) (n : ℕ) (a b : P) :
    net.admits (net.read a) (net.read b) ∧ p.verdict (net.read a) (net.read b) ∧
      c.Closed (live c ev n) ∧ liveLimit c (ev ∘ σ) = batch c ev :=
  ⟨net.shared a b, network_verdict_of_faithful net hp a b, live_closed c ev n,
    (live_limit_reindex c ev σ).trans (liveLimit_eq_batch c ev)⟩

/-! ## The reading -/

/-- **NRRF769.**  Closure is not a web protocol but a translational truth, and the live run of the
current architecture integrates with that principle:

* §1 a protocol verdict can hold without truth, fail with truth, and fail to be an equivalence,
  while all faithful protocols agree — the protocol is a carrier, the relation is the invariant;
* §2 closure transports along translation: the closure of an invariant body is invariant, while a
  protocol verdict need not be;
* §3 the live stage-by-stage integration is a monotone chain of closed stages whose limit is exactly
  the batch truth and is independent of delivery order, though an individual stage is not; and the
  running network's sharing is certified at every stage by any faithful protocol. -/
theorem nrrf769_answer {W : Type w} {P : Type w} {V : Type w}
    (c : Clo (Set α)) (r : Rendering α I) (hc : Contractive c r)
    (ev : ℕ → Set α) (hev : ∀ k, r.Invariant (ev k)) (n : ℕ) (σ : Equiv.Perm ℕ)
    (net : Network P V) (p : Protocol V W) (hp : p.Faithful net.admits) (a b : P) :
    -- §1  the protocol is not the closure
    (∃ (q : Protocol Bool Unit) (t : TransTruth Bool) (x y : Bool),
        q.verdict x y ∧ ¬ t.rel x y) ∧
      (∃ (q : Protocol Bool Unit) (t : TransTruth Bool) (x : Bool),
        t.rel x x ∧ ¬ q.verdict x x) ∧
      (∃ q : Protocol Bool Bool, ∀ t : TransTruth Bool, ∃ x y, ¬ (q.verdict x y ↔ t.rel x y)) ∧
      (∀ (W' : Type w) (q : Protocol V W'), q.Faithful net.admits →
        ∀ x y, (p.verdict x y ↔ q.verdict x y)) ∧
      p.verdict (net.read a) (net.read b) ∧
      -- §2  the truth is what transports along translation
      r.Invariant (c.cl (⋃ k, ev k)) ∧
      (∃ (r' : Rendering Bool Unit) (q : Protocol Bool Bool) (x y : Bool),
        q.verdict x y ∧ ¬ q.verdict (r'.map () x) (r'.map () y)) ∧
      -- §3  live integration
      Monotone (live c ev) ∧ c.Closed (live c ev n) ∧ live c ev n ⊆ batch c ev ∧
      liveLimit c ev = batch c ev ∧ liveLimit c (ev ∘ σ) = liveLimit c ev ∧
      r.Invariant (liveLimit c ev) ∧
      (∃ (d : Clo (Set ℕ)) (e : ℕ → Set ℕ) (τ : Equiv.Perm ℕ),
        batch d (e ∘ τ) = batch d e ∧ live d (e ∘ τ) 1 ≠ live d e 1) :=
  ⟨exists_verdict_without_truth, exists_truth_without_verdict, exists_verdict_not_transitive,
    fun _ _q hq x y => verdicts_agree_of_faithful hp hq x y,
    network_verdict_of_faithful net hp a b,
    invariant_cl hc (invariant_iUnion hev),
    exists_verdict_not_invariant,
    live_mono c ev, live_closed c ev n, live_subset_batch c ev n, liveLimit_eq_batch c ev,
    live_limit_reindex c ev σ, live_limit_invariant hc hev, exists_stage_order_dependent⟩

/-- A concrete instantiation: the identity closure on `ℕ`, the identity rendering, and the stream
of singletons. -/
theorem nrrf769_answer_bool (n : ℕ) (σ : Equiv.Perm ℕ) :
    Monotone (live (idClo ℕ) (fun k => ({k} : Set ℕ))) ∧
      (idClo ℕ).Closed (live (idClo ℕ) (fun k => ({k} : Set ℕ)) n) ∧
      liveLimit (idClo ℕ) (fun k => ({k} : Set ℕ)) = batch (idClo ℕ) (fun k => ({k} : Set ℕ)) ∧
      liveLimit (idClo ℕ) ((fun k => ({k} : Set ℕ)) ∘ σ) =
        liveLimit (idClo ℕ) (fun k => ({k} : Set ℕ)) ∧
      (Rendering.mk (fun (_ : Unit) (m : ℕ) => m)).Invariant
        (liveLimit (idClo ℕ) (fun k => ({k} : Set ℕ))) :=
  ⟨live_mono _ _, live_closed _ _ _, liveLimit_eq_batch _ _, live_limit_reindex _ _ _,
    live_limit_invariant (r := Rendering.mk (fun (_ : Unit) (m : ℕ) => m))
      (fun _ _ => le_of_eq (by ext x; simp [idClo_cl])) (fun _ _ => by rintro _ ⟨x, hx, rfl⟩; exact hx)⟩

/-! ## Axiom audit -/

#print axioms exists_verdict_without_truth
#print axioms exists_truth_without_verdict
#print axioms exists_verdict_not_transitive
#print axioms verdict_equivalence_of_faithful
#print axioms verdicts_agree_of_faithful
#print axioms network_verdict_of_faithful
#print axioms closure_is_not_the_protocol
#print axioms invariant_cl
#print axioms exists_verdict_not_invariant
#print axioms cl_iUnion_live_eq_batch
#print axioms batch_reindex
#print axioms exists_stage_order_dependent
#print axioms live_limit_invariant
#print axioms live_network_certification
#print axioms nrrf769_answer
#print axioms nrrf769_answer_bool

end NRRF769
