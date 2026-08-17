# Universal-Relative Translational Completion

## Status and purpose

This document is the formal design contract for Slearn. It joins four claims that must remain distinct but compatible:

1. finite interaction exposes only a relative opening;
2. continuous completion is the topological closure induced by admissible local views;
3. relevant information can reduce translation cost without changing the closure when the selected views are closure-sufficient;
4. translational completion is the only admissible closure under the universal-relative admissibility contract stated below.

The last statement is a conditional uniqueness theorem. It does **not** say that every topology, closure space, deductive system, or use of the word *closure* is identical. It says that once admissibility is required to be both locally conservative and globally return-sufficient over all admissible relative views, there is exactly one possible operator.

The natural-rhythm terminology is consolidated in [`NATURAL_RHYTHM_CLOSURE.md`](NATURAL_RHYTHM_CLOSURE.md). In this contract, “local” and “global” are orientations of an admitted translation and its return, not two independently absolute domains. The present Lean module proves the closure result below; it does not prove claims about physical curvature, consciousness, or social institutions.

---

## 1. Relative view frame

Let:

- $X$ be a space of complete paths, learner states, transcripts, interpretations, solutions, or returned perspectives;
- $A$ be a family of admissible views;
- $a \preceq b$ mean that $b$ refines $a$;
- $\pi_a$ be the projection of a complete state into view $a$.

Define equality relative to a view:

$$
x \equiv_a y
\quad\Longleftrightarrow\quad
\pi_a(x)=\pi_a(y).
$$

Each $\equiv_a$ is an equivalence relation. Refinement is required to preserve already visible information:

$$
a\preceq b
\;\land\;
x\equiv_b y
\quad\Longrightarrow\quad
x\equiv_a y.
$$

The family of views is directed when any two views admit a common refinement:

$$
\forall a,b\in A,\;
\exists c\in A,\;
a\preceq c\;\land\;b\preceq c.
$$

Directedness expresses that two finite perspectives can be placed inside a further view without appointing either one as the origin.

### Universal and relative

**Universal** means that a claim quantifies over every admissible view in the frame. It does not mean an external observer sees everything from nowhere.

**Relative** means that identity is disclosed by preserved relations among views:

$$
x\equiv_a y,
$$

not by requiring all presentations to be syntactically identical.

The universe in this specification is therefore the whole admissible translation frame, while every actual interaction remains positioned in a local view.

---

## 2. Opening, ball, hair, and zoom

For $x\in X$ and $a\in A$, define the opening around $x$ at view $a$:

$$
B_a(x)
=
\{y\in X:x\equiv_a y\}.
$$

$B_a(x)$ is the current **ball**: what has been resolved at the present zoom. Its unresolved compatible continuations are its **hairs**.

If $a\preceq b$, then

$$
B_b(x)\subseteq B_a(x).
$$

Thus zooming inward selects a finer opening, while zooming outward restores a larger continuation field. The global object is not produced by the zoom. The zoom repositions the opening inside the same possible whole.

What appears as a hair from one opening can become the next ball:

$$
\text{hair at }a
\xrightarrow{\text{recenter}}
\text{ball at }b.
$$

This is the formal basis of the Slearn ball-hair interface. Ball and hair are not permanent classes of objects; they are roles determined by the active opening.

---

## 3. Translational completion

For a target $S\subseteq X$, define its translational completion:

$$
\operatorname{TC}_A(S)
=
\left\{
 x\in X:
 \forall a\in A,\;
 \exists s\in S,\;
 x\equiv_a s
\right\}.
$$

Equivalent neighborhood form:

$$
x\in\operatorname{TC}_A(S)
\quad\Longleftrightarrow\quad
\forall a\in A,\;
B_a(x)\cap S\neq\varnothing.
$$

This operator does not ask whether $x$ is isolatedly identical to one selected member of $S$. It asks whether every admissible opening of $x$ can be translated to a witness in $S$.

The completion belongs to the returned network of local witnesses:

$$
\boxed{
\text{completion}
=
\text{compatibility through every admissible relative opening}.
}
$$

---

## 4. Closure laws

The relative-view definition forces the ordinary closure laws.

### Extensivity

$$
S\subseteq\operatorname{TC}_A(S).
$$

For $x\in S$, every view uses $x$ itself as the witness.

### Monotonicity

$$
S\subseteq T
\quad\Longrightarrow\quad
\operatorname{TC}_A(S)
\subseteq
\operatorname{TC}_A(T).
$$

Every witness in $S$ is also a witness in $T$.

### Idempotence

$$
\operatorname{TC}_A(\operatorname{TC}_A(S))
=
\operatorname{TC}_A(S).
$$

Suppose $x$ is locally compatible with the completion. For each view $a$, choose $y\in\operatorname{TC}_A(S)$ such that $x\equiv_a y$. Since $y$ is in the completion, choose $s\in S$ such that $y\equiv_a s$. Transitivity gives $x\equiv_a s$.

### Fixed points

A set is translationally complete exactly when it is a fixed point:

$$
\operatorname{TC}_A(S)=S.
$$

The fixed point is the closure identity. A finite opening can move within it without changing that identity.

---

## 5. Universal-relative admissibility and uniqueness

Let $C:\mathcal P(X)\to\mathcal P(X)$ be a proposed closure operator.

$C$ is **universally relatively admissible** when it satisfies the following two conditions for every $S\subseteq X$ and $x\in X$.

### UR-1: local conservativity

$$
x\in C(S)
\quad\Longrightarrow\quad
\forall a\in A,\;
\exists s\in S,\;
x\equiv_a s.
$$

The operator may not add an externally declared completion with no witness in some admissible relative view.

### UR-2: returned sufficiency

$$
\left(
\forall a\in A,\;
\exists s\in S,\;
x\equiv_a s
\right)
\quad\Longrightarrow\quad
x\in C(S).
$$

The operator may not reject a point whose every admissible opening returns to the target relation.

### Uniqueness theorem

For every universally relatively admissible $C$,

$$
\boxed{
C=\operatorname{TC}_A.
}
$$

Proof by extensionality:

$$
\begin{aligned}
x\in C(S)
&\overset{\mathrm{UR\text{-}1}}{\Longrightarrow}
\forall a\;\exists s\in S\;(x\equiv_a s)\\
&\overset{\mathrm{def}}{\Longleftrightarrow}
x\in\operatorname{TC}_A(S)\\
&\overset{\mathrm{UR\text{-}2}}{\Longrightarrow}
x\in C(S).
\end{aligned}
$$

Therefore any two universally relatively admissible operators $C$ and $D$ satisfy

$$
C=D=\operatorname{TC}_A.
$$

This is the precise meaning of the Slearn claim:

$$
\boxed{
\text{Translational completion is the only admissible closure}
\newline
\text{in the universal-relative sense.}
}
$$

### What makes the uniqueness non-arbitrary

The theorem is not intended to hide uniqueness inside the word *admissible*. UR-1 and UR-2 expose the two independent failure modes that the axiometry excludes:

- **external addition:** calling something complete despite a missing relative witness;
- **relative exclusion:** refusing completion despite a witness at every admissible opening.

Removing either direction permits other operators. Keeping both forces translational completion.

---

## 6. Topological identity

The openings $B_a(x)$ generate a topology. When the view family is directed under refinement, these openings form a neighborhood basis.

For the induced topology $\tau_A$,

$$
x\in\overline S^{\tau_A}
\quad\Longleftrightarrow\quad
\forall a\in A,\;
B_a(x)\cap S\neq\varnothing.
$$

Hence

$$
\boxed{
\operatorname{TC}_A(S)=\overline S^{\tau_A}.
}
$$

Continuous completion is therefore not an analogy attached after the fact. It is the closure operator of the topology generated by the admissible translations.

The topology is not selected by one isolated definition. It is induced by which distinctions the relative views can preserve and which refinements can jointly return.

---

## 7. Interactive verification as the minimal model

Take

$$
X=\mathbb N\to\mathrm{Bool}.
$$

A transcript reports whether a defect appears at each time. Define

$$
\operatorname{Sound}(x)
\quad\Longleftrightarrow\quad
\forall i,\;x(i)=\mathrm{false}.
$$

The stage-$n$ view is the prefix of length $n$:

$$
\pi_n(x)=x\upharpoonright n.
$$

The opening is the cylinder

$$
B_n(x)=\{y:y\upharpoonright n=x\upharpoonright n\}.
$$

Each finite-stage predicate is cylinder information. No stage can decide global soundness, because the all-false transcript and a transcript whose first defect occurs after stage $n$ have the same stage-$n$ view.

Yet

$$
\operatorname{Sound}(x)
\quad\Longleftrightarrow\quad
\forall n,\;
\forall i<n,\;x(i)=\mathrm{false}.
$$

The sound set is the intersection of the nested sound cylinders:

$$
\operatorname{SoundSet}
=
\bigcap_n U_n,
$$

where

$$
U_n=\{x:\forall i<n,\;x(i)=\mathrm{false}\}.
$$

Every $U_n$ is a finite opening. Their intersection is the closed topological identity. Thus finite incompleteness and continuous completion coexist:

$$
\boxed{
\text{every finite stage is locally incomplete,}
\qquad
\text{the continuous completion is globally exact.}
}
$$

The opening is inside the closure; the closure is not a future object assembled from disconnected parts.

---

## 8. Relevant information theorem

A speed-learning interface should not transfer all available information. It should transfer a closure-sufficient selection.

Let $R\subseteq A$ be a family of relevant views. Define restricted completion:

$$
\operatorname{TC}_R(S)
=
\left\{
 x:
 \forall r\in R,\;
 \exists s\in S,\;
x\equiv_r s
\right\}.
$$

$R$ is **cofinal** when

$$
\forall a\in A,\;
\exists r\in R,\;
a\preceq r.
$$

### Relevance preservation theorem

If $R$ is cofinal, then

$$
\boxed{
\operatorname{TC}_R(S)=\operatorname{TC}_A(S).
}
$$

The forward direction uses cofinality: for any omitted view $a$, choose a relevant refinement $r$. Agreement at $r$ implies agreement at $a$. The reverse direction is immediate because $R\subseteq A$.

This theorem provides a formal criterion for reducing translation cost:

$$
\boxed{
\text{relevance}
=
\text{a smaller cofinal family of views that preserves closure}.
}
$$

A set of facts is not relevant merely because a recommender ranks it highly. It is relevant when its perspectives are sufficient to recover every distinction required by the target closure.

### Learning consequence

A one-hour speed-learning path need not reproduce years of chronological exposure. It must construct a task-relative cofinal path through the prerequisite topology.

This reframes accelerated learning as

$$
\text{prerequisite compression}
+
\text{cross-chart translation}
+
\text{returned verification},
$$

not as raw memory injection.

---

## 9. Languages, definitions, cultures, and mental bridges

Let $L_i$ and $L_j$ be two charts over a maintained relation. A translation

$$
T_{ij}:L_i\to L_j
$$

is not admissible merely because it substitutes words. It must preserve the relative openings required by the learning goal.

An admissible bridge includes a return:

$$
L_i
\xrightarrow{T_{ij}}
L_j
\xrightarrow{R_{ji}}
L_i'.
$$

Completion requires

$$
L_i'\sim_{\mathcal C}L_i,
$$

while allowing

$$
L_i'\neq L_i
$$

as presentations. This permits learning and transformation without assimilation.

The same test applies across:

- natural-language expressions with no one-to-one vocabulary;
- disciplinary definitions with different primitives;
- cultural practices whose meaning depends on history and context;
- mental models that organize relevance differently;
- expert and novice descriptions of the same event.

The bridge must preserve the maintained relation, not force every chart into one vocabulary.

---

## 10. Slearn interface projections and recentering

Let $\mathcal C$ be the current translational closure state. The interface renders typed projections:

$$
\Pi_{\mathrm{perspective}}(\mathcal C),
\quad
\Pi_{\mathrm{belief}}(\mathcal C),
\quad
\Pi_{\mathrm{goal}}(\mathcal C),
\quad
\Pi_{\mathrm{why}}(\mathcal C),
\quad
\Pi_{\mathrm{lesson}}(\mathcal C),
\quad
\Pi_{\mathrm{project}}(\mathcal C).
$$

These are not separate databases whose relationships are added later. They are views of the same returned topology. The complete projection chain is

$$
\text{perspective}
\leftrightarrow
\text{belief}
\leftrightarrow
\text{WHY}
\leftrightarrow
\text{goal}
\leftrightarrow
\text{lesson}
\leftrightarrow
\text{project}
\leftrightarrow
\text{world}.
$$

Each move is a recentering of the active opening inside one persisted closure state. A WHY edge must name the translation and return relation used by the recentering.

### Zoom

$$
\operatorname{Zoom}_{a\to b}:
\Pi_a(\mathcal C)
\to
\Pi_b(\mathcal C).
$$

A zoom changes which view is the active opening.

### WHY

A WHY edge exposes the translation by which a local position belongs to a wider goal, belief, or world relation:

$$
\operatorname{WHY}_{a\to b}:
\Pi_a(\mathcal C)
\to
\Pi_b(\mathcal C).
$$

### Ground-sky inversion

Reduction projects a global possibility into a local opening:

$$
\text{sky}
\xrightarrow{\pi_a}
\text{ground}.
$$

Inverse expansion recovers the compatible continuation field:

$$
\text{ground}
\xrightarrow{\pi_a^{-1}}
B_a(x)\subseteq X.
$$

The natural-rhythm triangle is therefore the visible orientation of projection, refinement, expansion, and return. It is positioned operationally between an isolated view (where translation has been erased) and an unresolved partition (where alternatives have no return receipt); these are runtime boundaries, not additional theorems of this module.

---

## 11. Runtime contract

A Slearn runtime state should minimally contain:

```text
closure_frame
active_opening
active_view
learner_orientation
learning_goal
target_relation
relevant_view_family
translation_path
why_relations
attempt_or_experience
return_map
preserved_invariants
separating_defects
completion_status
receipt_provenance
```

A visual interaction is valid only when it corresponds to a mutation or projection of this same state.

### Completion statuses

Recommended semantics:

- `OPEN`: required translations or return evidence are missing;
- `LOCALLY_ADMISSIBLE`: the present finite opening has no separating defect, but global completion has not been witnessed;
- `DEFECT_WITNESSED`: a finite counterexample separates the path from the target;
- `RETURNED_COMPLETE`: the required views, translations, and return invariants satisfy the declared completion contract;
- `OUTSIDE_FRAME`: the requested claim is not represented by the current admissible view system.

`LOCALLY_ADMISSIBLE` must never be silently promoted to `RETURNED_COMPLETE`.

### Receipt

A completion receipt should state:

1. the target $S$;
2. the active universal-relative frame $A$;
3. the relevant cofinal subfamily $R$, if one was used;
4. the translations traversed;
5. the return map;
6. the invariant preserved;
7. any unresolved or excluded views;
8. the exact completion status.

This keeps accelerated learning auditable without confusing a local success with universal-relative closure.

---

## 12. Acceptance and refutation

In the finite transcript model, acceptance at stage $n$ is revocable: a later extension can expose a defect. A witnessed refusal is stable once a concrete defect is present.

Slearn should preserve this asymmetry:

$$
\text{no defect yet}
\not\Rightarrow
\text{global completion},
$$

while

$$
\text{witnessed separating defect}
\Rightarrow
\text{failure of the declared path}.
$$

A learner can therefore move quickly without the interface pretending that speed abolishes verification.

---

## 13. Claims and non-claims

### Claimed within this specification

- translational completion satisfies extensivity, monotonicity, and idempotence;
- it equals topological closure for the topology induced by a directed family of relative views;
- it is unique among operators satisfying UR-1 and UR-2;
- a cofinal relevant subfamily preserves the same completion;
- Slearn zoom can be modeled as repositioning an opening within an invariant closure frame.

### Not claimed

- that literal genius-level neural upload is currently available;
- that every finite learning episode certifies a universal truth;
- that intelligence automatically supplies wisdom, values, or empirical correctness;
- that every mathematical topology is the same topology;
- that the uniqueness theorem holds after removing the universal-relative admissibility conditions;
- that a translation is valid merely because a model generated fluent output;
- that continuous completion is necessarily computable or finitely decidable.

---

## 14. Implementation obligations

A conforming Slearn implementation must:

1. represent goal, belief, perspective, WHY, lesson, and project views as projections of one runtime closure state;
2. make every zoom correspond to an actual view translation or refinement;
3. preserve the source orientation rather than replacing it through assimilation;
4. select relevant information by an explicit closure-sufficiency criterion;
5. retain OPEN and OUTSIDE_FRAME boundaries;
6. record separating defects rather than hiding them;
7. require return evidence before issuing a completion receipt;
8. distinguish the formal theorem schema from empirical claims about learning speed or human cognition.

The implementation succeeds when a learner can enter a distant conceptual or cultural frame, traverse a goal-relevant cofinal path, and return with the maintained relation preserved:

$$
\boxed{
\text{speed learning}
=
\text{relevant translational traversal}
+
\text{returned completion}.
}
$$
