/-
Universal-relative translational completion for Slearn.

This module proves the abstract theorem schema used by the Slearn design:
translational completion is extensive, monotone, and idempotent; any operator
satisfying universal-relative local conservativity and returned sufficiency is
extensionally equal to translational completion; and a cofinal family of
relevant views preserves the same completion.
-/

universe u v

namespace Slearn

/--
A family of relative views on a space `X`.

`same a x y` means that `x` and `y` have the same presentation at view `a`.
`refines a b` means that `b` is at least as discriminating as `a`.
-/
structure RelativeFrame (X : Type u) where
  View : Type v
  same : View → X → X → Prop
  same_refl : ∀ a x, same a x x
  same_symm : ∀ a {x y}, same a x y → same a y x
  same_trans : ∀ a {x y z}, same a x y → same a y z → same a x z
  refines : View → View → Prop
  refines_refl : ∀ a, refines a a
  refines_trans : ∀ {a b c}, refines a b → refines b c → refines a c
  directed : ∀ a b, ∃ c, refines a c ∧ refines b c
  same_of_refines :
    ∀ {a b x y}, refines a b → same b x y → same a x y

namespace RelativeFrame

variable {X : Type u} (F : RelativeFrame X)

/-- The current local opening, or ball, around `x` at view `a`. -/
def opening (a : F.View) (x : X) : X → Prop :=
  fun y => F.same a x y

/--
Translational completion: `x` is complete relative to `S` when every
admissible view of `x` has a matching witness in `S`.
-/
def completion (S : X → Prop) : X → Prop :=
  fun x => ∀ a, ∃ y, S y ∧ F.same a x y

/-- Translational completion restricted to a selected family of views. -/
def completionOn (R : F.View → Prop) (S : X → Prop) : X → Prop :=
  fun x => ∀ a, R a → ∃ y, S y ∧ F.same a x y

/--
A selected family of views is cofinal when every admissible view has a
selected refinement.
-/
def Cofinal (R : F.View → Prop) : Prop :=
  ∀ a, ∃ r, R r ∧ F.refines a r

/-- Refining the zoom can only shrink the current opening. -/
theorem opening_antitone {a b : F.View} (hab : F.refines a b) :
    ∀ x y, F.opening b x y → F.opening a x y := by
  intro x y hxy
  exact F.same_of_refines hab hxy

/-- Every target is contained in its translational completion. -/
theorem completion_extensive (S : X → Prop) :
    ∀ x, S x → F.completion S x := by
  intro x hx a
  exact ⟨x, hx, F.same_refl a x⟩

/-- Translational completion is monotone. -/
theorem completion_mono {S T : X → Prop}
    (hST : ∀ x, S x → T x) :
    ∀ x, F.completion S x → F.completion T x := by
  intro x hx a
  obtain ⟨y, hyS, hxy⟩ := hx a
  exact ⟨y, hST y hyS, hxy⟩

/-- Translational completion is idempotent. -/
theorem completion_idem (S : X → Prop) :
    F.completion (F.completion S) = F.completion S := by
  funext x
  apply propext
  constructor
  · intro hx a
    obtain ⟨y, hy, hxy⟩ := hx a
    obtain ⟨z, hz, hyz⟩ := hy a
    exact ⟨z, hz, F.same_trans a hxy hyz⟩
  · intro hx a
    exact ⟨x, hx, F.same_refl a x⟩

/-- A target is complete when it is a fixed point of translational completion. -/
def IsComplete (S : X → Prop) : Prop :=
  F.completion S = S

/-- The completion of every target is a fixed point. -/
theorem completion_isComplete (S : X → Prop) :
    F.IsComplete (F.completion S) := by
  exact completion_idem F S

/--
The universal-relative admissibility contract for a proposed closure operator.

`local_conservative` excludes an externally added point with no witness in an
admissible view. `returned_sufficient` excludes rejection of a point that has a
matching target witness at every admissible view.
-/
structure UniversalRelativeAdmissible
    (C : (X → Prop) → X → Prop) : Prop where
  local_conservative :
    ∀ S x, C S x → ∀ a, ∃ y, S y ∧ F.same a x y
  returned_sufficient :
    ∀ S x, (∀ a, ∃ y, S y ∧ F.same a x y) → C S x

/-- Translational completion itself satisfies the admissibility contract. -/
theorem completion_admissible :
    F.UniversalRelativeAdmissible F.completion where
  local_conservative := by
    intro S x hx
    exact hx
  returned_sufficient := by
    intro S x hx
    exact hx

/--
Translational completion is the only closure operator satisfying the stated
universal-relative admissibility contract.
-/
theorem admissible_eq_completion
    {C : (X → Prop) → X → Prop}
    (hC : F.UniversalRelativeAdmissible C) :
    C = F.completion := by
  funext S x
  apply propext
  constructor
  · intro hx
    exact hC.local_conservative S x hx
  · intro hx
    exact hC.returned_sufficient S x hx

/-- Any two universally relatively admissible closure operators are equal. -/
theorem admissible_unique
    {C D : (X → Prop) → X → Prop}
    (hC : F.UniversalRelativeAdmissible C)
    (hD : F.UniversalRelativeAdmissible D) :
    C = D := by
  funext S x
  apply propext
  constructor
  · intro hx
    exact hD.returned_sufficient S x
      (hC.local_conservative S x hx)
  · intro hx
    exact hC.returned_sufficient S x
      (hD.local_conservative S x hx)

/--
A cofinal task-relevant family of views preserves the full translational
completion. This is the formal relevance-preservation theorem for Slearn.
-/
theorem completionOn_cofinal
    {R : F.View → Prop}
    (hR : F.Cofinal R)
    (S : X → Prop) :
    F.completionOn R S = F.completion S := by
  funext x
  apply propext
  constructor
  · intro hx a
    obtain ⟨r, hr, har⟩ := hR a
    obtain ⟨y, hyS, hxy⟩ := hx r hr
    exact ⟨y, hyS, F.same_of_refines har hxy⟩
  · intro hx a _
    exact hx a

end RelativeFrame

end Slearn

#print axioms Slearn.RelativeFrame.completion_idem
#print axioms Slearn.RelativeFrame.admissible_eq_completion
#print axioms Slearn.RelativeFrame.admissible_unique
#print axioms Slearn.RelativeFrame.completionOn_cofinal
