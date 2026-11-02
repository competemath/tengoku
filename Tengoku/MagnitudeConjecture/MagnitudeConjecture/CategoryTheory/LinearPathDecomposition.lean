import Tengoku.MagnitudeConjecture.MagnitudeConjecture.CategoryTheory.LinearPathLift
import Tengoku.MagnitudeConjecture.MagnitudeConjecture.CategoryTheory.LinearPathIncoming

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Decomposition by the first represented arrow

A morphism in the free reversed linear path category between distinct
vertices is a finite sum of one represented arrow out of its categorical
source followed by a coefficient path.  This is the free-category form used
by Ringel's recursive fullness construction.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open scoped BigOperators

namespace MagnitudeConjecture.LinearPathCategory

universe u v w

variable {k : Type u} [Field k]
variable {Q : Type v} [Quiver.{w} Q]

/-- Reversed quiver arrows whose represented categorical maps start at
`x`.-/
abbrev OutgoingArrow (x : Q) := Σ y : Q, y ⟶ x

variable [∀ x : Q, Fintype (OutgoingArrow x)]

/-- The free-path morphism represented by one arrow out of `x`.-/
def outgoingArrowHom {x : Q} (a : OutgoingArrow x) :
    obj k Q x ⟶ obj k Q a.1 :=
  pathHom a.2.toPath

/-- One free-path coefficient after every arrow out of `x`.-/
abbrev OutgoingCoefficient (x z : Q) :=
  ∀ a : OutgoingArrow x, obj k Q a.1 ⟶ obj k Q z

/-- Sum of all first-arrow factorizations.-/
def outgoingSum {x z : Q} (c : OutgoingCoefficient (k := k) x z) :
    obj k Q x ⟶ obj k Q z :=
  ∑ a : OutgoingArrow x, outgoingArrowHom (k := k) a ≫ c a

/-- A coefficient family supported after one outgoing arrow.-/
def singleOutgoingCoefficient {x z : Q} (a₀ : OutgoingArrow x)
    (f : obj k Q a₀.1 ⟶ obj k Q z) :
    OutgoingCoefficient (k := k) x z := by
  classical
  exact fun a ↦ if h : a₀ = a then
      eqToHom (congrArg (fun b : OutgoingArrow x ↦ obj k Q b.1) h.symm) ≫ f
    else 0

@[simp]
theorem outgoingSum_single {x z : Q} (a₀ : OutgoingArrow x)
    (f : obj k Q a₀.1 ⟶ obj k Q z) :
    outgoingSum (singleOutgoingCoefficient (k := k) a₀ f) =
      outgoingArrowHom (k := k) a₀ ≫ f := by
  classical
  rw [outgoingSum, Finset.sum_eq_single a₀]
  · simp [singleOutgoingCoefficient]
  · intro a _ ha
    simp [singleOutgoingCoefficient, Ne.symm ha]
  · simp

section Incoming

variable [∀ z : Q, Fintype (IncomingArrow z)]

end Incoming

section Realization

variable {C : Type*} [CategoryTheory.Category C] [Preadditive C]
  [CategoryTheory.Linear k C]
variable (F₀ : Q → C)
variable (F₁ : ∀ {i j : Q}, (i ⟶ j) → (F₀ j ⟶ F₀ i))

omit [(x : Q) → Fintype (OutgoingArrow x)] [Preadditive C] in
@[simp]
theorem pathMap_toPath {i j : Q} (a : i ⟶ j) :
    pathMap F₀ F₁ a.toPath = F₁ a := by
  rw [show a.toPath = (Quiver.Path.nil.cons a) from rfl,
    pathMap_cons, pathMap_nil, Category.comp_id]

end Realization

section Directed

variable [Preorder Q]

omit [(x : Q) → Fintype (OutgoingArrow x)] in
/-- If every quiver arrow strictly lowers an order, the endpoint of a path
is below its starting vertex.-/
theorem path_target_le_of_arrow_lt
    (harrow : ∀ {i j : Q}, (i ⟶ j) → j < i)
    {i j : Q} (p : Quiver.Path i j) :
    j ≤ i := by
  induction p with
  | nil => exact le_rfl
  | cons p a ih => exact (harrow a).le.trans ih

variable {C : Type*} [CategoryTheory.Category C] [Preadditive C]
  [CategoryTheory.Linear k C]

omit [(x : Q) → Fintype (OutgoingArrow x)] [Preadditive C] in
/-- Changing arrow representatives strictly above the start of a path does
not change its evaluation.-/
theorem pathMap_eq_of_eq_on_source_le
    (F₀ : Q → C)
    (F₁ G₁ : ∀ {i j : Q}, (i ⟶ j) → (F₀ j ⟶ F₀ i))
    (harrow : ∀ {i j : Q}, (i ⟶ j) → j < i)
    {i j : Q} (p : Quiver.Path i j)
    (h : ∀ {a b : Q} (e : a ⟶ b), a ≤ i → F₁ e = G₁ e) :
    pathMap F₀ F₁ p = pathMap F₀ G₁ p := by
  induction p with
  | nil => simp
  | @cons _ l p e ih =>
      rw [pathMap_cons, pathMap_cons, h e
        (path_target_le_of_arrow_lt harrow p), ih]

omit [(x : Q) → Fintype (OutgoingArrow x)] in
/-- The corresponding stability statement for a linear combination of
paths.-/
theorem homMap_eq_of_eq_on_source_le
    (F₀ : Q → C)
    (F₁ G₁ : ∀ {i j : Q}, (i ⟶ j) → (F₀ j ⟶ F₀ i))
    (harrow : ∀ {i j : Q}, (i ⟶ j) → j < i)
    {x z : Q} (f : obj k Q x ⟶ obj k Q z)
    (h : ∀ {a b : Q} (e : a ⟶ b), a ≤ z → F₁ e = G₁ e) :
    homMap F₀ F₁ (obj k Q x) (obj k Q z) f =
      homMap F₀ G₁ (obj k Q x) (obj k Q z) f := by
  let f' := homPathLinearEquiv (obj k Q x) (obj k Q z) f
  rw [← (homPathLinearEquiv (obj k Q x) (obj k Q z)).symm_apply_apply f]
  change
    homMap F₀ F₁ (obj k Q x) (obj k Q z)
        ((homPathLinearEquiv (obj k Q x) (obj k Q z)).symm f') =
      homMap F₀ G₁ (obj k Q x) (obj k Q z)
        ((homPathLinearEquiv (obj k Q x) (obj k Q z)).symm f')
  induction f' using Finsupp.induction_linear with
  | zero => simp
  | add f₁ f₂ hf₁ hf₂ => simp only [map_add, hf₁, hf₂]
  | single p r =>
      rw [homPathLinearEquiv_symm_single]
      simp only [map_smul, homMap_pathHom]
      rw [pathMap_eq_of_eq_on_source_le F₀ F₁ G₁ harrow p h]

end Directed

end MagnitudeConjecture.LinearPathCategory
