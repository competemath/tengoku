import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_eq_of_base_closedPoint_eq_and_exists_base_closedPoint_eq_and_isClosed_of_isAlgClosed.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_eq_of_base_closedPoint_eq_and_exists_base_closedPoint_eq_and_isClosed_of_isAlgClosed

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

/--
@isnad1 id=and.0h3v.s10.d32ff9b9530b from=translated src=- shape=6c607804 vocab=06f9c798
-/
theorem solution
    (κ : Type u) [Field κ] [IsAlgClosed κ] {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of κ)) [LocallyOfFiniteType f] :
    (∀ (y y' : Spec (CommRingCat.of κ) ⟶ Y), y ≫ f = 𝟙 _ → y' ≫ f = 𝟙 _ →
        y.base (IsLocalRing.closedPoint κ) = y'.base (IsLocalRing.closedPoint κ) → y = y') ∧
    (∀ q : Y, IsClosed ({q} : Set Y) →
        ∃ y : Spec (CommRingCat.of κ) ⟶ Y, y ≫ f = 𝟙 _ ∧ y.base (IsLocalRing.closedPoint κ) = q) ∧
    (Finite Y → ∀ q : Y, IsClosed ({q} : Set Y)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro y y' hy hy' h
    exact ext_of_apply_closedPoint_eq f hy hy' h
  · intro q hq
    exact ⟨pointOfClosedPoint f q hq, pointOfClosedPoint_comp f q hq,
      pointOfClosedPoint_apply f q hq _⟩
  · intro hY q
    haveI : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace f
    haveI : Finite Y := hY
    exact isClosed_discrete _
