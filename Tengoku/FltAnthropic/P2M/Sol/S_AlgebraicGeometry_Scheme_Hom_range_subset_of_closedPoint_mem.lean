import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_range_subset_of_closedPoint_mem.lean`: wrote out 5 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 3 `p2m_export`, 1 `p2m_open`, 1 `p2m_open_scoped`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_range_subset_of_closedPoint_mem

set_option autoImplicit false

universe u

open _root_.CategoryTheory open _root_.AlgebraicGeometry

namespace AlgebraicGeometry export _root_.AlgebraicGeometry (Scheme.Hom Spec Scheme) namespace Scheme export _root_.AlgebraicGeometry.Scheme (Hom Opens) namespace Hom export _root_.AlgebraicGeometry.Scheme.Hom (continuous) end AlgebraicGeometry.Scheme.Hom
open scoped _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Hom in
/--
@isnad1 id=le.1h4v.s9.4d89afaad2ec from=translated src=- shape=a163e300 vocab=5adf2bd4
-/
theorem AlgebraicGeometry.Scheme.Hom.range_subset_of_closedPoint_mem_aux {O : Type u} [CommRing O] [IsLocalRing O] {Y : Scheme.{u}}
    (W : Y.Opens) (σ : Spec (CommRingCat.of O) ⟶ Y) (hW : σ.base (IsLocalRing.closedPoint O) ∈ W) :
    Set.range σ.base ⊆ (W : Set Y) := by
  rintro _ ⟨x, rfl⟩
  exact ((IsLocalRing.specializes_closedPoint x).map σ.continuous).mem_open W.2 hW

/--
@isnad1 id=le.1h4v.s9.4d89afaad2ec from=translated src=- shape=a163e300 vocab=5adf2bd4
-/
theorem solution
    {O : Type u} [CommRing O] [IsLocalRing O] {Y : Scheme.{u}}
    (W : Y.Opens) (σ : Spec (CommRingCat.of O) ⟶ Y) (hW : σ.base (IsLocalRing.closedPoint O) ∈ W) :
    Set.range σ.base ⊆ (W : Set Y) :=
  AlgebraicGeometry.Scheme.Hom.range_subset_of_closedPoint_mem_aux W σ hW
