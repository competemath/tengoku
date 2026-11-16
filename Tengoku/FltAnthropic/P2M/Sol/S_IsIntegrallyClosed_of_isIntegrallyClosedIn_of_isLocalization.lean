import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IsIntegrallyClosed_of_isIntegrallyClosedIn_of_isLocalization.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open_scoped`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IsIntegrallyClosed_of_isIntegrallyClosedIn_of_isLocalization

namespace IsIntegrallyClosed export _root_.IsIntegrallyClosed (algebraMap_eq_of_integral) end IsIntegrallyClosed
open scoped _root_.IsIntegrallyClosed in

theorem IsIntegrallyClosed.of_isIntegrallyClosedIn_of_isLocalization
    {C : Type*} [CommRing C] [IsDomain C] (M : Submonoid C) (hM : M ≤ nonZeroDivisors C)
    (L : Type*) [CommRing L] [IsDomain L] [Algebra C L] [IsLocalization M L]
    [IsIntegrallyClosedIn C L] [IsIntegrallyClosed L] : IsIntegrallyClosed C := by
  let K := FractionRing C
  have hg : ∀ y : M, IsUnit (algebraMap C K y) := fun y =>
    isUnit_iff_ne_zero.mpr
      ((map_ne_zero_iff _ (IsFractionRing.injective C K)).mpr (nonZeroDivisors.ne_zero (hM y.2)))
  letI algLK : Algebra L K := (IsLocalization.lift (M := M) (S := L) hg).toAlgebra
  haveI : IsScalarTower C L K :=
    IsScalarTower.of_algebraMap_eq' (R := C) (S := L) (A := K) (IsLocalization.lift_comp (M := M) hg).symm
  haveI : IsFractionRing L K := IsFractionRing.isFractionRing_of_isLocalization M L K hM
  refine (isIntegrallyClosed_iff K).mpr fun {x} hx => ?_
  have hxL : IsIntegral L x := hx.tower_top
  obtain ⟨l, rfl⟩ := (isIntegrallyClosed_iff K).mp inferInstance hxL
  have hl : IsIntegral C l :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom C L K) (IsFractionRing.injective L K)).mp hx
  obtain ⟨c, rfl⟩ := IsIntegrallyClosedIn.algebraMap_eq_of_integral hl
  exact ⟨c, IsScalarTower.algebraMap_apply C L K c⟩

theorem solution
    {C : Type*} [CommRing C] [IsDomain C] (M : Submonoid C) (hM : M ≤ nonZeroDivisors C)
    (L : Type*) [CommRing L] [IsDomain L] [Algebra C L] [IsLocalization M L]
    [IsIntegrallyClosedIn C L] [IsIntegrallyClosed L] : IsIntegrallyClosed C :=
  IsIntegrallyClosed.of_isIntegrallyClosedIn_of_isLocalization M hM L
