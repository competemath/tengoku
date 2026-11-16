import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_Algebra_IsInvariant_moduleFinite_and_finiteType_of_finiteType

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Algebra_IsInvariant_flat_and_finiteType_of_isDedekindDomain.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Algebra_IsInvariant_flat_and_finiteType_of_isDedekindDomain

set_option autoImplicit false

/--
@isnad1 id=and.0h4v.s7.28d04280ca39 from=translated src=- shape=dd153807 vocab=7040db3a
-/
theorem solution
    {B S A : Type*} [CommRing B] [IsDedekindDomain B] [CommRing S] [CommRing A]
    [Algebra B S] [Algebra B A] [Algebra S A] [IsScalarTower B S A] [FaithfulSMul S A]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G A] [Algebra.IsInvariant S A G]
    [Module.Flat B A] [Algebra.FiniteType B A] :
    Module.Flat B S ∧ Algebra.FiniteType B S := by
  haveI : Module.IsTorsionFree B A := Module.Flat.isTorsionFree
  have hinj : Function.Injective (IsScalarTower.toAlgHom B S A) := FaithfulSMul.algebraMap_injective S A
  haveI : Module.IsTorsionFree B S :=
    hinj.moduleIsTorsionFree _ (fun r s => map_smul (IsScalarTower.toAlgHom B S A) r s)
  exact ⟨inferInstance, (Algebra.IsInvariant.moduleFinite_and_finiteType_of_finiteType B S A G).2⟩
