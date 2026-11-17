import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_Flat
import Tengoku.FltAnthropic.Theorems.Thm_Algebra_eq_zero_of_forall_algHom_apply_eq_zero_of_isReduced_tensorProduct
import Tengoku.FltAnthropic.Theorems.Thm_HopfAlgebra_isReduced_of_finiteType_of_charZero

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HopfAlgebra_eq_of_forall_algHom_algebraicClosure_apply_eq_of_flat_ratLocalizedAt.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HopfAlgebra_eq_of_forall_algHom_algebraicClosure_apply_eq_of_flat_ratLocalizedAt

set_option autoImplicit false

open scoped TensorProduct nonZeroDivisors

namespace HopfAlgebra
export _root_.HopfAlgebra (isReduced_of_finiteType_of_charZero)
namespace SepPoints
open _root_.HopfAlgebra

private theorem faithfulSMul_rat (p : ℕ) : FaithfulSMul (GaloisRep.ratLocalizedAt p) ℚ :=
  (faithfulSMul_iff_algebraMap_injective _ ℚ).mpr Subtype.val_injective

private theorem isFractionRing_rat (p : ℕ) : IsFractionRing (GaloisRep.ratLocalizedAt p) ℚ := by
  haveI := faithfulSMul_rat p
  refine IsFractionRing.of_field (R := GaloisRep.ratLocalizedAt p) (K := ℚ) fun z => ?_
  refine ⟨⟨(z.num : ℚ), ?_⟩, ⟨(z.den : ℚ), ?_⟩, ?_⟩
  · show ((z.num : ℚ)).den.Coprime p
    simp
  · show ((z.den : ℚ)).den.Coprime p
    simp
  · change z = (z.num : ℚ) / (z.den : ℚ)
    exact (Rat.num_div_den z).symm

private theorem noZeroSMulDivisors_of_flat (p : ℕ) (H : Type) [CommRing H]
    [Algebra (GaloisRep.ratLocalizedAt p) H] [Module.Flat (GaloisRep.ratLocalizedAt p) H] :
    NoZeroSMulDivisors (GaloisRep.ratLocalizedAt p) H := by
  refine ⟨fun {c x} h => or_iff_not_imp_left.2 fun hc => ?_⟩
  have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := H)
    (mem_nonZeroDivisors_of_ne_zero hc)
  exact hreg (h.trans (smul_zero c).symm)

end HopfAlgebra.SepPoints

open HopfAlgebra.SepPoints in
/--
@isnad1 id=eq.1h4v.s11.adabb70580db from=translated src=- shape=a8648ca4 vocab=1d13c998
-/
theorem solution
    (p : ℕ) (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Flat (GaloisRep.ratLocalizedAt p) H]
    (a b : H)
    (hab : ∀ f : H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ, f a = f b) :
    a = b := by
  haveI := HopfAlgebra.SepPoints.isFractionRing_rat p
  haveI := HopfAlgebra.SepPoints.noZeroSMulDivisors_of_flat p H
  haveI : Algebra.FiniteType ℚ (ℚ ⊗[GaloisRep.ratLocalizedAt p] H) := inferInstance
  haveI : IsReduced (ℚ ⊗[GaloisRep.ratLocalizedAt p] H) :=
    HopfAlgebra.isReduced_of_finiteType_of_charZero ℚ (ℚ ⊗[GaloisRep.ratLocalizedAt p] H)
  have h := Algebra.eq_zero_of_forall_algHom_apply_eq_zero_of_isReduced_tensorProduct
    (R := GaloisRep.ratLocalizedAt p) ℚ (AlgebraicClosure ℚ) (a - b)
    (fun f => by rw [map_sub, hab f, sub_self])
  exact sub_eq_zero.mp h
