import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicCurve_TwoChartIntegralModel_eq_chartAlgFin_of_isIntegral_of_integrallyClosed.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_eq_chartAlgFin_of_isIntegral_of_integrallyClosed

set_option autoImplicit false

open AlgebraicCurve.TwoChartIntegralModel

theorem solution
    (R : Type) [CommRing R] (F : Type) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (B : Subalgebra R F) (hj : j ∈ B)
    (hint : ∀ x ∈ B, IsIntegral (Algebra.adjoin R ({j} : Set F)) x)
    (hic : ∀ x : F, IsIntegral B x → x ∈ B) :
    B = chartAlgFin R F j := by
  apply le_antisymm
  · intro x hx
    exact (mem_chartAlg_iff R F).mpr (hint x hx)
  · intro x hx
    have hx' : IsIntegral (Algebra.adjoin R ({j} : Set F)) x := (mem_chartAlg_iff R F).mp hx
    have hle : Algebra.adjoin R ({j} : Set F) ≤ B := Algebra.adjoin_le (Set.singleton_subset_iff.mpr hj)
    exact hic x (hx'.map_of_comp_eq (Subalgebra.inclusion hle).toRingHom (RingHom.id F) (by ext; rfl))
