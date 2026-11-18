import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_MvFormalGroup_BasicV2
import Tengoku.FltAnthropic.P2M.Sol.S_MvFormalGroup_exists_subst_eq_X_of_linearPart_eq_one

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MvFormalGroup_exists_subst_eq_X_of_linearPart_eq_one.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
attribute [-instance] MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid
attribute [-simp] MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg' MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast

open MvPowerSeries

universe u

theorem Tengoku.FltAnthropic.MvFormalGroup.exists_subst_eq_X_of_linearPart_eq_one
    {𝓞 : Type u} [CommRing 𝓞] {d : ℕ}
    (φ : Fin d → MvPowerSeries (Fin d) 𝓞)
    (hφ0 : ∀ i, (φ i).constantCoeff = 0)
    (hφ1 : MvFormalGroup.linearPart φ = 1) :
    ∃ ψ : Fin d → MvPowerSeries (Fin d) 𝓞,
      (∀ i, (ψ i).constantCoeff = 0) ∧
      (∀ i, subst φ (ψ i) = X i) ∧
      (∀ i, subst ψ (φ i) = X i) := by exact @_root_.P2MW.S_MvFormalGroup_exists_subst_eq_X_of_linearPart_eq_one.solution 𝓞 _ d φ hφ0 hφ1
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
