import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_MvFormalGroup_BasicV2
import Tengoku.FltAnthropic.P2M.Sol.S_MvFormalGroup_coeff_eq_zero_of_linearPart_eq_zero_of_subst_eq_charP

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MvFormalGroup_coeff_eq_zero_of_linearPart_eq_zero_of_subst_eq_charP.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
attribute [-instance] MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing
attribute [-simp] MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg'

open MvPowerSeries

universe u

theorem Tengoku.FltAnthropic.MvFormalGroup.coeff_eq_zero_of_linearPart_eq_zero_of_subst_eq_charP
    {S : Type u} [CommRing S] (p : ℕ) [Fact p.Prime] [CharP S p]
    {g h : ℕ} (F : MvFormalGroup g S) (G : MvFormalGroup h S)
    (θ : Fin h → MvPowerSeries (Fin g) S)
    (hθ0 : ∀ i, (θ i).constantCoeff = 0)
    (hθ1 : MvFormalGroup.linearPart θ = 0)
    (hθF : ∀ i, subst F.toPowerSeries (θ i) =
      subst (Sum.elim
        (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) S)) (θ j))
        (fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) S)) (θ j)))
        (G.toPowerSeries i))
    (i : Fin h) (m : Fin g →₀ ℕ) (hm : ∃ j, ¬ p ∣ m j) :
    (θ i).coeff m = 0 := by exact @_root_.P2MW.S_MvFormalGroup_coeff_eq_zero_of_linearPart_eq_zero_of_subst_eq_charP.solution S _ p _ _ g h F G θ hθ0 hθ1 hθF i m hm
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
