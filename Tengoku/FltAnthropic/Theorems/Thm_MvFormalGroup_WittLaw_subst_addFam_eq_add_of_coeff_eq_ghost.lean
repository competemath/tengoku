import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_MvFormalGroup_NegV2
import Tengoku.FltAnthropic.Definitions.Def_MvFormalGroup_CartierModule
import Tengoku.FltAnthropic.P2M.Sol.S_MvFormalGroup_WittLaw_subst_addFam_eq_add_of_coeff_eq_ghost

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MvFormalGroup_WittLaw_subst_addFam_eq_add_of_coeff_eq_ghost.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
set_option autoImplicit false

universe u

/--
@isnad1 id=eq.2h4v.s9.b2f5117aaf11 from=translated src=- shape=6ad829b3 vocab=46b7a08c
-/
theorem Tengoku.FltAnthropic.MvFormalGroup.WittLaw.subst_addFam_eq_add_of_coeff_eq_ghost
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] (c : ℕ → R) (G : MvPowerSeries ℕ R)
    (hG : ∀ k n : ℕ, (MvPowerSeries.coeff (Finsupp.single k (p ^ n)) G : R) = (p : R) ^ k * c (k + n))
    (hG' : ∀ e : ℕ →₀ ℕ, (∀ k n : ℕ, e ≠ Finsupp.single k (p ^ n)) → (MvPowerSeries.coeff e G : R) = 0) :
    MvPowerSeries.subst (MvFormalGroup.WittLaw.addFam p R) G =
      MvPowerSeries.subst (fun m => (MvPowerSeries.X (0, m) : MvPowerSeries (Fin 2 × ℕ) R)) G +
        MvPowerSeries.subst (fun m => (MvPowerSeries.X (1, m) : MvPowerSeries (Fin 2 × ℕ) R)) G := by exact @_root_.P2MW.S_MvFormalGroup_WittLaw_subst_addFam_eq_add_of_coeff_eq_ghost.solution p _ R _ c G hG hG'
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
