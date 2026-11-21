import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_MvFormalGroup_NegV2
import Tengoku.FltAnthropic.P2M.Sol.S_MvFormalGroup_subst_nthSeries_eq_of_map_eq_and_exists_hom_of_ker_pow_eq_bot

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MvFormalGroup_subst_nthSeries_eq_of_map_eq_and_exists_hom_of_ker_pow_eq_bot.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
set_option autoImplicit false

universe u

/--
@isnad1 id=and.2h8v.s10.3440ded361c9 from=translated src=- shape=f80a9652 vocab=56a4041b
-/
theorem Tengoku.FltAnthropic.MvFormalGroup.subst_nthSeries_eq_of_map_eq_and_exists_hom_of_ker_pow_eq_bot
    {R S : Type u} [CommRing R] [CommRing S] (π : R →+* S) (μ : ℕ)
    (hI : RingHom.ker π ^ (μ + 1) = ⊥) (p n : ℕ) (hp : (p : R) ^ n = 0)
    {h : ℕ} (G : MvFormalGroup h R) [G.IsComm] :
    (∀ (τ : Type) (a b : Fin h → MvPowerSeries τ R),
        (∀ i, (a i).constantCoeff = 0) → (∀ i, (b i).constantCoeff = 0) →
        (∀ i, MvPowerSeries.map π (a i) = MvPowerSeries.map π (b i)) →
        ∀ i, MvPowerSeries.subst a (G.nthSeries (p ^ (n * μ)) i) =
          MvPowerSeries.subst b (G.nthSeries (p ^ (n * μ)) i)) ∧
    (∀ (g : ℕ) (F : MvFormalGroup g R) (φ : Fin h → MvPowerSeries (Fin g) R),
        (∀ i, (φ i).constantCoeff = 0) →
        (∃ f₀ : (F.map π).Hom (G.map π), ∀ i, f₀.toPowerSeries i = MvPowerSeries.map π (φ i)) →
        ∃ f : F.Hom G, ∀ i, f.toPowerSeries i = MvPowerSeries.subst φ (G.nthSeries (p ^ (n * μ)) i)) := by exact @_root_.P2MW.S_MvFormalGroup_subst_nthSeries_eq_of_map_eq_and_exists_hom_of_ker_pow_eq_bot.solution R S _ _ π μ hI p n hp h G _
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
