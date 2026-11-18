import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_MvFormalGroup_BasicV2
import Tengoku.FltAnthropic.P2M.Sol.S_MvFormalGroup_coeff_nthSeries_pow_eq_zero_of_hasseWitt_pow_eq_zero_zmodp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MvFormalGroup_coeff_nthSeries_pow_eq_zero_of_hasseWitt_pow_eq_zero_zmodp.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
attribute [-instance] MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing
attribute [-simp] MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg'

open MvPowerSeries

universe u

/--
@isnad1 id=eq.2h6v.s10.2a6f5fefdb65 from=translated src=- shape=0b82e4e9 vocab=a4fab963
-/
theorem Tengoku.FltAnthropic.MvFormalGroup.coeff_nthSeries_pow_eq_zero_of_hasseWitt_pow_eq_zero_zmodp
    (p : ℕ) [Fact p.Prime] {d : ℕ} (F : MvFormalGroup d (ZMod p)) [F.IsComm]
    (ν : ℕ)
    (hB : (Matrix.of fun i j : Fin d => (F.nthSeries p i).coeff (Finsupp.single j p)) ^ ν = 0)
    (i : Fin d) (m : Fin d →₀ ℕ) (hm : ∃ j, ¬ p ^ (ν + 1) ∣ m j) :
    (F.nthSeries (p ^ ν) i).coeff m = 0 := by exact @_root_.P2MW.S_MvFormalGroup_coeff_nthSeries_pow_eq_zero_of_hasseWitt_pow_eq_zero_zmodp.solution p _ d F _ ν hB i m hm
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
