import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_MvFormalGroup_BasicV2
import Tengoku.FltAnthropic.P2M.Sol.S_MvFormalGroup_coeff_iterate_sum_single_sub_coeff_nthSeries_single_mem_span

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MvFormalGroup_coeff_iterate_sum_single_sub_coeff_nthSeries_single_mem_span.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
attribute [-instance] MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing
attribute [-simp] MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg'

open MvPowerSeries

universe u

/--
@isnad1 id=mem.2h7v.s9.9dbf537a8436 from=translated src=- shape=9ac66f15 vocab=9b0df9a0
-/
theorem Tengoku.FltAnthropic.MvFormalGroup.coeff_iterate_sum_single_sub_coeff_nthSeries_single_mem_span
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] {d : ℕ} (F : MvFormalGroup d 𝓞) [F.IsComm]
    (G : (n : ℕ) → Fin d → MvPowerSeries (Fin n × Fin d) 𝓞)
    (hG1 : ∀ k, G 1 k = X ((0 : Fin 1), k))
    (hGsucc : ∀ (n : ℕ) (k : Fin d), G (n + 1) k =
      subst (Sum.elim
        (fun j => subst (fun sj : Fin n × Fin d => (X (Fin.castSucc sj.1, sj.2) :
          MvPowerSeries (Fin (n + 1) × Fin d) 𝓞)) (G n j))
        (fun j => (X (Fin.last n, j) : MvPowerSeries (Fin (n + 1) × Fin d) 𝓞)))
        (F.toPowerSeries k))
    (k i : Fin d) :
    (G p k).coeff (∑ s : Fin p, Finsupp.single (s, i) 1) -
        (F.nthSeries p k).coeff (Finsupp.single i p) ∈ Ideal.span {(p : 𝓞)} := by exact @_root_.P2MW.S_MvFormalGroup_coeff_iterate_sum_single_sub_coeff_nthSeries_single_mem_span.solution 𝓞 _ p _ d F _ G hG1 hGsucc k i
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
