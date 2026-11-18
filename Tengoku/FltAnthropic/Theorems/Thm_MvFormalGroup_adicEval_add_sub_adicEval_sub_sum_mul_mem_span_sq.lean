import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_MvFormalGroup_BasicV2
import Tengoku.FltAnthropic.Definitions.Def_MvFormalGroup_PointsV2
import Tengoku.FltAnthropic.P2M.Sol.S_MvFormalGroup_adicEval_add_sub_adicEval_sub_sum_mul_mem_span_sq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MvFormalGroup_adicEval_add_sub_adicEval_sub_sum_mul_mem_span_sq.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
open MvPowerSeries

universe u v

theorem Tengoku.FltAnthropic.MvFormalGroup.adicEval_add_sub_adicEval_sub_sum_mul_mem_span_sq
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
    (J : Ideal S) [IsAdicComplete J S] {d : ℕ}
    (f : MvPowerSeries (Fin d) R) (Df : Fin d → MvPowerSeries (Fin d) R)
    (hDf : ∀ (j : Fin d) (m : Fin d →₀ ℕ),
      (Df j).coeff m = ((m j + 1 : ℕ) : R) * f.coeff (m + Finsupp.single j 1))
    (x z : Fin d → S) (hx : ∀ s, x s ∈ J.radical) (hz : ∀ s, z s ∈ J.radical) :
    MvFormalGroup.adicEval J (x + z) f - MvFormalGroup.adicEval J x f
        - ∑ j, MvFormalGroup.adicEval J x (Df j) * z j ∈ (Ideal.span (Set.range z)) ^ 2 := by exact @_root_.P2MW.S_MvFormalGroup_adicEval_add_sub_adicEval_sub_sum_mul_mem_span_sq.solution R _ S _ _ J _ d f Df hDf x z hx hz
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
