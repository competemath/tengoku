import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_JqCoeff
import Tengoku.FltAnthropic.Theorems.Thm_ModularCurve_map_intCast_pow_char_eq_qExpand
import Tengoku.Seed.RingTheory.Algebraic.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_qExpand_jqNModC_eq_pow_unconditional.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_qExpand_jqNModC_eq_pow_unconditional

noncomputable section
open HahnSeries

namespace ModularCurve
export _root_.ModularCurve (jqModC jqNModC jqModC_eq_map_intCast qExpand qExpand_congr qExpand_qExpand jNum constantCoeff_jNum ofPowerSeries_coeff_of_neg jq_pow map_intCast_pow_char_eq_qExpand)
open _root_.ModularCurve
namespace CharLRows

variable (K : Type*) [CommRing K]

/--
@isnad1 id=eq.0h2v.s8.3de162a78d7f from=translated src=- shape=44ad32bf vocab=33b8cdbe
-/
theorem qExpand_jqModC_eq_pow (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ] :
    qExpand K ℓ (jqModC K) = (jqModC K) ^ ℓ := by
  rw [jqModC_eq_map_intCast K]
  exact (map_intCast_pow_char_eq_qExpand ℓ _).symm

/--
@isnad1 id=eq.0h3v.s8.74eea26ed224 from=translated src=- shape=b76beba9 vocab=c759e896
-/
theorem qExpand_jqNModC_eq_pow (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ] :
    qExpand K ℓ (jqNModC K N) = (jqNModC K N) ^ ℓ := by
  rw [jqNModC, qExpand_qExpand, qExpand_congr (mul_comm ℓ N), ← qExpand_qExpand,
    qExpand_jqModC_eq_pow K ℓ, map_pow]

end CharLRows

end ModularCurve
end

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_qExpand_jqNModC_eq_pow_unconditional.ModularCurve in
/--
@isnad1 id=eq.0h3v.s8.74eea26ed224 from=translated src=- shape=b76beba9 vocab=c759e896
-/
theorem solution (K : Type*) [CommRing K] (N : ℕ) [NeZero N] {ℓ : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] :
    qExpand K ℓ (jqNModC K N) = (jqNModC K N) ^ ℓ :=
  CharLRows.qExpand_jqNModC_eq_pow K N ℓ
