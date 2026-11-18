import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_X0
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_PhiGen

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_exists_aeval_jq_sub_holomorphicAtInfty.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_exists_aeval_jq_sub_holomorphicAtInfty

noncomputable section

open Polynomial

namespace ModularCurve
export _root_.ModularCurve (algebraMap_apply_eq_single jq coeff_jq_pow_self coeff_jq_pow_of_lt PoleOrderLE)
open _root_.ModularCurve

/--
@isnad1 id=poleorde.1h2v.s8.a2733dfc9ad1 from=translated src=- shape=d5fd7e0b vocab=3952884c
-/
theorem poleOrderLE_sub_aeval_jq_succ {f : LaurentSeries ℚ} {n : ℕ}
    (hf : PoleOrderLE f (n + 1)) :
    PoleOrderLE
      (f - Polynomial.aeval jq
        (Polynomial.C (f.coeff (-(n + 1 : ℕ) : ℤ)) * Polynomial.X ^ (n + 1))) n := by
  intro k hk
  rw [HahnSeries.coeff_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow,
    algebraMap_apply_eq_single, HahnSeries.coeff_single_zero_mul]
  rcases (show k ≤ -((n + 1 : ℕ) : ℤ) by omega).eq_or_lt with heq | hlt
  · rw [heq, coeff_jq_pow_self, mul_one, sub_self]
  · rw [hf k hlt, coeff_jq_pow_of_lt hlt, mul_zero, sub_zero]

/--
@isnad1 id=ex.1h2v.s8.1d233da9e2ec from=translated src=- shape=c74d3476 vocab=e68bfb57
-/
theorem exists_aeval_jq_sub_holomorphicAtInfty' (n : ℕ) :
    ∀ f : LaurentSeries ℚ, PoleOrderLE f n →
      ∃ P : Polynomial ℚ, P.natDegree ≤ n ∧ PoleOrderLE (f - Polynomial.aeval jq P) 0 := by
  induction n with
  | zero =>
    intro f hf
    exact ⟨0, by simp, by simpa using hf⟩
  | succ n ih =>
    intro f hf
    obtain ⟨Q, hQdeg, hQ⟩ := ih _ (poleOrderLE_sub_aeval_jq_succ hf)
    refine ⟨Polynomial.C (f.coeff (-(n + 1 : ℕ) : ℤ)) * Polynomial.X ^ (n + 1) + Q, ?_, ?_⟩
    · refine le_trans (Polynomial.natDegree_add_le _ _)
        (max_le (Polynomial.natDegree_C_mul_X_pow_le _ _) ?_)
      omega
    · intro k hk
      rw [map_add, sub_add_eq_sub_sub]
      exact hQ k hk

end ModularCurve

/--
@isnad1 id=ex.1h2v.s8.1d233da9e2ec from=translated src=- shape=c74d3476 vocab=e68bfb57
-/
theorem solution (n : ℕ) :
    ∀ f : LaurentSeries ℚ, ModularCurve.PoleOrderLE f n →
      ∃ P : Polynomial ℚ, P.natDegree ≤ n ∧ ModularCurve.PoleOrderLE (f - Polynomial.aeval ModularCurve.jq P) 0 :=
  ModularCurve.exists_aeval_jq_sub_holomorphicAtInfty' n

