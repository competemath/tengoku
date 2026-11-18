import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_JqCoeff
import Tengoku.FltAnthropic.Theorems.Thm_ModularCurve_frobenius_identity_geom_unconditional

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_jqNModC_pow_eq_jqNModC_mul_of_charP.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_jqNModC_pow_eq_jqNModC_mul_of_charP

set_option autoImplicit false

open ModularCurve

theorem solution
    (K : Type) [CommRing K] (q : ℕ) [Fact q.Prime] [CharP K q] (n : ℕ) [NeZero n] [NeZero (q * n)] :
    (jqNModC K n) ^ q = jqNModC K (q * n) := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  haveI : NeZero (n * q) := ⟨by rw [mul_comm]; exact NeZero.ne (q * n)⟩
  have h1 : jqNModC K q = (jqModC K) ^ q := ModularCurve.frobenius_identity_geom_unconditional K
  calc (jqNModC K n) ^ q = qExpand K n ((jqModC K) ^ q) := by rw [jqNModC, map_pow]
    _ = qExpand K n (qExpand K q (jqModC K)) := by rw [← h1, jqNModC]
    _ = qExpand K (n * q) (jqModC K) := by rw [qExpand_qExpand]
    _ = jqNModC K (q * n) := by rw [jqNModC, qExpand_congr (mul_comm n q)]
