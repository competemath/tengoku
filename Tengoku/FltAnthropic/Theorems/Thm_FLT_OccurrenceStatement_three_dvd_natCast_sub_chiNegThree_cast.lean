import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularForm_EisensteinChiNegThree
import Tengoku.FltAnthropic.P2M.Sol.S_FLT_OccurrenceStatement_three_dvd_natCast_sub_chiNegThree_cast

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_FLT_OccurrenceStatement_three_dvd_natCast_sub_chiNegThree_cast.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open EisensteinWeightOne
/--
@isnad1 id=dvd.0h2v.s6.f42a8396cff9 from=translated src=- shape=dc2606f7 vocab=e55f4cee
-/
theorem FLT.OccurrenceStatement.three_dvd_natCast_sub_chiNegThree_cast
    (R : Type*) [CommRing R] (ℓ : ℕ) :
    (3 : R) ∣ (ℓ : R) - ((chiNegThree ℓ : ℤ) : R) := by exact @_root_.P2MW.S_FLT_OccurrenceStatement_three_dvd_natCast_sub_chiNegThree_cast.solution R _ ℓ
