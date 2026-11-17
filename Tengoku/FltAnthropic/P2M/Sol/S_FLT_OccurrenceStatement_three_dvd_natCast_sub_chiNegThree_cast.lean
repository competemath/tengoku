import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularForm_EisensteinChiNegThree

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_FLT_OccurrenceStatement_three_dvd_natCast_sub_chiNegThree_cast.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_FLT_OccurrenceStatement_three_dvd_natCast_sub_chiNegThree_cast

open EisensteinWeightOne

/--
@isnad1 id=dvd.0h2v.s6.f42a8396cff9 from=translated src=- shape=dc2606f7 vocab=e55f4cee
-/
theorem solution (R : Type*) [CommRing R] (ℓ : ℕ) :
    (3 : R) ∣ (ℓ : R) - ((chiNegThree ℓ : ℤ) : R) := by
  have hint : (3 : ℤ) ∣ (ℓ : ℤ) - chiNegThree ℓ := by
    simp only [chiNegThree]
    split_ifs <;> omega
  obtain ⟨c, hc⟩ := hint
  refine ⟨(c : R), ?_⟩
  have h := congrArg (fun z : ℤ => (z : R)) hc
  push_cast at h
  convert h using 2
