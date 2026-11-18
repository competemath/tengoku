import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_LambdaSquared
import Tengoku.Seed.NumberTheory.NumberField.InfinitePlace.Basic
import Tengoku.Seed.NumberTheory.NumberField.Discriminant.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LanglandsTunnell_CubicInduction_lamSqArch_eq_neg_one_pow_nrComplexPlaces.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LanglandsTunnell_CubicInduction_lamSqArch_eq_neg_one_pow_nrComplexPlaces

set_option autoImplicit false

open NumberField

/--
@isnad1 id=eq.0h1v.s5.6a223c1ec485 from=translated src=- shape=66259890 vocab=1bb84841
-/
theorem solution
    (K : Type) [Field K] [NumberField K] :
    LanglandsTunnell.CubicInduction.lamSqArch K = (-1 : ℂ) ^ NumberField.InfinitePlace.nrComplexPlaces K := by
  classical
  have hiff : LanglandsTunnell.CubicInduction.discQ K < 0 ↔ discr K < 0 := by
    rw [← LanglandsTunnell.CubicInduction.discr_neg_iff K (integralBasis K), ← coe_discr, Int.cast_lt_zero]
  have hsign : (discr K).sign = (-1) ^ NumberField.InfinitePlace.nrComplexPlaces K := NumberField.sign_discr K
  unfold LanglandsTunnell.CubicInduction.lamSqArch
  by_cases hneg : discr K < 0
  · rw [ite_eq_left (hiff.mpr hneg)]
    rw [Int.sign_eq_neg_one_of_neg hneg] at hsign
    rcases Nat.even_or_odd (NumberField.InfinitePlace.nrComplexPlaces K) with h | h
    · rw [h.neg_one_pow] at hsign
      norm_num at hsign
    · rw [h.neg_one_pow]
  · rw [ite_eq_right (mt hiff.mp hneg)]
    have hpos : 0 < discr K := lt_of_le_of_ne (not_lt.mp hneg) (discr_ne_zero K).symm
    rw [Int.sign_eq_one_of_pos hpos] at hsign
    rcases Nat.even_or_odd (NumberField.InfinitePlace.nrComplexPlaces K) with h | h
    · rw [h.neg_one_pow]
    · rw [h.neg_one_pow] at hsign
      norm_num at hsign
