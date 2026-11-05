module

public import Tengoku.KummerCriterion.KummerCriterion.Reflection.ResidueSymbol.ArtinHasse.Part1
public import Tengoku.Seed.RingTheory.PowerSeries.Log
import Tengoku.Seed.Analysis.SpecialFunctions.Gamma.Basic
import Tengoku.Seed.RingTheory.WittVector.IsPoly
import Tengoku.Seed.Tactic.ENatToNat
import Tengoku.Seed.Tactic.NormNum.Irrational
import Tengoku.Seed.Tactic.NormNum.IsCoprime
import Tengoku.Seed.Tactic.NormNum.IsSquare
import Tengoku.Seed.Tactic.NormNum.LegendreSymbol
import Tengoku.Seed.Tactic.NormNum.ModEq
import Tengoku.Seed.Tactic.NormNum.NatFib
import Tengoku.Seed.Tactic.NormNum.NatLog
import Tengoku.Seed.Tactic.NormNum.NatSqrt
import Tengoku.Seed.Tactic.NormNum.Ordinal
import Tengoku.Seed.Tactic.NormNum.Parity
import Tengoku.Seed.Tactic.NormNum.Prime
import Tengoku.Seed.Tactic.NormNum.RealSqrt
import Tengoku.Seed.Tactic.ReduceModChar

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Formal Artin-Hasse logarithm identity

This file proves the formal identity
`logOf (artinHasseExpSeries ell) = artinHasseLogSeries ell` over `ℚ`, together
with coefficient forms used by the later finite denominator transport.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace KummerCriterion

namespace Furtwaengler

namespace FiniteArtinHasseFormal

open PowerSeries

theorem coeff_pow_eq_zero_of_lt_of_constantCoeff_eq_zero
    {A : Type*} [CommRing A] (F : PowerSeries A)
    (hF0 : PowerSeries.constantCoeff F = 0) {n d : ℕ} (hdn : d < n) :
    PowerSeries.coeff d (F ^ n) = 0 := by
  have hle : (n : ℕ∞) ≤ (F ^ n).order :=
    PowerSeries.le_order_pow_of_constantCoeff_eq_zero n hF0
  exact PowerSeries.coeff_of_lt_order d ((ENat.natCast_lt_natCast.mpr hdn).trans_le hle)

theorem coeff_subst_log_eq_sum_Icc
    {A : Type*} [CommRing A] [Algebra ℚ A] (F : PowerSeries A)
    (hF0 : PowerSeries.constantCoeff F = 0) (d : ℕ) :
    PowerSeries.coeff d (PowerSeries.subst F (PowerSeries.log A)) =
      ∑ n ∈ Finset.Icc 1 d,
        algebraMap ℚ A (((-1 : ℚ) ^ (n + 1)) / n) *
          PowerSeries.coeff d (F ^ n) := by
  classical
  have hsubst : PowerSeries.HasSubst F :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hF0
  rw [PowerSeries.coeff_subst' hsubst]
  rw [finsum_eq_sum_of_support_subset]
  · refine Finset.sum_congr rfl ?_
    intro n hn
    have hn0 : n ≠ 0 := by
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      exact Nat.ne_zero_of_lt hn1
    simp [PowerSeries.coeff_log, hn0, smul_eq_mul]
  · rw [Function.support_subset_iff]
    intro n hnmem
    by_contra hnI
    by_cases hn0 : n = 0
    · subst n
      simp at hnmem
    · have hdn : d < n := by
        by_contra hdn
        have hn1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn0)
        have hnd : n ≤ d := by omega
        exact hnI (Finset.mem_Icc.mpr ⟨hn1, hnd⟩)
      have hcoeff := coeff_pow_eq_zero_of_lt_of_constantCoeff_eq_zero F hF0 hdn
      simp [hcoeff] at hnmem

end FiniteArtinHasseFormal

end Furtwaengler

end KummerCriterion

end
