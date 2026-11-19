import Tengoku.MagicSquaresFieldsLean.MagicSquares.Characters.PowerIndicator
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Characters.PowerExpansion
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Weil.AffineMultiplicative
import Tengoku.MagicSquaresFieldsLean.MagicSquares.CenterOne.SquareCount

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares

open scoped BigOperators Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The unnormalized Section 14 indicator for eight affine power conditions.-/
noncomputable def affinePowerWeight (n d : ℕ) (coeff : Fin 8 → F) (t : F) : ℝ :=
  ∏ i, powerIndicatorNumerator n d (1 + coeff i * t)

/-- Exact expansion into the `d^8` character sums.
@isnad1 id=eq.4h5v.s8.86ab73fd21e6 from=translated src=- shape=a2132d66 vocab=44f034c6
-/
theorem affinePowerWeight_sum_expand {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (chi : MulChar F ℂ) (horder : orderOf chi = d)
    (hdgcd : d = powerIndex n (Fintype.card F)) (coeff : Fin 8 → F) :
    (∑ t : F, affinePowerWeight n d coeff t) =
      ∑ e : Fin 8 → Fin d,
        (∑ t : F, chi (∏ i, (1 + coeff i * t) ^ (e i : ℕ))).re := by
  have hc : ((∑ t : F, affinePowerWeight n d coeff t : ℝ) : ℂ) =
      ∑ e : Fin 8 → Fin d, ∑ t : F, chi (∏ i, (1 + coeff i * t) ^ (e i : ℕ)) := by
    rw [Complex.ofReal_sum, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    simp only [affinePowerWeight, Complex.ofReal_prod]
    simp_rw [← sum_character_powers_eq_indicator hn hd chi horder hdgcd]
    rw [Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro e _
    simp only [map_prod, map_pow]
  have hr := congrArg Complex.re hc
  simpa only [Complex.ofReal_re, Complex.re_sum] using hr

omit [Fintype F] in
/-- The weighted indicator is dominated by the exact power indicator,
including all parameters where an entry vanishes.
@isnad1 id=le.2h5v.s8.cf79896d356f from=translated src=- shape=a62f138e vocab=806a5aea
-/
theorem affinePowerWeight_le_indicator {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (coeff : Fin 8 → F) (t : F) :
    affinePowerWeight n d coeff t ≤
      if ∀ i, IsNthPower n (1 + coeff i * t) then (d : ℝ) ^ 8 else 0 := by
  by_cases h : ∀ i, IsNthPower n (1 + coeff i * t)
  · rw [ite_eq_left h]
    calc
      _ ≤ ∏ _i : Fin 8, (d : ℝ) := by
        apply Finset.prod_le_prod
        · intro i _
          exact powerIndicatorNumerator_nonneg _ _ _
        · intro i _
          exact powerIndicatorNumerator_le hd _
      _ = _ := by simp
  · rw [ite_eq_right h]
    push Not at h
    obtain ⟨i, hi⟩ := h
    have hz : affinePowerWeight n d coeff t = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      exact powerIndicatorNumerator_eq_zero_of_not_power hn hi
    exact hz.le

namespace Square3

omit [DecidableEq F] in
/--
@isnad1 id=iff.0h4v.s6.bdff40a449b2 from=translated src=- shape=67d469c5 vocab=79d70b1e
-/
theorem noncenter_powers_iff_mem (n : ℕ) (b t : F) :
    (∀ i, IsNthPower n (1 + centerOneNoncenterCoeff b i * t)) ↔
      t ∈ centerOnePowerParameters n b := by
  rw [mem_centerOnePowerParameters]
  constructor
  · intro h k
    by_cases hk : k = 4
    · subst k
      refine ⟨1, ?_⟩
      simp [centerOneCoeff]
    · obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hk
      exact h i
  · intro h i
    exact h ((4 : Fin 9).succAbove i)

end Square3
end MagicSquares

/-!
## General-power existence (paper, Theorem 14.1)

The counting estimate above now supplies the existence criterion.
-/

namespace MagicSquares.Square3

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

end MagicSquares.Square3
