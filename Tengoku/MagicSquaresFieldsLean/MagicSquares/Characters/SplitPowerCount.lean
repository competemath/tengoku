import Tengoku.MagicSquaresFieldsLean.MagicSquares.Characters.PowerIndicator
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Characters.PowerExpansion
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Weil.SharpMultiplicative

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares

open scoped BigOperators Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Unnormalized power indicator for a family of shifted linear factors.-/
noncomputable def splitPowerWeight {r : ℕ} (n d : ℕ) (roots : Fin r → F) (t : F) : ℝ :=
  ∏ i, powerIndicatorNumerator n d (t - roots i)

/-- Exact character expansion for an arbitrary finite family of roots.-/
theorem splitPowerWeight_sum_expand {r n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (chi : MulChar F ℂ) (horder : orderOf chi = d)
    (hdgcd : d = powerIndex n (Fintype.card F)) (roots : Fin r → F) :
    (∑ t : F, splitPowerWeight n d roots t) =
      ∑ e : Fin r → Fin d,
        (∑ t : F, chi (∏ i, (t - roots i) ^ (e i : ℕ))).re := by
  have hc : ((∑ t : F, splitPowerWeight n d roots t : ℝ) : ℂ) =
      ∑ e : Fin r → Fin d, ∑ t : F, chi (∏ i, (t - roots i) ^ (e i : ℕ)) := by
    rw [Complex.ofReal_sum, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    simp only [splitPowerWeight, Complex.ofReal_prod]
    simp_rw [← sum_character_powers_eq_indicator hn hd chi horder hdgcd]
    rw [Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro e _
    simp only [map_prod, map_pow]
  have hr := congrArg Complex.re hc
  simpa only [Complex.ofReal_re, Complex.re_sum] using hr

end MagicSquares
