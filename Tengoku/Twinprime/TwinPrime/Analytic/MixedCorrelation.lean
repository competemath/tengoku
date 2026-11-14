import Tengoku.Twinprime.TwinPrime.Analytic.PrimeDistribution
import Tengoku.Twinprime.TwinPrime.Analytic.EvenAsymptotics
import Tengoku.Twinprime.TwinPrime.Analytic.GrowthBounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The mixed correlation and its separate analytic inputs

The finite estimate separates reduced odd residue classes from the exceptional
even moduli. The smoothed Möbius/totient sum is an ordinary one-variable
arithmetic quantity; no shifted-prime lower bound is hidden in its definition.
-/

noncomputable section

open Finset ArithmeticFunction Filter
open scoped ArithmeticFunction.Moebius

namespace TwinPrime.Analytic

def truncatedWeight (U d : ℕ) : ℝ := (μ d : ℝ) * Real.log ((U : ℝ) / d)

/-- The smoothed odd Möbius/totient main coefficient.-/
def smoothedTotientSum (U : ℕ) : ℝ :=
  ∑ d ∈ range (U + 1) with Odd d, truncatedWeight U d / Nat.totient d

/--
@isnad1 id=eq.0h2v.s7.c7679edd3871 from=translated src=- shape=17fd30f0 vocab=18be03e2
-/
theorem mixedCorrelation_eq_odd_add_even (U X : ℕ) :
    mixedCorrelation U X =
      (∑ d ∈ range (U + 1) with Odd d, truncatedWeight U d *
        ∑ n ∈ Ioc X (2 * X) with d ∣ n, vonMangoldt (n + 2)) +
      ∑ d ∈ range (U + 1) with Even d, truncatedWeight U d *
        ∑ n ∈ Ioc X (2 * X) with d ∣ n, vonMangoldt (n + 2) := by
  rw [mixedCorrelation_eq_progressions]
  simpa only [truncatedWeight, Nat.not_odd_iff_even] using
    (sum_filter_add_sum_filter_not (range (U + 1)) Odd
      (fun d => (μ d : ℝ) * Real.log ((U : ℝ) / d) *
        ∑ n ∈ Ioc X (2 * X) with d ∣ n, vonMangoldt (n + 2))).symm

/-- The primary cutoff tends to infinity, so a known one-variable limit may
be applied to it without strengthening its quantifiers.
@isnad1 id=tendsto.0h0v.s3.3818bec24bfa from=translated src=- shape=41b74a9e vocab=d08327af
-/
theorem tendsto_primaryCutoff : Tendsto primaryCutoff atTop atTop := by
  exact tendsto_nat_floor_atTop.comp
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 5)).comp tendsto_natCast_atTop_atTop)

/-- Convert a normalized limit to an explicit eventual linear error budget.
@isnad1 id=eventual.2h3v.s6.798f248febdb from=translated src=- shape=75474e5a vocab=d415dacc
-/
theorem eventually_abs_sub_mul_le_of_tendsto_div (f : ℕ → ℝ) {C ε : ℝ}
    (hε : 0 < ε) (hf : Tendsto (fun X : ℕ => f X / X) atTop (nhds C)) :
    ∀ᶠ X : ℕ in atTop, |f X - C * X| ≤ ε * X := by
  have habs : Tendsto (fun X : ℕ => |f X / X - C|) atTop (nhds 0) := by
    simpa only [sub_self, abs_zero] using (hf.sub_const C).abs
  have hnear := habs.eventually (gt_mem_nhds hε)
  filter_upwards [hnear, eventually_ge_atTop 1] with X hX hX1
  have hx : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have heq : f X / X - C = (f X - C * X) / X := by field_simp
  rw [heq, abs_div, abs_of_pos hx] at hX
  exact ((div_lt_iff₀ hx).mp hX).le

end TwinPrime.Analytic
