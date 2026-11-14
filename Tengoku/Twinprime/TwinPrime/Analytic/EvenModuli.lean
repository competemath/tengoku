import Tengoku.Seed.NumberTheory.Chebyshev
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The non-reduced residue class at even moduli

For an even modulus dividing a positive `n`, the shifted integer `n+2` is
nonprime. Its von Mangoldt mass is bounded by the elementary `ψ-θ` estimate.
This deliberately loose bound is sufficient at the primary level `X^(2/5)`:
even after a logarithmic coefficient loss its total has power at most `X^(9/10)`.
No prime-distribution theorem is applied to a non-reduced residue class.
-/

noncomputable section

open Finset ArithmeticFunction

namespace TwinPrime.Analytic

/-- A uniform upper bound for any even-modulus shifted progression.-/
def evenProgressionBound (X : ℕ) : ℝ :=
  2 * Real.sqrt (2 * X + 2) * Real.log (2 * X + 2)

/--
@isnad1 id=le.0h1v.s3.3e1295a7acb4 from=translated src=- shape=b9369acb vocab=8fa2bb16
-/
theorem evenProgressionBound_nonneg (X : ℕ) : 0 ≤ evenProgressionBound X := by
  unfold evenProgressionBound
  apply mul_nonneg (by positivity)
  exact Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) X; linarith)

/--
@isnad1 id=not.3h2v.s5.b2b5f4b12cc6 from=translated src=- shape=991e4322 vocab=3213aabf
-/
theorem not_prime_add_two_of_even_dvd {q n : ℕ} (hq : Even q)
    (hqn : q ∣ n) (hn : 0 < n) : ¬ (n + 2).Prime := by
  intro hp
  have heven : Even n := even_iff_two_dvd.mpr ((even_iff_two_dvd.mp hq).trans hqn)
  have htwo : n + 2 = 2 := hp.even_iff.mp (heven.add (by decide : Even (2 : ℕ)))
  omega

/-- In particular, the exceptional even-modulus terms are never assigned `X/φ(q)`.
@isnad1 id=le.1h2v.s6.acd6e21099c7 from=translated src=- shape=91acaf38 vocab=18fcc921
-/
theorem even_shiftedProgression_le (X q : ℕ) (hq : Even q) :
    (∑ n ∈ Ioc X (2 * X) with q ∣ n, vonMangoldt (n + 2)) ≤
      evenProgressionBound X := by
  let Y : ℕ := 2 * X + 2
  have hY : (1 : ℝ) ≤ Y := by exact_mod_cast (show 1 ≤ Y by dsimp [Y]; omega)
  have hsub : ((Ioc X (2 * X)).filter (fun n => q ∣ n)).image (fun n => n + 2) ⊆
      (Ioc 0 Y).filter (fun n => ¬ n.Prime) := by
    intro m hm
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hm
    obtain ⟨hnI, hqn⟩ := mem_filter.mp hn
    have hnX := mem_Ioc.mp hnI
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega, by dsimp [Y]; omega⟩,
      not_prime_add_two_of_even_dvd hq hqn (by omega)⟩
  calc
    _ = ∑ n ∈ ((Ioc X (2 * X)).filter (fun n => q ∣ n)).image (fun n => n + 2),
        vonMangoldt n := by
      rw [sum_image (fun a _ b _ h => Nat.add_right_cancel h)]
    _ ≤ ∑ n ∈ (Ioc 0 Y).filter (fun n => ¬ n.Prime), vonMangoldt n :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => vonMangoldt_nonneg)
    _ = Chebyshev.psi Y - Chebyshev.theta Y := by
      rw [Chebyshev.psi_sub_theta_eq_sum_not_prime]
      simp
    _ ≤ 2 * Real.sqrt (Y : ℝ) * Real.log Y := Chebyshev.psi_sub_theta_le hY
    _ = evenProgressionBound X := by simp [Y, evenProgressionBound]

/-- The complete even-modulus contribution, with the actual coefficient norm retained.
@isnad1 id=le.1h3v.s7.ec54840d2133 from=translated src=- shape=c7a366ea vocab=9cc9cdf3
-/
theorem weighted_even_progression_le (X : ℕ) (s : Finset ℕ) (w : ℕ → ℝ)
    (hs : ∀ q ∈ s, Even q) :
    |∑ q ∈ s, w q * ∑ n ∈ Ioc X (2 * X) with q ∣ n, vonMangoldt (n + 2)| ≤
      (∑ q ∈ s, |w q|) * evenProgressionBound X := by
  calc
    _ ≤ ∑ q ∈ s, |w q * ∑ n ∈ Ioc X (2 * X) with q ∣ n, vonMangoldt (n + 2)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ s, |w q| * evenProgressionBound X := by
      apply sum_le_sum
      intro q hq
      rw [abs_mul, abs_of_nonneg (sum_nonneg (fun _ _ => vonMangoldt_nonneg))]
      exact mul_le_mul_of_nonneg_left (even_shiftedProgression_le X q (hs q hq)) (abs_nonneg _)
    _ = _ := (sum_mul ..).symm

end TwinPrime.Analytic
