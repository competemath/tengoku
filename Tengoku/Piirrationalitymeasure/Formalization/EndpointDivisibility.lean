import Tengoku.Piirrationalitymeasure.Formalization.EndpointFormula
import Tengoku.Piirrationalitymeasure.Formalization.EndpointArithmetic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Lemma 2.4 for the actual Gaussian-integer endpoint coefficients.
The auxiliary power of five is removed by a coprime-multiplier argument.
-/

namespace PiIrrationality

noncomputable def normalizedEndpointCoeff (n k : ℕ) : ℂ :=
  (2 : ℂ) ^ endpointTwoExponent n k * (endpointCoeff n k : ℂ)

/--
@isnad1 id=ex.2h2v.s6.770605b794c8 from=translated src=- shape=1d02c193 vocab=8729ba3b
-/
theorem normalizedEndpointCoeff_five_power_is_gaussian_integer
    (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : k < 3714 * n) :
    ∃ z : GI, (5 : ℂ) ^ (k + 1) * normalizedEndpointCoeff n k = (z : ℂ) := by
  choose z hz using fun j : Fin (5570 * n + 1) =>
    endpoint_scaled_bracket_is_gaussian_integer n hn j.val (Nat.le_of_lt_succ j.isLt) k
  refine ⟨-∑ j : Fin (5570 * n + 1), ((j.val + k).choose k : GI) * z j, ?_⟩
  unfold normalizedEndpointCoeff
  rw [endpointCoeff_formula n hn k hk]
  calc
    _ = -∑ j : Fin (5570 * n + 1), ((j.val + k).choose k : ℂ) *
        (5 ^ (k + 1) * 2 ^ endpointTwoExponent n k *
          (laurentCoeffRat n (j.val : ℤ) : ℂ) *
            ((-1 : ℂ) ^ k / (4 - 2 * Complex.I) ^ (j.val + k + 1) +
              1 / (6 + 2 * Complex.I) ^ (j.val + k + 1))) := by
      rw [← mul_assoc, mul_neg, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      simp_rw [hz]
      simp only [map_neg, map_sum, map_mul, map_natCast]

/--
@isnad1 id=ex.0h2v.s6.91a71b92d1e4 from=translated src=- shape=90d2b117 vocab=5c20886e
-/
theorem normalizedEndpointCoeff_two_power_is_gaussian_integer (n k : ℕ) :
    ∃ z : GI, (2 : ℂ) ^ (4645 * n) * normalizedEndpointCoeff n k = (z : ℂ) := by
  refine ⟨(2 : GI) ^ ((3 * k + 1) / 2 + 3) * endpointCoeff n k, ?_⟩
  unfold normalizedEndpointCoeff
  rw [← mul_assoc, ← zpow_natCast (2 : ℂ) (4645 * n),
    ← zpow_add₀ (by norm_num : (2 : ℂ) ≠ 0)]
  have he : ((4645 * n : ℕ) : ℤ) + endpointTwoExponent n k =
      ((((3 * k + 1) / 2 + 3 : ℕ)) : ℤ) := by
    unfold endpointTwoExponent
    omega
  rw [he, zpow_natCast]
  simp only [map_mul, map_pow, map_ofNat]

/--
@isnad1 id=ex.1h2v.s6.9c432aff2dc2 from=translated src=- shape=ea7b992d vocab=8288a52a
-/
theorem normalizedEndpointCoeff_is_gaussian_integer (n : ℕ) (hn : 1 ≤ n) (k : ℕ) :
    ∃ z : GI, normalizedEndpointCoeff n k = (z : ℂ) := by
  by_cases hk : k < 3714 * n
  · apply gaussian_integer_of_coprime_multipliers (normalizedEndpointCoeff n k)
      (2 ^ (4645 * n)) (5 ^ (k + 1))
      (((by norm_num : Nat.Coprime 2 5).pow_left _).pow_right _)
    · simpa only [Nat.cast_pow, Nat.cast_ofNat] using
        normalizedEndpointCoeff_two_power_is_gaussian_integer n k
    · simpa only [Nat.cast_pow, Nat.cast_ofNat] using
        normalizedEndpointCoeff_five_power_is_gaussian_integer n hn k hk
  · have he : 0 ≤ endpointTwoExponent n k := by
      unfold endpointTwoExponent
      omega
    refine ⟨(2 : GI) ^ (endpointTwoExponent n k).toNat * endpointCoeff n k, ?_⟩
    unfold normalizedEndpointCoeff
    rw [← Int.toNat_of_nonneg he, zpow_natCast]
    simp only [map_mul, map_pow, map_ofNat, Int.toNat_natCast]

end PiIrrationality
