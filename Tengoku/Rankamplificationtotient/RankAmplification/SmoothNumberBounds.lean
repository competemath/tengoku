import Tengoku.Rankamplificationtotient.RankAmplification.PrimeRankinFull

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Explicit smooth-number bounds The divisor-weighted estimate of Lemma 2.5 immediately dominates the ordinary smooth-number census. -/

namespace RankAmplification

noncomputable section

/-- Exact finite count `Ψ(X,R)` of positive `R`-smooth integers at most `X`.-/
def finiteSmoothCount (R X : ℕ) : ℕ :=
  (finiteSmoothSet R X).card

/-- Every positive integer has at least one divisor, so the ordinary smooth count is bounded by the divisor-weighted smooth count.-/
theorem finiteSmoothCount_cast_le_divisorWeighted (R X : ℕ) :
    (finiteSmoothCount R X : ℝ) ≤ finiteDivisorWeightedSmoothCount R X := by
  rw [finiteSmoothCount, finiteDivisorWeightedSmoothCount_eq]
  calc
    ((finiteSmoothSet R X).card : ℝ) =
        ∑ m ∈ finiteSmoothSet R X, (1 : ℝ) := by simp
    _ ≤ ∑ m ∈ finiteSmoothSet R X, (m.divisors.card : ℝ) := by
      apply Finset.sum_le_sum
      intro m hm
      have hm0 : m ≠ 0 :=
        Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (mem_finiteSmoothSet.mp hm).1)
      exact_mod_cast Finset.card_pos.mpr
        ⟨1, Nat.mem_divisors.mpr ⟨one_dvd m, hm0⟩⟩

theorem finiteSmoothCount_pos {R X : ℕ} (hX : 0 < X) :
    0 < finiteSmoothCount R X := by
  rw [finiteSmoothCount, Finset.card_pos]
  refine ⟨1, mem_finiteSmoothSet.mpr ⟨by norm_num, hX, ?_⟩⟩
  simp [IsSmooth]

/-- Full-range explicit de Bruijn-type upper bound inherited from `PrimeRankinFull`.-/
theorem finiteSmoothCount_le_full_paper_error {R X : ℕ}
    (hX : 0 < X) (hR : 2 ≤ R) (hu : 1 < rankinU X R)
    (huSqrt : rankinU X R ≤ Real.sqrt R) :
    (finiteSmoothCount R X : ℝ) ≤
      (X : ℝ) * Real.exp
        (-rankinU X R * Real.log (rankinU X R) + fullPaperDivisorError R X) := by
  exact (finiteSmoothCount_cast_le_divisorWeighted R X).trans
    (finiteDivisorWeightedSmoothCount_le_full_paper_error hX hR hu huSqrt)

/-- Clean exponential smooth-number estimate under the same explicit dominance condition.-/
theorem finiteSmoothCount_le_full_half_u_log_u {R X : ℕ}
    (hX : 0 < X) (hR : 2 ≤ R) (hu : 1 < rankinU X R)
    (huSqrt : rankinU X R ≤ Real.sqrt R)
    (hdom : fullPaperDivisorError R X ≤
      rankinU X R * Real.log (rankinU X R) / 2) :
    (finiteSmoothCount R X : ℝ) ≤
      (X : ℝ) * Real.exp
        (-(rankinU X R * Real.log (rankinU X R)) / 2) := by
  exact (finiteSmoothCount_cast_le_divisorWeighted R X).trans
    (finiteDivisorWeightedSmoothCount_le_full_half_u_log_u hX hR hu huSqrt hdom)

/-- Log-normalized general smooth-number bound.-/
theorem log_finiteSmoothCount_div_le_full_paper_error {R X : ℕ}
    (hX : 0 < X) (hR : 2 ≤ R) (hu : 1 < rankinU X R)
    (huSqrt : rankinU X R ≤ Real.sqrt R) :
    Real.log ((finiteSmoothCount R X : ℝ) / X) ≤
      -rankinU X R * Real.log (rankinU X R) + fullPaperDivisorError R X := by
  have hXreal : 0 < (X : ℝ) := by exact_mod_cast hX
  have hbound := finiteSmoothCount_le_full_paper_error hX hR hu huSqrt
  have hdiv : (finiteSmoothCount R X : ℝ) / X ≤
      Real.exp (-rankinU X R * Real.log (rankinU X R) +
        fullPaperDivisorError R X) := by
    apply (div_le_iff₀ hXreal).2
    simpa [mul_comm] using hbound
  have hdivpos : 0 < (finiteSmoothCount R X : ℝ) / X := by
    exact div_pos (by exact_mod_cast finiteSmoothCount_pos (R := R) hX) hXreal
  simpa only [Real.log_exp] using Real.log_le_log hdivpos hdiv

end

end RankAmplification
