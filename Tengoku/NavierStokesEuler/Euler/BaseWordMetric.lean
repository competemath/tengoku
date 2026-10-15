import Tengoku.NavierStokesEuler.Euler.FiniteMetricEnergy

/-! Exact identification of the source's base-Sobolev word sum and root metric energy. -/

noncomputable section

namespace EulerBaseWordMetric

open EulerLiftedGradientSpace EulerSpatialSobolevInverse EulerCylinderSobolev EulerFiniteMetricEnergy
open InnerProductSpace

/-- A base Sobolev word of any length at most s. -/
abbrev BaseWord (s : ℕ) := Σ n : Fin (s + 1), Fin n.val → Fin 4

variable (period : ℝ) [Fact (0 < period)]

/-- The finite family of actual strong derivatives indexed by all base Sobolev words. -/
def baseWordValues {s : ℕ} {f : LiftL2 period} (J : SpatialJet period standardDirection s f) :
    BaseWord s → LiftL2 period := fun w => J.word w.2

/-- The sigma-indexed family gives exactly the previously proved strong Sobolev sum norm.
@isnad1 id=eq.0h4v.s11.ad366705b79d from=translated src=- shape=c8f28536 vocab=c1ca1e99
-/
theorem sum_baseWordValues_norm {s : ℕ} {f : LiftL2 period}
    (J : SpatialJet period standardDirection s f) :
    (∑ w : BaseWord s, ‖baseWordValues period J w‖) = J.sobolevNorm := by
  rw [SpatialJet.sobolevNorm_eq_sum_words]
  simp only [baseWordValues, Fintype.sum_sigma]
  exact Fin.sum_univ_eq_sum_range (fun n => ∑ w : Fin n → Fin 4, ‖J.word w‖) (s + 1)

/-- The number of base derivative words depends only on the fixed Sobolev index.
@isnad1 id=eq.0h1v.s7.0f2dc8c3f367 from=translated src=- shape=8798198e vocab=bfc4cab2
-/
theorem card_baseWord (s : ℕ) : Fintype.card (BaseWord s) = ∑ n ∈ Finset.range (s + 1), 4 ^ n := by
  simp only [BaseWord, Fintype.card_sigma, Fintype.card_fun, Fintype.card_fin]
  exact Fin.sum_univ_eq_sum_range (fun n => 4 ^ n) (s + 1)

/-- The source's root-of-sum metric energy for all base Sobolev words. -/
def baseWordMetricNorm {s : ℕ} {f : LiftL2 period} (K : LiftL2 period →L[ℝ] LiftL2 period)
    (J : SpatialJet period standardDirection s f) : ℝ := familyMetricNorm K (baseWordValues period J)

/-- The Sobolev sum is controlled by its metric root with a fixed base-word cardinality constant.
@isnad1 id=le.2h6v.s15.fcf209c93d54 from=translated src=- shape=0698258e vocab=bc1e8688
-/
theorem sobolevNorm_le_baseWordMetric {s : ℕ} {f : LiftL2 period}
    (K : LiftL2 period →L[ℝ] LiftL2 period) (J : SpatialJet period standardDirection s f)
    (c : ℝ) (hc : 0 < c)
    (hK : ∀ u, c ^ 2 * ‖u‖ ^ 2 ≤ ⟪K u, u⟫_ℝ) :
    J.sobolevNorm ≤ (Real.sqrt (Fintype.card (BaseWord s) : ℝ) / c) * baseWordMetricNorm period K J := by
  rw [← sum_baseWordValues_norm period J]
  have hsum := sum_norm_le_card_sqrt_familyNorm (baseWordValues period J)
  have hmet := familyMetricNorm_lower K (baseWordValues period J) c hc.le hK
  have hn : familyNorm (baseWordValues period J) ≤ baseWordMetricNorm period K J / c := by
    apply (le_div_iff₀ hc).mpr
    simpa only [baseWordMetricNorm, mul_comm] using hmet
  have hh := mul_le_mul_of_nonneg_left hn (Real.sqrt_nonneg (Fintype.card (BaseWord s) : ℝ))
  exact hsum.trans (hh.trans_eq (by ring))

/-- The metric root is controlled by the actual base Sobolev sum with no extra word-count factor.
@isnad1 id=le.0h5v.s15.584316da5c33 from=translated src=- shape=cea63226 vocab=1a3475fc
-/
theorem baseWordMetric_le_sobolevNorm {s : ℕ} {f : LiftL2 period}
    (K : LiftL2 period →L[ℝ] LiftL2 period) (J : SpatialJet period standardDirection s f) :
    baseWordMetricNorm period K J ≤ Real.sqrt ‖K‖ * J.sobolevNorm := by
  have h := familyMetricNorm_upper K (baseWordValues period J)
  have hn := familyNorm_le_sum_norm (baseWordValues period J)
  rw [sum_baseWordValues_norm period J] at hn
  exact h.trans (mul_le_mul_of_nonneg_left hn (Real.sqrt_nonneg _))

end EulerBaseWordMetric
