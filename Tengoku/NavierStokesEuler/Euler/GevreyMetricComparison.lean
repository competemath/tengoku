import Tengoku.NavierStokesEuler.Euler.SobolevGevreyOperators
import Tengoku.NavierStokesEuler.Euler.BaseWordMetric
import Tengoku.NavierStokesEuler.Euler.WeightedCylinderEnergy

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Cutoff-independent comparison between actual Sobolev Gevrey sums and the source's metric root energies. -/

noncomputable section

namespace EulerGevreyMetricComparison

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerH6Pressure EulerJetProductBounds EulerPacketWeights
  EulerSobolevGevreyOperators EulerBaseWordMetric EulerFiniteMetricEnergy EulerWeightedCylinderEnergy
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- All external derivative words through the selected cutoff. -/
abbrev ExternalWord (N : ℕ) := Σ n : Fin (N+1), Fin n.val → Fin 4

/-- Literal base derivatives of each external word of an actual Sobolev field. -/
def energyValues {s : ℕ} (q N : ℕ) (hN : N+q ≤ s) (u : SobolevSpace period s) :
    ExternalWord N → BaseWord q → LiftL2 period := fun I =>
  baseWordValues period (EulerH6Pressure.SpatialJet.derivativeJet (q := q) (toJet period u) I.2 (by have := I.1.isLt; omega))

/-- Exact rewriting of a valid external Sobolev block as the actual base-word derivative sums.
@isnad1 id=eq.1h5v.s15.a9129a812d64 from=translated src=- shape=38d35b7a vocab=ee52eb41
-/
theorem blockNorm_baseWords {s q n : ℕ} (u : SobolevSpace period s) (h : n+q ≤ s) :
    blockNorm period (toJet period u) q n =
      ∑ w : Fin n → Fin 4, (EulerH6Pressure.SpatialJet.derivativeJet (q := q) (toJet period u) w h).sobolevNorm := by
  rw [blockNorm_eq_word_sizes (toJet period u) h]
  apply Finset.sum_congr rfl
  intro w _
  exact sobolevSize_eq period (EulerH6Pressure.SpatialJet.derivativeJet (q := q) (toJet period u) w h)

/-- The lower comparison at one external order uses only the fixed number of base Sobolev words.
@isnad1 id=le.3h7v.s16.a9d6667a9525 from=translated src=- shape=9c742c11 vocab=5594a4f8
-/
theorem blockNorm_metric_lower {s q n : ℕ} (u : SobolevSpace period s) (h : n+q ≤ s)
    (K : LiftL2 period →L[ℝ] LiftL2 period) (c : ℝ) (hc : 0 < c)
    (hK : ∀ v, c^2*‖v‖^2 ≤ ⟪K v,v⟫_ℝ) :
    blockNorm period (toJet period u) q n ≤
      (Real.sqrt (Fintype.card (BaseWord q) : ℝ)/c) *
        ∑ w : Fin n → Fin 4, baseWordMetricNorm period K
          (EulerH6Pressure.SpatialJet.derivativeJet (q := q) (toJet period u) w h) := by
  rw [blockNorm_baseWords period u h, Finset.mul_sum]
  exact Finset.sum_le_sum fun w _ => sobolevNorm_le_baseWordMetric period K _ c hc hK

/-- The upper metric comparison is independent of the external word count.
@isnad1 id=le.1h6v.s16.671baa373161 from=translated src=- shape=e3f02c75 vocab=b0431433
-/
theorem blockNorm_metric_upper {s q n : ℕ} (u : SobolevSpace period s) (h : n+q ≤ s)
    (K : LiftL2 period →L[ℝ] LiftL2 period) :
    (∑ w : Fin n → Fin 4, baseWordMetricNorm period K
      (EulerH6Pressure.SpatialJet.derivativeJet (q := q) (toJet period u) w h)) ≤
      Real.sqrt ‖K‖ * blockNorm period (toJet period u) q n := by
  rw [blockNorm_baseWords period u h, Finset.mul_sum]
  exact Finset.sum_le_sum fun w _ => baseWordMetric_le_sobolevNorm period K _

/-- The metric-weighted energy is exactly the external-word sum of fixed-base metric roots.
@isnad1 id=eq.1h7v.s16.8ca30dd4cf0e from=translated src=- shape=a69075ef vocab=adacb044
-/
theorem metricSum_eq {s : ℕ} (q N : ℕ) (hN : N+q ≤ s) (ρ : ℝ)
    (K : LiftL2 period →L[ℝ] LiftL2 period) (u : SobolevSpace period s) :
    weightedMetricSum ρ (fun I : ExternalWord N => I.1.val) K (energyValues period q N hN u) =
      ∑ n : Fin (N+1), weight ρ n.val * ∑ w : Fin n.val → Fin 4,
        baseWordMetricNorm period K (EulerH6Pressure.SpatialJet.derivativeJet (q := q) (toJet period u) w
          (by have := n.isLt; omega)) := by
  simp only [weightedMetricSum, Fintype.sum_sigma, Finset.mul_sum, energyValues, baseWordMetricNorm]

/-- The actual weighted Sobolev sum is controlled by metric roots with no external-cutoff constant.
@isnad1 id=le.4h8v.s16.0dc3f8b72643 from=translated src=- shape=f170b1fc vocab=90f88fc1
-/
theorem weightedNorm_metric_lower {s : ℕ} (q N : ℕ) (hN : N+q ≤ s) (ρ : ℝ) (hρ : 0 < ρ)
    (K : LiftL2 period →L[ℝ] LiftL2 period) (u : SobolevSpace period s) (c : ℝ) (hc : 0 < c)
    (hK : ∀ v, c^2*‖v‖^2 ≤ ⟪K v,v⟫_ℝ) :
    weightedNorm period q N ρ u ≤ (Real.sqrt (Fintype.card (BaseWord q) : ℝ)/c) *
      weightedMetricSum ρ (fun I : ExternalWord N => I.1.val) K (energyValues period q N hN u) := by
  rw [metricSum_eq, weightedNorm, ← Fin.sum_univ_eq_sum_range, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n _
  have h := mul_le_mul_of_nonneg_left (blockNorm_metric_lower period (q := q) (n := n.val) u (by have := n.isLt; omega) K c hc hK)
    (weight_pos hρ n.val).le
  exact h.trans_eq (by ring)

/-- The actual metric weighted energy is bounded by its Sobolev counterpart without a cutoff factor.
@isnad1 id=le.2h7v.s16.b8772e70b819 from=translated src=- shape=5c04297e vocab=df8bb96b
-/
theorem weightedNorm_metric_upper {s : ℕ} (q N : ℕ) (hN : N+q ≤ s) (ρ : ℝ) (hρ : 0 < ρ)
    (K : LiftL2 period →L[ℝ] LiftL2 period) (u : SobolevSpace period s) :
    weightedMetricSum ρ (fun I : ExternalWord N => I.1.val) K (energyValues period q N hN u) ≤
      Real.sqrt ‖K‖ * weightedNorm period q N ρ u := by
  rw [metricSum_eq, weightedNorm, ← Fin.sum_univ_eq_sum_range, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n _
  have h := mul_le_mul_of_nonneg_left (blockNorm_metric_upper period (q := q) (n := n.val) u (by have := n.isLt; omega) K)
    (weight_pos hρ n.val).le
  exact h.trans_eq (by ring)

/-- At the fixed base index six the comparison uses exactly 5461 base words.
@isnad1 id=eq.0h0v.s7.e551d23c2a37 from=translated src=- shape=88d4f5c9 vocab=7d175ea7
-/
theorem card_baseWord_six : Fintype.card (BaseWord 6) = 5461 := by
  rw [card_baseWord]
  norm_num [Finset.sum_range_succ]

end EulerGevreyMetricComparison
