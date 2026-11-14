import Tengoku.Piirrationalitymeasure.Formalization.SavingPartitionAffine

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Uniform exact local affine formulas for the actual measure on all open sectors. -/

set_option maxRecDepth 100000

namespace PiIrrationality

open Filter Set
open scoped Topology

theorem CandidateOpenSector.smul {i : Fin 12} {v : ℝ × ℝ}
    (hv : CandidateOpenSector i v) {s : ℝ} (hs : 0 < s) :
    CandidateOpenSector i (s • v) := by
  rcases hv with ⟨u, t, hu, ht, rfl⟩
  exact ⟨s * u, s * t, mul_pos hs hu, mul_pos hs ht,
    by rw [smul_add, smul_smul, smul_smul]⟩

theorem translatedSavingMeasure_partition_constant (i : Fin 12)
    (e : CandidateEndpointEnumeration) (eps : ℕ → ℝ) {rho : ℝ} (hrho : 0 < rho)
    (hmodel : ∀ z : ℝ × ℝ, CandidateOpenSector i z → parameterNormOne z < rho →
      translatedSavingMeasure 1857 3714 5570 z =
        candidatePartitionConstant e eps + candidatePartitionLinear e eps z) :
    candidatePartitionConstant e eps = translatedSavingMeasure 1857 3714 5570 0 := by
  obtain ⟨v, hv, _⟩ := candidateOpenSector_small_point i hrho
  have hpath : Tendsto (fun s : ℝ => s • v) (𝓝[>] 0) (𝓝 (0 : ℝ × ℝ)) := by
    have hc : ContinuousAt (fun s : ℝ => s • v) 0 := by fun_prop
    simpa only [zero_smul] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hsmall : ∀ᶠ z : ℝ × ℝ in 𝓝 0, parameterNormOne z < rho := by
    have hc : ContinuousAt parameterNormOne 0 := by unfold parameterNormOne; fun_prop
    exact hc.eventually_lt_const (by simpa [parameterNormOne] using hrho)
  have heq : (fun s : ℝ => translatedSavingMeasure 1857 3714 5570 (s • v)) =ᶠ[𝓝[>] 0]
      (fun s => candidatePartitionConstant e eps + s * candidatePartitionLinear e eps v) := by
    filter_upwards [self_mem_nhdsWithin, hpath.eventually hsmall] with s hs hsn
    rw [hmodel (s • v) (hv.smul hs) hsn, candidatePartitionLinear_smul]
  have hc : Continuous (translatedSavingMeasure 1857 3714 5570) :=
    continuous_translatedSavingMeasure (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hlim := (hc.tendsto 0).comp hpath
  have hconst : Tendsto
      (fun s : ℝ => candidatePartitionConstant e eps + s * candidatePartitionLinear e eps v)
      (𝓝[>] 0) (𝓝 (candidatePartitionConstant e eps)) := by
    have hh : ContinuousAt
        (fun s : ℝ => candidatePartitionConstant e eps + s * candidatePartitionLinear e eps v) 0 := by
      fun_prop
    simpa only [zero_mul, add_zero] using hh.tendsto.mono_left nhdsWithin_le_nhds
  exact (tendsto_nhds_unique hlim ((tendsto_congr' heq).mpr hconst)).symm

theorem translatedSavingMeasure_uniform_open_affine :
    ∃ rho : ℝ, 0 < rho ∧ rho ≤ 1 / 100 ∧ ∀ i : Fin 12,
      ∃ (e : CandidateEndpointEnumeration) (w : ℝ × ℝ),
        CandidateOpenSector i w ∧ parameterNormOne w < rho ∧ CandidateOrderedEndpoints e w ∧
        ∀ z : ℝ × ℝ, CandidateOpenSector i z → parameterNormOne z < rho →
          CandidateOrderedEndpoints e z ∧
          translatedSavingMeasure 1857 3714 5570 z =
            translatedSavingMeasure 1857 3714 5570 0 +
              candidatePartitionLinear e (candidatePartitionIndicator e w) z := by
  obtain ⟨rho, hrho, hrho100, henum⟩ := candidateEndpoint_uniform_enumeration
  refine ⟨rho, hrho, hrho100, ?_⟩
  intro i
  obtain ⟨e, w, hwi, hwn, hworder, hall⟩ := henum i
  have hw100 : parameterNormOne w ≤ 1 / 100 := le_trans hwn.le hrho100
  have hmodel : ∀ z : ℝ × ℝ, CandidateOpenSector i z → parameterNormOne z < rho →
      translatedSavingMeasure 1857 3714 5570 z =
        candidatePartitionConstant e (candidatePartitionIndicator e w) +
          candidatePartitionLinear e (candidatePartitionIndicator e w) z := by
    intro z hzi hzn
    exact translatedSavingMeasure_eq_partition_affine (hall z hzi hzn) hworder
      (le_trans hzn.le hrho100) hw100
  have hconst := translatedSavingMeasure_partition_constant i e
    (candidatePartitionIndicator e w) hrho hmodel
  refine ⟨e, w, hwi, hwn, hworder, ?_⟩
  intro z hzi hzn
  exact ⟨hall z hzi hzn, by rw [hmodel z hzi hzn, hconst]⟩

end PiIrrationality
