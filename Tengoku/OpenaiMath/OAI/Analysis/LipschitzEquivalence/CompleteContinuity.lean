import Tengoku.OpenaiMath.OAI.Analysis.LipschitzEquivalence.CompactLocalization

namespace OAI

universe uE uM uIndex

noncomputable section
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set

namespace LipschitzCounterexample.WeakSequences
open Filter Topology
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
omit [NormedSpace ℝ E] in
theorem exists_large_subsequence (u : ℕ → E) (hu : ¬ Tendsto u atTop (𝓝 0)) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ s : ℕ → ℕ, StrictMono s ∧ ∀ i, ε ≤ ‖u (s i)‖ := by
  rw [Metric.tendsto_atTop] at hu
  push Not at hu
  obtain ⟨ε,hε,hlarge⟩ := hu
  simp only [dist_zero_right] at hlarge
  have hstep (p : ℕ) : ∃ n : ℕ, p < n ∧ ε ≤ ‖u n‖ := by
    obtain ⟨n,hn,hun⟩ := hlarge (p+1)
    exact ⟨n,lt_of_lt_of_le (Nat.lt_succ_self p) hn,hun⟩
  let next (p : ℕ) : ℕ := Classical.choose (hstep p)
  let seq : ℕ → ℕ := fun j => Nat.rec 0 (fun _ p => next p) j
  have hseq (j : ℕ) : seq j < seq (j+1) ∧ ε ≤ ‖u (seq (j+1))‖ :=
    Classical.choose_spec (hstep (seq j))
  have hm : StrictMono seq := strictMono_nat_of_lt_succ (fun j => (hseq j).1)
  exact ⟨ε,hε,(fun i => seq (i+1)),(fun _ _ h => hm (Nat.add_lt_add_right h 1)),fun i => (hseq i).2⟩

def unitNormalize (u : ℕ → E) (i : ℕ) : E := ‖u i‖⁻¹ • u i

theorem norm_unitNormalize (u : ℕ → E) {ε : ℝ} (hε : 0 < ε)
    (hu : ∀ i, ε ≤ ‖u i‖) (i : ℕ) : ‖unitNormalize u i‖ = 1 := by
  have hn : ‖u i‖ ≠ 0 := ne_of_gt (hε.trans_le (hu i))
  simp [unitNormalize,norm_smul,hn]

theorem WeakNull.unitNormalize {u : ℕ → E} (hw : WeakNull u) {ε : ℝ} (hε : 0 < ε)
    (hu : ∀ i, ε ≤ ‖u i‖) : WeakNull (unitNormalize u) := by
  intro f
  apply Metric.tendsto_atTop.mpr
  intro δ hδ
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp (hw f) (δ*ε) (mul_pos hδ hε)
  refine ⟨N,fun i hi => ?_⟩
  have hn : 0 < ‖u i‖ := hε.trans_le (hu i)
  have hfi := hN i hi
  simp only [dist_zero_right,Real.norm_eq_abs] at hfi ⊢
  change |f (‖u i‖⁻¹ • u i)| < δ
  rw [map_smul,smul_eq_mul,abs_mul,abs_inv,abs_norm]
  rw [← div_eq_inv_mul]
  apply (div_lt_iff₀ hn).mpr
  exact hfi.trans_le (mul_le_mul_of_nonneg_left (hu i) hδ.le)
end LipschitzCounterexample.WeakSequences

namespace LipschitzCounterexample.LocalizedLinearization
open Filter Set Topology LocalLipschitz CoordinateSpaces LocalGeometry
open scoped NNReal InnerProductSpace
variable {M : Type uM} [MetricSpace M] [Zero M]
variable {ι : ℕ → Type uIndex} [∀ n, Fintype (ι n)]

omit [Zero M] in
theorem scalar_test_lipschitz (D : M → Hilbert (ι := ι)) {L : ℝ≥0}
    (hD : LipschitzWith L D) (b : Hilbert (ι := ι)) (hb : ‖b‖ ≤ 1) :
    LipschitzWith L (fun x => ⟪D x,b⟫_ℝ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq,← inner_sub_left]
  exact (abs_real_inner_le_norm _ _).trans
    ((mul_le_mul_of_nonneg_left hb (norm_nonneg _)).trans (by simpa only [mul_one,← dist_eq_norm] using hD.dist_le_mul x y))

end LipschitzCounterexample.LocalizedLinearization

end

end OAI
