import Tengoku.OddcyclegoodmanLean.OddCycleBound.DenseRegion.Diagonal.Commonality

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Degree variance and equality in strengthened extended commonality (Proposition 6.1)

`Ψ_m(W)` is the gap in Theorem 1.3. Through the excursion expansion it equals
`momentPhi m q (specMoment U μ)`, whose top excursion term (`r = (m-1)/2`) is
`(m - 1) · (s 0)^((m-1)/2)` with `s 0 = ∫ (d_W - p)²`, while every other term is nonnegative.
-/

open MeasureTheory
open scoped BigOperators

namespace OddCycleBound.DenseRegion

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {W : Ω → Ω → ℝ}

/-- The gap `Ψ_m(W)` between the two sides of Theorem 1.3.-/
noncomputable def commonalityGap (W : Ω → Ω → ℝ) (μ : Measure Ω) (m : ℕ) : ℝ :=
  cycleDensity μ W m + cycleDensity μ (compl W) m - pathDensity (compl W) μ (m - 1)
    - (edgeDensity W μ ^ m - edgeDensity W μ * (1 - edgeDensity W μ) ^ (m - 1))

/--
@isnad1 id=eq.1h5v.s5.332828b3d2a3 from=translated src=- shape=5aecba81 vocab=61af339b
-/
lemma momentPhiTerm_congr_of_le {m r : ℕ} (q : ℝ) {s t : ℕ → ℝ}
    (h : ∀ j ≤ m, s j = t j) : momentPhiTerm m r q s = momentPhiTerm m r q t := by
  unfold momentPhiTerm momentShiftTerm momentPathTerm
  congr 1 <;> refine Finset.sum_congr rfl fun j hj => ?_
  all_goals
    rw [momentConv_congr_of_le _ _ fun ell hell => h ell (by
      have hjlt : j < m - 2 * r + 1 := Finset.mem_range.mp hj
      omega)]

/-- Every excursion term of `Ψ_m` is nonnegative for `p ≥ 2/3`.
@isnad1 id=le.5h5v.s7.72b4bfd3b545 from=translated src=- shape=a9c117f0 vocab=5dff0076
-/
lemma momentPhiTerm_specMoment_nonneg (hW : IsGraphon W μ) (hp : 2 / 3 ≤ edgeDensity W μ)
    {m r : ℕ} (hm : Odd m) (hr : 1 ≤ r) (h2r : 2 * r < m) :
    0 ≤ momentPhiTerm m r (1 - edgeDensity W μ) (specMoment (compl W) μ) := by
  have hU := isGraphon_compl hW
  rw [momentPhiTerm_congr_of_le (t := atomicMoment (graphonAtomWeight hU m)
      (graphonAtomEigenvalue hU m)) _ fun j hj => specMoment_eq_graphonAtomicMoment hU hj,
    momentPhiTerm_eq_momentKernelTerm]
  exact momentKernelTerm_nonneg_of_atomic (by omega) (by omega) _ _ _
    (graphonAtomWeight_nonneg hU m) (graphonAtomEigenvalue_mem_halfInterval hU m)
    fun ell hell => diagKernel_nonneg_uniform diagKernelPosEll_unconditional hm hr h2r
      (by linarith [edgeDensity_le_one hW]) (by linarith) hell

/--
@isnad1 id=eq.2h3v.s6.f17a28a0e6fc from=translated src=- shape=4dd388d0 vocab=77b91880
-/
lemma specMoment_compl_eq_zero_of_regular (hW : IsGraphon W μ)
    (hreg : ∀ᵐ x ∂μ, degree W μ x = edgeDensity W μ) :
    specMoment (compl W) μ = fun _ => 0 := by
  funext j
  show ∫ x, degCentered (compl W) μ x * compressIter (compl W) μ j x ∂μ = 0
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hreg] with x hx
  rw [degCentered_compl hW]
  simp [degCentered, hx]

/--
@isnad1 id=eq.0h2v.s4.60f5338b8a5b from=translated src=- shape=f4ad1fbb vocab=410cca0e
-/
lemma momentPhi_zero_seq (m : ℕ) (q : ℝ) : momentPhi m q (fun _ => 0) = 0 := by
  unfold momentPhi momentPhiTerm momentShiftTerm momentPathTerm
  refine Finset.sum_eq_zero fun k _ => ?_
  simp [momentConv_succ]

end OddCycleBound.DenseRegion
