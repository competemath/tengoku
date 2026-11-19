import Tengoku.OddcyclegoodmanLean.OddCycleBound.DenseRegion.GraphonReduction
import Tengoku.OddcyclegoodmanLean.OddCycleBound.General.PathRecurrence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open MeasureTheory
open scoped BigOperators

namespace OddCycleBound.DenseRegion

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {U W : Ω → Ω → ℝ}

lemma kernelOp_compl (hU : IsGraphon U μ) {f : Ω → ℝ} (hf : Good f) (x : Ω) :
    kernelOp (compl U) μ f x = mean μ f - kernelOp U μ f x := by
  have hfun : (fun y => compl U x y * f y) = (fun y => f y - U x y * f y) := by
    funext y; rw [compl]; ring
  show (∫ y, compl U x y * f y ∂μ) = mean μ f - kernelOp U μ f x
  rw [hfun, integral_sub hf.integrable (integrable_Uf hU hf x)]
  rfl

private lemma integral_const_prob (c : ℝ) : (∫ (_ : Ω), c ∂μ) = c := by simp

omit [IsProbabilityMeasure μ] in
lemma kernelOp_const_mul (c : ℝ) (f : Ω → ℝ) (x : Ω) :
    kernelOp U μ (fun y => c * f y) x = c * kernelOp U μ f x := by
  show (∫ y, U x y * (c * f y) ∂μ) = c * ∫ y, U x y * f y ∂μ
  rw [← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ fun y => by ring)

omit [IsProbabilityMeasure μ] in
lemma compress_const_mul (c : ℝ) (f : Ω → ℝ) :
    compress W μ (fun y => c * f y) = fun x => c * compress W μ f x := by
  funext x
  show kernelOp W μ (fun y => c * f y) x - mean μ (kernelOp W μ (fun y => c * f y))
      = c * (kernelOp W μ f x - mean μ (kernelOp W μ f))
  rw [kernelOp_const_mul]
  have hmean : mean μ (kernelOp W μ (fun y => c * f y)) = c * mean μ (kernelOp W μ f) := by
    show (∫ x, kernelOp W μ (fun y => c * f y) x ∂μ) = c * mean μ (kernelOp W μ f)
    rw [integral_congr_ae (ae_of_all _ fun x => kernelOp_const_mul c f x), integral_const_mul]
    rfl
  rw [hmean]; ring

lemma degree_compl (hW : IsGraphon W μ) (x : Ω) :
    degree (compl W) μ x = 1 - degree W μ x := by
  show ∫ y, compl W x y ∂μ = 1 - degree W μ x
  have hc : (fun y => compl W x y) = (fun y => (1 : ℝ) - W x y) := by funext y; rw [compl]
  rw [hc, integral_sub (integrable_const 1) ((goodK_of_isGraphon hW).integrable_row x),
    integral_const_prob]
  rfl

lemma edgeDensity_compl (hW : IsGraphon W μ) :
    edgeDensity (compl W) μ = 1 - edgeDensity W μ := by
  show mean μ (degree (compl W) μ) = 1 - edgeDensity W μ
  have hdeg : degree (compl W) μ = fun x => 1 - degree W μ x := funext (degree_compl hW)
  rw [hdeg]
  show (∫ x, (1 - degree W μ x) ∂μ) = 1 - edgeDensity W μ
  rw [integral_sub (integrable_const 1) (good_degree hW).integrable, integral_const_prob]
  rfl

lemma degCentered_compl (hW : IsGraphon W μ) :
    degCentered (compl W) μ = fun x => - degCentered W μ x := by
  funext x
  show degree (compl W) μ x - edgeDensity (compl W) μ = -(degree W μ x - edgeDensity W μ)
  rw [degree_compl hW x, edgeDensity_compl hW]; ring

lemma compress_compl (hW : IsGraphon W μ) {f : Ω → ℝ} (hf : Good f) :
    compress (compl W) μ f = fun x => - compress W μ f x := by
  funext x
  show kernelOp (compl W) μ f x - mean μ (kernelOp (compl W) μ f)
      = -(kernelOp W μ f x - mean μ (kernelOp W μ f))
  have hk : ∀ y, kernelOp (compl W) μ f y = mean μ f - kernelOp W μ f y :=
    fun y => kernelOp_compl hW hf y
  have hmean : mean μ (kernelOp (compl W) μ f) = mean μ f - mean μ (kernelOp W μ f) := by
    show (∫ y, kernelOp (compl W) μ f y ∂μ) = mean μ f - mean μ (kernelOp W μ f)
    rw [integral_congr_ae (ae_of_all _ hk),
      integral_sub (integrable_const _) (good_kernelOp hW hf).integrable, integral_const_prob]
    rfl
  rw [hk x, hmean]; ring

lemma pathIter_expansion (hU : IsGraphon U μ) (a : ℕ) :
    pathIter U μ a
      = fun z => pathDensity U μ a
          + ∑ k ∈ Finset.range a, pathDensity U μ (a - 1 - k) * compressIter U μ k z := by
  induction a with
  | zero =>
    funext z
    show (1 : ℝ)
        = pathDensity U μ 0 + ∑ k ∈ Finset.range 0, pathDensity U μ (0 - 1 - k) * compressIter U μ k z
    have h0 : pathDensity U μ 0 = 1 := mean_one
    rw [Finset.range_zero, Finset.sum_empty, add_zero, h0]
  | succ a ih =>
    funext z
    show (∫ y, U z y * pathIter U μ a y ∂μ)
        = pathDensity U μ (a + 1)
          + ∑ k ∈ Finset.range (a + 1), pathDensity U μ (a + 1 - 1 - k) * compressIter U μ k z

    have hib : ∀ y, U z y * pathIter U μ a y
        = pathDensity U μ a * U z y
          + ∑ k ∈ Finset.range a, pathDensity U μ (a - 1 - k) * (U z y * compressIter U μ k y) := by
      intro y
      have ihy : pathIter U μ a y
          = pathDensity U μ a + ∑ k ∈ Finset.range a, pathDensity U μ (a - 1 - k) * compressIter U μ k y :=
        congrFun ih y
      rw [ihy, mul_add, Finset.mul_sum]
      congr 1
      · ring
      · exact Finset.sum_congr rfl fun k _ => by ring
    rw [integral_congr_ae (ae_of_all _ hib)]
    have hInt1 : Integrable (fun y => pathDensity U μ a * U z y) μ :=
      ((goodK_of_isGraphon hU).integrable_row z).const_mul _
    have hInt2 : Integrable
        (fun y => ∑ k ∈ Finset.range a,
          pathDensity U μ (a - 1 - k) * (U z y * compressIter U μ k y)) μ :=
      integrable_finsetSum _ fun k _ => (integrable_Uf hU (good_compressIter hU k) z).const_mul _
    rw [integral_add hInt1 hInt2, integral_const_mul,
      integral_finsetSum _ fun k _ => (integrable_Uf hU (good_compressIter hU k) z).const_mul _]
    have hterm : ∀ k, (∫ y, pathDensity U μ (a - 1 - k) * (U z y * compressIter U μ k y) ∂μ)
        = pathDensity U μ (a - 1 - k) * kernelOp U μ (compressIter U μ k) z := by
      intro k; rw [integral_const_mul]; rfl
    rw [Finset.sum_congr rfl fun k _ => hterm k,
      show (∫ y, U z y ∂μ) = degree U μ z from rfl, degree_eq' z]
    simp only [kernelOp_compressIter' hU, mul_add, Finset.sum_add_distrib]

    rw [pathDensity_succ hU a, Finset.sum_range_succ' (fun k =>
      pathDensity U μ (a + 1 - 1 - k) * compressIter U μ k z) a]
    have eMom : ∑ i ∈ Finset.range a, specMoment U μ i * pathDensity U μ (a - 1 - i)
        = ∑ k ∈ Finset.range a, pathDensity U μ (a - 1 - k) * specMoment U μ k :=
      Finset.sum_congr rfl fun k _ => by ring
    have eShift : ∑ k ∈ Finset.range a,
          pathDensity U μ (a + 1 - 1 - (k + 1)) * compressIter U μ (k + 1) z
        = ∑ k ∈ Finset.range a, pathDensity U μ (a - 1 - k) * compressIter U μ (k + 1) z :=
      Finset.sum_congr rfl fun k _ => by
        rw [show a + 1 - 1 - (k + 1) = a - 1 - k from by omega]
    rw [eMom, eShift, show a + 1 - 1 - 0 = a from by omega]
    ring

end OddCycleBound.DenseRegion
