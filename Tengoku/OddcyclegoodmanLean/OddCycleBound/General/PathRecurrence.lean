import Tengoku.OddcyclegoodmanLean.OddCycleBound.Necklace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open MeasureTheory

namespace OddCycleBound

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {U : Ω → Ω → ℝ}

lemma pathDensity_succ_aux (hU : IsGraphon U μ) (n : ℕ) :
    pathDensity U μ (n + 1) = edgeDensity U μ * pathDensity U μ n + pairing μ (compressIter U μ 0) (pathIter U μ n) := by
  have e1 : mean μ (kernelOp U μ (pathIter U μ n)) = ∫ x, pathIter U μ n x * degree U μ x ∂μ := by
    show ∫ x, kernelOp U μ (pathIter U μ n) x ∂μ = _
    rw [show (∫ x, kernelOp U μ (pathIter U μ n) x ∂μ) = ∫ x, kernelOp U μ (pathIter U μ n) x * 1 ∂μ from by simp,
      kernelOp_selfadj hU (good_pathIter hU n) good_one, kernelOp_one hU]
  show mean μ (kernelOp U μ (pathIter U μ n)) = _
  rw [e1]
  have e2 : ∀ x, pathIter U μ n x * degree U μ x
      = edgeDensity U μ * pathIter U μ n x + pathIter U μ n x * compressIter U μ 0 x := fun x => by
    rw [degree_eq']; ring
  rw [integral_congr_ae (ae_of_all _ e2),
    integral_add ((good_pathIter hU n).integrable.const_mul _)
      ((good_pathIter hU n).mul (good_compressIter hU 0)).integrable,
    integral_const_mul]
  congr 1
  show ∫ x, pathIter U μ n x * compressIter U μ 0 x ∂μ = pairing μ (compressIter U μ 0) (pathIter U μ n)
  simp only [pairing]; exact integral_congr_ae (ae_of_all _ fun x => by ring)

lemma pairing_compressIter_pathIter_zero (hU : IsGraphon U μ) (k : ℕ) :
    pairing μ (compressIter U μ k) (pathIter U μ 0) = 0 := by
  show ∫ x, compressIter U μ k x * pathIter U μ 0 x ∂μ = 0
  rw [integral_congr_ae (ae_of_all _ fun x => by
    show compressIter U μ k x * pathIter U μ 0 x = compressIter U μ k x; show compressIter U μ k x * 1 = _; ring)]
  exact mean_compressIter hU k

lemma pairing_compressIter_pathIter_succ (hU : IsGraphon U μ) (k n : ℕ) :
    pairing μ (compressIter U μ k) (pathIter U μ (n + 1))
      = specMoment U μ k * pathDensity U μ n + pairing μ (compressIter U μ (k + 1)) (pathIter U μ n) := by
  have hT : pairing μ (compressIter U μ k) (pathIter U μ (n + 1))
      = ∫ x, kernelOp U μ (compressIter U μ k) x * pathIter U μ n x ∂μ := by
    show ∫ x, compressIter U μ k x * kernelOp U μ (pathIter U μ n) x ∂μ = _
    exact (kernelOp_selfadj hU (good_compressIter hU k) (good_pathIter hU n)).symm
  rw [hT]
  have e : ∀ x, kernelOp U μ (compressIter U μ k) x * pathIter U μ n x
      = specMoment U μ k * pathIter U μ n x + compressIter U μ (k + 1) x * pathIter U μ n x := fun x => by
    rw [kernelOp_compressIter' hU k]; ring
  rw [integral_congr_ae (ae_of_all _ e),
    integral_add ((good_pathIter hU n).integrable.const_mul _)
      ((good_compressIter hU (k + 1)).mul (good_pathIter hU n)).integrable,
    integral_const_mul]
  rfl

lemma pairing_compressIter_pathIter_closed (hU : IsGraphon U μ) : ∀ (n k : ℕ),
    pairing μ (compressIter U μ k) (pathIter U μ n)
      = ∑ i ∈ Finset.range n, specMoment U μ (k + i) * pathDensity U μ (n - 1 - i) := by
  intro n
  induction n with
  | zero => intro k; simp [pairing_compressIter_pathIter_zero hU k]
  | succ n ih =>
      intro k
      rw [pairing_compressIter_pathIter_succ hU k n, ih (k + 1),
        Finset.sum_range_succ' (fun i => specMoment U μ (k + i) * pathDensity U μ (n + 1 - 1 - i)) n]
      have hcong : ∀ i ∈ Finset.range n,
          specMoment U μ (k + (i + 1)) * pathDensity U μ (n + 1 - 1 - (i + 1))
            = specMoment U μ (k + 1 + i) * pathDensity U μ (n - 1 - i) := by
        intro i _
        have a1 : k + (i + 1) = k + 1 + i := by omega
        have a2 : n + 1 - 1 - (i + 1) = n - 1 - i := by omega
        rw [a1, a2]
      rw [Finset.sum_congr rfl hcong]
      have b1 : n + 1 - 1 - 0 = n := by omega
      simp only [Nat.add_zero, b1]
      ring

lemma pathDensity_succ (hU : IsGraphon U μ) (n : ℕ) :
    pathDensity U μ (n + 1)
      = edgeDensity U μ * pathDensity U μ n + ∑ i ∈ Finset.range n, specMoment U μ i * pathDensity U μ (n - 1 - i) := by
  rw [pathDensity_succ_aux hU n, pairing_compressIter_pathIter_closed hU n 0]
  simp only [Nat.zero_add]

end OddCycleBound
