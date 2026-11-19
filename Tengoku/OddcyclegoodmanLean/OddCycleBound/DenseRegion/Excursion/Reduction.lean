import Tengoku.OddcyclegoodmanLean.OddCycleBound.DenseRegion.Excursion.Projections
import Tengoku.OddcyclegoodmanLean.OddCycleBound.Excursion.Bijections

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Excursion expansions (Lemmas 3.1, 3.2, 3.3)

* `cycleDensity_excursions` (Lemma `lem:cycle-excursions`): expanding the `m`-fold kernel product
  over words, the all-`P` word gives `q^m`, the all-`Q` word gives `τ = Tr(A^m)`, and the words
  with `r ≥ 1` excursions contribute `(m/r) ∑_{tuples} q^{∑α} ∏ gᵀ A^{βᵢ} g`, by the marked-word
  count (`sum_numMarks_eq`), the bijection with block-length tuples (`sum_pq_eq_sum_tuples`) and the
  block evaluation (`applyWord_blockWord`).
* `pathDensity_excursions` (Lemma `lem:path-excursions`): the same for paths, with fixed endpoints.
* `neckSum_eq_baseline_add_momentPhi` (Lemma `lem:polynomial-reduction`): adding the cycle
  expansions of `W` and `U = 1 - W`, where the all-`Q` words cancel because `m` is odd, and
  subtracting the path expansion gives `p^m + q^m - q^{m-1} + Φ_m`.
-/

open MeasureTheory
open scoped BigOperators

namespace OddCycleBound.DenseRegion

open Excursion

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {V W : Ω → Ω → ℝ}

/-! ### Evaluation of traces of words -/

lemma trace_listKer_false_cons (hV : IsGraphon V μ) (l : List Bool) (x : Ω) :
    trace μ (listKer V μ (false :: l)) = applyWord V μ (false :: l) (fun _ => 1) x := by
  rw [applyWord_false_cons hV l]

/-! ### Cycle densities by excursions (Lemma 3.1) -/

/-! ### Path densities by excursions (Lemma 3.2) -/

lemma kernelOp_finset_sum (hV : IsGraphon V μ) {ι : Type*} (s : Finset ι) {f : ι → Ω → ℝ}
    (hf : ∀ i ∈ s, Good (f i)) (x : Ω) :
    kernelOp V μ (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, kernelOp V μ (f i) x := by
  simp only [kernelOp, Finset.mul_sum]
  exact integral_finsetSum s fun i hi => integrable_Uf hV (hf i hi) x

/-- The path expansion over words: `T_V^k 1 = ∑_{words of length k} (R₁ M_V ⋯ R_k M_V) 1`.-/
lemma pathIter_eq_sum_words (hV : IsGraphon V μ) : ∀ k : ℕ,
    pathIter V μ k = fun x => ∑ w ∈ allWords k, applyWord V μ w (fun _ => 1) x
  | 0 => by
      funext x
      simp [allWords, listsOf, applyWord, pathIter]
  | k + 1 => by
      funext x
      show kernelOp V μ (pathIter V μ k) x = _
      rw [pathIter_eq_sum_words hV k,
        kernelOp_finset_sum hV _ fun w _ => good_applyWord hV good_one w, sum_allWords_succ]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [kernelOp_eq_kerP_add_kerQ hV (good_applyWord hV good_one w)]
      rfl

lemma mean_compress (hV : IsGraphon V μ) {f : Ω → ℝ} (hf : Good f) :
    mean μ (compress V μ f) = 0 := by
  unfold mean compress
  rw [integral_sub (good_kernelOp hV hf).integrable (integrable_const _)]
  simp [mean]

lemma mean_applyWord_true_cons (hV : IsGraphon V μ) (l : List Bool) :
    mean μ (applyWord V μ (true :: l) (fun _ => 1)) = 0 := by
  show mean μ (kernelOp (kerQ V μ) μ (applyWord V μ l fun _ => 1)) = 0
  rw [kernelOp_kerQ hV (good_applyWord hV good_one l)]
  exact mean_compress hV (good_applyWord hV good_one l)

lemma sum_range_ite_le (K c : ℕ) (f : ℕ → ℝ) :
    ∑ N ∈ Finset.range (K + 1), (if c + N ≤ K then f N else 0) =
      if c ≤ K then ∑ N ∈ Finset.range (K - c + 1), f N else 0 := by
  rw [← Finset.sum_filter]
  split_ifs with hc
  · refine Finset.sum_congr ?_ fun _ _ => rfl
    ext N; simp only [Finset.mem_filter, Finset.mem_range]; omega
  · refine Finset.sum_eq_zero fun N hN => ?_
    simp only [Finset.mem_filter] at hN; omega

/-- **Lemma 3.2** (`lem:path-excursions`), in moment form:
`t(P_k, V) = ∑_{r, 2r ≤ k} ∑_j h_{k-2r-j}(q^{×(r+1)}) · momentConv s r j`.-/
theorem pathDensity_excursions (hV : IsGraphon V μ) (k : ℕ) :
    pathDensity V μ k = ∑ r ∈ Finset.range (k + 1),
      if 2 * r ≤ k then
        conv (fun d => hsym (List.replicate (r + 1) (edgeDensity V μ)) d)
          (momentConv (specMoment V μ) r) (k - 2 * r)
      else 0 := by
  classical
  have hsum : pathDensity V μ k =
      ∑ w ∈ allWords k, mean μ (applyWord V μ w (fun _ => 1)) := by
    rw [pathDensity, pathIter_eq_sum_words hV k, mean]
    exact integral_finsetSum _ fun w _ => (good_applyWord hV good_one w).integrable
  rw [hsum, ← Finset.sum_filter_add_sum_filter_not (allWords k) (fun l => l.head? ≠ some true)]
  have hzero : ∑ w ∈ (allWords k).filter (fun l => ¬ l.head? ≠ some true),
      mean μ (applyWord V μ w (fun _ => 1)) = 0 := by
    refine Finset.sum_eq_zero fun w hw => ?_
    rw [Finset.mem_filter, not_not] at hw
    obtain ⟨l, rfl⟩ : ∃ l, w = true :: l := by
      cases w with
      | nil => simp at hw
      | cons b l => simp at hw; exact ⟨l, by rw [hw.2]⟩
    exact mean_applyWord_true_cons hV l
  rw [hzero, add_zero, sum_head_ne_true_eq]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hinner : ∀ N, (∑ t ∈ tuples r N, mean μ (applyWord V μ
      (blockWord t ++ List.replicate (k - 2 * r - N) false) fun _ => 1)) =
      edgeDensity V μ ^ (k - 2 * r - N) * tupleSum (edgeDensity V μ) (specMoment V μ) r N := by
    intro N
    rw [tupleSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [applyWord_blockWord hV, mean_const]
  simp only [hinner]
  rw [show (fun N => if 2 * r + N ≤ k then edgeDensity V μ ^ (k - 2 * r - N) *
      tupleSum (edgeDensity V μ) (specMoment V μ) r N else 0) =
      fun N => if 2 * r + N ≤ k then edgeDensity V μ ^ (k - 2 * r - N) *
      tupleSum (edgeDensity V μ) (specMoment V μ) r N else 0 from rfl, sum_range_ite_le]
  split_ifs with h2r
  · rw [List.replicate_succ, hsym_cons_eq_conv, conv_assoc, ← tupleSum_eq, conv_comm]
    unfold conv
    refine Finset.sum_congr rfl fun N hN => ?_
    rw [Finset.mem_range] at hN
    rw [show k - 2 * r - N = k - 2 * r - N from rfl]
    ring
  · rfl

/-! ### The reduction to excursion polynomials (Lemma 3.3) -/

lemma sum_range_ite_two_mul_le (R : ℕ) (f : ℕ → ℝ) :
    ∑ k ∈ Finset.range (2 * R + 1), (if 2 * (k + 1) ≤ 2 * R + 1 then f k else 0) =
      ∑ k ∈ Finset.range R, f k := by
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

lemma sum_range_ite_two_mul_le' (R : ℕ) (f : ℕ → ℝ) :
    ∑ r ∈ Finset.range (2 * R + 1), (if 2 * r ≤ 2 * R then f r else 0) =
      f 0 + ∑ k ∈ Finset.range R, f (k + 1) := by
  rw [← Finset.sum_filter]
  rw [show (Finset.range (2 * R + 1)).filter (fun r => 2 * r ≤ 2 * R) = Finset.range (R + 1) by
    ext r; simp only [Finset.mem_filter, Finset.mem_range]; omega]
  rw [Finset.sum_range_succ', add_comm]

end OddCycleBound.DenseRegion
