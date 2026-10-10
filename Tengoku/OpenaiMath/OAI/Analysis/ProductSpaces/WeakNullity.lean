import Tengoku.OpenaiMath.OAI.Analysis.ProductSpaces.PathMoments

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uH uα

namespace IndependentProducts
section HilbertTools

variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

lemma weaklyNull_of_orthogonal_fixed_norm (u : ℕ → H) (c : ℝ) (hc : 0 < c)
    (hn : ∀ n, ‖u n‖ = c) (hi : Pairwise (fun n m => inner ℝ (u n) (u m) = 0)) :
    WeaklyNull u := by
  let w : ℕ → H := fun n => c⁻¹ • u n
  have hw : Orthonormal ℝ w := by
    constructor
    · intro n
      simp [w, norm_smul, hn, Real.norm_eq_abs, abs_of_pos hc, hc.ne']
    · intro n m hnm
      simp [w, inner_smul_left, inner_smul_right, hi hnm]
  intro f
  let y := (InnerProductSpace.toDual ℝ H).symm f
  have hs := (hw.inner_products_summable y).tendsto_atTop_zero
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  have hnorm : Tendsto (fun n => ‖f (w n)‖) atTop (𝓝 0) := by
    have he : ∀ n, inner ℝ (w n) y = f (w n) := fun n => by
      rw [real_inner_comm]
      exact InnerProductSpace.toDual_symm_apply
    simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero, he] using hsqrt
  have hfw := tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  have heq : (fun n => f (u n)) = (fun n => c * f (w n)) := by
    funext n
    rw [← smul_eq_mul, ← map_smul]
    congr 1
    dsimp [w]
    rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
  rw [heq]
  simpa using hfw.const_mul c

variable {α : Type uα} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]

end HilbertTools

section ChildL2
variable (μ : Measure ℝ) [IsProbabilityMeasure μ]
variable (h₂ : MemLp (fun w : ℝ => w) 2 μ)

lemma indepFun_pathSquare_mul_child (v : Vertex) {n m : ℕ} (hnm : n ≠ m) :
    IndepFun (fun ω : Sample => pathProduct v ω ^ 2 * (ω (childEdge v n) - 1))
      (fun ω : Sample => ω (childEdge v m)) (productMeasure μ) := by
  classical
  let f : Edge → ℝ → ℝ := fun e w => if e = childEdge v n then w - 1 else w ^ 2
  have hf : ∀ e, Measurable (f e) := fun e => by
    dsimp [f]
    split_ifs
    · exact measurable_id.sub_const 1
    · exact measurable_id.pow_const 2
  have hnot : childEdge v m ∉ insert (childEdge v n) (pathEdges v) := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨fun he => hnm ((childEdge_injective v he).symm), childEdge_not_mem_pathEdges v m⟩
  have hi := indepFun_finset_coordinates μ (insert (childEdge v n) (pathEdges v)) f hf
    (childEdge v m) hnot
  have he : (fun ω : Sample => ∏ i ∈ insert (childEdge v n) (pathEdges v), f i (ω i)) =
      (fun ω => pathProduct v ω ^ 2 * (ω (childEdge v n) - 1)) := by
    funext ω
    rw [Finset.prod_insert (childEdge_not_mem_pathEdges v n)]
    have hp : (∏ i ∈ pathEdges v, f i (ω i)) = pathProduct v ω ^ 2 := by
      rw [pathProduct_eq_prod_pathEdges, ← Finset.prod_pow]
      apply Finset.prod_congr rfl
      intro i hi
      have hne : i ≠ childEdge v n := fun h => childEdge_not_mem_pathEdges v n (h ▸ hi)
      simp [f, hne]
    simp only [f, ite_eq_left rfl, hp]
    ring
  rwa [he] at hi

end ChildL2
end IndependentProducts

namespace IndependentProducts

end IndependentProducts

end

end OAI
