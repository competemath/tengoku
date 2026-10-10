import Tengoku.OpenaiMath.OAI.Analysis.ProductSpaces.ClosedTails

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uι uκ

namespace IndependentProducts
section FiniteRepresentatives
variable (μ : Measure ℝ) [hμprob : IsProbabilityMeasure μ]
  (h₂ : MemLp (fun w : ℝ => w) 2 μ)

omit hμprob in
lemma representative_sum [IsProbabilityMeasure μ] {ι : Type uι} [Fintype ι]
    (x : ι → productSpan μ)
    (f : ι → Sample → ℝ) (hf : ∀ i, (x i).val =ᵐ[productMeasure μ] f i) (a : ι → ℝ) :
    ((∑ i, a i • x i).val : Sample → ℝ) =ᵐ[productMeasure μ] fun ω => ∑ i, a i * f i ω := by
  have hs : (∑ i, a i • x i).val = ∑ i, a i • (x i).val := by simp
  rw [hs]
  have ha : ∀ i, (a i • (x i).val : Lp ℝ 1 (productMeasure μ)) =ᵐ[productMeasure μ]
      fun ω => a i * f i ω := by
    intro i
    filter_upwards [Lp.coeFn_smul (a i) (x i).val, hf i] with ω hω hi
    simpa only [Pi.smul_apply, smul_eq_mul, hi] using hω
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i => a i • (x i).val),
    ae_all_iff.mpr ha] with ω hsum hall
  rw [hsum]
  exact Finset.sum_congr rfl (fun i _ => hall i)

omit hμprob in
lemma representative_sub [IsProbabilityMeasure μ] (x y : productSpan μ) (f g : Sample → ℝ)
    (hf : x.val =ᵐ[productMeasure μ] f) (hg : y.val =ᵐ[productMeasure μ] g) :
    ((x - y).val : Sample → ℝ) =ᵐ[productMeasure μ] fun ω => f ω - g ω := by
  change (↑(x.val - y.val) : Sample → ℝ) =ᵐ[productMeasure μ] _
  filter_upwards [Lp.coeFn_sub x.val y.val, hf, hg] with ω he hx hy
  simpa only [Pi.sub_apply, hx, hy] using he

omit hμprob in
lemma norm_eq_integral_abs_rep [IsProbabilityMeasure μ] (x : productSpan μ) (f : Sample → ℝ)
    (hf : x.val =ᵐ[productMeasure μ] f) : ‖x‖ = ∫ ω, |f ω| ∂productMeasure μ := by
  change ‖x.val‖ = _
  rw [L1.norm_eq_integral_norm]
  apply integral_congr_ae
  filter_upwards [hf] with ω hω
  simp only [hω, Real.norm_eq_abs]

lemma integrable_rep (x : productSpan μ) (f : Sample → ℝ)
    (hf : x.val =ᵐ[productMeasure μ] f) : Integrable f (productMeasure μ) :=
  ((Lp.memLp x.val).integrable le_rfl).congr hf

namespace FiniteHead
variable (T : FiniteHead)

end FiniteHead
end FiniteRepresentatives

/-- Descendant-only factor after the first exit. -/
def residualProduct (v : Vertex) (e : Edge) (ω : Sample) : ℝ :=
  ∏ d ∈ pathEdges v \ pathEdges e.val, ω d

lemma measurable_residualProduct (v : Vertex) (e : Edge) : Measurable (residualProduct v e) := by
  unfold residualProduct
  fun_prop

namespace FiniteHead
section FiniteTailData
variable {ι : Type uι} {κ : Type uκ} [hιfinite : Fintype ι] [Fintype κ] [DecidableEq ι]
variable (T : FiniteHead) (e : ι → T.Boundary) (v : κ → Vertex) (j : κ → ι) (a : κ → ℝ)

/-- Coefficients conditionally independent below the exit forest. -/
noncomputable def tailCoefficient (old : Sample) (i : ι) (desc : Sample) : ℝ :=
  ∑ k, if j k = i then a k * pathProduct (e i).val.val.dropLast old *
    residualProduct (v k) (e i).val desc else 0

lemma measurable_tailCoefficient {ι : Type uι} {κ : Type uκ}
    [Fintype ι] [Fintype κ] [DecidableEq ι]
    (T : FiniteHead) (e : ι → T.Boundary) (v : κ → Vertex) (j : κ → ι) (a : κ → ℝ) (i : ι) :
    Measurable (fun z : Sample × Sample => T.tailCoefficient e v j a z.1 i z.2) := by
  classical
  unfold tailCoefficient
  apply Finset.measurable_sum
  intro k hk
  split_ifs
  · exact ((measurable_const.mul ((measurable_pathProduct _).comp measurable_fst)).mul
      ((measurable_residualProduct _ _).comp measurable_snd))
  · fun_prop

lemma sum_tailCoefficient (z : ((ι → Sample) × Sample) × Sample)
    (he : Function.Injective e) (hv : ∀ k, (e (j k)).val.val <+: v k) :
    ∑ k, a k * pathProduct (v k) (T.stitched e z) =
      ∑ i, T.tailCoefficient e v j a z.2 i (z.1.1 i) * z.1.2 (e i).val := by
  classical
  simp only [tailCoefficient, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [T.stitched_path e he z (v k) (j k) (hv k)]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, residualProduct]
  ring

end FiniteTailData
end FiniteHead
end IndependentProducts

end

end OAI
