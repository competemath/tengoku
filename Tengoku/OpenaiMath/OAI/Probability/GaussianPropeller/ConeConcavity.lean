import Tengoku.OpenaiMath.OAI.Probability.GaussianPropeller.SoftMinimum

namespace OAI

universe uX uι uκ

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal

namespace GaussianPropeller.EhrhardCone
open GaussianPropeller.Quantile GaussianPropeller.EhrhardSmooth
variable {ι : Type uι} {κ : Type uκ} [Fintype ι] [Fintype κ] [Nonempty κ]
local notation "E" => EuclideanSpace ℝ ι
local notation "γ" => stdGaussian E

def cone (v : κ → E) : Set E := {y | ∀ i, 0 ≤ ⟪v i,y⟫}
def shifted (v : κ → E) (x : E) : Set E := {y | x+y ∈ cone v}
noncomputable def prob (v : κ → E) (x : E) : ℝ := (γ).real (shifted v x)

omit [Nonempty κ] in
lemma measurableSet_shifted [Nonempty κ] (v : κ → E) (x : E) : MeasurableSet (shifted v x) := by
  change MeasurableSet {y : E | ∀ i, 0 ≤ ⟪v i,x+y⟫}
  simpa only [ofPred_forall] using MeasurableSet.iInter (fun i =>
    measurableSet_le (measurable_const : Measurable (fun _ : E => (0:ℝ)))
      (show Measurable (fun y : E => ⟪v i,x+y⟫) by fun_prop))

lemma gaussian_open_pos {U : Set E} (hU : IsOpen U) (hne : U.Nonempty) : 0 < γ U := by
  have hac : (volume : Measure E) ≪ γ := by
    rw [Translation.stdGaussian_density]
    exact withDensity_absolutelyContinuous' Translation.measurable_stdDensity.ennreal_ofReal.aemeasurable
      (ae_of_all _ (fun x => ne_of_gt (ENNReal.ofReal_pos.mpr (Translation.stdDensity_pos x))))
  by_contra! hz
  have heq : γ U = 0 := le_antisymm hz bot_le
  exact ne_of_gt (hU.measure_pos volume hne) (hac heq)

lemma prob_mem (v : κ → E) (e : E) (he : ∀ i, 0 < ⟪v i,e⟫) (x : E) :
    prob v x ∈ Ioo (0:ℝ) 1 := by
  let U : Set E := {y | ∀ i, 0 < ⟪v i,x+y⟫}
  have hU : IsOpen U := by
    simpa only [U, ofPred_forall] using isOpen_iInter_of_finite (fun i =>
      isOpen_lt (continuous_const : Continuous (fun _ : E => (0:ℝ)))
        (show Continuous (fun y : E => ⟪v i,x+y⟫) by fun_prop))
  have hn : U.Nonempty := ⟨e-x, by simpa only [U, mem_ofPred_eq, show x+(e-x)=e by abel] using he⟩
  have hs : U ⊆ shifted v x := fun y hy i => (hy i).le
  have hp : 0 < (γ).real (shifted v x) := ENNReal.toReal_pos
    (ne_of_gt ((gaussian_open_pos hU hn).trans_le (measure_mono hs))) (measure_ne_top _ _)
  obtain ⟨i⟩ := ‹Nonempty κ›
  have hv : v i ≠ 0 := by intro hh; simpa only [hh, inner_zero_left, lt_self_iff_false] using he i
  let V : Set E := {y | ⟪v i,x+y⟫ < 0}
  have hV : IsOpen V := isOpen_lt (by fun_prop) continuous_const
  have hnV : V.Nonempty := by
    refine ⟨-v i-x,?_⟩
    change ⟪v i,x+(-v i-x)⟫ < 0
    rw [show x+(-v i-x)= -v i by abel, inner_neg_right]
    exact neg_neg_of_pos (real_inner_self_pos.mpr hv)
  have hsV : V ⊆ (shifted v x)ᶜ := by
    intro y hy hz
    exact (not_lt_of_ge (hz i)) hy
  have hc : 0 < (γ).real (shifted v x)ᶜ := ENNReal.toReal_pos
    (ne_of_gt ((gaussian_open_pos hV hnV).trans_le (measure_mono hsV))) (measure_ne_top _ _)
  rw [probReal_compl_eq_one_sub (measurableSet_shifted v x)] at hc
  exact ⟨hp, by change (γ).real (shifted v x) < 1; linarith only [hc]⟩

lemma gaussian_hyperplane_null (z : E) (hz : z ≠ 0) (c : ℝ) :
    γ {x | ⟪z,x⟫ = c} = 0 := by
  let L : StrongDual ℝ E := innerSL ℝ z
  have hL : L ≠ 0 := by
    intro heq
    have hx : ⟪z,z⟫ = 0 := by
      have h := DFunLike.congr_fun heq z
      simpa [L] using h
    exact hz (inner_self_eq_zero.mp hx)
  have hv : (variance L γ).toNNReal ≠ 0 := by
    rw [variance_dual_stdGaussian]
    exact ne_of_gt (Real.toNNReal_pos.mpr (sq_pos_of_pos (norm_pos_iff.mpr hL)))
  have instN : NullSingletonClass (gaussianReal (∫ x, L x ∂γ) (variance L γ).toNNReal) :=
    nullSingletonClass_gaussianReal hv
  have h := congrArg (fun μ : Measure ℝ => μ {c}) (IsGaussian.map_eq_gaussianReal (μ := γ) L)
  rw [Measure.map_apply L.continuous.measurable (measurableSet_singleton c), measure_singleton] at h
  exact h

omit [Nonempty κ] in
lemma ae_no_boundary [Nonempty κ] (v : κ → E) (hv : ∀ i, v i ≠ 0) (x : E) :
    ∀ᵐ y ∂γ, ∀ i, ⟪v i,x+y⟫ ≠ 0 := by
  apply ae_all_iff.mpr
  intro i
  have hh := gaussian_hyperplane_null (v i) (hv i) (-⟪v i,x⟫)
  have hh' : ∀ᵐ y ∂γ, ⟪v i,y⟫ ≠ -⟪v i,x⟫ := by
    rw [ae_iff]
    simpa only [not_not] using hh
  filter_upwards [hh'] with y hy
  rw [inner_add_right]
  intro hzero
  apply hy
  linarith only [hzero]

lemma cdf_softmin_limit (v : κ → E) (y : E) (hy : ∀ i, ⟪v i,y⟫ ≠ 0) :
    Tendsto (fun n : ℕ => Φ (SoftMin.value (fun i => (n:ℝ) • v i) y)) atTop
      (𝓝 ((cone v).indicator (fun _ => (1:ℝ)) y)) := by
  classical
  by_cases hmem : y ∈ cone v
  · rw [Set.indicator_of_mem hmem]
    exact tendsto_Φ_atTop.comp (SoftMin.value_tendsto_atTop v y
      (fun i => lt_of_le_of_ne (hmem i) (Ne.symm (hy i))))
  · rw [Set.indicator_of_notMem hmem]
    simp only [cone, mem_ofPred_eq, not_forall, not_le] at hmem
    obtain ⟨i,hi⟩ := hmem
    exact tendsto_Φ_atBot.comp (SoftMin.value_tendsto_atBot v y i hi)

end GaussianPropeller.EhrhardCone

namespace GaussianPropeller.Quantile

lemma Φ_eq_gaussianReal (a : ℝ) : Φ a = (gaussianReal 0 1).real (Iic a) := by
  rw [measureReal_def, gaussianReal_apply_eq_integral 0 (by norm_num : (1:NNReal) ≠ 0),
    ENNReal.toReal_ofReal (integral_nonneg (fun x => gaussianPDFReal_nonneg 0 1 x))]
  unfold Φ
  congr 1
  funext x
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, φ]

lemma integrable_mul_φ : Integrable (fun x : ℝ => x*φ x) := by
  have hi := (integrable_mul_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/2)).const_mul
    ((Real.sqrt (2*Real.pi))⁻¹)
  convert hi using 1
  funext x
  simp only [φ]
  rw [show -x^2/2 = -(1/2:ℝ)*x^2 by ring]
  ring

lemma tendsto_φ_atBot : Tendsto φ atBot (𝓝 0) := by
  have htop : Tendsto (fun x : ℝ => Real.exp (-(1/2:ℝ)*x^2)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp ((tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg (by norm_num : (-(1/2:ℝ)) < 0))
  have ht : Tendsto (fun x : ℝ => Real.exp (-(1/2:ℝ)*x^2)) atBot (𝓝 0) := by
    simpa only [Function.comp_def, neg_sq] using htop.comp tendsto_neg_atBot_atTop
  convert ht.const_mul ((Real.sqrt (2*Real.pi))⁻¹) using 1
  · funext x; unfold φ; congr 2; ring
  · simp only [mul_zero]

lemma tail_integrable {X : Type uX} [MeasurableSpace X] {μ : Measure X} {f : X → ℝ}
    (hi : Integrable f μ) (hn : 0 ≤ᵐ[μ] f) :
    IntegrableOn (fun t : ℝ => μ.real {x | t ≤ f x}) (Ioi 0) := by
  apply integrable_toReal_of_lintegral_ne_top
  · exact (show Antitone (fun t : ℝ => μ {x | t ≤ f x}) from
      fun _ _ hst => measure_mono (fun _ h => hst.trans h)).measurable.aemeasurable
  · rw [← lintegral_eq_lintegral_meas_le μ hn hi.aemeasurable]
    exact hi.lintegral_lt_top.ne

end GaussianPropeller.Quantile

namespace GaussianPropeller.EhrhardCone
open GaussianPropeller.Quantile
variable {ι : Type uι} {κ : Type uκ} [Fintype ι] [Fintype κ] [Nonempty κ]
local notation "E" => EuclideanSpace ℝ ι
local notation "γ" => stdGaussian E

lemma measurableSet_cone (v : κ → E) : MeasurableSet (cone v) := by
  simpa only [shifted, zero_add, ofPred_mem_eq] using measurableSet_shifted v 0

omit [Fintype κ] [Nonempty κ] in
lemma prob_zero [Fintype κ] [Nonempty κ] (v : κ → E) : prob v 0 = (γ).real (cone v) := by
  simp only [prob, shifted, zero_add, ofPred_mem_eq]

end GaussianPropeller.EhrhardCone

end OAI
