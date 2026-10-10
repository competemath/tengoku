import Tengoku.OpenaiMath.OAI.Analysis.LpDimension.CoordinateLaws

namespace OAI

noncomputable section
open MeasureTheory Filter ProbabilityTheory Set Finset Matrix
open scoped BigOperators Topology Matrix ENNReal NNReal RealInnerProductSpace
universe u uE uI uV uΩ

namespace SubpolynomialLp

lemma integrated_power_perturbation {Ω : Type uΩ} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p ε C b : ℝ)
    (hp : 0 < p) (hScalar : ∀ a t : ℝ, abs (|a+t|^p-|a|^p) ≤ ε*|a|^p+C*|t|^p)
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ x, |X x| ≤ B ∧ |Y x| ≤ B)
    (hYb : (∫ x, |Y x|^p ∂μ)=b) :
    |(∫ x, |X x|^p ∂μ)-b| ≤ ε*b+C*(∫ x, |X x-Y x|^p ∂μ) := by
  have hXi := bounded_power_integrable μ X hX p B hp hB0 (fun x => (hB x).1)
  have hYi := bounded_power_integrable μ Y hY p B hp hB0 (fun x => (hB x).2)
  have hDi := bounded_power_integrable μ (fun x => X x-Y x) (hX.sub hY) p (2*B) hp
    (by positivity) (fun x => (abs_sub _ _).trans (by linarith [(hB x).1,(hB x).2]))
  calc
    _ = |∫ x, |X x|^p-|Y x|^p ∂μ| := by rw [integral_sub hXi hYi,hYb]
    _ ≤ ∫ x, abs (|X x|^p-|Y x|^p) ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, ε*|Y x|^p+C*|X x-Y x|^p ∂μ := by
      apply integral_mono (hXi.sub hYi).abs ((hYi.const_mul ε).add (hDi.const_mul C))
      intro x
      simpa only [Pi.sub_apply,Pi.add_apply,add_sub_cancel_left,add_sub_cancel_right,add_sub_cancel] using hScalar (Y x) (X x-Y x)
    _ = _ := by rw [integral_add (hYi.const_mul ε) (hDi.const_mul C),integral_const_mul,integral_const_mul,hYb]

variable {E : Type uE} [Fintype E]

def projectedRampLaw (μ : Measure (E → ℝ)) (P : Matrix E E ℝ) (ℓ : ℕ) : Measure (E → ℝ) :=
  symmetricLaw (μ.map (fun v => P.mulVec (fun e => dyadicRamp ℓ (v e))))

lemma projectedRampLaw_bounded (μ : Measure (E → ℝ)) (P : Matrix E E ℝ) (ℓ : ℕ)
    (H : ℝ) (hr : ∀ e, matrixRowNorm P e ≤ H) :
    ∀ᵐ z ∂projectedRampLaw μ P ℓ, ∀ e, |z e| ≤ H*2^(2*ℓ) := by
  apply ae_all_iff.mpr
  intro e
  apply symmetricLaw_ae
  · apply (ae_map_iff (show Measurable (fun v : E → ℝ => P.mulVec (fun a => dyadicRamp ℓ (v a))) by change Measurable (fun v : E → ℝ => fun e => ∑ a, P e a*dyadicRamp ℓ (v a)); fun_prop).aemeasurable
      (measurableSet_le (show Measurable (fun z : E → ℝ => |z e|) by fun_prop) measurable_const)).mpr
    apply ae_of_all
    intro v
    exact (matrix_mulVec_bound P _ _ (fun a => abs_dyadicRamp_le ℓ (v a)) e).trans
      (mul_le_mul_of_nonneg_right (hr e) (by positivity))
  · intro z hz
    simpa only [Pi.neg_apply,abs_neg] using hz

lemma projectedRampLaw_range {V : Type uV} [Fintype V]
    (μ : Measure (E → ℝ)) (P : Matrix E E ℝ) (ℓ : ℕ) (A : Matrix E V ℝ)
    (hP : P ∈ retractions A) :
    ∀ᵐ z ∂projectedRampLaw μ P ℓ, ∃ x, A.mulVec x=z := by
  classical
  have hm : MeasurableSet {z : E → ℝ | ∃ x, A.mulVec x=z} :=
    (LinearMap.range (Matrix.toLin' A)).closed_of_finiteDimensional.measurableSet
  apply symmetricLaw_ae
  · apply (ae_map_iff (show Measurable (fun v : E → ℝ => P.mulVec (fun a => dyadicRamp ℓ (v a))) by change Measurable (fun v : E → ℝ => fun e => ∑ a, P e a*dyadicRamp ℓ (v a)); fun_prop).aemeasurable hm).mpr
    exact ae_of_all _ (fun v => retraction_range A P hP _)
  · rintro z ⟨x,hx⟩
    exact ⟨-x,by rw [Matrix.mulVec_neg,hx]⟩

lemma projectedRampLaw_moment (μ : Measure (E → ℝ)) [IsProbabilityMeasure μ]
    (P : Matrix E E ℝ) (ℓ : ℕ) (q : ℝ) (hq : 0 < q) (e : E) :
    (∫ z, |z e|^q ∂projectedRampLaw μ P ℓ) =
      ∫ v, |P.mulVec (fun a => dyadicRamp ℓ (v a)) e|^q ∂μ := by
  let F := fun v : E → ℝ => P.mulVec (fun a => dyadicRamp ℓ (v a))
  have hF : Measurable F := by dsimp [F,Matrix.mulVec,dotProduct]; fun_prop
  have hi : Integrable (fun z : E → ℝ => |z e|^q) (μ.map F) := by
    rw [integrable_map_measure (show Measurable (fun z : E → ℝ => |z e|^q) by fun_prop).aestronglyMeasurable hF.aemeasurable]
    exact bounded_power_integrable μ (fun v => F v e) (by fun_prop) q
      (matrixRowNorm P e*2^(2*ℓ)) hq (by positivity [matrixRowNorm_nonneg P e])
      (fun v => matrix_mulVec_bound P _ _ (fun a => abs_dyadicRamp_le ℓ (v a)) e)
  rw [projectedRampLaw,symmetricLaw_even_integral _ _ (by fun_prop) hi
    (fun z => by simp only [Pi.neg_apply,abs_neg]),integral_map hF.aemeasurable (show Measurable (fun z : E → ℝ => |z e|^q) by fun_prop).aestronglyMeasurable]

end SubpolynomialLp

end

end OAI
