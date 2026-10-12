import Tengoku
import Tengoku.OpenaiMath.OAI.Probability.Subsphere.Mixture.BetaTheory

namespace OAI

noncomputable section

namespace SubsphereCurrent.Mixture
section
open MeasureTheory ProbabilityTheory Set

section
open scoped ENNReal NNReal RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

lemma measurable_directionSampler (V N : Submodule ℝ E) :
    Measurable (fun z : Orthogonal Vᗮ × N => blockIso V 1 z.1 (z.2 : E)) :=
  ((continuous_blockIso V).comp
    ((continuous_const.prodMk continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))).measurable

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma latitude_norm (V : Submodule ℝ E) (e : Metric.sphere (0 : V) 1)
    (x : latitudeSpace V e) (hx : ‖x‖ = 1) {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    ‖Real.sqrt (1-q) • (e.val : E)+Real.sqrt q • (x : E)‖ = 1 := by
  have ho : ⟪Real.sqrt (1-q) • (e.val : E),Real.sqrt q • (x : E)⟫ = 0 := by
    have := Submodule.mem_orthogonal_singleton_iff_inner_right.mp x.prop
    simp [real_inner_smul_left,real_inner_smul_right,this]
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_real ho
  have hn : ‖(x : E)‖ = 1 := hx
  simp only [← pow_two,norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
    latitude_e_norm V e,hn,mul_one,Real.sq_sqrt (sub_nonneg.mpr hq1),Real.sq_sqrt hq] at h
  nlinarith [norm_nonneg (Real.sqrt (1-q) • (e.val : E)+Real.sqrt q • (x : E))]

omit [MeasurableSpace E] [BorelSpace E] in
lemma latitude_coordinate (V : Submodule ℝ E) (e : Metric.sphere (0 : V) 1)
    (u : Orthogonal V) (x : latitudeSpace V e) {q : ℝ} (hq : 0 ≤ q) :
    perpCoordinate V (blockIso V u 1
      (Real.sqrt (1-q) • (e.val : E)+Real.sqrt q • (x : E))) =
      q * perpCoordinate V (x : E) := by
  rw [perpCoordinate_blockIso,perpCoordinate,map_add,map_smul,map_smul,
    Vᗮ.orthogonalProjectionOnto_apply_of_mem_orthogonal (by simp)]
  simp only [smul_zero,zero_add,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,Real.sq_sqrt hq,perpCoordinate]

omit [MeasurableSpace E] [BorelSpace E] in
lemma latitude_rank_one (V : Submodule ℝ E) (e : Metric.sphere (0 : V) 1)
    (hV : Module.finrank ℝ V = 1) : latitudeSpace V e = Vᗮ := by
  have he : (e.val : E) ≠ 0 := by intro h; have := latitude_e_norm V e; simp [h] at this
  have hspan : ℝ ∙ (e.val : E) = V := by
    apply Submodule.eq_of_le_of_finrank_eq
    · exact Submodule.span_le.mpr (by simp)
    · rw [finrank_span_singleton he,hV]
  exact congrArg Submodule.orthogonal hspan

omit [MeasurableSpace E] [BorelSpace E] in
lemma latitude_coordinate_rank_one (V : Submodule ℝ E) (e : Metric.sphere (0 : V) 1)
    (hV : Module.finrank ℝ V = 1) (x : latitudeSpace V e) :
    perpCoordinate V (x : E) = ‖x‖^2 := by
  have hx : (x : E) ∈ Vᗮ := (latitude_rank_one V e hV) ▸ x.prop
  unfold perpCoordinate
  change ‖Vᗮ.starProjection (x : E)‖^2 = ‖(x : E)‖^2
  rw [Submodule.starProjection_eq_self_iff.mpr hx]

lemma measurable_latitudeSampler (V : Submodule ℝ E) (e : Metric.sphere (0 : V) 1) :
    Measurable (fun z : ℝ × (Orthogonal V × latitudeSpace V e) => blockIso V z.2.1 1
      (Real.sqrt (1-z.1) • (e.val : E)+Real.sqrt z.1 • (z.2.2 : E))) :=
  ((continuous_blockIso V).comp
    (((continuous_fst.comp continuous_snd).prodMk continuous_const).prodMk
      (((continuous_const.sub continuous_fst).sqrt.smul continuous_const).add
        (continuous_fst.sqrt.smul (continuous_subtype_val.comp
          (continuous_snd.comp continuous_snd)))))).measurable

end
open scoped ENNReal NNReal

lemma beta_product_preserving {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    MeasurePreserving (fun z : ℝ × ℝ => z.1*z.2)
      ((betaMeasure a b).prod (betaMeasure (a+b) c)) (betaMeasure a (b+c)) := by
  let : IsProbabilityMeasure (gammaMeasure a 1) := isProbabilityMeasure_gammaMeasure ha (by norm_num)
  let : IsProbabilityMeasure (gammaMeasure b 1) := isProbabilityMeasure_gammaMeasure hb (by norm_num)
  let : IsProbabilityMeasure (gammaMeasure c 1) := isProbabilityMeasure_gammaMeasure hc (by norm_num)
  let : IsProbabilityMeasure (gammaMeasure (a+b) 1) :=
    isProbabilityMeasure_gammaMeasure (add_pos ha hb) (by norm_num)
  let : IsProbabilityMeasure (gammaMeasure (b+c) 1) :=
    isProbabilityMeasure_gammaMeasure (add_pos hb hc) (by norm_num)
  let : IsProbabilityMeasure (betaMeasure a b) := isProbabilityMeasureBeta ha hb
  let μ := ((gammaMeasure a 1).prod (gammaMeasure b 1)).prod (gammaMeasure c 1)
  have hF : MeasurePreserving
      (fun z : (ℝ × ℝ) × ℝ => (z.1.1/(z.1.1+z.1.2),(z.1.1+z.1.2)/(z.1.1+z.1.2+z.2)))
      μ ((betaMeasure a b).prod (betaMeasure (a+b) c)) := by
    exact ((MeasurePreserving.id (betaMeasure a b)).prod (gamma_ratio_preserving (add_pos ha hb) hc)).comp
      ((measurePreserving_prodAssoc (betaMeasure a b) (gammaMeasure (a+b) 1) (gammaMeasure c 1)).comp
        ((betaJoin_preserving ha hb).prod (MeasurePreserving.id (gammaMeasure c 1))))
  have hG : MeasurePreserving (fun z : (ℝ × ℝ) × ℝ => z.1.1/(z.1.1+(z.1.2+z.2)))
      μ (betaMeasure a (b+c)) := by
    exact (gamma_ratio_preserving ha (add_pos hb hc)).comp
      (((MeasurePreserving.id (gammaMeasure a 1)).prod (gamma_sum_preserving hb hc)).comp
        (measurePreserving_prodAssoc (gammaMeasure a 1) (gammaMeasure b 1) (gammaMeasure c 1)))
  refine ⟨by fun_prop,?_⟩
  rw [← hF.map_eq,Measure.map_map (by fun_prop) hF.measurable]
  calc
    _ = Measure.map (fun z : (ℝ × ℝ) × ℝ => z.1.1/(z.1.1+(z.1.2+z.2))) μ := by
      apply Measure.map_congr
      have hpos : ∀ᵐ z : (ℝ × ℝ) × ℝ ∂μ, 0 < z.1.1 ∧ 0 < z.1.2 :=
        (measurePreserving_fst.quasiMeasurePreserving.ae (gamma_prod_ae_domain a b hb))
      filter_upwards [hpos] with z hz
      dsimp only [Function.comp_apply]
      rw [← mul_div_assoc,div_mul_cancel₀ _ (add_pos hz.1 hz.2).ne',add_assoc]
    _ = _ := hG.map_eq

end
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

end SubsphereCurrent.Mixture

end

end OAI
