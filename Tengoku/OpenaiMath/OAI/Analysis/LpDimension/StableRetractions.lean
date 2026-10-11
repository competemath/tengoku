import Tengoku.OpenaiMath.OAI.Analysis.LpDimension.ClippedMoments

namespace OAI

noncomputable section
open MeasureTheory Filter Matrix NormedSpace Metric Module Set ProbabilityTheory
open scoped BigOperators Topology Matrix Matrix.Norms.Operator ENNReal NNReal RealInnerProductSpace
universe u uE uV uΩ uε uι

namespace SubpolynomialLp

lemma below_projection_moments {Ω : Type uΩ} {E : Type uE} [MeasurableSpace Ω] [Fintype E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → E → ℝ)
    (hm : ∀ e, Measurable (fun x => Y x e)) (P : Matrix E E ℝ)
    (lam : E → ℝ) (hlam : ∀ e, 0 ≤ lam e) (hls : ∑ e, lam e = 1)
    (p T a H b err B : ℝ) (hp : 1 < p) (hp2 : p < 2) (hT : 0 ≤ T)
    (ha : 0 < a) (hH : 0 ≤ H) (herr : 0 ≤ err)
    (hrow : ∀ e, (∑ f, |P e f|) ≤ H) (hPY : ∀ x, P.mulVec (Y x) = Y x)
    (hex : ∀ e, Integrable (fun x => max (|Y x e|-T) 0) μ)
    (hexm : ∀ e, (∫ x, max (|Y x e|-T) 0 ∂μ) ≤ err)
    (hb : ∀ e, (∫ x, (min |Y x e| a)^p ∂μ) = b)
    (henergy : (∑ e, lam e*(∫ x, (P.mulVec (fun f => clip T (Y x f)) e)^2 ∂μ)) ≤ B) :
    (∑ e, lam e*|(∫ x, |P.mulVec (fun f => clip T (Y x f)) e|^p ∂μ)-b|) ≤
      (p*a^(p-1))*H*err+a^(p-2)*B := by
  let F : Ω → E → ℝ := fun x => P.mulVec (fun f => clip T (Y x f))
  have hFm (e : E) : Measurable (fun x => F x e) := by
    exact Finset.measurable_sum _ (fun f _ =>
      measurable_const.mul ((clip_measurable T).comp (hm f)))
  have hFb (x : Ω) (e : E) : |F x e| ≤ H*T :=
    (matrix_clip_bounds P (Y x) T H hT hrow (hPY x)).1 e
  have hFp (e : E) : Integrable (fun x => |F x e|^p) μ :=
    bounded_power_integrable μ _ (hFm e) p (H*T) (by linarith) (mul_nonneg hH hT) (fun x => hFb x e)
  have hFc (e : E) : Integrable (fun x => (min |F x e| a)^p) μ :=
    bounded_capped_integrable μ _ (hFm e) p a (by linarith) ha.le
  have hYc (e : E) : Integrable (fun x => (min |Y x e| a)^p) μ :=
    bounded_capped_integrable μ _ (hm e) p a (by linarith) ha.le
  have hFe (e : E) : Integrable (fun x => (F x e)^2) μ := by
    simpa only [Real.rpow_two, sq_abs] using
      bounded_power_integrable μ _ (hFm e) 2 (H*T) (by norm_num) (mul_nonneg hH hT) (fun x => hFb x e)
  have hd (e : E) : (∫ x, |Y x e-F x e| ∂μ) ≤ H*err ∧
      Integrable (fun x => |Y x e-F x e|) μ := by
    have hi : Integrable (fun x => ∑ f, |P e f| *max (|Y x f|-T) 0) μ :=
      integrable_finsetSum _ (fun f _ => (hex f).const_mul _)
    have hle (x : Ω) : |Y x e-F x e| ≤ ∑ f, |P e f| *max (|Y x f|-T) 0 :=
      (matrix_clip_bounds P (Y x) T H hT hrow (hPY x)).2 e
    have hdi : Integrable (fun x => |Y x e-F x e|) μ :=
      hi.mono' ((hm e).sub (hFm e)).abs.aestronglyMeasurable
        (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs, abs_abs] using hle x))
    refine ⟨?_,hdi⟩
    calc
      _ ≤ ∫ x, ∑ f, |P e f| *max (|Y x f|-T) 0 ∂μ := integral_mono hdi hi hle
      _ = ∑ f, |P e f| *(∫ x, max (|Y x f|-T) 0 ∂μ) := by
        rw [integral_finsetSum _ (fun f _ => (hex f).const_mul _)]
        simp only [integral_const_mul]
      _ ≤ ∑ f, |P e f| *err := Finset.sum_le_sum (fun f _ =>
        mul_le_mul_of_nonneg_left (hexm f) (abs_nonneg _))
      _ = (∑ f, |P e f|)*err := (Finset.sum_mul ..).symm
      _ ≤ H*err := mul_le_mul_of_nonneg_right (hrow e) herr
  have hc (e : E) : |(∫ x, (min |F x e| a)^p ∂μ)-b| ≤ (p*a^(p-1))*H*err := by
    rw [← hb e, ← integral_sub (hFc e) (hYc e)]
    calc
      _ ≤ ∫ x, |(min |F x e| a)^p-(min |Y x e| a)^p| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ x, (p*a^(p-1))*|Y x e-F x e| ∂μ := by
        apply integral_mono ((hFc e).sub (hYc e)).abs ((hd e).2.const_mul _)
        intro x
        simpa only [Pi.sub_apply, abs_sub_comm] using capped_power_lipschitz p a hp.le ha.le (F x e) (Y x e)
      _ = (p*a^(p-1))*(∫ x, |Y x e-F x e| ∂μ) := integral_const_mul _ _
      _ ≤ (p*a^(p-1))*H*err := by
        have hpos : 0 ≤ p*a^(p-1) := mul_nonneg (by linarith) (Real.rpow_nonneg ha.le _)
        nlinarith [mul_le_mul_of_nonneg_left (hd e).1 hpos]
  have htail (e : E) : 0 ≤ (∫ x, |F x e|^p ∂μ)-(∫ x, (min |F x e| a)^p ∂μ) ∧
      (∫ x, |F x e|^p ∂μ)-(∫ x, (min |F x e| a)^p ∂μ) ≤ a^(p-2)*(∫ x, (F x e)^2 ∂μ) := by
    rw [← integral_sub (hFp e) (hFc e), ← integral_const_mul]
    refine ⟨integral_nonneg (fun x => (capped_power_tail_bound p a (F x e) (by linarith) hp2 ha).1), ?_⟩
    exact integral_mono ((hFp e).sub (hFc e)) ((hFe e).const_mul _)
      (fun x => (capped_power_tail_bound p a (F x e) (by linarith) hp2 ha).2)
  calc
    _ ≤ ∑ e, lam e*((p*a^(p-1))*H*err+a^(p-2)*(∫ x, (F x e)^2 ∂μ)) := by
      apply Finset.sum_le_sum
      intro e _
      apply mul_le_mul_of_nonneg_left _ (hlam e)
      have ht := abs_add_le ((∫ x, |F x e|^p ∂μ)-(∫ x, (min |F x e| a)^p ∂μ))
        ((∫ x, (min |F x e| a)^p ∂μ)-b)
      rw [sub_add_sub_cancel, abs_of_nonneg (htail e).1] at ht
      linarith [(htail e).2, hc e]
    _ = (p*a^(p-1))*H*err+a^(p-2)*(∑ e, lam e*(∫ x, (F x e)^2 ∂μ)) := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hls, one_mul]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      ring
    _ ≤ _ := add_le_add_right (mul_le_mul_of_nonneg_left henergy (Real.rpow_nonneg ha.le _)) _

lemma L2_norm_sq {Ω : Type uΩ} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ) (hf : MemLp f 2 μ) : ‖hf.toLp f‖^2 = ∫ x, (f x)^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  simp only [hx, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

lemma Lp_coe_sum {Ω : Type uΩ} {ι : Type uι} [MeasurableSpace Ω] (μ : Measure Ω)
    (s : Finset ι) (f : ι → Lp ℝ 2 μ) :
    (fun x => (∑ i ∈ s, f i) x) =ᵐ[μ] (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero ℝ 2 μ] with x hx
    simpa only [Finset.sum_empty, Pi.zero_apply] using hx
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (f i) (∑ j ∈ s, f j), ih] with x hx hy
    simp only [Pi.add_apply] at hx
    rw [hx, hy]

lemma L2_hilbertMul_energy {Ω : Type uΩ} {E : Type uE} [MeasurableSpace Ω] [Fintype E]
    (μ : Measure Ω) (f : E → Ω → ℝ) (hf : ∀ e, MemLp (f e) 2 μ)
    (P : Matrix E E ℝ) (e : E) :
    ‖hilbertMul P (fun e => (hf e).toLp (f e)) e‖^2 =
      ∫ x, (∑ a, P e a*f a x)^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  have hc : ∀ a, (fun x => (P e a • (hf a).toLp (f a)) x) =ᵐ[μ] fun x => P e a*f a x := by
    intro a
    filter_upwards [Lp.coeFn_smul (P e a) ((hf a).toLp (f a)), (hf a).coeFn_toLp] with x hx hy
    simpa only [Pi.smul_apply, smul_eq_mul, hy] using hx
  apply integral_congr_ae
  filter_upwards [Lp_coe_sum μ Finset.univ (fun a => P e a • (hf a).toLp (f a)),
    ae_all_iff.mpr hc] with x hx hy
  change inner ℝ ((∑ a, P e a • (hf a).toLp (f a)) x)
    ((∑ a, P e a • (hf a).toLp (f a)) x) = _
  rw [hx]
  simp only [hy, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

lemma charFun_linear_sum {ι : Type uι} [Fintype ι] (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (g : ι → ℝ) (t : ℝ) :
    charFun ((Measure.pi μ).map (fun x : ι → ℝ => ∑ i, g i*x i)) t =
      ∏ i, charFun (μ i) (t*g i) := by
  have hm : Measurable (fun x : ι → ℝ => ∑ i, g i*x i) :=
    Finset.measurable_sum _ (fun i _ => measurable_const.mul (measurable_pi_apply i))
  rw [charFun_apply_real, integral_map hm.aemeasurable (by fun_prop)]
  simp_rw [Complex.ofReal_sum]
  have he : ∀ x : ι → ℝ,
      Complex.exp ((t:ℂ)*(∑ i, ((g i*x i:ℝ):ℂ))*Complex.I) =
        ∏ i, Complex.exp ((((t*g i:ℝ):ℂ)*x i)*Complex.I) := by
    intro x
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [he]
  rw [integral_fintype_prod_eq_prod (fun i (x : ℝ) => Complex.exp ((((t*g i:ℝ):ℂ)*x)*Complex.I))]
  simp only [charFun_apply_real]

lemma clip_sq (T x : ℝ) (hT : 0 ≤ T) : (clip T x)^2 = min (x^2) (T^2) := by
  rw [← sq_abs (clip T x), clip_abs T x hT]
  by_cases hx : |x| ≤ T
  · rw [min_eq_left hx, sq_abs, min_eq_left]
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg x) hT).mpr hx
  · have ht : T ≤ |x| := le_of_not_ge hx
    rw [min_eq_right ht, min_eq_right]
    nlinarith [sq_abs x, abs_nonneg x]

end SubpolynomialLp

end

end OAI
