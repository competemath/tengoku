import Tengoku.OpenaiMath.OAI.Geometry.KahlerSplitting.GlobalProjections

namespace OAI

section

noncomputable section
open Set Filter Topology
open scoped Manifold unitInterval
namespace UniversalCoverSplitting
namespace FirstGerm
variable {n r s : ℕ} {X Z : ComplexManifold n} {S : HolomorphicSplitting X r s}
    {π : OrdinaryUniversalCover X Z} {o : Z.Carrier}
    {h₁ : Integrable S.projection} {h₂ : Integrable (complementaryProjection S)}

end FirstGerm
end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Filter Topology Metric MeasureTheory
namespace UniversalCoverSplitting
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem hasFDerivAt_compact_parametric_integral
    {U : Set E} (hU : IsOpen U) {K : Set ℝ} (hK : IsCompact K)
    {f : E → ℝ → F} {df : E → ℝ → E →L[ℂ] F}
    (hc : ContinuousOn f.uncurry (U ×ˢ K))
    (hdc : ContinuousOn df.uncurry (U ×ˢ K))
    (hd : ∀ x ∈ U, ∀ t ∈ K, HasFDerivAt (fun y ↦ f y t) (df x t) x)
    {x : E} (hx : x ∈ U) :
    HasFDerivAt (fun y ↦ ∫ t in K, f y t) (∫ t in K, df x t) x := by
  let : NormedSpace ℝ F := NormedSpace.restrictScalars ℝ ℂ F
  obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  have hsub : closedBall x (r/2) ⊆ U := by
    intro y hy
    apply hrU
    exact lt_of_le_of_lt (mem_closedBall.mp hy) (by linarith : r/2 < r)
  have hcomp := (isCompact_closedBall x (r/2)).prod hK
  obtain ⟨C,hC⟩ := hcomp.exists_bound_of_continuousOn
    (hdc.mono (prod_mono hsub Subset.rfl))
  have hc_slice (y : E) (hy : y ∈ U) : ContinuousOn (f y) K :=
    hc.comp (continuous_const.prodMk continuous_id).continuousOn (fun t ht ↦ ⟨hy,ht⟩)
  have hdc_slice (y : E) (hy : y ∈ U) : ContinuousOn (df y) K :=
    hdc.comp (continuous_const.prodMk continuous_id).continuousOn (fun t ht ↦ ⟨hy,ht⟩)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := ball x (r/2)) (bound := fun _ ↦ C) (ball_mem_nhds x (by linarith))
  · filter_upwards [hU.mem_nhds hx] with y hy
    exact (hc_slice y hy).aestronglyMeasurable hK.measurableSet
  · exact (hc_slice x hx).integrableOn_compact hK
  · exact (hdc_slice x hx).aestronglyMeasurable hK.measurableSet
  · filter_upwards [ae_restrict_mem hK.measurableSet] with t ht
    intro y hy
    exact hC (y,t) ⟨ball_subset_closedBall hy,ht⟩
  · exact continuousOn_const.integrableOn_compact hK
  · filter_upwards [ae_restrict_mem hK.measurableSet] with t ht
    intro y hy
    exact hd y (hsub (ball_subset_closedBall hy)) t ht

end UniversalCoverSplitting

noncomputable section
open Set Filter Topology Metric MeasureTheory Complex
open scoped ContDiff
namespace UniversalCoverSplitting
universe u
variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

lemma differentiableOn_directional_cauchy {U V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    {f : E → F} (hf : DifferentiableOn ℂ f U) (e : E) {r : ℝ} (hr : 0 < r)
    (hmap : ∀ z ∈ V, ∀ θ : ℝ, z+circleMap 0 r θ • e ∈ U) :
    DifferentiableOn ℂ (fun z ↦ cderiv r (fun w : ℂ ↦ f (z+w • e)) 0) V := by
  let k : ℝ → ℂ := fun θ ↦ (circleMap 0 r θ * Complex.I) * ((circleMap 0 r θ)^2)⁻¹
  let g : E → ℝ → F := fun z θ ↦ k θ • f (z+circleMap 0 r θ • e)
  let dg : E → ℝ → E →L[ℂ] F := fun z θ ↦ k θ • fderiv ℂ f (z+circleMap 0 r θ • e)
  have hne (θ : ℝ) : circleMap 0 r θ ≠ 0 := circleMap_ne_mem_ball (mem_ball_self hr) θ
  have hk : Continuous k := by
    apply Continuous.mul
    · exact (continuous_circleMap 0 r).mul continuous_const
    · exact ((continuous_circleMap 0 r).pow 2).inv₀ (fun θ ↦ pow_ne_zero 2 (hne θ))
  have hj : Continuous (fun p : E × ℝ ↦ p.1+circleMap 0 r p.2 • e) := by fun_prop
  have hm : MapsTo (fun p : E × ℝ ↦ p.1+circleMap 0 r p.2 • e) (V ×ˢ Icc 0 (2*Real.pi)) U :=
    fun p hp ↦ hmap p.1 hp.1 p.2
  have hdf : ContinuousOn (fderiv ℂ f) U := by
    intro p hp
    apply ContinuousAt.continuousWithinAt
    rw [continuousAt_clm_apply]
    exact continuousAt_directional_fderiv hU hf hp
  have hc : ContinuousOn g.uncurry (V ×ˢ Icc 0 (2*Real.pi)) :=
    (hk.comp continuous_snd).continuousOn.smul (hf.continuousOn.comp hj.continuousOn hm)
  have hdc : ContinuousOn dg.uncurry (V ×ˢ Icc 0 (2*Real.pi)) :=
    (hk.comp continuous_snd).continuousOn.smul (hdf.comp hj.continuousOn hm)
  have hd (z : E) (hz : z ∈ V) (θ : ℝ) : HasFDerivAt (fun y ↦ g y θ) (dg z θ) z := by
    have H := ((hf.differentiableAt (hU.mem_nhds (hmap z hz θ))).hasFDerivAt.comp z
      ((hasFDerivAt_id (𝕜 := ℂ) z).add_const (circleMap 0 r θ • e))).const_smul (k θ)
    convert H using 1 <;> simp only [g, dg, ContinuousLinearMap.comp_id, Function.comp_def, id_eq]
    rfl
  have heq : (fun z ↦ cderiv r (fun w : ℂ ↦ f (z+w • e)) 0)=
      (fun z ↦ ((2*Real.pi*Complex.I : ℂ)⁻¹) • ∫ θ in Icc 0 (2*Real.pi), g z θ) := by
    funext z
    rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2*Real.pi)]
    simp only [cderiv,circleIntegral,deriv_circleMap,g,k,circleMap,zero_add,sub_zero,smul_smul]
  rw [heq]
  intro z hz
  exact ((hasFDerivAt_compact_parametric_integral hV isCompact_Icc hc hdc
    (fun y hy θ _ ↦ hd y hy θ) hz).const_smul _).differentiableAt.differentiableWithinAt

lemma differentiableAt_directional_fderiv {U : Set E} (hU : IsOpen U)
    {f : E → F} (hf : DifferentiableOn ℂ f U) {p : E} (hp : p ∈ U) (e : E) :
    DifferentiableAt ℂ (fun z ↦ fderiv ℂ f z e) p := by
  obtain ⟨d,hd,hdU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hp)
  let r : ℝ := d/(2*(‖e‖+1))
  have he : 0 < ‖e‖+1 := by positivity
  have hr : 0 < r := div_pos hd (by positivity)
  have hre : r*‖e‖ ≤ d/2 := by
    have hprod : r*(‖e‖+1)=d/2 := by dsimp [r]; field_simp
    nlinarith
  let V := ball p (d/2)
  have hV : V ∈ 𝓝 p := ball_mem_nhds _ (by linarith)
  have hmap (z : E) (hz : z ∈ V) (w : ℂ) (hw : w ∈ closedBall 0 r) : z+w • e ∈ U := by
    apply hdU
    rw [mem_ball,dist_eq_norm] at hz ⊢
    rw [mem_closedBall,dist_zero_right] at hw
    calc ‖z+w • e-p‖ = ‖(z-p)+w • e‖ := by congr 1; abel
         _ ≤ ‖z-p‖+‖w • e‖ := norm_add_le _ _
         _ = ‖z-p‖+‖w‖*‖e‖ := by rw [norm_smul]
         _ ≤ ‖z-p‖+r*‖e‖ := by gcongr
         _ < d := by linarith
  have hdiff := differentiableOn_directional_cauchy hU isOpen_ball hf e hr
    (fun z hz θ ↦ hmap z hz _ (circleMap_mem_closedBall _ hr.le _))
  apply (hdiff.differentiableAt hV).congr_of_eventuallyEq
  filter_upwards [hV] with z hz
  let W := (fun w : ℂ ↦ z+w • e) ⁻¹' U
  have hW : IsOpen W := hU.preimage (by fun_prop)
  have hline : DifferentiableOn ℂ (fun w : ℂ ↦ f (z+w • e)) W :=
    hf.comp (by fun_prop) (fun _ hw ↦ hw)
  rw [cderiv_eq_deriv hW hline hr (hmap z hz)]
  have hzU : z ∈ U := by simpa using hmap z hz 0 (mem_closedBall_self hr.le)
  have hdline : HasDerivAt (fun w : ℂ ↦ z+w • e) e 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const e).const_add z
  have H := (show HasFDerivAt f (fderiv ℂ f z) (z+(0:ℂ) • e) from by
    simpa using (hf.differentiableAt (hU.mem_nhds hzU)).hasFDerivAt).comp_hasDerivAt 0 hdline
  exact H.deriv.symm

lemma finite_holomorphic_fderiv {U : Set E} (hU : IsOpen U)
    {f : E → F} (hf : DifferentiableOn ℂ f U) : DifferentiableOn ℂ (fderiv ℂ f) U := by
  classical
  let b := Module.finBasis ℂ E
  let c := fun i ↦ (b.coord i).toContinuousLinearMap
  have heq : fderiv ℂ f=(fun z ↦ ∑ i, (c i).smulRight (fderiv ℂ f z (b i))) := by
    funext z
    ext v
    simp only [sum_apply,ContinuousLinearMap.smulRight_apply]
    change fderiv ℂ f z v=∑ i,b.repr v i • fderiv ℂ f z (b i)
    conv_lhs => rw [←b.sum_repr v]
    simp only [map_sum, map_smul]
  rw [heq]
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.fun_sum
  intro i _
  exact ((ContinuousLinearMap.smulRightL ℂ E F) (c i)).differentiableAt.comp z
    (differentiableAt_directional_fderiv hU hf hz (b i))

lemma finite_holomorphic_contDiffOn_nat (k : ℕ) {U : Set E} (hU : IsOpen U)
    {f : E → F} (hf : DifferentiableOn ℂ f U) : ContDiffOn ℂ k f U := by
  induction k generalizing F with
  | zero => exact contDiffOn_zero.mpr hf.continuousOn
  | succ k ih =>
    rw [Nat.cast_add,Nat.cast_one,contDiffOn_succ_iff_fderiv_of_isOpen hU]
    exact ⟨hf,by simp,ih (finite_holomorphic_fderiv hU hf)⟩

lemma finite_holomorphic_contDiffOn {U : Set E} (hU : IsOpen U)
    {f : E → F} (hf : DifferentiableOn ℂ f U) : ContDiffOn ℂ ∞ f U := by
  rw [contDiffOn_infty]
  exact fun k ↦ finite_holomorphic_contDiffOn_nat k hU hf

end UniversalCoverSplitting
end
end
end

end OAI
