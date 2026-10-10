import Tengoku.OpenaiMath.OAI.Analysis.IntegralMeans.InverseDensity

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

attribute [local irreducible] classWeight
attribute [local irreducible] classFun
attribute [local irreducible] rerootClass
attribute [local irreducible] inverseDensity inverseJacDensity

lemma lintegral_Icc_inv {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫⁻ y in Icc a b, ENNReal.ofReal y⁻¹) = ENNReal.ofReal (Real.log (b/a)) := by
  have hc : ContinuousOn (fun y : ℝ => y⁻¹) (Icc a b) :=
    continuousOn_id.inv₀ (fun y hy => ne_of_gt (ha.trans_le hy.1))
  have hi : IntegrableOn (fun y : ℝ => y⁻¹) (Icc a b) volume := hc.integrableOn_Icc
  rw [← ofReal_integral_eq_lintegral_ofReal hi]
  · rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hab,integral_inv_of_pos ha (ha.trans_le hab)]
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    exact inv_nonneg.mpr (ha.le.trans hy.1)

lemma lintegral_transportBox_inv {R a b : ℝ} (hR : 0 ≤ R) (ha : 0 < a) (hab : a ≤ b) :
    (∫⁻ z in transportBox R a b, ENNReal.ofReal z.im⁻¹) =
      ENNReal.ofReal (2*R*Real.log (b/a)) := by
  have he : Complex.measurableEquivRealProd ⁻¹' (Icc (-R) R ×ˢ Icc a b) = transportBox R a b := by
    ext z
    simp only [Complex.measurableEquivRealProd_apply,mem_preimage,mem_prod,mem_Icc,transportBox,mem_ofPred_eq,abs_le]
  have hprod := Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding (fun p : ℝ × ℝ => ENNReal.ofReal p.2⁻¹)
    (Icc (-R) R ×ˢ Icc a b)
  rw [he] at hprod
  change (∫⁻ z in transportBox R a b, ENNReal.ofReal z.im⁻¹) = _ at hprod
  rw [hprod,show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl,
    setLIntegral_prod _ (by fun_prop)]
  dsimp only
  rw [lintegral_Icc_inv ha hab,
    lintegral_const,Measure.restrict_apply_univ,Real.volume_Icc]
  rw [show R - -R = 2*R from by ring,mul_comm,← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*R)]

def rootJac (k σ : ℝ) (g : DiskClass) : ℝ≥0∞ :=
  ENNReal.ofReal (σ * normalizedJacobian (classFun g) k Complex.I)

lemma measurable_rootJac (k σ : ℝ) : Measurable (rootJac k σ) := by
  exact (measurable_const.mul ((continuous_class_normalizedJacobian k).comp
    (continuous_id.prodMk (continuous_const (y := halfOne)))).measurable).ennreal_ofReal

lemma rootJac_reroot (g : DiskClass) {k : ℝ} (hk : 0 < k) (σ : ℝ) (z : halfPlane) :
    rootJac k σ (rerootClass g z) = ENNReal.ofReal (σ * normalizedJacobian (classFun g) k z) := by
  rw [rootJac,class_normalizedJacobian_root g hk z]

def rootWindow (k N : ℝ) : Set DiskClass := {g | (g,halfOne) ∈ transportWindow k N}

def windowTest (k N : ℝ) : DiskClass → ℝ≥0∞ := (rootWindow k N).indicator (rootJac k 1)

def rootException (k : ℝ) : Set DiskClass :=
  {g | ¬GoodPair (classFun g) k (criticalMap (classFun g) k Complex.I)}

def exceptionTest (k : ℝ) : DiskClass → ℝ≥0∞ := (rootException k).indicator (rootJac k 1)

lemma averagedDensity_exception (g : DiskClass) (β : ℝ) {k : ℝ} (hk : 0 < k) (z : halfPlane) :
    averagedDensity β (exceptionTest k) (g,z) =
      transportDensity g β z * ENNReal.ofReal (normalizedJacobian (classFun g) k z) *
        {z : ℂ | z ∈ halfPlane ∧ ¬GoodPair (classFun g) k (criticalMap (classFun g) k z)}.indicator 1 z := by
  rw [averagedDensity_of_mem,exceptionTest]
  have he := class_goodPair_root g hk z
  by_cases hg : GoodPair (classFun g) k (criticalMap (classFun g) k z)
  · rw [indicator_of_notMem (show rerootClass g z ∉ rootException k from fun h => h (he.mpr hg)),
      indicator_of_notMem (show z.val ∉ {z : ℂ | z ∈ halfPlane ∧ ¬GoodPair (classFun g) k (criticalMap (classFun g) k z)} from fun h => h.2 hg)]
    simp
  · rw [indicator_of_mem (show rerootClass g z ∈ rootException k from fun h => hg (he.mp h)),
      rootJac_reroot g hk 1 z,one_mul,indicator_of_mem (show z.val ∈ {z : ℂ | z ∈ halfPlane ∧ ¬GoodPair (classFun g) k (criticalMap (classFun g) k z)} from ⟨z.property,hg⟩)]
    simp

lemma setLIntegral_mul_indicator_one {S T : Set ℂ} (hS : MeasurableSet S) (hST : S ⊆ T)
    (f : ℂ → ℝ≥0∞) :
    (∫⁻ z in T, f z * S.indicator 1 z) = ∫⁻ z in S, f z := by
  have he : (fun z => f z * S.indicator 1 z) = S.indicator f := by
    funext z
    by_cases hz : z ∈ S <;> simp [hz]
  rw [he,setLIntegral_indicator hS,inter_eq_left.mpr hST]

lemma transport_ratio_tendsto (N : ℝ) :
    Tendsto (fun Y : ℝ => (1+N/Y)*(1+2*Real.log N/Real.log Y)) atTop (𝓝 1) := by
  have h1 : Tendsto (fun Y : ℝ => N/Y) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have h2 : Tendsto (fun Y : ℝ => 2*Real.log N/Real.log Y) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  simpa using ((tendsto_const_nhds (x := (1 : ℝ))).add h1).mul ((tendsto_const_nhds (x := (1 : ℝ))).add h2)

lemma transport_box_limit {A B : ℝ≥0∞} (hA : A ≠ ∞) (hB : B ≠ ∞)
    {N : ℝ} (hN : 1 ≤ N)
    (h : ∀ Y : ℝ, 1 < Y →
      ENNReal.ofReal (2*Y^2*Real.log Y)*A ≤
        ENNReal.ofReal (2*(Y^2+N*Y)*Real.log (N^2*Y))*B) : A ≤ B := by
  have hn : 0 < N := zero_lt_one.trans_le hN
  have hineq : ∀ Y : ℝ, 1 < Y → A.toReal ≤ (1+N/Y)*(1+2*Real.log N/Real.log Y)*B.toReal := by
    intro Y hY
    have hy : 0 < Y := zero_lt_one.trans hY
    have hl : 0 < Real.log Y := Real.log_pos hY
    have hny : 1 < N^2*Y := by nlinarith [sq_nonneg (N-1)]
    have hlny : 0 ≤ Real.log (N^2*Y) := Real.log_nonneg hny.le
    have hb := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hB) (h Y hY)
    rw [ENNReal.toReal_mul,ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*Y^2*Real.log Y),
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*(Y^2+N*Y)*Real.log (N^2*Y))] at hb
    have hlog : Real.log (N^2*Y) = 2*Real.log N + Real.log Y := by
      rw [Real.log_mul (by positivity) (ne_of_gt hy),Real.log_pow]
      norm_num
    rw [hlog] at hb
    apply (mul_le_mul_iff_right₀ (show 0 < 2*Y^2*Real.log Y by positivity)).mp
    calc
      _ ≤ 2*(Y^2+N*Y)*(2*Real.log N+Real.log Y)*B.toReal := hb
      _ = _ := by field_simp; ring
  apply (ENNReal.toReal_le_toReal hA hB).mp
  have ht := (transport_ratio_tendsto N).mul_const B.toReal
  simp only [one_mul] at ht
  apply ge_of_tendsto ht
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with Y hY
  exact hineq Y hY

lemma windowTest_le (k N : ℝ) (g : DiskClass) : windowTest k N g ≤ rootJac k 1 g := by
  by_cases hg : g ∈ rootWindow k N <;> simp [windowTest,indicator_of_mem,indicator_of_notMem,hg]

end Brennan

end

end OAI
