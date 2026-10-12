import Tengoku.OpenaiMath.OAI.Probability.GaussianReplacement.Tilt

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory

lemma sphere_moment_log_bound {d : ℕ} (hd : 1 ≤ d) :
    Real.log (1+(momentConstant 9 d (3*4^d) (3*4^d)).toReal) ≤ 20*d := by
  have hB : (0:ℝ) < 3*4^d := by positivity
  have he : (momentConstant 9 d (3*4^d) (3*4^d)).toReal =
      Real.exp (9*d)*(3*4^d) := by
    simp [momentConstant,ENNReal.toReal_ofReal (by positivity :
      0 ≤ Real.exp (9*d)*(3*4^d))]
  rw [he]
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hpow : (1:ℝ) ≤ 4^d := one_le_pow₀ (by norm_num)
  have hexp : (1:ℝ) ≤ Real.exp (9*d) := Real.one_le_exp_iff.mpr (by positivity)
  have ht : 1 ≤ Real.exp (9*d)*(3*4^d) := by nlinarith
  have hl := Real.log_le_log (by positivity : 0<1+Real.exp (9*d)*(3*4^d))
    (show 1+Real.exp (9*d)*(3*4^d) ≤ 2*(Real.exp (9*d)*(3*4^d)) by linarith)
  rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by positivity),
    Real.log_mul (Real.exp_ne_zero _) hB.ne',Real.log_exp,
    Real.log_mul (by norm_num : (3:ℝ) ≠ 0) (by positivity),Real.log_pow] at hl
  have h2 := Real.log_le_self (by norm_num : (0:ℝ) ≤ 2)
  have h3 := Real.log_le_self (by norm_num : (0:ℝ) ≤ 3)
  have h4 := Real.log_le_self (by norm_num : (0:ℝ) ≤ 4)
  nlinarith

def conditionalReferenceKL {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (P : Measure (A×B)) (ν : Measure B) : ℝ≥0∞ := klDiv P (P.fst.prod ν)

lemma conditionalReferenceKL_add_condition {C A B : Type*} [MeasurableSpace C]
    [MeasurableSpace A] [MeasurableSpace B] [StandardBorelSpace A] [StandardBorelSpace B]
    [Nonempty A] [Nonempty B]
    (P : Measure (C×(A×B))) [IsProbabilityMeasure P]
    (π : Measure B) [IsProbabilityMeasure π] :
    conditionalReferenceKL (P.map MeasurableEquiv.prodAssoc.symm) π =
      conditionalReferenceKL (P.map (Prod.map id Prod.snd)) π +
      conditionalMutualInformation P := by
  let μ := P.fst
  let κ := P.condKernel
  have hP : μ ⊗ₘ κ = P := P.disintegrate P.condKernel
  have hfst : (P.map MeasurableEquiv.prodAssoc.symm).fst = μ ⊗ₘ κ.fst := by
    rw [←hP]
    exact fst_map_assoc_compProd μ κ
  have hsnd : P.map (Prod.map id Prod.snd) = μ ⊗ₘ κ.snd := by
    rw [Kernel.snd_eq,Measure.compProd_map measurable_snd,hP]
  have href : (μ ⊗ₘ (κ.fst ×ₖ Kernel.const C π)).map MeasurableEquiv.prodAssoc.symm =
      (μ ⊗ₘ κ.fst).prod π := by
    rw [compProd_prod_assoc]
    have he : (Kernel.const C π).comap Prod.fst measurable_fst = Kernel.const (C×A) π := rfl
    rw [he,Measure.compProd_const]
  have h := conditionalKL_chain μ κ π
  rw [hP] at h
  have hc := conditionalMutualInformation_compProd μ κ
  simp only [hP] at hc
  unfold conditionalReferenceKL
  rw [hfst,←href,klDiv_map_equiv,h,←hc,hsnd,Measure.fst_compProd]

lemma conditionalMutualInformation_symm {C A B : Type*} [MeasurableSpace C]
    [MeasurableSpace A] [MeasurableSpace B] [StandardBorelSpace A] [StandardBorelSpace B]
    [Nonempty A] [Nonempty B]
    (P : Measure (C×(A×B))) [IsProbabilityMeasure P] :
    conditionalMutualInformation (P.map (Prod.map id Prod.swap)) =
      conditionalMutualInformation P := by
  let μ := P.fst
  let κ := P.condKernel
  have hP : μ ⊗ₘ κ = P := P.disintegrate P.condKernel
  have hmap : P.map (Prod.map id Prod.swap) = μ ⊗ₘ κ.map Prod.swap := by
    rw [Measure.compProd_map measurable_swap,hP]
  have hfst : (κ.map Prod.swap).fst = κ.snd := by
    rw [Kernel.fst_eq,Kernel.snd_eq,←Kernel.map_comp_right _ measurable_swap measurable_fst]
    rfl
  have hsnd : (κ.map Prod.swap).snd = κ.fst := by
    rw [Kernel.fst_eq,Kernel.snd_eq,←Kernel.map_comp_right _ measurable_swap measurable_snd]
    rfl
  have href : μ ⊗ₘ (κ.snd ×ₖ κ.fst) =
      (μ ⊗ₘ (κ.fst ×ₖ κ.snd)).map (Prod.map id Prod.swap) := by
    rw [←Measure.compProd_map measurable_swap,Kernel.map_prod_swap]
  have : IsMarkovKernel (κ.map Prod.swap) := Kernel.IsMarkovKernel.map κ measurable_swap
  have hc := conditionalMutualInformation_compProd μ (κ.map Prod.swap)
  simp only [hfst,hsnd,href,Measure.compProd_map measurable_swap] at hc
  have he := klDiv_map_equiv (μ ⊗ₘ κ) (μ ⊗ₘ (κ.fst ×ₖ κ.snd))
    ((MeasurableEquiv.refl C).prodCongr MeasurableEquiv.prodComm)
  change klDiv ((μ ⊗ₘ κ).map (Prod.map id Prod.swap))
    ((μ ⊗ₘ (κ.fst ×ₖ κ.snd)).map (Prod.map id Prod.swap)) = _ at he
  rw [he,←conditionalMutualInformation_compProd μ κ] at hc
  simpa only [hP] using hc

def gaussianLabels (k : ℕ) : Measure (Fin k → ℝ) := Measure.pi (fun _ => gaussianReal 0 1)

lemma gaussianLabels_density (k : ℕ) :
    (volume : Measure (Fin k → ℝ)).withDensity
      (fun y => ENNReal.ofReal (gaussianProductPDF 1 0 y)) = gaussianLabels k := by
  symm
  apply Measure.pi_eq
  intro t ht
  rw [withDensity_apply _ (MeasurableSet.univ_pi ht)]
  simp only [gaussianProductPDF,radiusVariance,one_pow,Pi.zero_apply]
  change (∫⁻ y in Set.univ.pi t, ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (y i))) = _
  rw [←ofReal_integral_eq_lintegral_ofReal]
  · change ENNReal.ofReal (∫ y, ∏ i, gaussianPDFReal 0 1 (y i)
        ∂(Measure.pi (fun _ : Fin k => (volume : Measure ℝ))).restrict (Set.univ.pi t)) = _
    rw [Measure.restrict_pi_pi,integral_fintype_prod_eq_prod,
      ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (fun _ => (gaussianPDFReal_pos 0 1 _ (by norm_num)).le))]
    congr 1
    funext i
    rw [gaussianReal_apply 0 (by norm_num : (1:ℝ≥0) ≠ 0)]
    exact ofReal_integral_eq_lintegral_ofReal (integrable_gaussianPDFReal 0 1).integrableOn
      (ae_of_all _ (fun x => (gaussianPDFReal_pos 0 1 x (by norm_num)).le))
  · exact (Integrable.fintype_prod (fun _ : Fin k => integrable_gaussianPDFReal 0 1)).integrableOn
  · exact ae_of_all _ (fun y => Finset.prod_nonneg (fun i _ => (gaussianPDFReal_pos 0 1 (y i) (by norm_num)).le))

lemma log_gaussianLabelsPDF {k : ℕ} (y : Fin k → ℝ) :
    Real.log (gaussianProductPDF 1 0 y) = -(k:ℝ)*Real.log (normalizer 1) -
      (∑ i, (y i)^2)/2 := by
  simpa using log_gaussianProductPDF (k:=k) (show (0:ℝ)<1 by norm_num) (0:Fin k→ℝ) y

lemma projectionSquare_sphere_joint_integrable {d k : ℕ}
    (ρ : Measure (Sphere d)) [IsProbabilityMeasure ρ] :
    Integrable (fun z : Rows k d × Sphere d => projectionSquare z.1 (z.2:Vector d))
      ((gaussianRows k d).prod ρ) := by
  have hm : Measurable (fun z : Rows k d × Sphere d => projectionSquare z.1 (z.2:Vector d)) := by
    unfold projectionSquare label
    fun_prop
  apply (integrable_prod_iff' hm.aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ (fun s => projectionSquare_integrable (s:Vector d)),?_⟩
  have he : (fun s : Sphere d => ∫ G, ‖projectionSquare G (s:Vector d)‖ ∂gaussianRows k d) =
      fun _ => (k:ℝ) := by
    funext s
    simp_rw [Real.norm_eq_abs,abs_of_nonneg (projectionSquare_nonneg _ _)]
    rw [projectionSquare_integral,norm_eq_of_mem_sphere s]
    simp
  rw [he]
  exact integrable_const _

lemma projectionSquare_sphere_joint_integral {d k : ℕ}
    (ρ : Measure (Sphere d)) [IsProbabilityMeasure ρ] :
    (∫ z : Rows k d × Sphere d, projectionSquare z.1 (z.2:Vector d)
      ∂(gaussianRows k d).prod ρ) = k := by
  rw [integral_prod_symm _ (projectionSquare_sphere_joint_integrable ρ)]
  simp only [projectionSquare_integral,norm_eq_of_mem_sphere,
    one_pow,mul_one,integral_const,probReal_univ,one_smul]

lemma weighted_log_integral {T : Type*} [MeasurableSpace T]
    (μ : Measure T) (w g : T → ℝ)
    (hw : ∀ t, 0 < w t) (hg : ∀ t, 0 < g t)
    (hwi : Integrable w μ) (hgi : Integrable g μ)
    (hli : Integrable (fun t => w t * (Real.log (g t) - Real.log (w t))) μ)
    (hA : 0 < ∫ t, w t ∂μ) (hM : 0 < ∫ t, g t ∂μ) :
    (∫ t, w t * (Real.log (g t) - Real.log (w t)) ∂μ) ≤
      (∫ t, w t ∂μ) * (Real.log (∫ t, g t ∂μ) - Real.log (∫ t, w t ∂μ)) := by
  let A := ∫ t, w t ∂μ
  let M := ∫ t, g t ∂μ
  change 0 < A at hA
  change 0 < M at hM
  have hp (t : T) : w t * (Real.log (g t) - Real.log (w t)) ≤
      w t * (Real.log M - Real.log A) + (A/M)*g t - w t := by
    have hh := Real.log_le_sub_one_of_pos (div_pos (div_pos (hg t) (hw t)) (div_pos hM hA))
    rw [Real.log_div (div_ne_zero (hg t).ne' (hw t).ne') (div_ne_zero hM.ne' hA.ne'),
      Real.log_div (hg t).ne' (hw t).ne',Real.log_div hM.ne' hA.ne'] at hh
    have hh' := mul_le_mul_of_nonneg_left hh (hw t).le
    have he : w t * ((g t / w t) / (M / A) - 1) = (A/M)*g t - w t := by
      field_simp [hA.ne',hM.ne',(hw t).ne']
    rw [he] at hh'
    nlinarith
  have hi : Integrable (fun t => w t*(Real.log M-Real.log A)+(A/M)*g t-w t) μ :=
    ((hwi.mul_const _).add (hgi.const_mul (A/M))).sub hwi
  have hb := integral_mono hli hi hp
  have hv : (∫ t, w t * (Real.log M-Real.log A) + (A/M)*g t - w t ∂μ) =
      A * (Real.log M-Real.log A) + (A/M)*M - A := by
    calc
      _ = (∫ t, w t * (Real.log M-Real.log A) + (A/M)*g t ∂μ) - A :=
        integral_sub ((hwi.mul_const _).add (hgi.const_mul _)) hwi
      _ = A * (Real.log M-Real.log A) + (A/M)*M - A := by
        rw [integral_add (hwi.mul_const (Real.log M-Real.log A)) (hgi.const_mul (A/M))]
        simp only [integral_mul_const, integral_const_mul, A, M]
  rw [hv,div_mul_cancel₀ _ hM.ne'] at hb
  linarith

def regularizedReciprocal {d : ℕ} (e : ℝ) (s t : Sphere d) : ℝ :=
  (max (dist s t) e)⁻¹

def regularizedScale {d : ℕ} (μ : Measure (Sphere d)) (e : ℝ) (s : Sphere d) : ℝ :=
  ∫ t, regularizedReciprocal e s t ∂μ

lemma sphere_subtype_dist_le_two {d : ℕ} (s t : Sphere d) : dist s t ≤ 2 := by
  simpa only [Subtype.dist_eq,dist_eq_norm,norm_eq_of_mem_sphere s,
    norm_eq_of_mem_sphere t,one_add_one_eq_two] using norm_sub_le (s:Vector d) (t:Vector d)

lemma regularizedReciprocal_pos {d : ℕ} {e : ℝ} (he : 0 < e) (s t : Sphere d) :
    0 < regularizedReciprocal e s t := inv_pos.mpr (he.trans_le (le_max_right _ _))

lemma regularizedReciprocal_bounds {d : ℕ} {e : ℝ} (he : 0 < e) (he1 : e ≤ 1)
    (s t : Sphere d) : 1/2 ≤ regularizedReciprocal e s t ∧ regularizedReciprocal e s t ≤ e⁻¹ := by
  have hmax : 0 < max (dist s t) e := he.trans_le (le_max_right _ _)
  constructor
  · simp only [one_div,regularizedReciprocal]
    change (2:ℝ)⁻¹ ≤ (max (dist s t) e)⁻¹
    exact (inv_le_inv₀ (by norm_num) hmax).mpr (max_le (sphere_subtype_dist_le_two s t) (by linarith))
  · exact (inv_le_inv₀ hmax he).mpr (le_max_right _ _)

lemma integrable_regularizedReciprocal {d : ℕ} (μ : Measure (Sphere d)) [IsProbabilityMeasure μ]
    {e : ℝ} (he : 0 < e) (s : Sphere d) : Integrable (regularizedReciprocal e s) μ := by
  apply (integrable_const (e⁻¹)).mono' (by unfold regularizedReciprocal; fun_prop)
  apply ae_of_all
  intro t
  rw [Real.norm_eq_abs,abs_of_pos (regularizedReciprocal_pos he s t)]
  exact (inv_le_inv₀ (he.trans_le (le_max_right _ _)) he).mpr (le_max_right _ _)

lemma regularizedScale_bounds {d : ℕ} (μ : Measure (Sphere d)) [IsProbabilityMeasure μ]
    {e : ℝ} (he : 0 < e) (he1 : e ≤ 1) (s : Sphere d) :
    1/2 ≤ regularizedScale μ e s ∧ regularizedScale μ e s ≤ e⁻¹ := by
  have hi := integrable_regularizedReciprocal μ he s
  constructor
  · simpa [regularizedScale] using integral_mono (integrable_const (1/2:ℝ)) hi
      (fun t => (regularizedReciprocal_bounds he he1 s t).1)
  · simpa [regularizedScale] using integral_mono hi (integrable_const (e⁻¹))
      (fun t => (regularizedReciprocal_bounds he he1 s t).2)

lemma log_regularizedReciprocal {d : ℕ} (e : ℝ) (s t : Sphere d) :
    Real.log (regularizedReciprocal e s t) = -Real.log (max (dist s t) e) := Real.log_inv _

end CurrentProjection

end

end OAI
