import Tengoku.OpenaiMath.OAI.Probability.GaussianReplacement.FreshRows

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory

def dependentMapKernel {A B D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace D] (κ : Kernel A B) (f : A×B → D) : Kernel A D :=
  (Kernel.id ×ₖ κ).map f

lemma dependentMapKernel_markov {A B D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace D] (κ : Kernel A B) [IsMarkovKernel κ] (f : A×B → D)
    (hf : Measurable f) : IsMarkovKernel (dependentMapKernel κ f) :=
  Kernel.IsMarkovKernel.map _ hf

lemma dependentMapKernel_apply {A B D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace D] (κ : Kernel A B) [IsSFiniteKernel κ] (f : A×B → D)
    (hf : Measurable f) (a : A) : dependentMapKernel κ f a = (κ a).map (fun b => f (a,b)) := by
  rw [dependentMapKernel,Kernel.map_apply _ hf,Kernel.prod_apply,Kernel.id_apply,
    Measure.dirac_prod,Measure.map_map hf (measurable_prodMk_left (x:=a))]
  rfl

lemma compProd_dependentMapKernel {A B D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace D] (μ : Measure A) [SFinite μ]
    (κ : Kernel A B) [IsSFiniteKernel κ] (f : A×B → D) (hf : Measurable f) :
    μ ⊗ₘ dependentMapKernel κ f = (μ ⊗ₘ κ).map (fun z => (z.1,f z)) := by
  have : IsSFiniteKernel (dependentMapKernel κ f) := by unfold dependentMapKernel; infer_instance
  ext t ht
  rw [Measure.compProd_apply ht,Measure.map_apply (measurable_fst.prodMk hf) ht,
    Measure.compProd_apply (ht.preimage (measurable_fst.prodMk hf))]
  apply lintegral_congr
  intro a
  rw [dependentMapKernel_apply κ f hf a,
    Measure.map_apply (show Measurable (fun b => f (a,b)) from hf.comp measurable_prodMk_left)
      (ht.preimage (measurable_prodMk_left (x:=a)))]
  rfl

lemma compProd_conditional_prod_swap {C S X : Type*} [MeasurableSpace C]
    [MeasurableSpace S] [MeasurableSpace X] (μ : Measure C) [SFinite μ]
    (κ : Kernel C S) [IsSFiniteKernel κ] (γ : Measure X) [SFinite γ] :
    ((μ.prod γ) ⊗ₘ κ.comap Prod.fst measurable_fst).map
      (fun z : (C×X)×S => ((z.1.1,z.2),z.1.2)) = (μ ⊗ₘ κ).prod γ := by
  have h1 := compProd_prod_assoc μ (Kernel.const C γ) κ
  rw [Measure.compProd_const] at h1
  rw [←h1,Measure.map_map (by fun_prop) MeasurableEquiv.prodAssoc.symm.measurable]
  have h2 := compProd_prod_assoc μ κ (Kernel.const C γ)
  have hconst : (Kernel.const C γ).comap (Prod.fst : C×S → C) measurable_fst = Kernel.const _ γ := rfl
  rw [hconst,Measure.compProd_const] at h2
  rw [←h2,←Kernel.map_prod_swap (Kernel.const C γ) κ,Measure.compProd_map measurable_swap,
    Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable (measurable_id.prodMap measurable_swap)]
  rfl

def scalarProjectionKernel {d : ℕ} {C : Type*} [MeasurableSpace C]
    (κ : Kernel C (Sphere d)) : Kernel (C×Vector d) ℝ :=
  dependentMapKernel (κ.comap Prod.fst measurable_fst)
    (fun z : (C×Vector d)×Sphere d => ⟪(z.2:Vector d),z.1.2⟫)

instance scalarProjectionKernel_markov {d : ℕ} {C : Type*} [MeasurableSpace C]
    (κ : Kernel C (Sphere d)) [IsMarkovKernel κ] : IsMarkovKernel (scalarProjectionKernel κ) :=
  dependentMapKernel_markov _ _ (by fun_prop)

lemma scalarProjectionKernel_apply {d : ℕ} {C : Type*} [MeasurableSpace C]
    (κ : Kernel C (Sphere d)) [IsSFiniteKernel κ] (z : C×Vector d) :
    scalarProjectionKernel κ z = (κ z.1).map (fun s : Sphere d => ⟪(s:Vector d),z.2⟫) :=
  dependentMapKernel_apply _ _ (by fun_prop) _

def scalarObservation {d : ℕ} {C : Type*} (z : (C×Sphere d)×Vector d) : (C×Vector d)×ℝ :=
  ((z.1.1,z.2),⟪(z.1.2:Vector d),z.2⟫)

lemma measurable_scalarObservation {d : ℕ} {C : Type*} [MeasurableSpace C] :
    Measurable (scalarObservation (d:=d) (C:=C)) := by unfold scalarObservation; fun_prop

def scalarObservationLaw {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) : Measure ((C×Vector d)×ℝ) :=
  (Γ.prod (stdGaussian (Vector d))).map scalarObservation

instance scalarObservationLaw_probability {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] : IsProbabilityMeasure (scalarObservationLaw Γ) := by
  exact (Measure.isProbabilityMeasure_map_iff
    measurable_scalarObservation.aemeasurable).mpr inferInstance

lemma scalarObservationLaw_disintegrate {d : ℕ} [Nonempty (Sphere d)]
    {C : Type*} [MeasurableSpace C] (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] :
    (Γ.fst.prod (stdGaussian (Vector d))) ⊗ₘ scalarProjectionKernel Γ.condKernel = scalarObservationLaw Γ := by
  rw [scalarProjectionKernel,compProd_dependentMapKernel _ _ _ (by fun_prop),scalarObservationLaw]
  have he := compProd_conditional_prod_swap Γ.fst Γ.condKernel (stdGaussian (Vector d))
  rw [Γ.disintegrate Γ.condKernel] at he
  rw [←he,Measure.map_map measurable_scalarObservation (by fun_prop)]
  rfl

lemma scalarObservationLaw_fst {d : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] :
    (scalarObservationLaw Γ).fst = Γ.fst.prod (stdGaussian (Vector d)) := by
  rw [←scalarObservationLaw_disintegrate Γ,Measure.fst_compProd]

lemma scalarCube_projection {d : ℕ} {C : Type*} [MeasurableSpace C]
    (κ : Kernel C (Sphere d)) [IsSFiniteKernel κ] (z : C×Vector d) (s : Sphere d) (δ : ℝ) :
    scalarCube (scalarProjectionKernel κ z) ⟪(s:Vector d),z.2⟫ δ =
      ∫⁻ t : Sphere d, cubeKernel δ ⟪(t:Vector d)-(s:Vector d),z.2⟫ ∂κ z.1 := by
  rw [scalarCube,scalarProjectionKernel_apply,lintegral_map
    (f:=fun t : ℝ => cubeKernel δ (t-⟪(s:Vector d),z.2⟫))
    ((measurable_cubeKernel δ).comp (by fun_prop)) (by fun_prop)]
  simp only [inner_sub_left]

lemma scalarObservationLaw_kernel_ac {d : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ]
    (h : conditionalReferenceKL (scalarObservationLaw Γ) (gaussianReal 0 1) ≠ ∞) :
    ∀ᵐ a ∂Γ.fst.prod (stdGaussian (Vector d)), scalarProjectionKernel Γ.condKernel a ≪ volume := by
  have hac := (klDiv_ne_top_iff.mp h).1
  have hgv : gaussianReal 0 1 ≪ (volume : Measure ℝ) := by
    rw [gaussianReal_of_var_ne_zero _ (by norm_num)]
    exact withDensity_absolutelyContinuous _ _
  change scalarObservationLaw Γ ≪ (scalarObservationLaw Γ).fst.prod (gaussianReal 0 1) at hac
  have hh : (Γ.fst.prod (stdGaussian (Vector d))) ⊗ₘ scalarProjectionKernel Γ.condKernel ≪
      (Γ.fst.prod (stdGaussian (Vector d))) ⊗ₘ Kernel.const _ (gaussianReal 0 1) := by
    rw [Measure.compProd_const,scalarObservationLaw_disintegrate Γ,←scalarObservationLaw_fst Γ]
    exact hac
  exact hh.kernel_of_compProd.mono (fun a ha => ha.trans hgv)

lemma scalarObservationLaw_density {d : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ]
    (h : conditionalReferenceKL (scalarObservationLaw Γ) (gaussianReal 0 1) ≠ ∞) :
    ((scalarObservationLaw Γ).fst.prod volume).withDensity
      (fun z => scalarDensity (scalarProjectionKernel Γ.condKernel z.1) z.2) = scalarObservationLaw Γ := by
  rw [scalarObservationLaw_fst,←scalarObservationLaw_disintegrate Γ]
  exact kernel_scalarDensity_withDensity _ _ (scalarObservationLaw_kernel_ac Γ h)

lemma scalarObservationLaw_ae_limit {d : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ]
    (h : conditionalReferenceKL (scalarObservationLaw Γ) (gaussianReal 0 1) ≠ ∞) :
    ∀ᵐ z ∂scalarObservationLaw Γ, Tendsto
      (fun n : ℕ => scalarCube (scalarProjectionKernel Γ.condKernel z.1) z.2 (1/(n:ℝ)))
      atTop (𝓝 (scalarDensity (scalarProjectionKernel Γ.condKernel z.1) z.2)) := by
  have ha : scalarObservationLaw Γ ≪ (scalarObservationLaw Γ).fst.prod volume := by
    have hh := withDensity_absolutelyContinuous
      ((scalarObservationLaw Γ).fst.prod volume)
      (fun z => scalarDensity (scalarProjectionKernel Γ.condKernel z.1) z.2)
    rwa [scalarObservationLaw_density Γ h] at hh
  exact ha.ae_le (kernel_scalarDensity_ae_limit (scalarObservationLaw Γ).fst
    (scalarProjectionKernel Γ.condKernel))

lemma prod_map_swap23 {A B D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace D] (μ : Measure A) (ν : Measure B) (π : Measure D)
    [SFinite μ] [SFinite ν] [SFinite π] :
    ((μ.prod ν).prod π).map (fun z : (A×B)×D => ((z.1.1,z.2),z.1.2)) = (μ.prod π).prod ν := by
  have h : ((μ.prod ν).prod π).map (fun z : (A×B)×D => ((z.1.1,z.2),z.1.2)) =
      (((μ.prod ν).prod π).map MeasurableEquiv.prodAssoc).map
        ((MeasurableEquiv.prodAssoc : (A×D)×B ≃ᵐ A×(D×B)).symm ∘ Prod.map id Prod.swap) := by
    rw [Measure.map_map (by fun_prop) MeasurableEquiv.prodAssoc.measurable]
    rfl
  rw [h,Measure.prodAssoc_prod,←Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable
    (measurable_id.prodMap measurable_swap),←Measure.map_prod_map _ _ measurable_id measurable_swap,
    Measure.map_id,Measure.prod_swap,←Measure.prodAssoc_prod,MeasurableEquiv.map_symm_map]

def residualLabelObservation {d r : ℕ} {C : Type*}
    (w : ((C×Sphere d)×Vector d)×Rows r d) : ((C×(Rows r d×(Fin r→ℝ)))×Vector d)×ℝ :=
  (((w.1.1.1,(w.2,label w.2 (w.1.1.2:Vector d))),w.1.2),⟪(w.1.1.2:Vector d),w.1.2⟫)

lemma measurable_residualLabelObservation {d r : ℕ} {C : Type*} [MeasurableSpace C] :
    Measurable (residualLabelObservation (d:=d) (r:=r) (C:=C)) := by
  unfold residualLabelObservation label
  fun_prop

def residualLabelLaw {d : ℕ} {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) (r : ℕ) :
    Measure (((C×(Rows r d×(Fin r→ℝ)))×Vector d)×ℝ) :=
  (P.prod (gaussianRows r d)).map residualLabelObservation

instance residualLabelLaw_probability {d : ℕ} {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) [IsProbabilityMeasure P] (r : ℕ) :
    IsProbabilityMeasure (residualLabelLaw P r) := by
  exact (Measure.isProbabilityMeasure_map_iff
    measurable_residualLabelObservation.aemeasurable).mpr inferInstance

lemma residualLabelLaw_fresh {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] (r : ℕ) :
    residualLabelLaw (Γ.prod (stdGaussian (Vector d))) r =
      scalarObservationLaw (residualLaw Γ r) := by
  unfold scalarObservationLaw residualLaw
  have he : ((Γ.prod (gaussianRows r d)).map residualObservation).prod (stdGaussian (Vector d)) =
      ((Γ.prod (gaussianRows r d)).prod (stdGaussian (Vector d))).map
        (Prod.map residualObservation id) := by
    simpa only [Measure.map_id] using Measure.map_prod_map
      (Γ.prod (gaussianRows r d)) (stdGaussian (Vector d)) measurable_residualObservation measurable_id
  rw [he,←prod_map_swap23 Γ (stdGaussian (Vector d)) (gaussianRows r d),
    Measure.map_map (measurable_residualObservation.prodMap measurable_id) (by fun_prop),
    Measure.map_map measurable_scalarObservation
      ((measurable_residualObservation.prodMap measurable_id).comp (by fun_prop))]
  rfl

lemma klDiv_prod_same {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ ν : Measure A) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (π : Measure B) [IsProbabilityMeasure π] : klDiv (μ.prod π) (ν.prod π) = klDiv μ ν := by
  rw [←Measure.compProd_const,←Measure.compProd_const]
  exact klDiv_compProd_left _ _ _

lemma residualLabelLaw_kl_le {d : ℕ} {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) [IsProbabilityMeasure P] (r : ℕ) :
    klDiv (residualLabelLaw P r) (scalarObservationLaw (residualLaw P.fst r)) ≤
      klDiv P (P.fst.prod (stdGaussian (Vector d))) := by
  rw [←residualLabelLaw_fresh P.fst r]
  exact (klDiv_map_le _ _ measurable_residualLabelObservation).trans_eq
    (klDiv_prod_same _ _ _)

def residualExact {d r : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ]
    (w : ((C×Sphere d)×Vector d)×Rows r d) : ℝ≥0∞ :=
  scalarDensity (scalarProjectionKernel (residualLaw Γ r).condKernel
    (residualLabelObservation w).1) (residualLabelObservation w).2 /
    residualScale Γ w.1.1 w.2

lemma measurable_residualExact {d r : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] :
    Measurable (residualExact (r:=r) Γ) := by
  exact ((measurable_scalarDensity (scalarProjectionKernel (residualLaw Γ r).condKernel)).comp
    measurable_residualLabelObservation).div ((measurable_residualScale Γ).comp
      (measurable_fst.fst.prodMk measurable_snd))

lemma residualExact_finite {d r : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ]
    (w : ((C×Sphere d)×Vector d)×Rows r d) : residualExact Γ w ≠ ∞ := by
  exact ENNReal.div_ne_top (scalarDensity_finite _ _)
    (ne_of_gt (lt_of_lt_of_le (by norm_num) (residualScale_lower Γ w.1.1 w.2)))

lemma residualCube_ae_limit_actual {d r : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) [IsProbabilityMeasure P]
    (hKL : klDiv P (P.fst.prod (stdGaussian (Vector d))) ≠ ∞)
    (href : conditionalReferenceKL (scalarObservationLaw (residualLaw P.fst r)) (gaussianReal 0 1) ≠ ∞) :
    ∀ᵐ w ∂P.prod (gaussianRows r d), Tendsto
      (fun n : ℕ => residualCube P.fst (1/(n:ℝ)) w) atTop (𝓝 (residualExact P.fst w)) := by
  have hk := ne_top_of_le_ne_top hKL (residualLabelLaw_kl_le P r)
  have ha := (klDiv_ne_top_iff.mp hk).1
  have ht := ha.ae_le (scalarObservationLaw_ae_limit (residualLaw P.fst r) href)
  have hh := ae_of_ae_map measurable_residualLabelObservation.aemeasurable ht
  filter_upwards [hh] with w hw
  have hd := ENNReal.Tendsto.div_const hw (Or.inr
    (ne_of_gt (lt_of_lt_of_le (by norm_num) (residualScale_lower P.fst w.1.1 w.2))))
  convert hd using 1
  · funext n
    dsimp only [residualLabelObservation,Prod.fst,Prod.snd]
    rw [scalarCube_projection]
    rfl
  · rfl

lemma residualSignalLaw {d r : ℕ} {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) [IsProbabilityMeasure P] :
    (P.prod (gaussianRows r d)).map
      (fun w => residualObservation (w.1.1,w.2)) = residualLaw P.fst r := by
  unfold residualLaw
  have he : (P.fst.prod (gaussianRows r d)) =
      (P.prod (gaussianRows r d)).map (Prod.map Prod.fst id) := by
    simpa only [Measure.map_id,Measure.fst] using Measure.map_prod_map P (gaussianRows r d) measurable_fst measurable_id
  rw [he,Measure.map_map measurable_residualObservation (measurable_fst.prodMap measurable_id)]
  rfl

lemma density_positive_ae {A : Type*} [MeasurableSpace A]
    (Q Λ : Measure A) [IsProbabilityMeasure Q] [SigmaFinite Λ]
    (p : A → ℝ≥0∞) (hp : Measurable p) (he : Λ.withDensity p = Q) :
    ∀ᵐ a ∂Q, 0 < p a := by
  have ha : Q ≪ Λ := by rw [←he]; exact withDensity_absolutelyContinuous _ _
  have hr : Q.rnDeriv Λ =ᵐ[Λ] p := by rw [←he]; exact Measure.rnDeriv_withDensity _ hp
  filter_upwards [ha.ae_le hr,Measure.rnDeriv_pos ha] with a h1 h2
  rwa [←h1]

lemma log_le_log_scale_add {p A : ℝ≥0∞} (hp : 0 < p) (hpt : p ≠ ∞)
    (hA : 0 < A) (hAt : A ≠ ∞) :
    Real.log p.toReal ≤ Real.log A.toReal+Real.log (1+(p/A).toReal) := by
  have hp' := ENNReal.toReal_pos hp.ne' hpt
  have hA' := ENNReal.toReal_pos hA.ne' hAt
  rw [ENNReal.toReal_div]
  have hl := Real.log_le_log (div_pos hp' hA') (le_add_of_nonneg_left (show (0:ℝ)≤1 by norm_num) : p.toReal/A.toReal ≤ 1+p.toReal/A.toReal)
  rw [Real.log_div hp'.ne' hA'.ne'] at hl
  linarith

def hybridRowConstant : ℝ := cauchyTiltConstant+Real.log (1+5*kernelSmallBallConstant)

end CurrentProjection

end

end OAI
