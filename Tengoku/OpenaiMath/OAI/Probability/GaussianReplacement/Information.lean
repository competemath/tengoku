import Tengoku.OpenaiMath.OAI.Probability.GaussianReplacement.CriticalEntropy

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory

lemma klDiv_prod_chain {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [StandardBorelSpace B] [Nonempty B]
    (P : Measure (A×B)) [IsProbabilityMeasure P]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    klDiv P (μ.prod ν) = klDiv P.fst μ + klDiv P (P.fst.prod ν) := by
  have h := klDiv_compProd_eq_add P.fst μ P.condKernel (Kernel.const A ν)
  simpa only [P.disintegrate P.condKernel,Measure.compProd_const] using h

lemma mutualInformation_reference {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [StandardBorelSpace B] [Nonempty B]
    (P : Measure (A×B)) [IsProbabilityMeasure P]
    (μ : Measure A) [IsProbabilityMeasure μ] :
    klDiv P (μ.prod P.snd) = klDiv P.fst μ + mutualInformation P :=
  klDiv_prod_chain P μ P.snd

lemma klDiv_map_leftInverse {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (P Q : Measure A) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (f : A → B) (g : B → A) (hf : Measurable f) (hg : Measurable g)
    (hgf : Function.LeftInverse g f) :
    klDiv (P.map f) (Q.map f) = klDiv P Q := by
  apply le_antisymm (klDiv_map_le P Q hf)
  have h := klDiv_map_le (P.map f) (Q.map f) hg
  have he : g ∘ f = id := funext hgf
  simpa only [Measure.map_map hg hf,he,Measure.map_id] using h

lemma mutualInformation_map_left {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] (P : Measure (A×B)) [IsProbabilityMeasure P]
    (f : A → C) (g : C → A) (hf : Measurable f) (hg : Measurable g)
    (hgf : Function.LeftInverse g f) :
    mutualInformation (P.map (Prod.map f id)) = mutualInformation P := by
  have hT : Measurable (Prod.map f (id : B → B)) := hf.prodMap measurable_id
  have hfst : (P.map (Prod.map f id)).fst = P.fst.map f := by
    simp only [Measure.fst,Measure.map_map measurable_fst hT,Measure.map_map hf measurable_fst]
    rfl
  have hsnd : (P.map (Prod.map f id)).snd = P.snd := by
    simp only [Measure.snd,Measure.map_map measurable_snd hT]
    rfl
  unfold mutualInformation
  have hRef : (P.fst.prod P.snd).map (Prod.map f id) = (P.fst.map f).prod P.snd := by
    rw [←Measure.map_prod_map _ _ hf measurable_id,Measure.map_id]
  rw [hfst,hsnd,←hRef]
  exact klDiv_map_leftInverse P (P.fst.prod P.snd) (Prod.map f id) (Prod.map g id)
    hT (hg.prodMap measurable_id) (fun x => by ext <;> simp [hgf x.1])

lemma mutualInformation_swap {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (P : Measure (A×B)) [IsProbabilityMeasure P] :
    mutualInformation (P.map Prod.swap) = mutualInformation P := by
  have hf : (P.map Prod.swap).fst = P.snd := by
    simp only [Measure.fst,Measure.snd,Measure.map_map measurable_fst measurable_swap]; rfl
  have hs : (P.map Prod.swap).snd = P.fst := by
    simp only [Measure.fst,Measure.snd,Measure.map_map measurable_snd measurable_swap]; rfl
  unfold mutualInformation
  rw [hf,hs,←Measure.prod_swap]
  exact klDiv_map_equiv P (P.fst.prod P.snd) MeasurableEquiv.prodComm

lemma mutualInformation_rows_chain {S W X : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    (P : Measure ((S×W)×X)) [IsProbabilityMeasure P]
    (ν : Measure S) (γ : Measure X) [IsProbabilityMeasure ν] [IsProbabilityMeasure γ]
    (hInd : (P.map swapLast).fst = ν.prod γ) :
    mutualInformation (P.map swapLast) = mutualInformation P.fst + rowInformation P γ := by
  have hSW : P.fst.fst = ν := by
    have h := congrArg Measure.fst hInd
    rw [Measure.fst_prod] at h
    convert h using 1
    simp only [Measure.fst,Measure.map_map measurable_fst swapLast.measurable,
      Measure.map_map measurable_fst measurable_fst,
      Measure.map_map measurable_fst (measurable_fst.comp swapLast.measurable)]
    rfl
  have hW : (P.map swapLast).snd = P.fst.snd := by
    simp only [Measure.snd,Measure.fst,Measure.map_map measurable_snd swapLast.measurable,
      Measure.map_map measurable_snd measurable_fst]; rfl
  have h := klDiv_prod_chain P (ν.prod P.fst.snd) γ
  unfold mutualInformation rowInformation
  rw [hInd,hW,←map_swapLast_prod,klDiv_map_equiv,h,hSW]

lemma mutualInformation_independent_rows {S W X : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [MeasurableSpace X] (P : Measure (S×W)) [IsProbabilityMeasure P]
    (γ : Measure X) [IsProbabilityMeasure γ] :
    mutualInformation ((P.prod γ).map swapLast) = mutualInformation P := by
  have hf : ((P.prod γ).map swapLast).fst = P.fst.prod γ := by
    rw [Measure.fst,Measure.map_map measurable_fst swapLast.measurable]
    change (P.prod γ).map (Prod.map Prod.fst id) = _
    rw [←Measure.map_prod_map P γ measurable_fst measurable_id,Measure.map_id]
    rfl
  have hs : ((P.prod γ).map swapLast).snd = P.snd := by
    rw [Measure.snd,Measure.map_map measurable_snd swapLast.measurable]
    change (P.prod γ).map (Prod.snd ∘ Prod.fst) = _
    rw [←Measure.map_map measurable_snd measurable_fst,←Measure.fst,Measure.fst_prod]
    rfl
  unfold mutualInformation
  rw [hf,hs,←map_swapLast_prod,klDiv_map_equiv]
  have h := klDiv_compProd_left P (P.fst.prod P.snd) (Kernel.const (S×W) γ)
  simpa only [Measure.compProd_const] using h

lemma mutualInformation_reference_comparison {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    [StandardBorelSpace W] [Nonempty W]
    (P Q : Measure (Z×W)) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (μ : Measure Z) [IsProbabilityMeasure μ]
    (hfst : P.fst = Q.fst) (hsnd : P.snd = Q.snd)
    (hPQ : klDiv P Q ≠ ∞) (hQR : klDiv Q (μ.prod Q.snd) ≠ ∞)
    (hi : Integrable (llr Q (μ.prod Q.snd)) P) :
    mutualInformation P ≠ ∞ ∧ mutualInformation Q ≠ ∞ ∧
      (mutualInformation P).toReal = (mutualInformation Q).toReal + (klDiv P Q).toReal +
        (∫ z, llr Q (μ.prod Q.snd) z ∂P) - (∫ z, llr Q (μ.prod Q.snd) z ∂Q) := by
  obtain ⟨hPR,hchain⟩ := klDiv_chain_finite P Q (μ.prod Q.snd) hPQ
    (klDiv_ne_top_iff.mp hQR).1 hi
  have hP := mutualInformation_reference P μ
  have hQ := mutualInformation_reference Q μ
  rw [hsnd,hfst] at hP
  have hbase : klDiv Q.fst μ ≠ ∞ := by
    exact ne_top_of_le_ne_top hQR (hQ ▸ le_add_right le_rfl)
  have hMP : mutualInformation P ≠ ∞ := by
    exact ne_top_of_le_ne_top hPR (hP ▸ le_add_left le_rfl)
  have hMQ : mutualInformation Q ≠ ∞ := by
    exact ne_top_of_le_ne_top hQR (hQ ▸ le_add_left le_rfl)
  refine ⟨hMP,hMQ,?_⟩
  have hP' := congrArg ENNReal.toReal hP
  have hQ' := congrArg ENNReal.toReal hQ
  rw [ENNReal.toReal_add hbase hMP] at hP'
  rw [ENNReal.toReal_add hbase hMQ] at hQ'
  have hQR' : (klDiv Q (μ.prod Q.snd)).toReal = ∫ z, llr Q (μ.prod Q.snd) z ∂Q := by
    exact toReal_klDiv_of_measure_eq (klDiv_ne_top_iff.mp hQR).1 (by simp)
  rw [hQR'] at hQ'
  linarith

lemma density_mutualInformation_comparison {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    [StandardBorelSpace W] [Nonempty W]
    (P Q : Measure (Z×W)) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (Λ : Measure Z) [SigmaFinite Λ] (g : Z → ℝ) (hg : Measurable g) (hgpos : ∀ z, 0<g z)
    (μ : Measure Z) [IsProbabilityMeasure μ]
    (hμ : Λ.withDensity (fun z => ENNReal.ofReal (g z)) = μ)
    (p : Z×W → ℝ≥0∞) (hp : Measurable p)
    (hQ : (Λ.prod Q.snd).withDensity p = Q)
    (hfst : P.fst = Q.fst) (hsnd : P.snd = Q.snd) (hPQ : klDiv P Q ≠ ∞)
    (hpP : Integrable (fun z => logPositive (p z)) P)
    (hpQ : Integrable (fun z => logPositive (p z)) Q)
    (hgQ : Integrable (fun z => Real.log (g z)) Q.fst) :
    Integrable (fun z => Real.log (p z).toReal) P ∧
    Integrable (fun z => Real.log (p z).toReal) Q ∧
    mutualInformation P ≠ ∞ ∧ mutualInformation Q ≠ ∞ ∧
    (mutualInformation P).toReal = (mutualInformation Q).toReal + (klDiv P Q).toReal +
      (∫ z, Real.log (p z).toReal ∂P) - (∫ z, Real.log (p z).toReal ∂Q) := by
  let R := μ.prod Q.snd
  have hR : (Λ.prod Q.snd).withDensity (fun z => ENNReal.ofReal (g z.1)) = R := by
    rw [←prod_withDensity_left hg.ennreal_ofReal,hμ]
  obtain ⟨hQR,he⟩ := llr_of_two_densities Q R (Λ.prod Q.snd) p hp hQ
    (fun z => g z.1) (hg.comp measurable_fst) (fun z => hgpos z.1) hR
  have hPQac := (klDiv_ne_top_iff.mp hPQ).1
  have heP := hPQac.ae_le he
  have hgiQ : Integrable (fun z : Z×W => Real.log (g z.1)) Q :=
    (integrable_map_measure hg.log.aestronglyMeasurable measurable_fst.aemeasurable).mp hgQ
  have hgiP : Integrable (fun z : Z×W => Real.log (g z.1)) P :=
    (integrable_map_measure hg.log.aestronglyMeasurable measurable_fst.aemeasurable).mp (by change Integrable _ P.fst; rw [hfst]; exact hgQ)
  have huP : Integrable (fun z => logPositive (p z) - Real.log (g z.1)) P := hpP.sub hgiP
  have huQ : Integrable (fun z => logPositive (p z) - Real.log (g z.1)) Q := hpQ.sub hgiQ
  have hleP : ∀ᵐ z ∂P, llr Q R z ≤ logPositive (p z) - Real.log (g z.1) := by
    filter_upwards [heP] with z hz
    rw [hz]
    exact sub_le_sub_right (le_max_left _ _) _
  have hleQ : ∀ᵐ z ∂Q, llr Q R z ≤ logPositive (p z) - Real.log (g z.1) := by
    filter_upwards [he] with z hz
    rw [hz]
    exact sub_le_sub_right (le_max_left _ _) _
  obtain ⟨hcP,_⟩ := cross_llr_integrable P Q R hPQ hQR _ huP hleP
  obtain ⟨hcQ,hQRfinite⟩ := cross_llr_integrable Q Q R (by simp) hQR _ huQ hleQ
  have hpPi : Integrable (fun z => Real.log (p z).toReal) P := by
    apply (hcP.add hgiP).congr
    filter_upwards [heP] with z hz
    simp only [Pi.add_apply,hz]
    ring
  have hpQi : Integrable (fun z => Real.log (p z).toReal) Q := by
    apply (hcQ.add hgiQ).congr
    filter_upwards [he] with z hz
    simp only [Pi.add_apply,hz]
    ring
  obtain ⟨hMP,hMQ,hinfo⟩ := mutualInformation_reference_comparison P Q μ hfst hsnd hPQ hQRfinite hcP
  refine ⟨hpPi,hpQi,hMP,hMQ,?_⟩
  have hgint : (∫ z : Z×W, Real.log (g z.1) ∂P) = ∫ z : Z×W, Real.log (g z.1) ∂Q := by
    rw [←integral_map measurable_fst.aemeasurable hg.log.aestronglyMeasurable,
      ←integral_map measurable_fst.aemeasurable hg.log.aestronglyMeasurable]
    change (∫ z, Real.log (g z) ∂P.fst) = ∫ z, Real.log (g z) ∂Q.fst
    rw [hfst]
  change _ = _ + _ + (∫ z, llr Q R z ∂P) - (∫ z, llr Q R z ∂Q) at hinfo
  rw [integral_congr_ae heP,integral_congr_ae he,
    integral_sub hpPi hgiP,integral_sub hpQi hgiQ,hgint] at hinfo
  linarith

def observedMessageMap {d k : ℕ} {W : Type*} (p : (Sphere d×W)×Rows k d) :
    (Rows k d×(Fin k→ℝ))×W := ((p.2,label p.2 (p.1.1:Vector d)),p.1.2)

def observedMessage {d k : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows k d)) : Measure ((Rows k d×(Fin k→ℝ))×W) :=
  P.map observedMessageMap

lemma prod_posterior_map {S W G Z : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [MeasurableSpace G] [MeasurableSpace Z] [StandardBorelSpace S] [Nonempty S]
    (P : Measure (S×W)) [IsProbabilityMeasure P] (γ : Measure G) [IsProbabilityMeasure γ]
    (f : S×G → Z) (hf : Measurable f) :
    (P.prod γ).map (fun p => (f (p.1.1,p.2),p.1.2)) =
      (P.snd ⊗ₘ ((messagePosterior P ×ₖ Kernel.const W γ).map f)).map Prod.swap := by
  let κ := messagePosterior P
  have hpost : P.snd ⊗ₘ κ = P.map Prod.swap := by
    have h := congrArg (fun μ : Measure (S×W) => μ.map Prod.swap) (messagePosterior_disintegrate P)
    rw [Measure.map_map measurable_swap measurable_swap] at h
    simpa only [show (Prod.swap ∘ Prod.swap : W×S → W×S) = id from rfl,Measure.map_id] using h
  have hbase : (P.snd ⊗ₘ (κ ×ₖ Kernel.const W γ)).map MeasurableEquiv.prodAssoc.symm =
      (P.map Prod.swap).prod γ := by
    rw [compProd_prod_assoc,hpost]
    have hc : (Kernel.const W γ).comap (Prod.fst : W×S → W) measurable_fst =
        Kernel.const (W×S) γ := by ext x t ht; rfl
    rw [hc,Measure.compProd_const]
  have hbase' : P.snd ⊗ₘ (κ ×ₖ Kernel.const W γ) =
      ((P.map Prod.swap).prod γ).map MeasurableEquiv.prodAssoc := by
    rw [←hbase,MeasurableEquiv.map_map_symm]
  rw [Measure.compProd_map hf]
  change _ = ((P.snd ⊗ₘ (κ ×ₖ Kernel.const W γ)).map (Prod.map id f)).map Prod.swap
  rw [hbase',Measure.map_map (measurable_id.prodMap hf) MeasurableEquiv.prodAssoc.measurable,
    Measure.map_map measurable_swap ((measurable_id.prodMap hf).comp MeasurableEquiv.prodAssoc.measurable)]
  have hp : (P.map Prod.swap).prod γ = (P.prod γ).map (Prod.map Prod.swap id) := by
    rw [←Measure.map_prod_map _ _ measurable_swap measurable_id,Measure.map_id]
  rw [hp,Measure.map_map (measurable_swap.comp ((measurable_id.prodMap hf).comp MeasurableEquiv.prodAssoc.measurable))
    (measurable_swap.prodMap measurable_id)]
  rfl

lemma swapped_compProd_withDensity {W Z : Type*} [MeasurableSpace W] [MeasurableSpace Z]
    (π : Measure W) (Λ : Measure Z) [SFinite π] [SFinite Λ]
    (κ : Kernel W Z) [IsSFiniteKernel κ] (p : Z×W → ℝ≥0∞) (hp : Measurable p)
    (h : ∀ᵐ w ∂π, Λ.withDensity (fun z => p (z,w)) = κ w) :
    (Λ.prod π).withDensity p = (π ⊗ₘ κ).map Prod.swap := by
  apply Measure.ext
  intro t ht
  rw [withDensity_apply _ ht,←lintegral_indicator ht,
    lintegral_prod_symm _ (hp.indicator ht).aemeasurable,
    Measure.map_apply measurable_swap ht,Measure.compProd_apply (ht.preimage measurable_swap)]
  apply lintegral_congr_ae
  filter_upwards [h] with w hw
  change _ = κ w ((fun z : Z => (z,w)) ⁻¹' t)
  have ht' : MeasurableSet ((fun z : Z => (z,w)) ⁻¹' t) :=
    ht.preimage (measurable_id.prodMk measurable_const)
  rw [←hw,withDensity_apply _ ht',←lintegral_indicator ht']
  rfl

def posteriorProjectionKernel {d k : ℕ} {W : Type*} [MeasurableSpace W]
    [Nonempty (Sphere d)] (P : Measure (Sphere d×W)) [IsFiniteMeasure P]
    (γ : Measure (Rows k d)) : Kernel W (Rows k d×(Fin k→ℝ)) :=
  (messagePosterior P ×ₖ Kernel.const W γ).map
    (fun z : Sphere d×Rows k d => (z.2,label z.2 (z.1:Vector d)))

lemma criticalPosterior_probability {d ℓ j : ℕ} (F : Measure (Sphere d))
    [IsProbabilityMeasure F] (q : ℤ) (hη : 0 < F (criticalClass F ℓ j q)) :
    IsProbabilityMeasure (criticalPosterior F ℓ j q) := by
  constructor
  change (F (criticalClass F ℓ j q))⁻¹ * (F.restrict (criticalClass F ℓ j q)) Set.univ = 1
  simp only [Measure.restrict_apply_univ]
  exact ENNReal.inv_mul_cancel hη.ne' (measure_ne_top F _)

lemma criticalPosterior_ae_class {d ℓ j : ℕ} (F : Measure (Sphere d))
    [IsFiniteMeasure F] (q : ℤ) :
    ∀ᵐ s ∂criticalPosterior F ℓ j q, s ∈ criticalClass F ℓ j q := by
  exact (Measure.smul_absolutelyContinuous).ae_le (ae_restrict_mem (measurableSet_criticalClass F ℓ j q))

lemma independent_rows_signal {S W G : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [MeasurableSpace G] (P : Measure (S×W)) [IsProbabilityMeasure P]
    (γ : Measure G) [IsProbabilityMeasure γ] :
    ((P.prod γ).map swapLast).fst = P.fst.prod γ := by
  rw [Measure.fst,Measure.map_map measurable_fst swapLast.measurable]
  change (P.prod γ).map (Prod.map Prod.fst id) = _
  rw [←Measure.map_prod_map _ _ measurable_fst measurable_id,Measure.map_id]
  rfl

lemma swapLast_snd {S W G : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [MeasurableSpace G] (P : Measure ((S×W)×G)) : (P.map swapLast).snd = P.fst.snd := by
  rw [Measure.snd,Measure.fst,Measure.snd,Measure.map_map measurable_snd swapLast.measurable,
    Measure.map_map measurable_snd measurable_fst]
  rfl

end CurrentProjection

end

end OAI
