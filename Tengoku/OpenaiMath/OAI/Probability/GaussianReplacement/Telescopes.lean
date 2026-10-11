import Tengoku.OpenaiMath.OAI.Probability.GaussianReplacement.ArrayBounds

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory

lemma averaged_telescope_block {m a b : ℕ} (hab : a ≤ b)
    (J T : ℕ → ℕ → ℝ) (K : ℕ → ℝ) (C S B q : ℝ) (hq : 0 < q)
    (hstep : ∀ i < m, ∀ k ∈ Finset.Icc a b,
      J i k-J (i+1) k ≤ C+K i/q+T i (k+1)-T i k)
    (hfirst : ∀ i < m, 0 ≤ T i a)
    (hlast : ∀ i < m, T i (b+1) ≤ S)
    (hK : ∑ i ∈ Finset.range m, K i ≤ B) :
    (∑ k ∈ Finset.Icc a b, J 0 k)/(b-a+1:ℕ) -
      (∑ k ∈ Finset.Icc a b, J m k)/(b-a+1:ℕ) ≤
        C*m+(m:ℝ)/(b-a+1:ℕ)*S+B/q := by
  let N : ℝ := (b-a+1:ℕ)
  have hN : 0 < N := by dsimp [N]; positivity
  have hcard : ((Finset.Icc a b).card:ℝ) = N := by
    dsimp [N]
    simp only [Nat.card_Icc]
    congr 1
    omega
  have he : Finset.Icc a b = Finset.Ico a (b+1) := by
    ext k
    simp only [Finset.mem_Icc,Finset.mem_Ico]
    omega
  have hs (i : ℕ) : ∑ k ∈ Finset.Icc a b, (T i (k+1)-T i k) = T i (b+1)-T i a := by
    rw [he]
    exact Finset.sum_Ico_sub _ (by omega)
  let F : ℕ → ℝ := fun i => (∑ k ∈ Finset.Icc a b, J i k)/N
  have hrow (i : ℕ) (hi : i < m) : F i-F (i+1) ≤ C+S/N+K i/q := by
    have h := Finset.sum_le_sum (fun k hk => hstep i hi k hk)
    have hrepr : ∑ k ∈ Finset.Icc a b, (C+K i/q+T i (k+1)-T i k) =
        N*(C+K i/q)+T i (b+1)-T i a := by
      simp_rw [show ∀ k, C+K i/q+T i (k+1)-T i k = (C+K i/q)+(T i (k+1)-T i k) by intro k; ring]
      rw [Finset.sum_add_distrib,hs,Finset.sum_const,nsmul_eq_mul,hcard]
      ring
    rw [hrepr,Finset.sum_sub_distrib] at h
    dsimp only [F]
    rw [←sub_div]
    apply (div_le_iff₀ hN).mpr
    have hfirst' := hfirst i hi
    have hlast' := hlast i hi
    calc
      _ ≤ N*(C+K i/q)+S := by linarith
      _ = (C+S/N+K i/q)*N := by field_simp; ring
  have hsum := Finset.sum_le_sum (fun i hi => hrow i (Finset.mem_range.mp hi))
  rw [Finset.sum_range_sub'] at hsum
  have hsumr : ∑ i ∈ Finset.range m, (C+S/N+K i/q) =
      (m:ℝ)*(C+S/N)+(∑ i ∈ Finset.range m, K i)/q := by
    rw [Finset.sum_add_distrib,Finset.sum_div,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  rw [hsumr] at hsum
  have hKq := div_le_div_of_nonneg_right hK hq.le
  change F 0-F m ≤ C*m+(m:ℝ)/N*S+B/q
  calc
    _ ≤ (m:ℝ)*(C+S/N)+(∑ i ∈ Finset.range m, K i)/q := hsum
    _ ≤ (m:ℝ)*(C+S/N)+B/q := add_le_add_right hKq _
    _ = _ := by ring

def processedKernel {Z A B C : Type*} [MeasurableSpace Z] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] (α : Kernel Z (A×B))
    (η : Kernel (Z×B) C) : Kernel Z (A×C) :=
  (α ⊗ₖ η.comap (Prod.map id Prod.snd) (measurable_id.prodMap measurable_snd)).map
    (fun z => (z.1.1,z.2))

instance processedKernel_markov {Z A B C : Type*} [MeasurableSpace Z] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] (α : Kernel Z (A×B)) [IsMarkovKernel α]
    (η : Kernel (Z×B) C) [IsMarkovKernel η] : IsMarkovKernel (processedKernel α η) := by
  unfold processedKernel
  exact Kernel.IsMarkovKernel.map _ (measurable_fst.fst.prodMk measurable_snd)

lemma processedKernel_apply_prod {Z A B C : Type*} [MeasurableSpace Z] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] (α : Kernel Z (A×B)) [IsMarkovKernel α]
    (η : Kernel (Z×B) C) [IsMarkovKernel η] (z : Z)
    {s : Set A} {t : Set C} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    processedKernel α η z (s×ˢt) = ∫⁻ p in s×ˢSet.univ, η (z,p.2) t ∂α z := by
  rw [processedKernel,Kernel.map_apply _ (measurable_fst.fst.prodMk measurable_snd),Measure.map_apply (measurable_fst.fst.prodMk measurable_snd) (hs.prod ht)]
  rw [show (fun p : (A×B)×C => (p.1.1,p.2)) ⁻¹' (s×ˢt) = (s×ˢSet.univ)×ˢt by ext p; simp]
  rw [Kernel.compProd_apply_prod (hs.prod MeasurableSet.univ) ht]
  rfl

lemma processedKernel_fst {Z A B C : Type*} [MeasurableSpace Z] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] (α : Kernel Z (A×B)) [IsMarkovKernel α]
    (η : Kernel (Z×B) C) [IsMarkovKernel η] : (processedKernel α η).fst = α.fst := by
  rw [processedKernel,Kernel.fst_eq,←Kernel.map_comp_right _ (measurable_fst.fst.prodMk measurable_snd) measurable_fst]
  change (α ⊗ₖ η.comap (Prod.map id Prod.snd) (measurable_id.prodMap measurable_snd)).map (Prod.fst ∘ Prod.fst) = _
  rw [Kernel.map_comp_right _ measurable_fst measurable_fst]
  rw [←Kernel.fst_eq,←Kernel.fst_eq,Kernel.fst_compProd]

lemma processedKernel_snd_apply {Z A B C : Type*} [MeasurableSpace Z] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] (α : Kernel Z (A×B)) [IsMarkovKernel α]
    (η : Kernel (Z×B) C) [IsMarkovKernel η] (z : Z) {t : Set C} (ht : MeasurableSet t) :
    (processedKernel α η).snd z t = ∫⁻ b, η (z,b) t ∂α.snd z := by
  rw [Kernel.snd_apply' _ _ ht]
  rw [show (Prod.snd : A×C → C) ⁻¹' t = Set.univ×ˢt by ext p; simp]
  rw [processedKernel_apply_prod α η z MeasurableSet.univ ht]
  simp only [Set.univ_prod_univ,Measure.restrict_univ]
  rw [Kernel.snd_eq,Kernel.map_apply _ measurable_snd]
  rw [lintegral_map (by exact (η.measurable_coe ht).comp (measurable_const.prodMk measurable_id)) measurable_snd]

lemma processedKernel_reference {Z A B C : Type*} [MeasurableSpace Z] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] (α : Kernel Z (A×B)) [IsMarkovKernel α]
    (η : Kernel (Z×B) C) [IsMarkovKernel η] :
    processedKernel (α.fst ×ₖ α.snd) η = (processedKernel α η).fst ×ₖ (processedKernel α η).snd := by
  rw [processedKernel_fst]
  ext z : 1
  apply Measure.ext_prod
  intro s t hs ht
  rw [processedKernel_apply_prod _ _ _ hs ht,Kernel.prod_apply_prod,processedKernel_snd_apply _ _ _ ht,
    Kernel.prod_apply,←Measure.prod_restrict (s:=s) (t:=Set.univ),Measure.restrict_univ]
  rw [lintegral_prod _ (by exact ((η.measurable_coe ht).comp (measurable_const.prodMk measurable_snd)).aemeasurable)]
  simp only [lintegral_const,Measure.restrict_apply_univ]
  rw [mul_comm]

lemma compProd_processedKernel {Z A B C : Type*} [MeasurableSpace Z] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] (μ : Measure Z) [IsFiniteMeasure μ]
    (α : Kernel Z (A×B)) [IsMarkovKernel α] (η : Kernel (Z×B) C) [IsMarkovKernel η] :
    μ ⊗ₘ processedKernel α η =
      ((μ ⊗ₘ α) ⊗ₘ η.comap (Prod.map id Prod.snd) (measurable_id.prodMap measurable_snd)).map
        (fun z => (z.1.1,(z.1.2.1,z.2))) := by
  rw [processedKernel,Measure.compProd_map (measurable_fst.fst.prodMk measurable_snd),
    ←Measure.compProd_assoc,Measure.map_map
      (measurable_fst.fst.prodMk (measurable_fst.snd.fst.prodMk measurable_snd))
      MeasurableEquiv.prodAssoc.symm.measurable]
  rfl

lemma conditionalMutualInformation_processedKernel_le {Z A B C : Type*}
    [MeasurableSpace Z] [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    [StandardBorelSpace A] [StandardBorelSpace B] [StandardBorelSpace C]
    [Nonempty A] [Nonempty B] [Nonempty C]
    (μ : Measure Z) [IsProbabilityMeasure μ]
    (α : Kernel Z (A×B)) [IsMarkovKernel α] (η : Kernel (Z×B) C) [IsMarkovKernel η] :
    conditionalMutualInformation (μ ⊗ₘ processedKernel α η) ≤ conditionalMutualInformation (μ ⊗ₘ α) := by
  rw [conditionalMutualInformation_compProd,conditionalMutualInformation_compProd,
    ←processedKernel_reference,compProd_processedKernel,compProd_processedKernel]
  calc
    _ ≤ klDiv ((μ ⊗ₘ α) ⊗ₘ η.comap (Prod.map id Prod.snd) (measurable_id.prodMap measurable_snd))
      ((μ ⊗ₘ (α.fst ×ₖ α.snd)) ⊗ₘ η.comap (Prod.map id Prod.snd) (measurable_id.prodMap measurable_snd)) :=
      klDiv_map_le _ _ (measurable_fst.fst.prodMk (measurable_fst.snd.fst.prodMk measurable_snd))
    _ = _ := klDiv_compProd_left _ _ _

def processedLaw {Z A B C : Type*} [MeasurableSpace Z] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] (P : Measure (Z×(A×B)))
    (η : Kernel (Z×B) C) : Measure (Z×(A×C)) :=
  (P ⊗ₘ η.comap (Prod.map id Prod.snd) (measurable_id.prodMap measurable_snd)).map
    (fun z => (z.1.1,(z.1.2.1,z.2)))

instance processedLaw_probability {Z A B C : Type*} [MeasurableSpace Z] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] (P : Measure (Z×(A×B))) [IsProbabilityMeasure P]
    (η : Kernel (Z×B) C) [IsMarkovKernel η] : IsProbabilityMeasure (processedLaw P η) := by
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_fst.fst.prodMk (measurable_fst.snd.fst.prodMk measurable_snd)).aemeasurable).mpr
    inferInstance

lemma conditionalMutualInformation_processed_le {Z A B C : Type*}
    [MeasurableSpace Z] [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    [StandardBorelSpace A] [StandardBorelSpace B] [StandardBorelSpace C]
    [Nonempty A] [Nonempty B] [Nonempty C]
    (P : Measure (Z×(A×B))) [IsProbabilityMeasure P] (η : Kernel (Z×B) C) [IsMarkovKernel η] :
    conditionalMutualInformation (processedLaw P η) ≤ conditionalMutualInformation P := by
  have h := conditionalMutualInformation_processedKernel_le P.fst P.condKernel η
  simpa only [compProd_processedKernel,P.disintegrate P.condKernel,processedLaw] using h

lemma compProd_map_base {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] (μ : Measure A) [IsProbabilityMeasure μ]
    (κ : Kernel B C) [IsMarkovKernel κ] (f : A → B) (hf : Measurable f) :
    μ.map f ⊗ₘ κ = (μ ⊗ₘ κ.comap f hf).map (Prod.map f id) := by
  apply Measure.ext_prod
  intro s t hs ht
  rw [Measure.compProd_apply_prod hs ht,Measure.map_apply (hf.prodMap measurable_id) (hs.prod ht)]
  change _ = (μ ⊗ₘ κ.comap f hf) ((f ⁻¹' s)×ˢt)
  rw [Measure.compProd_apply_prod (hs.preimage hf) ht,setLIntegral_map hs (κ.measurable_coe ht) hf]
  rfl

lemma compProd_independent_swap {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] (μ : Measure A) [IsProbabilityMeasure μ]
    (κ : Kernel A B) [IsMarkovKernel κ] (γ : Measure C) [IsProbabilityMeasure γ] :
    ((μ ⊗ₘ κ).prod γ).map (fun z => ((z.1.1,z.2),z.1.2)) =
      (μ.prod γ) ⊗ₘ κ.comap Prod.fst measurable_fst := by
  apply Measure.ext_prod₃'
  intro s t u hs ht hu
  rw [Measure.map_apply ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd) ((hs.prod ht).prod hu)]
  have he : (fun z : (A×B)×C => ((z.1.1,z.2),z.1.2)) ⁻¹' ((s×ˢt)×ˢu) = (s×ˢu)×ˢt := by
    ext z; simp only [Set.mem_preimage,Set.mem_prod]; tauto
  rw [he,Measure.prod_prod,Measure.compProd_apply_prod hs hu,Measure.compProd_apply_prod (hs.prod ht) hu,
    ←Measure.prod_restrict,lintegral_prod _ (by exact ((κ.measurable_coe hu).comp measurable_fst).aemeasurable)]
  simp only [Kernel.comap_apply,lintegral_const,Measure.restrict_apply_univ]
  rw [lintegral_mul_const _ (κ.measurable_coe hu)]

lemma probability_prod_subsingleton {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [Subsingleton B] (μ : Measure (A×B)) [IsProbabilityMeasure μ]
    (γ : Measure B) [IsProbabilityMeasure γ] : μ = μ.fst.prod γ := by
  apply Measure.ext_prod
  intro s t hs ht
  by_cases ht0 : t = ∅
  · simp [ht0]
  · have ht1 : t = Set.univ := (Set.nonempty_iff_ne_empty.mpr ht0).eq_univ
    rw [ht1,Measure.prod_prod,measure_univ,mul_one]
    rw [Measure.fst_apply hs]
    congr 1
    ext z; simp

lemma measurable_endingRowMap {d m : ℕ} {U V : Type*} [MeasurableSpace U] [MeasurableSpace V] :
    Measurable (fun z : (((Sphere d×U)×Rows m d)×V) => ((z.1.1.1,z.2),z.1.2)) :=
  (measurable_fst.fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd

def blockObservedInput {d m r : ℕ} {U : Type*}
    (z : (Rows (m+r) d×(Fin (m+r)→ℝ))×U) : U×(Rows m d×(Fin m→ℝ)) :=
  (z.2, (fun j => z.1.1 (Fin.castAdd r j)), (fun j => z.1.2 (Fin.castAdd r j)))

lemma measurable_blockObservedInput {d m r : ℕ} {U : Type*} [MeasurableSpace U] :
    Measurable (blockObservedInput (d:=d) (m:=m) (r:=r) (U:=U)) := by
  unfold blockObservedInput
  fun_prop

def blockExposedBaseMap {d m r : ℕ} {U : Type*}
    (z : ((Sphere d×U)×Rows m d)×Rows r d) :
    (Rows (m+r) d×(Fin (m+r)→ℝ))×(Sphere d×U) :=
  exposedJointMap (z.1.1,Fin.append z.1.2 z.2)

lemma blockObservedInput_exposed {d m r : ℕ} {U : Type*}
    (z : ((Sphere d×U)×Rows m d)×Rows r d) :
    blockObservedInput ((blockExposedBaseMap z).1,(blockExposedBaseMap z).2.2) = blockInput z.1 := by
  unfold blockObservedInput blockExposedBaseMap exposedJointMap blockInput
  congr 2
  · funext j; simp
  · funext j; simp [label]

end CurrentProjection

end

end OAI
