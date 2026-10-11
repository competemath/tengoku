import Tengoku.OpenaiMath.OAI.Analysis.Steinitz.HeatL2

namespace OAI

/-! Gaussian heat kernels and autoregressive path laws. -/

section

open MeasureTheory ProbabilityTheory WithLp
open scoped NNReal ENNReal RealInnerProductSpace
namespace GaussianKernel
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma scaleMap_selfAdjoint (v : ι → ℝ≥0) : IsSelfAdjoint (scaleMap v) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  apply Finset.sum_congr rfl
  intro i _
  change y i * (scaleMap v x) i = (scaleMap v y) i * x i
  rw [scaleMap_apply, scaleMap_apply]
  ring

noncomputable def symbol (v : ι → ℝ≥0) (ξ : EuclideanSpace ℝ ι) : ℝ :=
  (∑ i, (v i : ℝ)*(2*Real.pi*ξ i)^2)/2

lemma symbol_eq (v : ι → ℝ≥0) : HeatL2.gaussianSymbol (scaleMap v) = symbol v := by
  ext ξ
  rw [HeatL2.gaussianSymbol, (scaleMap_selfAdjoint v).adjoint_eq,
    EuclideanSpace.real_norm_sq_eq]
  unfold symbol
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [PiLp.smul_apply, smul_eq_mul, scaleMap_apply, mul_pow,
    Real.sq_sqrt (v i).coe_nonneg]
  ring

omit [DecidableEq ι] in
lemma symbol_continuous (v : ι → ℝ≥0) : Continuous (symbol v) := by
  unfold symbol
  fun_prop

omit [DecidableEq ι] in
lemma symbol_nonneg (v : ι → ℝ≥0) (ξ : EuclideanSpace ℝ ι) : 0 ≤ symbol v ξ := by
  unfold symbol
  positivity

end GaussianKernel

open MeasureTheory ProbabilityTheory Set WithLp
open scoped NNReal ENNReal
namespace GaussianKernel

lemma gaussianPDF_logconcave {v : ℝ≥0} (hv : v ≠ 0) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    (x y : ℝ) :
    gaussianPDFReal 0 v x ^ (1-t) * gaussianPDFReal 0 v y ^ t ≤
      gaussianPDFReal 0 v ((1-t)*x+t*y) := by
  have hvp : (0:ℝ)<v := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have hc : 0 < (Real.sqrt (2 * Real.pi * (v:ℝ)))⁻¹ := by positivity
  simp only [gaussianPDFReal, sub_zero]
  rw [Real.mul_rpow hc.le (Real.exp_pos _).le,
    Real.mul_rpow hc.le (Real.exp_pos _).le, ← Real.exp_mul, ← Real.exp_mul]
  calc
    _ = (((Real.sqrt (2 * Real.pi * (v:ℝ)))⁻¹)^(1-t) *
        ((Real.sqrt (2 * Real.pi * (v:ℝ)))⁻¹)^t) *
        Real.exp ((-(x^2)/(2*(v:ℝ)))*(1-t)+ (-(y^2)/(2*(v:ℝ)))*t) := by
      rw [Real.exp_add]; ring
    _ = ((Real.sqrt (2 * Real.pi * (v:ℝ)))⁻¹) *
        Real.exp ((-(x^2)/(2*(v:ℝ)))*(1-t)+ (-(y^2)/(2*(v:ℝ)))*t) := by
      rw [← Real.rpow_add hc, sub_add_cancel, Real.rpow_one]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hc.le
      have hq : ((1-t)*x+t*y)^2 ≤ (1-t)*x^2+t*y^2 := by
        nlinarith [mul_nonneg (mul_nonneg ht.1 (sub_nonneg.mpr ht.2)) (sq_nonneg (x-y))]
      have : -( (1-t)*x^2+t*y^2)/(2*(v:ℝ)) ≤ -(((1-t)*x+t*y)^2)/(2*(v:ℝ)) :=
        div_le_div_of_nonneg_right (neg_le_neg hq) (by positivity)
      convert this using 1; ring

variable {ι : Type*} [Fintype ι]

end GaussianKernel

end

section

open MeasureTheory Set Filter
open scoped ENNReal ComplexInnerProductSpace
namespace HeatL2

lemma integral_pi_fin_cons {X G : Type*} [MeasurableSpace X]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (μ : Measure X) [SigmaFinite μ]
    {n : ℕ} {f : (Fin (n+1) → X) → G} (hf : Integrable f (Measure.pi fun _ => μ)) :
    (∫ p, f p ∂Measure.pi (fun _ : Fin (n+1) => μ)) =
      ∫ x, ∫ p, f (Fin.cons x p) ∂Measure.pi (fun _ : Fin n => μ) ∂μ := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => X) 0
  have he : ∀ z : X × (Fin n → X), e.symm z = Fin.cons z.1 z.2 := by
    intro z
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [e]
    · simp [e]
  have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) 0).symm
  have hi : Integrable (fun z : X × (Fin n → X) => f (e.symm z)) (μ.prod (Measure.pi fun _ => μ)) :=
    hp.integrable_comp_of_integrable hf
  rw [← hp.integral_comp e.symm.measurableEmbedding f]
  rw [integral_prod _ hi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => integral_congr_ae
    (Filter.Eventually.of_forall fun p => congrArg f (he (x,p)))

section Chain
variable {X : Type*} [MeasurableSpace X] (k : BoundedKernel X)
noncomputable def tailWeight : (n : ℕ) → X → (Fin n → X) → ℝ
  | 0, _, _ => 1
  | n+1, x, p => k.value (x,p 0) * tailWeight n (p 0) (fun i => p i.succ)

lemma tailWeight_nonneg (n : ℕ) (x : X) (p : Fin n → X) : 0 ≤ tailWeight k n x p := by
  induction n generalizing x with
  | zero => exact zero_le_one
  | succ n hn => exact mul_nonneg (k.nonneg _) (hn _ _)

lemma tailWeight_le (n : ℕ) (x : X) (p : Fin n → X) : tailWeight k n x p ≤ k.bound^n := by
  induction n generalizing x with
  | zero => exact le_rfl
  | succ n hn =>
    rw [tailWeight, pow_succ']
    exact mul_le_mul (k.le_bound _) (hn _ _) (tailWeight_nonneg k n _ _) k.bound_nonneg

noncomputable def walk (μ : Measure X) (n : ℕ) (x : X) : ℝ :=
  ∫ p, tailWeight k n x p ∂Measure.pi (fun _ : Fin n => μ)

lemma walk_zero (μ : Measure X) (x : X) : walk k μ 0 x = 1 := by
  simp [walk,tailWeight, Measure.real]

lemma walk_nonneg (μ : Measure X) (n : ℕ) (x : X) : 0 ≤ walk k μ n x :=
  integral_nonneg (fun p => tailWeight_nonneg k n x p)

noncomputable def chainWeight (n : ℕ) (p : Fin (n+1) → X) : ℝ :=
  tailWeight k n (p 0) (fun i => p i.succ)

end Chain
end HeatL2

open MeasureTheory Set
namespace HeatL2
section ChainContinuity
variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
variable (k : BoundedKernel X) (hc : Continuous k.value)
include hc
lemma tailWeight_continuous (n : ℕ) : Continuous (fun z : X × (Fin n → X) => tailWeight k n z.1 z.2) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    change Continuous (fun z : X × (Fin (n+1) → X) =>
      k.value (z.1,z.2 0) * tailWeight k n (z.2 0) (fun i => z.2 i.succ))
    apply Continuous.mul
    · exact hc.comp (continuous_fst.prodMk ((continuous_apply 0).comp continuous_snd))
    · exact ih.comp (((continuous_apply 0).comp continuous_snd).prodMk
        (continuous_pi (fun (i : Fin n) => (continuous_apply i.succ).comp continuous_snd)))

lemma chainWeight_continuous (n : ℕ) : Continuous (chainWeight k n) := by
  let f : (Fin (n+1) → X) → X × (Fin n → X) := fun p => (p 0, fun i => p i.succ)
  have hf : Continuous f := by fun_prop
  exact (tailWeight_continuous k hc n).comp hf
end ChainContinuity
section ChainPos
variable {X : Type*} [MeasurableSpace X] (k : BoundedKernel X)
lemma tailWeight_pos (hp : ∀ z, 0 < k.value z) (n : ℕ) (x : X) (p : Fin n → X) :
    0 < tailWeight k n x p := by
  induction n generalizing x with
  | zero => exact zero_lt_one
  | succ n ih => exact mul_pos (hp _) (ih _ _)
end ChainPos
section ChainConcavity
variable {X : Type*} [MeasurableSpace X] [AddCommGroup X] [Module ℝ X]
variable (k : BoundedKernel X) {t : ℝ}
variable (hl : ∀ x y : X × X, k.value x^(1-t) * k.value y^t ≤ k.value ((1-t)•x+t•y))
include hl
lemma tailWeight_logconcave (n : ℕ) (x y : X) (p q : Fin n → X) :
    tailWeight k n x p^(1-t) * tailWeight k n y q^t ≤
      tailWeight k n ((1-t)•x+t•y) ((1-t)•p+t•q) := by
  induction n generalizing x y with
  | zero => simp [tailWeight]
  | succ n ih =>
    simp only [tailWeight, Pi.add_apply, Pi.smul_apply]
    rw [Real.mul_rpow (k.nonneg _) (tailWeight_nonneg k n _ _),
      Real.mul_rpow (k.nonneg _) (tailWeight_nonneg k n _ _)]
    calc
      _ = (k.value (x,p 0)^(1-t) * k.value (y,q 0)^t) *
          (tailWeight k n (p 0) (fun i => p i.succ)^(1-t) *
            tailWeight k n (q 0) (fun i => q i.succ)^t) := by ring
      _ ≤ _ := mul_le_mul (hl (x,p 0) (y,q 0)) (ih _ _ _ _)
        (mul_nonneg (Real.rpow_nonneg (tailWeight_nonneg k n _ _) _)
          (Real.rpow_nonneg (tailWeight_nonneg k n _ _) _)) (k.nonneg _)

lemma chainWeight_logconcave (n : ℕ) (p q : Fin (n+1) → X) :
    chainWeight k n p^(1-t) * chainWeight k n q^t ≤ chainWeight k n ((1-t)•p+t•q) :=
  tailWeight_logconcave k hl n (p 0) (q 0) (fun i => p i.succ) (fun i => q i.succ)
end ChainConcavity
end HeatL2

end

section

open MeasureTheory
namespace HeatL2
variable {X : Type*} [MeasurableSpace X]

lemma chainWeight_prod (k : BoundedKernel X) (n : ℕ) (p : Fin (n+1) → X) :
    chainWeight k n p = ∏ t : Fin n,k.value (p t.castSucc,p t.succ) := by
  induction n with
  | zero => simp [chainWeight,tailWeight]
  | succ n ih =>
    change k.value (p 0,p (Fin.succ 0))*chainWeight k n (fun t => p t.succ)=_
    rw [ih,Fin.prod_univ_succ]
    congr 1

lemma fin_sum_differences {n : ℕ} (f : Fin (n+1) → ℝ) :
    (∑ t : Fin n,(f t.castSucc-f t.succ))=f 0-f (Fin.last n) := by
  rw [Finset.sum_sub_distrib]
  have ha := Fin.sum_univ_castSucc f
  have hb := Fin.sum_univ_succ f
  linarith

end HeatL2

end

section

open MeasureTheory WithLp Set
namespace GaussianAR

lemma measurePreserving_curry (T I : Type*) [Fintype T] [Fintype I] :
    MeasurePreserving (MeasurableEquiv.curry T I ℝ) := by
  apply MeasurePreserving.symm (MeasurableEquiv.curry T I ℝ).symm
  refine ⟨(MeasurableEquiv.curry T I ℝ).symm.measurable,?_⟩
  rw [volume_pi]
  apply (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply (MeasurableEquiv.curry T I ℝ).symm.measurable (MeasurableSet.univ_pi hs)]
  have he : (MeasurableEquiv.curry T I ℝ).symm ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun t => Set.univ.pi (fun i => s (t,i))) := by ext x; simp
  rw [he,volume_pi,Measure.pi_pi]
  simp only [Measure.pi_pi,Fintype.prod_prod_type]

noncomputable def unpack (T I : Type*) [Fintype T] [Fintype I] :
    EuclideanSpace ℝ (T×I) ≃ᵐ (T → EuclideanSpace ℝ I) :=
  (MeasurableEquiv.toLp 2 (T×I → ℝ)).symm.trans ((MeasurableEquiv.curry T I ℝ).trans
    (MeasurableEquiv.piCongrRight (fun _ : T => (MeasurableEquiv.toLp 2 (I → ℝ)))))

lemma unpack_apply {T I : Type*} [Fintype T] [Fintype I]
    (x : EuclideanSpace ℝ (T×I)) (t : T) (i : I) : unpack T I x t i=x (t,i) := rfl

lemma unpack_preserving (T I : Type*) [Fintype T] [Fintype I] :
    MeasurePreserving (unpack T I) := by
  have hp : MeasurePreserving (MeasurableEquiv.piCongrRight
      (fun _ : T => MeasurableEquiv.toLp 2 (I → ℝ))) := by
    refine ⟨(MeasurableEquiv.piCongrRight (fun _ : T => MeasurableEquiv.toLp 2 (I → ℝ))).measurable,?_⟩
    change (volume : Measure (T → I → ℝ)).map (fun x t => toLp 2 (x t)) =
      (volume : Measure (T → EuclideanSpace ℝ I))
    let : SigmaFinite ((volume : Measure (I → ℝ)).map (toLp 2)) := by
      rw [(PiLp.volume_preserving_toLp I).map_eq]
      infer_instance
    rw [volume_pi,Measure.pi_map_pi (fun _ => (PiLp.volume_preserving_toLp I).measurable.aemeasurable)]
    simp only [(PiLp.volume_preserving_toLp I).map_eq,← volume_pi]
  exact hp.comp ((measurePreserving_curry T I).comp (PiLp.volume_preserving_ofLp (T×I)))

end GaussianAR

end

section

open Matrix MeasureTheory ProbabilityTheory WithLp
open scoped RealInnerProductSpace ENNReal NNReal BigOperators
namespace GaussianAR
open GaussianKernel
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def transition (r : ι → ℝ) (x y : EuclideanSpace ℝ ι) : ℝ :=
  ∏ i,(Real.sqrt (1-(r i)^2))⁻¹*gaussianPDFReal 0 1 ((y i-r i*x i)/Real.sqrt (1-(r i)^2))

omit [DecidableEq ι] in
lemma transition_nonneg (r : ι → ℝ) (x y : EuclideanSpace ℝ ι) : 0≤transition r x y := by
  apply Finset.prod_nonneg
  intro i _
  exact mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (gaussianPDFReal_nonneg _ _ _)

lemma path_density_eq (r : ι → ℝ) (hr : ∀ i,0≤r i) (hr1 : ∀ i,r i<1) (n : ℕ)
    (x : EuclideanSpace ℝ (Fin (n+1)×ι)) :
    |(pathEquiv r hr hr1 n).symm.toContinuousLinearMap.det| *
      density (fun _ => 1) ((pathEquiv r hr hr1 n).symm x) =
    density (fun _ => 1) (unpack (Fin (n+1)) ι x 0) *
      ∏ t : Fin n,transition r (unpack (Fin (n+1)) ι x t.castSucc) (unpack (Fin (n+1)) ι x t.succ) := by
  have hd : (pathEquiv r hr hr1 n).symm.toContinuousLinearMap.det =
      ((∏ i,Real.sqrt (1-(r i)^2))^n)⁻¹ := by
    change (pathEquiv r hr hr1 n).toLinearEquiv.symm.toLinearMap.det=_
    rw [LinearEquiv.det_coe_symm]
    exact congrArg Inv.inv (pathEquiv_det r hr hr1 n)
  rw [hd,abs_of_nonneg (by positivity)]
  simp only [density,Fintype.prod_prod_type,Fin.prod_univ_succ,pathEquiv_symm_initial,
    pathEquiv_symm_step,transition,unpack_apply,Finset.prod_mul_distrib,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin,← Finset.prod_inv_distrib,← inv_pow]
  ring

end GaussianAR

end

section

open Matrix MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace NNReal ENNReal BigOperators
namespace GaussianAR
open GaussianKernel HeatL2 GaussianTail
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

end GaussianAR

end

end OAI
