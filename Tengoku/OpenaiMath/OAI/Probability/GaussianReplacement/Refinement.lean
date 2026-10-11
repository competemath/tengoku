import Tengoku.OpenaiMath.OAI.Probability.GaussianReplacement.Information

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory

lemma mutualInformation_map_right_le {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] (P : Measure (A×B)) [IsProbabilityMeasure P]
    (f : B → C) (hf : Measurable f) :
    mutualInformation (P.map (Prod.map id f)) ≤ mutualInformation P := by
  have hT : Measurable (Prod.map (id : A→A) f) := measurable_id.prodMap hf
  have hfst : (P.map (Prod.map id f)).fst = P.fst := by
    rw [Measure.fst,Measure.map_map measurable_fst hT]; rfl
  have hsnd : (P.map (Prod.map id f)).snd = P.snd.map f := by
    rw [Measure.snd,Measure.snd,Measure.map_map measurable_snd hT,Measure.map_map hf measurable_snd]; rfl
  have hRef : (P.fst.prod P.snd).map (Prod.map id f) = P.fst.prod (P.snd.map f) := by
    rw [←Measure.map_prod_map _ _ measurable_id hf,Measure.map_id]
  unfold mutualInformation
  rw [hfst,hsnd,←hRef]
  exact klDiv_map_le _ _ hT

lemma critical_moment_log_bound {d ℓ : ℕ} (hd : 1 ≤ d) (hℓ : ℓ ≤ d)
    (q t s : ℝ) (hs : 0 ≤ s) (hb : 0 ≤ q+(ℓ:ℝ)*Real.log 4+t) :
    Real.log (1+momentBound 9 d (Real.exp (q+(ℓ:ℝ)*Real.log 4+t))
      (Real.exp s*(3*4^d))) ≤ (q+t)+18*d+Real.log (1+s) := by
  let b := q+(ℓ:ℝ)*Real.log 4+t
  let B := Real.exp b
  let D := Real.exp s*(3*4^d)
  let M := momentBound 9 d B D
  have hB : 0 < B := Real.exp_pos _
  have hD : 0 < D := by dsimp [D]; positivity
  have hB1 : 1 ≤ B := Real.one_le_exp_iff.mpr hb
  have hlog4 : Real.log 4 ≤ 3 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)]
  have hlog3 : Real.log 3 ≤ 2 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)]
  have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hlogD : Real.log D ≤ s+2+3*d := by
    dsimp only [D]
    rw [Real.log_mul (Real.exp_pos _).ne' (by positivity),Real.log_exp,
      Real.log_mul (by norm_num : (3:ℝ) ≠ 0) (by positivity),Real.log_pow]
    nlinarith [Nat.cast_nonneg (α:=ℝ) d]
  have hmax : max (Real.log (D/B)) 0 ≤ s+2+3*d := by
    apply max_le _ (by positivity)
    rw [Real.log_div hD.ne' hB.ne',show Real.log B=b from Real.log_exp b]
    linarith
  have hu : 0 < 1+max (Real.log (D/B)) 0 := by positivity
  have hM : 0 < M := by dsimp [M,momentBound]; positivity
  have hM1 : 1 ≤ M := by
    have hExp : 1 ≤ Real.exp (9*(d:ℝ)) := Real.one_le_exp_iff.mpr (by positivity)
    have hU : 1 ≤ 1+max (Real.log (D/B)) 0 := le_add_of_nonneg_right (le_max_right _ _)
    dsimp only [M,momentBound]
    calc
      1 = 1*1*1 := by ring
      _ ≤ Real.exp (9*(d:ℝ))*B*(1+max (Real.log (D/B)) 0) :=
        mul_le_mul (mul_le_mul hExp hB1 (by norm_num) (by positivity)) hU (by norm_num) (by positivity)
  have hupp : Real.log (1+max (Real.log (D/B)) 0) ≤ 2+3*d+Real.log (1+s) := by
    have hprod : 1+max (Real.log (D/B)) 0 ≤ (3+3*(d:ℝ))*(1+s) := by
      nlinarith [Nat.cast_nonneg (α:=ℝ) d]
    have hh := Real.log_le_log hu hprod
    rw [Real.log_mul (by positivity) (by positivity)] at hh
    have hc : Real.log (3+3*(d:ℝ)) ≤ 2+3*d := by
      linarith [Real.log_le_sub_one_of_pos (by positivity : (0:ℝ)<3+3*(d:ℝ))]
    linarith
  have hh : Real.log (1+M) ≤ Real.log 2+Real.log M := by
    have hh := Real.log_le_log (by positivity : 0<1+M) (show 1+M ≤ 2*M by linarith)
    rwa [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hM.ne'] at hh
  have hmLog : Real.log M = 9*(d:ℝ)+b+Real.log (1+max (Real.log (D/B)) 0) := by
    dsimp only [M,momentBound]
    rw [Real.log_mul (by positivity) hu.ne',Real.log_mul (Real.exp_pos _).ne' hB.ne',
      Real.log_exp,show Real.log B=b from Real.log_exp b]
  rw [hmLog] at hh
  change Real.log (1+M) ≤ _
  have hd' : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hl' : (ℓ:ℝ) ≤ d := by exact_mod_cast hℓ
  dsimp only [b] at hh
  nlinarith [Nat.cast_nonneg (α:=ℝ) ℓ]

lemma integrable_log_one_add_real {A : Type*} [MeasurableSpace A]
    (μ : Measure A) {f : A → ℝ} (hf : Integrable f μ)
    (hm : Measurable f) (h0 : ∀ᵐ x ∂μ, 0 ≤ f x) :
    Integrable (fun x => Real.log (1+f x)) μ := by
  apply hf.mono' (measurable_const.add hm |>.log.aestronglyMeasurable)
  filter_upwards [h0] with x hx
  change ‖Real.log (1+f x)‖ ≤ f x
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg (by linarith))]
  linarith [Real.log_le_sub_one_of_pos (by linarith : 0<1+f x)]

lemma integral_log_one_add_real_le {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] {f : A → ℝ} (hf : Integrable f μ)
    (hm : Measurable f) (h0 : ∀ᵐ x ∂μ, 0 ≤ f x) :
    (∫ x, Real.log (1+f x) ∂μ) ≤ Real.log (1+∫ x, f x ∂μ) := by
  have hLi := integrable_log_one_add_real μ hf hm h0
  let M := 1+∫ x, f x ∂μ
  have hM : 0<M := by dsimp only [M]; linarith [integral_nonneg_of_ae h0]
  have hb : ∀ᵐ x ∂μ, Real.log (1+f x) ≤ Real.log M+(1+f x)/M-1 := by
    filter_upwards [h0] with x hx
    have hh := Real.log_le_sub_one_of_pos (show 0<(1+f x)/M by positivity)
    rw [Real.log_div (by positivity) hM.ne'] at hh
    linarith
  have h1f : Integrable (fun x => 1+f x) μ := (integrable_const 1).add hf
  have hdiv : Integrable (fun x => (1+f x)/M) μ := h1f.div_const M
  have hsum : Integrable (fun x => Real.log M+(1+f x)/M) μ := (integrable_const _).add hdiv
  have hi : Integrable (fun x => Real.log M+(1+f x)/M-1) μ := hsum.sub (integrable_const 1)
  have hb' := integral_mono_ae hLi hi hb
  rw [integral_sub hsum (integrable_const 1),integral_add (integrable_const (Real.log M)) hdiv,
    integral_div,integral_add (integrable_const 1) hf] at hb'
  simp only [integral_const,probReal_univ,one_smul] at hb'
  change _ ≤ Real.log M at ⊢
  have he : (1+∫ x, f x ∂μ)/M=1 := div_self hM.ne'
  rw [he] at hb'
  linarith

lemma refineSignal_probability {S W E : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [MeasurableSpace E] (P : Measure (S×W)) [IsProbabilityMeasure P]
    (e : S×W → E) (he : Measurable e) : IsProbabilityMeasure (refineSignal P e) := by
  unfold refineSignal
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_fst.prodMk (measurable_snd.prodMk he)).aemeasurable).mpr inferInstance

lemma refineSignal_fst {S W E : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [MeasurableSpace E] (P : Measure (S×W)) (e : S×W → E) (he : Measurable e) :
    (refineSignal P e).fst = P.fst := by
  rw [refineSignal,Measure.fst,Measure.map_map measurable_fst
    (measurable_fst.prodMk (measurable_snd.prodMk he))]
  rfl

lemma refineSignal_snd_fst {S W E : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [MeasurableSpace E] (P : Measure (S×W)) (e : S×W → E) (he : Measurable e) :
    (refineSignal P e).snd.fst = P.snd := by
  rw [refineSignal,Measure.fst,Measure.snd,Measure.map_map measurable_fst measurable_snd,
    Measure.map_map (measurable_fst.comp measurable_snd)
      (measurable_fst.prodMk (measurable_snd.prodMk he))]
  rfl

lemma refineSignal_snd_snd {S W E : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [MeasurableSpace E] (P : Measure (S×W)) (e : S×W → E) (he : Measurable e) :
    (refineSignal P e).snd.snd = P.map e := by
  rw [refineSignal,Measure.snd,Measure.snd,Measure.map_map measurable_snd measurable_snd,
    Measure.map_map (measurable_snd.comp measurable_snd)
      (measurable_fst.prodMk (measurable_snd.prodMk he))]
  rfl

def refinementLoss {S W E : Type*} [MeasurableSpace S] [MeasurableSpace W] [MeasurableSpace E]
    (P : Measure (S×W)) (e : S×W → E) (v : W×E) : ℝ :=
  -Real.log ((refineSignal P e).snd {v}).toReal + Real.log (P.snd {v.1}).toReal

lemma refinementLoss_nonneg {S W E : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [MeasurableSpace E] [MeasurableSingletonClass W] [MeasurableSingletonClass E]
    (P : Measure (S×W)) [IsProbabilityMeasure P] (e : S×W → E) (he : Measurable e)
    {v : W×E} (hv : (refineSignal P e).snd {v} ≠ 0) : 0 ≤ refinementLoss P e v := by
  have hh : (refineSignal P e).snd {v} ≤ P.snd {v.1} := by
    rw [←refineSignal_snd_fst P e he,Measure.fst_apply (measurableSet_singleton _)]
    exact measure_mono (by intro x hx; have hx' : x=v := hx; simp only [mem_preimage,mem_singleton_iff,hx'])
  have hl := Real.log_le_log (ENNReal.toReal_pos hv (measure_ne_top _ _))
    (ENNReal.toReal_mono (measure_ne_top _ _) hh)
  dsimp only [refinementLoss]
  linarith

lemma refinementLoss_eq {S W E : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [MeasurableSpace E] [StandardBorelSpace S] [Nonempty S]
    [MeasurableSingletonClass W] [MeasurableSingletonClass E]
    (P : Measure (S×W)) [IsProbabilityMeasure P] (e : S×W → E) (he : Measurable e)
    {v : W×E} (hv : (refineSignal P e).snd {v} ≠ 0) :
    refinementLoss P e v = -Real.log (messagePosterior P v.1 {x | e (x,v.1)=v.2}).toReal := by
  have hw := refineSignal_positive_original P e he hv
  have hmass := refineSignal_mass P e he hw v.2
  have hη : messagePosterior P v.1 {x | e (x,v.1)=v.2} ≠ 0 := by
    intro hz
    rw [hmass,hz,mul_zero] at hv
    exact hv rfl
  unfold refinementLoss
  rw [hmass,ENNReal.toReal_mul,Real.log_mul
    (ENNReal.toReal_ne_zero.mpr ⟨hw,measure_ne_top _ _⟩)
    (ENNReal.toReal_ne_zero.mpr ⟨hη,measure_ne_top _ _⟩)]
  ring

lemma refinement_entropy_and_loss {S W E : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [MeasurableSpace E] [Countable W] [Countable E]
    [MeasurableSingletonClass W] [MeasurableSingletonClass E]
    (P : Measure (S×W)) [IsProbabilityMeasure P] (e : S×W → E) (he : Measurable e)
    (hW : shannonEntropy P.snd ≠ ∞) (hE : shannonEntropy (P.map e) ≠ ∞) :
    shannonEntropy (refineSignal P e).snd ≠ ∞ ∧
    (shannonEntropy (refineSignal P e).snd).toReal ≤ (shannonEntropy P.snd).toReal +
      (shannonEntropy (P.map e)).toReal ∧
    Integrable (refinementLoss P e) (refineSignal P e).snd ∧
    (∫ v, refinementLoss P e v ∂(refineSignal P e).snd) ≤ (shannonEntropy (P.map e)).toReal := by
  let := refineSignal_probability P e he
  obtain ⟨hHW,hbound⟩ := shannonEntropy_subadd (refineSignal P e).snd
    (by rwa [refineSignal_snd_fst P e he]) (by rwa [refineSignal_snd_snd P e he])
  rw [refineSignal_snd_fst P e he,refineSignal_snd_snd P e he] at hbound
  have hpi := entropy_finite_integrable (refineSignal P e).snd hHW
  have hwi : Integrable (fun v : W×E => -Real.log (P.snd {v.1}).toReal) (refineSignal P e).snd := by
    apply (integrable_map_measure (measurable_of_countable
      (fun w : W => -Real.log (P.snd {w}).toReal)).aestronglyMeasurable measurable_fst.aemeasurable).mp
    change Integrable _ (refineSignal P e).snd.fst
    rw [refineSignal_snd_fst P e he]
    exact entropy_finite_integrable P.snd hW
  have hloss : Integrable (refinementLoss P e) (refineSignal P e).snd := by
    convert hpi.sub hwi using 1
    ext v
    simp [refinementLoss]
  refine ⟨hHW,hbound,hloss,?_⟩
  have heq : (∫ v, refinementLoss P e v ∂(refineSignal P e).snd) =
      (shannonEntropy (refineSignal P e).snd).toReal - (shannonEntropy P.snd).toReal := by
    have hfun : refinementLoss P e = (fun v => -Real.log ((refineSignal P e).snd {v}).toReal -
        -Real.log (P.snd {v.1}).toReal) := by funext v; simp [refinementLoss]
    rw [hfun,integral_sub hpi hwi,integral_surprisal]
    have hh : (∫ v : W×E, -Real.log (P.snd {v.1}).toReal ∂(refineSignal P e).snd) =
        (shannonEntropy P.snd).toReal := by
      rw [←integral_map measurable_fst.aemeasurable (measurable_of_countable
        (fun w => -Real.log (P.snd {w}).toReal)).aestronglyMeasurable]
      change (∫ w, -Real.log (P.snd {w}).toReal ∂(refineSignal P e).snd.fst) = _
      rw [refineSignal_snd_fst P e he,integral_surprisal]
    rw [hh]
  linarith

lemma refineSignal_snd {S W E : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [MeasurableSpace E] (P : Measure (S×W)) (e : S×W → E) (he : Measurable e) :
    (refineSignal P e).snd = P.map (fun p => (p.2,e p)) := by
  rw [refineSignal,Measure.snd,Measure.map_map measurable_snd
    (measurable_fst.prodMk (measurable_snd.prodMk he))]
  rfl

end CurrentProjection

end

end OAI
