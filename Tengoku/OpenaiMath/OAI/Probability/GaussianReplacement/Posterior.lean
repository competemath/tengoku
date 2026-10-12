import Tengoku.OpenaiMath.OAI.Probability.GaussianReplacement.Refinement

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory

def criticalSignal {d : ℕ} {W : Type*} [MeasurableSpace W] [Nonempty (Sphere d)]
    (P : Measure (Sphere d×W)) [IsFiniteMeasure P] (ℓ : ℕ) : Measure (Sphere d×(W×(ℕ×ℤ))) :=
  refineSignal P (criticalRefinement P ℓ)

instance criticalSignal_probability {d : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] [Nonempty (Sphere d)]
    (P : Measure (Sphere d×W)) [IsProbabilityMeasure P] (ℓ : ℕ) :
    IsProbabilityMeasure (criticalSignal P ℓ) :=
  refineSignal_probability P _ (measurable_criticalRefinement P ℓ)

def criticalB {d : ℕ} {W : Type*} [MeasurableSpace W] [Nonempty (Sphere d)]
    (P : Measure (Sphere d×W)) [IsFiniteMeasure P] (ℓ : ℕ) (v : W×(ℕ×ℤ)) : ℝ :=
  Real.exp ((v.2.2:ℝ)+(ℓ:ℝ)*Real.log 4+refinementLoss P (criticalRefinement P ℓ) v)

def criticalD {d : ℕ} {W : Type*} [MeasurableSpace W] [Nonempty (Sphere d)]
    (P : Measure (Sphere d×W)) [IsFiniteMeasure P] (ℓ : ℕ) (v : W×(ℕ×ℤ)) : ℝ :=
  Real.exp (-Real.log ((criticalSignal P ℓ).snd {v}).toReal)*(3*4^d)

lemma criticalSignal_fst {d : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] [Nonempty (Sphere d)]
    (P : Measure (Sphere d×W)) [IsProbabilityMeasure P] (ℓ : ℕ) :
    (criticalSignal P ℓ).fst = P.fst :=
  refineSignal_fst P _ (measurable_criticalRefinement P ℓ)

lemma criticalSignal_posterior {d ℓ : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] [Nonempty (Sphere d)]
    (P : Measure (Sphere d×W)) [IsProbabilityMeasure P]
    {v : W×(ℕ×ℤ)} (hv : (criticalSignal P ℓ).snd {v} ≠ 0) :
    messagePosterior (criticalSignal P ℓ) v = criticalPosterior (messagePosterior P v.1) ℓ v.2.1 v.2.2 ∧
    0 < messagePosterior P v.1 (criticalClass (messagePosterior P v.1) ℓ v.2.1 v.2.2) ∧
    P.snd {v.1} ≠ 0 := by
  have he := measurable_criticalRefinement P ℓ
  have hw := refineSignal_positive_original P _ he hv
  have hc : {s : Sphere d | criticalRefinement P ℓ (s,v.1) = v.2} =
      criticalClass (messagePosterior P v.1) ℓ v.2.1 v.2.2 := by
    ext s
    simp only [criticalRefinement,criticalClass,mem_ofPred_eq,Prod.ext_iff]
  have hmass := refineSignal_mass P _ he hw v.2
  rw [hc] at hmass
  change (criticalSignal P ℓ).snd {v} = _ at hmass
  have hη : messagePosterior P v.1 (criticalClass (messagePosterior P v.1) ℓ v.2.1 v.2.2) ≠ 0 := by
    intro hz
    rw [hmass,hz,mul_zero] at hv
    exact hv rfl
  refine ⟨?_,hη.bot_lt,hw⟩
  have hp := messagePosterior_refinement P _ he hv
  rw [hc] at hp
  exact hp

lemma criticalB_eq {d ℓ : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] [Nonempty (Sphere d)]
    (P : Measure (Sphere d×W)) [IsProbabilityMeasure P]
    {v : W×(ℕ×ℤ)} (hv : (criticalSignal P ℓ).snd {v} ≠ 0) :
    criticalB P ℓ v = (4:ℝ)^ℓ * Real.exp (v.2.2:ℝ) /
      (messagePosterior P v.1 (criticalClass (messagePosterior P v.1) ℓ v.2.1 v.2.2)).toReal := by
  have he := measurable_criticalRefinement P ℓ
  have hc : {s : Sphere d | criticalRefinement P ℓ (s,v.1) = v.2} =
      criticalClass (messagePosterior P v.1) ℓ v.2.1 v.2.2 := by
    ext s
    simp only [criticalRefinement,criticalClass,mem_ofPred_eq,Prod.ext_iff]
  have hδ := refinementLoss_eq P _ he hv
  rw [hc] at hδ
  have hη := (criticalSignal_posterior P hv).2.1
  have hηr := ENNReal.toReal_pos hη.ne' (measure_ne_top _ _)
  unfold criticalB
  rw [hδ,Real.exp_add,Real.exp_add,Real.exp_neg,Real.exp_log hηr,
    ←Real.log_pow,Real.exp_log (by positivity : (0:ℝ)<4^ℓ)]
  ring

lemma criticalD_eq {d ℓ : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] [Nonempty (Sphere d)]
    (P : Measure (Sphere d×W)) [IsProbabilityMeasure P]
    {v : W×(ℕ×ℤ)} (hv : (criticalSignal P ℓ).snd {v} ≠ 0) :
    criticalD P ℓ v = ((criticalSignal P ℓ).snd {v}).toReal⁻¹*(3*4^d) := by
  rw [criticalD,Real.exp_neg,Real.exp_log (ENNReal.toReal_pos hv (measure_ne_top _ _))]

lemma criticalFamily_growth {d ℓ : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] [Nonempty (Sphere d)]
    (P : Measure (Sphere d×W)) [IsProbabilityMeasure P] (hσ : P.fst = uniformSphere d)
    (hℓ : ℓ < d-1) {v : W×(ℕ×ℤ)} (hv : (criticalSignal P ℓ).snd {v} ≠ 0) :
    LocalGrowth (messagePosterior (criticalSignal P ℓ) v) ℓ (criticalB P ℓ v) ∧
    LocalGrowth (messagePosterior (criticalSignal P ℓ) v) (d-1) (criticalD P ℓ v) ∧
    0 ≤ (v.2.2:ℝ)+(ℓ:ℝ)*Real.log 4+refinementLoss P (criticalRefinement P ℓ) v ∧
    messagePosterior (criticalSignal P ℓ) v ≪ uniformSphere d := by
  obtain ⟨hpost,hη,hw⟩ := criticalSignal_posterior P hv
  have hd : 1 ≤ d := by omega
  have hg := posterior_sphere_growth P hσ hd hw
  let D := (P.snd {v.1}).toReal⁻¹*(3*4^d)
  have hD : 1 ≤ D := by
    have ha := ENNReal.toReal_pos hw (measure_ne_top _ _)
    have ha1 : (P.snd {v.1}).toReal ≤ 1 := by
      exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (by simpa using (prob_le_one : P.snd {v.1} ≤ 1))
    have hinv : 1 ≤ (P.snd {v.1}).toReal⁻¹ := (one_le_inv₀ ha).mpr ha1
    have hp : (1:ℝ) ≤ 4^d := one_le_pow₀ (by norm_num)
    dsimp only [D]
    nlinarith
  have hsigma : (criticalSignal P ℓ).fst = uniformSphere d := (criticalSignal_fst P ℓ).trans hσ
  refine ⟨?_,?_,?_,?_⟩
  · rw [hpost,criticalB_eq P hv]
    exact criticalPosterior_growth (messagePosterior P v.1) D (by linarith) hg hℓ v.2.2 hη
  · rw [criticalD_eq P hv]
    exact posterior_sphere_growth (criticalSignal P ℓ) hsigma hd hv
  · obtain ⟨s,hs⟩ := nonempty_of_measure_ne_zero hη.ne'
    have hq := (criticalLevel_bounds (messagePosterior P v.1) D hD hg hℓ s).1
    rw [hs.2] at hq
    have hl4 : 1 ≤ Real.log 4 := by
      have hh : Real.log 4 = 2*Real.log 2 := by
        have hh := (Real.log_pow (2:ℝ) 2)
        norm_num at hh ⊢
        exact hh
      linarith [Real.log_two_gt_d9]
    have ht := refinementLoss_nonneg P _ (measurable_criticalRefinement P ℓ) hv
    nlinarith [Nat.cast_nonneg (α:=ℝ) ℓ]
  · have hh := messagePosterior_le (criticalSignal P ℓ) hv
    rw [hsigma] at hh
    exact hh.absolutelyContinuous.trans Measure.smul_absolutelyContinuous

lemma criticalLevel_integrable {d ℓ : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] [Nonempty (Sphere d)]
    (P : Measure (Sphere d×W)) [IsProbabilityMeasure P] (hσ : P.fst = uniformSphere d)
    (hℓ : ℓ < d-1) (hH : shannonEntropy P.snd ≠ ∞) :
    Integrable (fun v : W×(ℕ×ℤ) => (v.2.2:ℝ)) (criticalSignal P ℓ).snd := by
  let e := criticalRefinement P ℓ
  have he := measurable_criticalRefinement P ℓ
  have hw : Integrable (fun p : Sphere d×W => -Real.log (P.snd {p.2}).toReal) P :=
    (integrable_map_measure (measurable_of_countable _).aestronglyMeasurable measurable_snd.aemeasurable).mp
      (entropy_finite_integrable P.snd hH)
  have hbi : Integrable (fun p : Sphere d×W => 20*((d:ℝ)+1-Real.log (P.snd {p.2}).toReal)) P := by
    convert ((integrable_const ((d:ℝ)+1)).add hw).const_mul 20 using 1
    first
      | (all_goals grind; done)
      | (all_goals simp_all; done)
      | (all_goals aesop; done)
      | (all_goals omega; done)
      | (all_goals norm_num; done)
      | (all_goals positivity; done)
      | (all_goals linarith; done)
      | (all_goals decide; done)
      | (all_goals tauto; done)
  have hqi : Integrable (fun p => ((e p).2:ℝ)) P := by
    apply hbi.mono' ((measurable_of_countable (fun x : ℕ×ℤ => (x.2:ℝ))).comp he).aestronglyMeasurable
    have hp := (ae_map_iff measurable_snd.aemeasurable ((Set.to_countable _).measurableSet)).mp
      (ae_positive_atom P.snd)
    filter_upwards [hp] with p hp
    have hb := criticalRefinement_size P hσ hℓ hp
    change ‖((e p).2:ℝ)‖ ≤ _
    rw [Real.norm_eq_abs]
    have habs : |((e p).2:ℝ)| = ((e p).2.natAbs:ℝ) := by simp
    rw [habs]
    change ((e p).1:ℝ)+2*((e p).2.natAbs:ℝ) ≤ _ at hb
    nlinarith [Nat.cast_nonneg (α:=ℝ) (e p).1,Nat.cast_nonneg (α:=ℝ) (e p).2.natAbs]
  change Integrable _ (refineSignal P e).snd
  rw [refineSignal_snd P e he]
  exact (integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
    (measurable_snd.prodMk he).aemeasurable).mpr hqi

lemma completeFamily_restrict_apply {W T : Type*} [MeasurableSpace W]
    (π : Measure W) (f : W → T) (t₀ : T) {w : W} (hw : π {w} ≠ 0) :
    completeFamily π (fun v => f v.1) t₀ w = f w := by
  have hp : 0 < π {w} := pos_iff_ne_zero.mpr hw
  rw [completeFamily, dite_eq_left hp]

lemma completeFamily_restrict_ae {W T : Type*} [MeasurableSpace W] [Countable W]
    [MeasurableSingletonClass W] (π : Measure W) (f : W → T) (t₀ : T) :
    completeFamily π (fun v => f v.1) t₀ =ᵐ[π] f := by
  filter_upwards [ae_positive_atom π] with w hw
  exact completeFamily_restrict_apply π f t₀ hw

def refineRows {d m : ℕ} {W E : Type*} [MeasurableSpace W] [MeasurableSpace E]
    (P : Measure ((Sphere d×W)×Rows m d)) (e : Sphere d×W → E) :
    Measure ((Sphere d×(W×E))×Rows m d) :=
  P.map (fun p => ((p.1.1,(p.1.2,e p.1)),p.2))

lemma measurable_refineRowsMap {d m : ℕ} {W E : Type*} [MeasurableSpace W] [MeasurableSpace E]
    (e : Sphere d×W → E) (he : Measurable e) :
    Measurable (fun p : (Sphere d×W)×Rows m d => ((p.1.1,(p.1.2,e p.1)),p.2)) :=
  (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk (he.comp measurable_fst))).prodMk measurable_snd

lemma refineRows_probability {d m : ℕ} {W E : Type*} [MeasurableSpace W] [MeasurableSpace E]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P]
    (e : Sphere d×W → E) (he : Measurable e) : IsProbabilityMeasure (refineRows P e) := by
  unfold refineRows
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_refineRowsMap e he).aemeasurable).mpr inferInstance

lemma refineRows_fst {d m : ℕ} {W E : Type*} [MeasurableSpace W] [MeasurableSpace E]
    (P : Measure ((Sphere d×W)×Rows m d)) (e : Sphere d×W → E) (he : Measurable e) :
    (refineRows P e).fst = refineSignal P.fst e := by
  rw [refineRows,Measure.fst,refineSignal,Measure.fst,
    Measure.map_map measurable_fst (measurable_refineRowsMap e he),
    Measure.map_map (measurable_fst.prodMk (measurable_snd.prodMk he)) measurable_fst]
  rfl

lemma refineRows_signal_rows {d m : ℕ} {W E : Type*} [MeasurableSpace W] [MeasurableSpace E]
    (P : Measure ((Sphere d×W)×Rows m d)) (e : Sphere d×W → E) (he : Measurable e) :
    ((refineRows P e).map swapLast).fst = (P.map swapLast).fst := by
  rw [Measure.fst,Measure.fst,Measure.map_map measurable_fst swapLast.measurable,
    Measure.map_map measurable_fst swapLast.measurable,refineRows,
    Measure.map_map (measurable_fst.comp swapLast.measurable) (measurable_refineRowsMap e he)]
  rfl

lemma refineRows_drop {d m : ℕ} {W E : Type*} [MeasurableSpace W] [MeasurableSpace E]
    (P : Measure ((Sphere d×W)×Rows m d)) (e : Sphere d×W → E) (he : Measurable e) :
    (refineRows P e).map (fun p => ((p.1.1,p.1.2.1),p.2)) = P := by
  rw [refineRows,Measure.map_map
    ((measurable_fst.fst.prodMk measurable_fst.snd.fst).prodMk measurable_snd)
    (measurable_refineRowsMap e he)]
  exact Measure.map_id

lemma independent_refineSignal_drop {d k : ℕ} {W E : Type*} [MeasurableSpace W] [MeasurableSpace E]
    (P : Measure (Sphere d×W)) [IsFiniteMeasure P] (e : Sphere d×W → E) (he : Measurable e) :
    ((refineSignal P e).prod (gaussianRows k d)).map (fun p => ((p.1.1,p.1.2.1),p.2)) =
      P.prod (gaussianRows k d) := by
  let : IsFiniteMeasure (refineSignal P e) := Measure.isFiniteMeasure_map _ _
  have hb : (refineSignal P e).map (fun p => (p.1,p.2.1)) = P := by
    rw [refineSignal,Measure.map_map (measurable_fst.prodMk measurable_snd.fst)
      (measurable_fst.prodMk (measurable_snd.prodMk he))]
    exact Measure.map_id
  have hh := Measure.map_prod_map (refineSignal P e) (gaussianRows k d)
    (measurable_fst.prodMk measurable_snd.fst) measurable_id
  rw [Measure.map_id,hb] at hh
  exact hh.symm

lemma signal_marginal_of_independence {S W G : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [MeasurableSpace G] (P : Measure ((S×W)×G)) (ν : Measure S)
    (γ : Measure G) [IsProbabilityMeasure γ] [SFinite ν]
    (hInd : (P.map swapLast).fst = ν.prod γ) : P.fst.fst = ν := by
  have hh := congrArg Measure.fst hInd
  rw [Measure.fst_prod] at hh
  convert hh using 1
  simp only [Measure.fst,Measure.map_map measurable_fst measurable_fst,
    Measure.map_map measurable_fst swapLast.measurable,
    Measure.map_map measurable_fst (measurable_fst.comp swapLast.measurable)]
  rfl

end CurrentProjection

end

end OAI
