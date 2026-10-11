import Tengoku.OpenaiMath.OAI.Probability.GaussianReplacement.RowOrder

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory

def arrayReference {d k : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows k d)) : ℝ≥0∞ :=
  conditionalReferenceKL (observationSignalLaw P).fst (gaussianObservations k d)

lemma freshArrayLaw_assoc_first {d k r : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows k d)) [IsProbabilityMeasure P] :
    ((freshArrayLaw (observationSignalLaw P) r).map MeasurableEquiv.prodAssoc).map
      (Prod.map id Prod.fst) = (observationSignalLaw P).fst := by
  rw [Measure.map_map (measurable_id.prodMap measurable_fst) MeasurableEquiv.prodAssoc.measurable]
  change (freshArrayLaw (observationSignalLaw P) r).fst = _
  rw [freshArrayLaw_fst]

def baselineCost (d k : ℕ) : ℝ≥0∞ :=
  klDiv (projectionJoint (uniformSphere d) (gaussianRows k d))
    ((gaussianRows k d).prod (gaussianLabels k))

def hybridBaselineConstant : ℝ := 20 + |Real.log (normalizer 1)+1/2|

lemma hybridBaselineConstant_pos : 0 < hybridBaselineConstant := by
  unfold hybridBaselineConstant
  positivity

lemma nextActualRowLaw_signal_row {d m : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P]
    (ν : Measure (Sphere d)) [IsProbabilityMeasure ν]
    (hInd : (P.map swapLast).fst = ν.prod (gaussianRows m d)) (i : ℕ) (hi : i < m) :
    (nextActualRowLaw P i hi).map (fun z => (z.1.2,z.2)) = ν.prod (stdGaussian (Vector d)) := by
  have he := congrArg (fun μ : Measure (Sphere d×Rows m d) => μ.map (Prod.map id (fun X => X ⟨i,hi⟩))) hInd
  rw [←Measure.map_prod_map _ _ measurable_id (measurable_pi_apply _),Measure.map_id] at he
  have hev : (gaussianRows m d).map (fun X => X ⟨i,hi⟩) = stdGaussian (Vector d) :=
    (measurePreserving_eval (fun _ : Fin m => stdGaussian (Vector d)) ⟨i,hi⟩).map_eq
  rw [hev] at he
  rw [nextActualRowLaw,Measure.map_map (measurable_fst.snd.prodMk measurable_snd) (measurable_nextActualRow hi)]
  rw [Measure.fst,Measure.map_map measurable_fst swapLast.measurable,
    Measure.map_map (measurable_id.prodMap (measurable_pi_apply _)) (measurable_fst.comp swapLast.measurable)] at he
  exact he

lemma gaussian_sphere_inner_mixture {d : ℕ} (ν : Measure (Sphere d)) [IsProbabilityMeasure ν] :
    (ν.prod (stdGaussian (Vector d))).map (fun z => ⟪(z.1:Vector d),z.2⟫) = gaussianReal 0 1 := by
  ext t ht
  rw [Measure.map_apply (by fun_prop) ht,Measure.prod_apply (ht.preimage (by fun_prop))]
  have he (s : Sphere d) : stdGaussian (Vector d) {x | ⟪(s:Vector d),x⟫ ∈ t} = gaussianReal 0 1 t := by
    have h := congrArg (fun μ : Measure ℝ => μ t) (gaussian_inner_map_sphere s)
    rwa [Measure.map_apply (by fun_prop) ht] at h
  change (∫⁻ s : Sphere d, stdGaussian (Vector d) {x | ⟪(s:Vector d),x⟫ ∈ t} ∂ν) = _
  simp_rw [he]
  simp

lemma nextActualRowLaw_label {d m : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P]
    (ν : Measure (Sphere d)) [IsProbabilityMeasure ν]
    (hInd : (P.map swapLast).fst = ν.prod (gaussianRows m d)) (i : ℕ) (hi : i < m) (r : ℕ) :
    (residualLabelLaw (nextActualRowLaw P i hi) r).snd = gaussianReal 0 1 := by
  rw [residualLabelLaw,Measure.snd,Measure.map_map measurable_snd measurable_residualLabelObservation]
  have hel : Measurable (fun z : ((W×Observations i d)×Sphere d)×Vector d => ⟪(z.1.2:Vector d),z.2⟫) := by fun_prop
  change ((nextActualRowLaw P i hi).prod (gaussianRows r d)).map ((fun z => ⟪(z.1.2:Vector d),z.2⟫) ∘ Prod.fst) = _
  rw [←Measure.map_map hel measurable_fst,←Measure.fst,Measure.fst_prod]
  have he := congrArg (fun μ : Measure (Sphere d×Vector d) => μ.map (fun z => ⟪(z.1:Vector d),z.2⟫))
    (nextActualRowLaw_signal_row P ν hInd i hi)
  rw [Measure.map_map (by fun_prop) (measurable_fst.snd.prodMk measurable_snd),gaussian_sphere_inner_mixture] at he
  exact he

end CurrentProjection

end

end OAI
