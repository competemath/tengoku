import Tengoku

/-!
# Continuous PAC-Bayes change of measure

This module packages the Radon-Nikodym/tilting change-of-measure step used by
continuous-posterior PAC-Bayes certificates.
-/

namespace FormalSLT.PACBayes.ContinuousChangeOfMeasure

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {Θ : Type*} [MeasurableSpace Θ]

/--
Continuous Donsker-Varadhan variational inequality.

For probability measures `ρ ≪ π`, the posterior integral of `g` is bounded by
`KL(ρ‖π)` plus the prior log-moment of `g`.
@isnad1 id=le.4h4v.s7.d9d90c967632 from=translated src=- shape=5fcfd374 vocab=d7f5b8ea
-/
theorem continuous_donsker_varadhan
    (ρ π : Measure Θ) [IsProbabilityMeasure ρ] [IsProbabilityMeasure π]
    (hρπ : ρ ≪ π) (g : Θ → ℝ)
    (hg_exp : Integrable (fun x => Real.exp (g x)) π)
    (hg_int : Integrable g ρ)
    (h_llr : Integrable (llr ρ π) ρ) :
    ∫ x, g x ∂ρ ≤
      (InformationTheory.klDiv ρ π).toReal +
        Real.log (∫ x, Real.exp (g x) ∂π) := by
  haveI : IsProbabilityMeasure (π.tilted g) :=
    isProbabilityMeasure_tilted hg_exp
  have hπ_tilted : π ≪ π.tilted g := absolutelyContinuous_tilted hg_exp
  have hρπ_tilted : ρ ≪ π.tilted g := hρπ.trans hπ_tilted
  have h_llr_tilted : Integrable (llr ρ (π.tilted g)) ρ :=
    integrable_llr_tilted_right hρπ hg_int h_llr hg_exp
  have h_nonneg : 0 ≤ (InformationTheory.klDiv ρ (π.tilted g)).toReal :=
    ENNReal.toReal_nonneg
  have h_kl_tilted :
      (InformationTheory.klDiv ρ (π.tilted g)).toReal =
        ∫ x, llr ρ (π.tilted g) x ∂ρ := by
    rw [InformationTheory.toReal_klDiv hρπ_tilted h_llr_tilted]
    simp [measureReal_def]
  have h_kl_base :
      (InformationTheory.klDiv ρ π).toReal =
        ∫ x, llr ρ π x ∂ρ := by
    rw [InformationTheory.toReal_klDiv hρπ h_llr]
    simp [measureReal_def]
  have h_tilted_integral :
      ∫ x, llr ρ (π.tilted g) x ∂ρ =
        ∫ x, llr ρ π x ∂ρ - ∫ x, g x ∂ρ +
          Real.log (∫ x, Real.exp (g x) ∂π) := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      integral_llr_tilted_right hρπ hg_int hg_exp h_llr
  have h_identity :
      (InformationTheory.klDiv ρ (π.tilted g)).toReal =
        (InformationTheory.klDiv ρ π).toReal - ∫ x, g x ∂ρ +
          Real.log (∫ x, Real.exp (g x) ∂π) := by
    rw [h_kl_tilted, h_tilted_integral, h_kl_base]
  linarith

/--
Continuous Catoni fixed-`lambda` change-of-measure bound.

The prior log-MGF certificate is supplied in log form:
`log E_π exp(lambda * (risk - empiricalRisk)) ≤ lambda^2 * B + log(1/delta)`.
@isnad1 id=le.8h8v.s8.e567e93018c8 from=translated src=- shape=56e351e5 vocab=a9e7adcd
-/
theorem continuous_catoni_changeOfMeasure_bound
    (ρ π : Measure Θ) [IsProbabilityMeasure ρ] [IsProbabilityMeasure π]
    (hρπ : ρ ≪ π)
    (risk empiricalRisk : Θ → ℝ)
    {lambda delta B : ℝ}
    (hlambda : 0 < lambda) (hdelta : 0 < delta)
    (hrisk_int : Integrable risk ρ)
    (hempirical_int : Integrable empiricalRisk ρ)
    (hllr : Integrable (llr ρ π) ρ)
    (hmgf_int :
      Integrable (fun θ => Real.exp (lambda * (risk θ - empiricalRisk θ))) π)
    (hlog_mgf :
      Real.log
          (∫ θ, Real.exp (lambda * (risk θ - empiricalRisk θ)) ∂π)
        ≤ lambda ^ (2 : Nat) * B + Real.log (1 / delta)) :
    ∫ θ, risk θ ∂ρ ≤
      ∫ θ, empiricalRisk θ ∂ρ +
        ((InformationTheory.klDiv ρ π).toReal + Real.log (1 / delta)) / lambda +
          lambda * B := by
  have _ := hdelta
  let gap : Θ → ℝ := fun θ => lambda * (risk θ - empiricalRisk θ)
  have hgap_int : Integrable gap ρ := by
    dsimp [gap]
    exact (hrisk_int.sub hempirical_int).const_mul lambda
  have hdv :=
    continuous_donsker_varadhan ρ π hρπ gap hmgf_int hgap_int hllr
  have hgap_integral :
      ∫ θ, gap θ ∂ρ =
        lambda * (∫ θ, risk θ ∂ρ - ∫ θ, empiricalRisk θ ∂ρ) := by
    dsimp [gap]
    rw [integral_const_mul, integral_sub hrisk_int hempirical_int]
  have hgap_bound :
      lambda * (∫ θ, risk θ ∂ρ - ∫ θ, empiricalRisk θ ∂ρ) ≤
        (InformationTheory.klDiv ρ π).toReal +
          (lambda ^ (2 : Nat) * B + Real.log (1 / delta)) := by
    rw [← hgap_integral]
    linarith
  have hdiff :
      ∫ θ, risk θ ∂ρ - ∫ θ, empiricalRisk θ ∂ρ ≤
        ((InformationTheory.klDiv ρ π).toReal +
          lambda ^ (2 : Nat) * B + Real.log (1 / delta)) / lambda := by
    rw [le_div_iff₀ hlambda]
    nlinarith
  calc
    ∫ θ, risk θ ∂ρ
        = ∫ θ, empiricalRisk θ ∂ρ +
            (∫ θ, risk θ ∂ρ - ∫ θ, empiricalRisk θ ∂ρ) := by ring
    _ ≤ ∫ θ, empiricalRisk θ ∂ρ +
            ((InformationTheory.klDiv ρ π).toReal +
              lambda ^ (2 : Nat) * B + Real.log (1 / delta)) / lambda :=
        by linarith
    _ = ∫ θ, empiricalRisk θ ∂ρ +
          ((InformationTheory.klDiv ρ π).toReal + Real.log (1 / delta)) / lambda +
            lambda * B := by
        field_simp [ne_of_gt hlambda]
        ring

/-! ### Concrete non-vacuity witness -/

/-- Two-point parameter space for a concrete continuous-measure witness. -/
abbrev TwoPointParameter := Bool

/-- A Dirac prior on the two-point parameter space. -/
def twoPointPriorMeasure : Measure TwoPointParameter := Measure.dirac true

/-- A matching Dirac posterior, so the KL term is finite and equal to zero. -/
def twoPointPosteriorMeasure : Measure TwoPointParameter := Measure.dirac true

/-- A nonzero gap observable on the two-point space. -/
def twoPointGap : TwoPointParameter → ℝ := fun θ => if θ then (1 : ℝ) / 4 else 0

/-- A nonzero risk observable for the Catoni witness. -/
def twoPointRisk : TwoPointParameter → ℝ := twoPointGap

/-- Zero empirical risk for the Catoni witness. -/
def twoPointEmpiricalRisk : TwoPointParameter → ℝ := fun _ => 0

/--
@isnad1 id=isprobab.0h0v.s2.c05d8eacfb93 from=translated src=- shape=54c8eceb vocab=1d870f10
-/
instance twoPointPrior_isProbabilityMeasure :
    IsProbabilityMeasure twoPointPriorMeasure := by
  unfold twoPointPriorMeasure
  infer_instance

/--
@isnad1 id=isprobab.0h0v.s2.9a715983e02d from=translated src=- shape=54c8eceb vocab=1da145d9
-/
instance twoPointPosterior_isProbabilityMeasure :
    IsProbabilityMeasure twoPointPosteriorMeasure := by
  unfold twoPointPosteriorMeasure
  infer_instance

/-- The two-point posterior is absolutely continuous with respect to the prior.
@isnad1 id=absolute.0h0v.s2.8aafde1247e5 from=translated src=- shape=93eefbde vocab=7a9c6b65
-/
theorem twoPoint_absolutelyContinuous :
    twoPointPosteriorMeasure ≪ twoPointPriorMeasure :=
  Measure.AbsolutelyContinuous.rfl

/-- The continuous Donsker-Varadhan theorem applies to a nonzero two-point gap.
@isnad1 id=le.0h0v.s5.27ff61de4ced from=translated src=- shape=aab64561 vocab=392a719e
-/
theorem twoPoint_continuous_dv_nonvacuous :
    ∫ θ, twoPointGap θ ∂twoPointPosteriorMeasure ≤
      (InformationTheory.klDiv twoPointPosteriorMeasure twoPointPriorMeasure).toReal +
        Real.log (∫ θ, Real.exp (twoPointGap θ) ∂twoPointPriorMeasure) := by
  refine continuous_donsker_varadhan
    twoPointPosteriorMeasure twoPointPriorMeasure
    twoPoint_absolutelyContinuous twoPointGap ?_ ?_ ?_
  · simp [twoPointPriorMeasure, twoPointGap]
  · simp [twoPointPosteriorMeasure]
  · unfold twoPointPosteriorMeasure twoPointPriorMeasure
    rw [integrable_congr (llr_self (Measure.dirac true))]
    exact integrable_zero TwoPointParameter ℝ (Measure.dirac true)

/-- The two-point gap is strictly below the trivial unit bound.
@isnad1 id=lt.0h0v.s4.3bcacc5d095a from=translated src=- shape=a2f93b9d vocab=3a0374ae
-/
theorem twoPoint_gap_strictly_below_one :
    ∫ θ, twoPointGap θ ∂twoPointPosteriorMeasure < (1 : ℝ) := by
  norm_num [twoPointPosteriorMeasure, twoPointGap]

/-- The continuous Catoni theorem gives a finite nonzero two-point certificate.
@isnad1 id=le.0h0v.s6.a773c4acb5cc from=translated src=- shape=d37f8eee vocab=8cf33931
-/
theorem twoPoint_continuous_certificate_nonvacuous :
    ∫ θ, twoPointRisk θ ∂twoPointPosteriorMeasure ≤
      ∫ θ, twoPointEmpiricalRisk θ ∂twoPointPosteriorMeasure +
        ((InformationTheory.klDiv twoPointPosteriorMeasure twoPointPriorMeasure).toReal +
            Real.log (1 / (1 : ℝ))) / (1 : ℝ) +
          (1 : ℝ) * 1 := by
  refine continuous_catoni_changeOfMeasure_bound
    twoPointPosteriorMeasure twoPointPriorMeasure
    twoPoint_absolutelyContinuous twoPointRisk twoPointEmpiricalRisk
    (lambda := 1) (delta := 1) (B := 1)
    (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ ?_
  · simp [twoPointPosteriorMeasure, twoPointRisk]
  · simp [twoPointPosteriorMeasure]
  · unfold twoPointPosteriorMeasure twoPointPriorMeasure
    rw [integrable_congr (llr_self (Measure.dirac true))]
    exact integrable_zero TwoPointParameter ℝ (Measure.dirac true)
  · simp [twoPointPriorMeasure, twoPointRisk, twoPointEmpiricalRisk, twoPointGap]
  · norm_num [twoPointPriorMeasure, twoPointRisk, twoPointEmpiricalRisk, twoPointGap]

end

end FormalSLT.PACBayes.ContinuousChangeOfMeasure
