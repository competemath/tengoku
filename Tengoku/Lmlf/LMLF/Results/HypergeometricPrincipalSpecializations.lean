import Tengoku.Lmlf.LMLF.ODE.Hypergeometric.Principal
import Tengoku.Seed.Analysis.Analytic.Binomial

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Principal Gauss hypergeometric specializations

This file identifies the principal specialization `F(a, 1; 1; z)` with the principal complex
power and records its geometric-series specialization.
-/

open Filter Metric Set
open scoped ComplexOrder Topology

namespace LMLF.Definitions

private theorem one_ne_neg_natCast (n : ℕ) : (1 : ℂ) ≠ -(n : ℂ) := by
  intro h
  have hreal := congrArg Complex.re h
  have hn : (0 : ℝ) ≤ n := by positivity
  norm_num at hreal
  linarith

private theorem natCast_ne_neg_one (n : ℕ) : (n : ℂ) ≠ -(1 : ℂ) := by
  intro h
  have hreal := congrArg Complex.re h
  have hn : (0 : ℝ) ≤ n := by positivity
  norm_num at hreal
  linarith

private theorem gaussHypergeometricSeriesSum_one_one
    (a : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    gaussHypergeometricSeriesSum a 1 1 z = (1 - z) ^ (-a) := by
  have hseries :
      binomialSeries ℂ (-a) =
        (ordinaryHypergeometricSeries ℂ a 1 1).compContinuousLinearMap
          (-ContinuousLinearMap.id ℂ ℂ) := by
    simpa only [neg_neg] using
      (binomialSeries_eq_ordinaryHypergeometricSeries
        (𝔸 := ℂ) (a := -a) (b := (1 : ℂ)) natCast_ne_neg_one)
  have hgauss :
      HasFPowerSeriesOnBall
        (fun x : ℂ ↦ gaussHypergeometricSeriesSum a 1 1 (-x))
        (binomialSeries ℂ (-a)) 0 1 := by
    have hbase :
        HasFPowerSeriesOnBall
          (gaussHypergeometricSeriesSum a 1 1)
          (ordinaryHypergeometricSeries ℂ a 1 1)
          ((-ContinuousLinearMap.id ℂ ℂ) (0 : ℂ)) 1 := by
      simpa only [map_zero] using
        (gaussHypergeometricSeriesSum_hasFPowerSeriesOnBall
          (a := a) (b := (1 : ℂ)) (c := (1 : ℂ)) one_ne_neg_natCast)
    have hcomp :=
      hbase.compContinuousLinearMap
          (u := -ContinuousLinearMap.id ℂ ℂ) (x := (0 : ℂ))
    simpa [Function.comp_def, hseries, enorm_eq_nnnorm,
      ContinuousLinearMap.nnnorm_id] using hcomp
  have hbinomial :
      HasFPowerSeriesOnBall (fun x : ℂ ↦ (1 + x) ^ (-a))
        (binomialSeries ℂ (-a)) 0 1 :=
    Complex.one_add_cpow_hasFPowerSeriesOnBall_zero
  have hball : (-z) ∈ Metric.eball (0 : ℂ) (1 : ENNReal) := by
    rw [← ENNReal.ofReal_one, Metric.eball_ofReal]
    simpa using hz
  have hsumGauss := hgauss.hasSum hball
  have hsumBinomial := hbinomial.hasSum hball
  simpa only [zero_add, neg_neg, sub_eq_add_neg] using hsumGauss.unique hsumBinomial

/-- The principal specialization `F(a, 1; 1; z)` is the principal power `(1 - z) ^ (-a)`.
@isnad1 id=eq.1h2v.s5.8f086ffbf21d from=translated src=- shape=3a82af57 vocab=c544fc27
-/
theorem gaussHypergeometric_one_one
    (a : ℂ) {z : ℂ} (hz : z ∈ gaussHypergeometricDomain) :
    gaussHypergeometric a 1 1 z = (1 - z) ^ (-a) := by
  let v : ℂ → ℂ := fun w ↦ (1 - w) ^ (-a)
  have hv : AnalyticOnNhd ℂ v gaussHypergeometricDomain := by
    dsimp only [v]
    apply (analyticOnNhd_const.sub analyticOnNhd_id).cpow analyticOnNhd_const
    intro w hw
    rw [Complex.mem_slitPlane_iff_not_le_zero]
    change ¬(1 - w ≤ 0)
    rw [sub_nonpos]
    simpa only [gaussHypergeometricDomain, Set.mem_compl_iff, Set.mem_Ici] using hw
  have hvgerm : Set.EqOn v (gaussHypergeometricSeriesSum a 1 1) (Metric.ball 0 1) := by
    intro w hw
    exact (gaussHypergeometricSeriesSum_one_one a (by simpa using hw)).symm
  exact gaussHypergeometric_eqOn_of_eqOn_seriesSum a 1 1 one_ne_neg_natCast hv hvgerm hz

/-- At denominator parameter one, the regularized principal function agrees with the ordinary
principal specialization.
@isnad1 id=eq.1h2v.s5.936f750850fe from=translated src=- shape=3a82af57 vocab=eda0cd68
-/
theorem regularizedGaussHypergeometric_one_one
    (a : ℂ) {z : ℂ} (hz : z ∈ gaussHypergeometricDomain) :
    regularizedGaussHypergeometric a 1 1 z = (1 - z) ^ (-a) := by
  have hquotient := gaussHypergeometric_div_Gamma a 1 1 one_ne_neg_natCast z
  rw [gaussHypergeometric_one_one a hz, Complex.Gamma_one, div_one] at hquotient
  exact hquotient.symm

/-- The principal Gauss function `F(1, 1; 1; z)` is the reciprocal of `1 - z`.
@isnad1 id=eq.1h1v.s5.c63018a953e4 from=translated src=- shape=4bbea949 vocab=5147eb17
-/
theorem gaussHypergeometric_geometric
    {z : ℂ} (hz : z ∈ gaussHypergeometricDomain) :
    gaussHypergeometric 1 1 1 z = (1 - z)⁻¹ := by
  simpa only [neg_one_mul, Complex.cpow_neg_one] using
    (gaussHypergeometric_one_one (1 : ℂ) hz)

/-- Inside the unit disk, the geometric series sums to the principal Gauss specialization.
@isnad1 id=hassum.1h1v.s6.276bd25559a3 from=translated src=- shape=46120cb5 vocab=787e7c4b
-/
theorem hasSum_gaussHypergeometric_geometric
    {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ ↦ z ^ n) (gaussHypergeometric 1 1 1 z) := by
  have hzDomain : z ∈ gaussHypergeometricDomain := by
    rw [mem_gaussHypergeometricDomain_iff]
    right
    exact lt_of_le_of_lt (Complex.re_le_norm z) hz
  simpa only [gaussHypergeometric_geometric hzDomain] using
    (hasSum_geometric_of_norm_lt_one hz)

end LMLF.Definitions
