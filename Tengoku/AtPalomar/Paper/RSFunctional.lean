module

public import Tengoku.AtPalomar.Paper.Gaussian
public import Tengoku.AtPalomar.Paper.Variational
public import Tengoku.Seed.MeasureTheory.Measure.ProbabilityMeasure
public import Tengoku.Seed.MeasureTheory.Measure.Support
public import Tengoku.Seed.Analysis.SpecialFunctions.Integrals.Basic
public import Tengoku.Seed.Analysis.SpecialFunctions.Log.Deriv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-!
# Concrete Parisi measures and replica-symmetric functional

`ParisiMeasure` is the actual type of probability measures on `[0,1]`.
The functional is parameterized by a potential `u`; this file does not claim
that an arbitrary supplied potential is the weak Parisi PDE solution.
-/

open Set MeasureTheory

namespace Paper

abbrev Overlap := Set.Icc (0 : ℝ) 1
abbrev ParisiMeasure := ProbabilityMeasure Overlap

/-- The real cumulative mass of a probability measure on `[0,1]`.-/
noncomputable def parisiCDF (μ : ParisiMeasure) (s : ℝ) : ℝ :=
  ((μ : Measure Overlap) {t : Overlap | (t : ℝ) ≤ s}).toReal

/--
@isnad1 id=le.0h2v.s4.299a7a2af944 from=translated src=- shape=787c1379 vocab=e66e9643
-/
theorem parisiCDF_nonneg (μ : ParisiMeasure) (s : ℝ) : 0 ≤ parisiCDF μ s :=
  ENNReal.toReal_nonneg

/-- The cumulative masses are monotone because the threshold sets are nested.
@isnad1 id=monotone.0h1v.s3.dc5454d4c3bb from=translated src=- shape=8735051e vocab=9a7ba7be
-/
theorem parisiCDF_monotone (μ : ParisiMeasure) : Monotone (parisiCDF μ) := by
  intro s t hst
  apply ENNReal.toReal_mono (measure_ne_top (μ : Measure Overlap) _)
  exact measure_mono (fun x hx => hx.trans hst)

/-- Probability mass bounds the CDF by one.
@isnad1 id=le.0h2v.s4.b1a40d02e8bb from=translated src=- shape=4f17ad3b vocab=e66e9643
-/
theorem parisiCDF_le_one (μ : ParisiMeasure) (s : ℝ) : parisiCDF μ s ≤ 1 := by
  have hle : (μ : Measure Overlap) {t : Overlap | (t : ℝ) ≤ s} ≤ 1 := by
    calc
      (μ : Measure Overlap) {t : Overlap | (t : ℝ) ≤ s} ≤ (μ : Measure Overlap) univ :=
        measure_mono (subset_univ _)
      _ = 1 := measure_univ
  simpa only [parisiCDF, ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top hle

/-- The correction integrand is genuinely integrable for every Parisi measure.
@isnad1 id=interval.0h3v.s5.e9fabaec632f from=translated src=- shape=eaf0fc5f vocab=3fe88600
-/
theorem parisiCorrection_intervalIntegrable (μ : ParisiMeasure) (a b : ℝ) :
    IntervalIntegrable (fun s => s * parisiCDF μ s) volume a b := by
  have hc : IntervalIntegrable (parisiCDF μ) volume a b :=
    (parisiCDF_monotone μ).intervalIntegrable
  simpa only [id_eq, mul_comm] using hc.mul_continuousOn (continuous_id.continuousOn)

/-- The actual Parisi functional of the supplied potential family.-/
noncomputable def parisiFunctional (β h : ℝ) (u : ParisiMeasure → ℝ → ℝ → ℝ)
    (μ : ParisiMeasure) : ℝ :=
  Real.log 2 + u μ 0 h - β ^ 2 / 2 * ∫ s in 0..1, s * parisiCDF μ s

/-- Explicit hard-side potential; identifying it with a weak solution would
require the separate PDE existence/uniqueness argument.-/
noncomputable def rsHardPotential (β t x : ℝ) : ℝ :=
  β ^ 2 / 2 * (1 - t) + Real.log (Real.cosh x)

/-- Explicit soft-side Gaussian potential.-/
noncomputable def rsSoftPotential (β q t x : ℝ) : ℝ :=
  β ^ 2 / 2 * (1 - q) + gaussianExpectation
    (fun z => Real.log (Real.cosh (x + β * Real.sqrt (q - t) * z)))

/-- The Gaussian expectation in the soft explicit formula is integrable.
@isnad1 id=integrab.0h4v.s6.a5d1749ff5b9 from=translated src=- shape=b31a9d3d vocab=8375bfd7
-/
theorem rsSoftPotential_integrable (β q t x : ℝ) :
    Integrable (fun z => Real.log (Real.cosh (x + β * Real.sqrt (q - t) * z)))
      (ProbabilityTheory.gaussianReal 0 1) := by
  exact integrable_gaussian_logcosh_affine x (β * Real.sqrt (q - t))

/-- The two explicit potential formulas agree at the interface.
@isnad1 id=eq.0h3v.s4.79bf26407ad8 from=translated src=- shape=4e4f5e66 vocab=81c69eba
-/
theorem rsPotential_interface (β q x : ℝ) :
    rsSoftPotential β q q x = rsHardPotential β q x := by
  simp [rsSoftPotential, rsHardPotential]

/--
@isnad1 id=eq.0h2v.s4.46b2568dad96 from=translated src=- shape=3326c922 vocab=5a6dfffb
-/
@[simp] theorem rsHardPotential_terminal (β x : ℝ) :
    rsHardPotential β 1 x = Real.log (Real.cosh x) := by
  simp [rsHardPotential]

/--
@isnad1 id=hasderiv.0h1v.s5.35860a802c01 from=translated src=- shape=ef4ab573 vocab=089f1363
-/
lemma hasDerivAt_log_cosh (x : ℝ) :
    HasDerivAt (fun y => Real.log (Real.cosh y)) (Real.tanh x) x := by
  simpa only [Real.tanh_eq_sinh_div_cosh] using
    (Real.hasDerivAt_cosh x).log (ne_of_gt (Real.cosh_pos x))

/-- The hard-side spatial derivative is the actual `tanh`.
@isnad1 id=hasderiv.0h3v.s5.cc24b627b4f4 from=translated src=- shape=1c986f5e vocab=d466559a
-/
theorem hasDerivAt_rsHardPotential_spatial (β t x : ℝ) :
    HasDerivAt (rsHardPotential β t) (Real.tanh x) x := by
  exact (hasDerivAt_log_cosh x).const_add (β ^ 2 / 2 * (1 - t))

/--
@isnad1 id=eq.0h3v.s5.bde0c8affdc9 from=translated src=- shape=07efcdb6 vocab=ac0ab065
-/
@[simp] theorem deriv_rsHardPotential_spatial (β t x : ℝ) :
    deriv (rsHardPotential β t) x = Real.tanh x :=
  (hasDerivAt_rsHardPotential_spatial β t x).deriv

/-- The soft explicit formula supplies exactly the required time-zero value.
@isnad1 id=eq.0h3v.s6.3aec7ad4b55d from=translated src=- shape=2883914c vocab=691f1774
-/
theorem rsSoftPotential_zero (β h q : ℝ) :
    rsSoftPotential β q 0 h = β ^ 2 / 2 * (1 - q) +
      gaussianExpectation (fun z => Real.log (Real.cosh (gaussianField β h q z))) := by
  unfold rsSoftPotential gaussianField
  simp only [sub_zero]
  congr 2
  funext z
  rw [add_comm]

end Paper
