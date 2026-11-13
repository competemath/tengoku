import Tengoku.Seed.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Tengoku.Seed.MeasureTheory.Constructions.BorelSpace.Real
import Tengoku.Seed.MeasureTheory.Integral.Bochner.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Bounded-above extended logarithmic integrals

A logarithm may have an infinite negative part, in particular at zero.  Its
extended integral is expressed using a nonnegative logarithmic deficit; no
Bochner integrability of the logarithm at zero is assumed.
-/

noncomputable section

open Filter Set
open scoped ENNReal Topology

namespace MeasureTheory

/-- The nonnegative deficit below the real upper bound `c`, using the extended
logarithm with `log 0 = -∞`.-/
def logDeficit (c x : ℝ) : ℝ≥0∞ :=
  ((c : EReal) - ENNReal.log (ENNReal.ofReal x)).toENNReal

/-- The extended integral of a bounded-above logarithm on a probability space.
When `log g ≤ c`, this is the usual positive-minus-negative extended integral,
written as `c - ∫ (c - log g)`.  In particular, a nonintegrable negative part
produces `-∞`, rather than the default value of a nonintegrable Bochner integral.-/
def upperLogIntegral {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (g : α → ℝ) (c : ℝ) : EReal :=
  (c : EReal) - ((∫⁻ x, logDeficit c (g x) ∂μ) : EReal)

/--
@isnad1 id=eq.0h1v.s3.2b9d4214a8d1 from=translated src=- shape=6661a3ed vocab=c11113a5
-/
@[simp]
theorem logDeficit_zero (c : ℝ) : logDeficit c 0 = ∞ := by
  simp [logDeficit]

/-- For a positive argument the extended deficit is the nonnegative real
part of `c - log x`.
@isnad1 id=eq.1h2v.s4.add07cdb4638 from=translated src=- shape=00821be5 vocab=12433f78
-/
theorem logDeficit_of_pos (c : ℝ) {x : ℝ} (hx : 0 < x) :
    logDeficit c x = ENNReal.ofReal (c - Real.log x) := by
  rw [logDeficit, ENNReal.log_ofReal_of_pos hx, ← EReal.coe_sub,
    EReal.real_coe_toENNReal]

/-- The logarithmic deficit decreases when its argument increases.
@isnad1 id=antitone.0h1v.s3.7349a89d05c0 from=translated src=- shape=9bb0b988 vocab=6a71a6db
-/
theorem logDeficit_antitone (c : ℝ) : Antitone (logDeficit c) := by
  intro x y hxy
  exact EReal.toENNReal_le_toENNReal (EReal.sub_le_sub le_rfl
    (ENNReal.log_monotone (ENNReal.ofReal_le_ofReal hxy)))

/-- The extended deficit is continuous, including at zero where its value
is infinite.
@isnad1 id=continuo.0h1v.s3.ea2f16cf5bfd from=translated src=- shape=9bb0b988 vocab=80a35edf
-/
theorem continuous_logDeficit (c : ℝ) : Continuous (logDeficit c) := by
  have hc : Continuous (fun y : EReal => (c : EReal) - y) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    exact (EReal.continuousAt_add (Or.inl (EReal.coe_ne_top c))
      (Or.inl (EReal.coe_ne_bot c))).comp
        (continuous_const.prodMk continuous_neg).continuousAt
  exact EReal.continuous_toENNReal.comp
    (hc.comp (ENNReal.continuous_log.comp ENNReal.continuous_ofReal))

/-- The deficit of a measurable real function is measurable.
@isnad1 id=measurab.1h3v.s4.86186ff7dc12 from=translated src=- shape=9df91a0e vocab=3a9cbd36
-/
theorem _root_.Measurable.logDeficit {α : Type*} [MeasurableSpace α]
    {g : α → ℝ} (hg : Measurable g) (c : ℝ) :
    Measurable (fun x => logDeficit c (g x)) :=
  (continuous_logDeficit c).measurable.comp hg

/-- When the ordinary logarithm is integrable and bounded above, the extended
logarithmic integral agrees with its Bochner integral.
@isnad1 id=eq.3h4v.s6.5a596bc9ad41 from=translated src=- shape=6ef61554 vocab=95334c32
-/
theorem upperLogIntegral_eq_integral {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {g : α → ℝ} {c : ℝ}
    (hpos : ∀ᵐ x ∂μ, 0 < g x)
    (hlog : Integrable (fun x => Real.log (g x)) μ)
    (hle : ∀ᵐ x ∂μ, Real.log (g x) ≤ c) :
    upperLogIntegral μ g c = ((∫ x, Real.log (g x) ∂μ : ℝ) : EReal) := by
  have hnonneg : 0 ≤ᵐ[μ] fun x => c - Real.log (g x) := by
    filter_upwards [hle] with x hx using sub_nonneg.mpr hx
  have hi := (integrable_const c).sub hlog
  have heq : (∫⁻ x, logDeficit c (g x) ∂μ) =
      ENNReal.ofReal (c - ∫ x, Real.log (g x) ∂μ) := by
    calc
      _ = ∫⁻ x, ENNReal.ofReal (c - Real.log (g x)) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hpos] with x hx using logDeficit_of_pos c hx
      _ = ENNReal.ofReal (c - ∫ x, Real.log (g x) ∂μ) := by
        simpa only [Pi.sub_apply, integral_sub (integrable_const c) hlog, integral_const,
          probReal_univ, one_smul] using
          (ofReal_integral_eq_lintegral_ofReal hi hnonneg).symm
  have hnonnegint : 0 ≤ c - ∫ x, Real.log (g x) ∂μ := by
    simpa only [Pi.sub_apply, integral_sub (integrable_const c) hlog, integral_const,
      probReal_univ, one_smul] using integral_nonneg_of_ae hnonneg
  rw [upperLogIntegral, heq, EReal.coe_ennreal_ofReal,
    max_eq_left hnonnegint, ← EReal.coe_sub]
  congr 1
  ring

/-- If `g = 0` almost everywhere, its extended logarithmic integral is `-∞`.
@isnad1 id=eq.1h4v.s5.9085e694d09e from=translated src=- shape=82ac8d24 vocab=72f5bc29
-/
theorem upperLogIntegral_eq_bot_of_ae_zero {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {g : α → ℝ} (c : ℝ)
    (hg : g =ᵐ[μ] 0) : upperLogIntegral μ g c = ⊥ := by
  have hdef : (fun x => logDeficit c (g x)) =ᵐ[μ] fun _ => ∞ := by
    filter_upwards [hg] with x hx
    simp [hx]
  simp [upperLogIntegral, lintegral_congr_ae hdef]

end MeasureTheory
