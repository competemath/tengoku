import Tengoku.WasowAsymptoticsLean.NormalFormGoal
import Tengoku.Seed.Analysis.SpecialFunctions.Integrals.Basic
import Tengoku.Seed.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Tengoku.Seed.Analysis.SpecialFunctions.ExpDeriv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms tailExtension_continuous` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms gauge_inverse` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms primitive_hasDerivAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms gauge_hasDerivAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms primitive_norm_le` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms gauge_norm_bounds` (it only prints; the queue checks the axioms of every declaration). -/

/-! Explicit scalar gauges for a continuous O(1/r) residual. Both the gauge and
its inverse are polynomially bounded; the logarithmic primitive is constructed
by an actual interval integral. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace WasowScalarGauge

def tailExtension (b : ℝ → ℂ) (R : ℝ) (r : ℝ) : ℂ := b (max R r)
def primitive (b : ℝ → ℂ) (R r : ℝ) : ℂ := ∫ s in R..r, tailExtension b R s
def gauge (b : ℝ → ℂ) (R r : ℝ) : ℂ := Complex.exp (primitive b R r)
def inverseGauge (b : ℝ → ℂ) (R r : ℝ) : ℂ := Complex.exp (-primitive b R r)

/--
@isnad1 id=continuo.1h2v.s5.0ecec7ab4064 from=translated src=- shape=06ede008 vocab=739b515c
-/
theorem tailExtension_continuous {b : ℝ → ℂ} {R : ℝ}
    (hb : ContinuousOn b (Ici R)) : Continuous (tailExtension b R) := by
  exact hb.comp_continuous (continuous_const.max continuous_id) (fun r => le_max_left R r)

/--
@isnad1 id=and.0h3v.s5.16cd5ce7163a from=translated src=- shape=0601f430 vocab=a7faa14e
-/
theorem gauge_inverse (b : ℝ → ℂ) (R r : ℝ) :
    inverseGauge b R r * gauge b R r = 1 ∧ gauge b R r * inverseGauge b R r = 1 := by
  simp [gauge, inverseGauge, Complex.exp_neg, Complex.exp_ne_zero]

/--
@isnad1 id=hasderiv.2h3v.s6.4c854ef10b87 from=translated src=- shape=b6b7ce6f vocab=6fbf72eb
-/
theorem primitive_hasDerivAt {b : ℝ → ℂ} {R r : ℝ}
    (hb : ContinuousOn b (Ici R)) (hr : R ≤ r) :
    HasDerivAt (primitive b R) (b r) r := by
  have hc := tailExtension_continuous hb
  have hd := intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable R r) hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  convert hd using 1 <;> first | rfl | simp [tailExtension, max_eq_right hr]

/--
@isnad1 id=hasderiv.2h3v.s6.581145cbf49a from=translated src=- shape=e4df2862 vocab=2bafe8e9
-/
theorem gauge_hasDerivAt {b : ℝ → ℂ} {R r : ℝ}
    (hb : ContinuousOn b (Ici R)) (hr : R ≤ r) :
    HasDerivAt (gauge b R) (b r * gauge b R r) r := by
  convert (primitive_hasDerivAt hb hr).cexp using 1 <;> first | rfl | simp [gauge, mul_comm]

/-- The residual's reciprocal bound gives a genuine logarithmic integral bound.
@isnad1 id=le.5h4v.s6.4e6ad21a20cc from=translated src=- shape=647a973a vocab=6194b4b1
-/
theorem primitive_norm_le {b : ℝ → ℂ} {R C r : ℝ}
    (hR : 1 ≤ R) (hC : 0 ≤ C) (hb : ContinuousOn b (Ici R))
    (hbound : ∀ s : ℝ, R ≤ s → ‖b s‖ ≤ C/s) (hr : R ≤ r) :
    ‖primitive b R r‖ ≤ C * Real.log r := by
  have hR0 : 0 < R := by linarith
  have hr0 : 0 < r := hR0.trans_le hr
  have hc := tailExtension_continuous hb
  have hi : IntervalIntegrable (fun s : ℝ => C/s) volume R r := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.div continuousOn_id
    intro s hs
    have hs' : s ∈ Icc R r := by simpa only [uIcc_of_le hr] using hs
    change s ≠ 0
    have hsR := hs'.1
    linarith
  calc
    ‖primitive b R r‖ ≤ ∫ s in R..r, ‖tailExtension b R s‖ :=
      intervalIntegral.norm_integral_le_integral_norm hr
    _ ≤ ∫ s in R..r, C/s := intervalIntegral.integral_mono_on hr
      (hc.norm.intervalIntegrable R r) hi (fun s hs => by
        simpa only [tailExtension, max_eq_right hs.1] using hbound s hs.1)
    _ = C * Real.log (r/R) := by
      simp only [div_eq_mul_inv, intervalIntegral.integral_const_mul,
        integral_inv_of_pos hR0 hr0]
    _ ≤ C * Real.log r := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact Real.log_le_log (div_pos hr0 hR0) (div_le_self hr0.le hR)

/-- Both directions of the explicit scalar gauge have the same polynomial bound.
@isnad1 id=and.5h4v.s7.f74bacacc69b from=translated src=- shape=780eb0f6 vocab=28fbe07a
-/
theorem gauge_norm_bounds {b : ℝ → ℂ} {R C r : ℝ}
    (hR : 1 ≤ R) (hC : 0 ≤ C) (hb : ContinuousOn b (Ici R))
    (hbound : ∀ s : ℝ, R ≤ s → ‖b s‖ ≤ C/s) (hr : R ≤ r) :
    ‖gauge b R r‖ ≤ r^C ∧ ‖inverseGauge b R r‖ ≤ r^C := by
  have hr0 : 0 < r := by linarith
  have hp := primitive_norm_le hR hC hb hbound hr
  have hexp : Real.exp (C*Real.log r) = r^C := by
    rw [Real.rpow_def_of_pos hr0, mul_comm]
  constructor
  · exact (Complex.norm_exp_le_exp_norm _).trans ((Real.exp_le_exp.mpr hp).trans_eq hexp)
  · apply (Complex.norm_exp_le_exp_norm _).trans
    rw [norm_neg]
    exact (Real.exp_le_exp.mpr hp).trans_eq hexp

end WasowScalarGauge
