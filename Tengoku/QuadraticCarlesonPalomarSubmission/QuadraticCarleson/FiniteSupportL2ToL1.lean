import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.HilbertPoissonFourier
import Tengoku.Seed.MeasureTheory.Function.LpSeminorm.Indicator

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Filter MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson

set_option autoImplicit false

/-- Cauchy--Schwarz on a common finite-measure support.  This is the
quantitative step converting an `L²` approximation into an `L¹`
approximation without changing its support.
@isnad1 id=le.4h2v.s8.930472249e37 from=translated src=- shape=d0dc1477 vocab=70583207
-/
theorem integral_norm_le_sqIntegral_mul_measureReal_sqrt
    {f : ℝ → ℂ} {s : Set ℝ} (hs : MeasurableSet s)
    (hμs : volume s ≠ ∞) (hf : MemLp f 2 volume)
    (hfs : ∀ᵐ x ∂volume, x ∉ s → f x = 0) :
    ∫ x, ‖f x‖ ≤
      (∫ x, ‖f x‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
        (volume.real s) ^ (1 / (2 : ℝ)) := by
  let g : ℝ → ℂ := s.indicator (fun _ ↦ 1)
  have hg : MemLp g 2 volume := memLp_indicator_const 2 hs 1 (Or.inr hμs)
  have hf' : MemLp f (ENNReal.ofReal 2) volume := by simpa using hf
  have hg' : MemLp g (ENNReal.ofReal 2) volume := by simpa using hg
  have hholder := integral_mul_norm_le_Lp_mul_Lq
    (p := (2 : ℝ)) (q := (2 : ℝ)) Real.HolderConjugate.two_two hf' hg'
  have hnorm : ∀ᵐ x ∂volume, ‖f x‖ = ‖f x‖ * ‖g x‖ := by
    filter_upwards [hfs] with x hx
    by_cases hxs : x ∈ s
    · simp [g, hxs]
    · simp [g, hxs, hx hxs]
  have hgint : (∫ x, ‖g x‖ ^ (2 : ℝ)) = volume.real s := by
    calc
      _ = ∫ x in s, (1 : ℝ) := by
        rw [← integral_indicator hs]
        congr 1
        funext x
        by_cases hx : x ∈ s <;> simp [g, hx]
      _ = _ := by simp [Measure.real]
  rw [integral_congr_ae hnorm]
  rw [hgint] at hholder
  exact hholder

/-- Difference form used for a common-support approximation sequence.
@isnad1 id=le.6h3v.s8.78368e306aa8 from=translated src=- shape=4ea6e5e9 vocab=c2c8a96d
-/
theorem integral_norm_sub_le_sqIntegral_mul_measureReal_sqrt
    {f g : ℝ → ℂ} {s : Set ℝ} (hs : MeasurableSet s)
    (hμs : volume s ≠ ∞) (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (hfs : ∀ᵐ x ∂volume, x ∉ s → f x = 0)
    (hgs : ∀ᵐ x ∂volume, x ∉ s → g x = 0) :
    ∫ x, ‖f x - g x‖ ≤
      (∫ x, ‖f x - g x‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
        (volume.real s) ^ (1 / (2 : ℝ)) := by
  apply integral_norm_le_sqIntegral_mul_measureReal_sqrt hs hμs (hf.sub hg)
  filter_upwards [hfs, hgs] with x hfx hgx hx
  simp only [Pi.sub_apply, hfx hx, hgx hx, sub_zero]

end QuadraticCarleson
