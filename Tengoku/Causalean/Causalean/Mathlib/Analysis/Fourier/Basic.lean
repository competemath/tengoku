module
public import Tengoku

/-!
# Weighted inverse-Fourier energies

Reusable real-line energies with Lebesgue measure. The Fourier convention used by the
other modules is Mathlib's `𝓕⁻ G(v) = ∫ ξ, exp(2π i ξv) G(ξ)`, so its unweighted
Plancherel constant is one and its quadratic moment constant is `(2π)⁻²`.
-/

@[expose] public section

noncomputable section
open MeasureTheory
namespace Causalean.Mathlib.Analysis.Fourier

/-- [The ordinary squared L² energy](goal) of [a complex-valued function on the real line](hyp:g) is [the Lebesgue integral of its squared modulus](step:1). -/
def energy (g : ℝ → ℂ) : ℝ := ∫ v, ‖g v‖ ^ 2

/-- [The weighted squared L² energy](goal) for [a moment exponent](hyp:κ) and [a complex-valued function on the real line](hyp:g) is [the Lebesgue integral weighted by the κ-th power of distance from zero](step:1). -/
def weightedEnergy (κ : ℝ) (g : ℝ → ℂ) : ℝ := ∫ v, |v| ^ κ * ‖g v‖ ^ 2

/-- [A complex-valued function on the real line](hyp:g) has [nonnegative ordinary squared L² energy](goal).
@isnad1 id=le.0h1v.s3.a4b052f6f4de from=translated src=- shape=e456648f vocab=ed01fea2
-/
theorem energy_nonneg (g : ℝ → ℂ) : 0 ≤ energy g :=
  integral_nonneg fun _ => sq_nonneg _

/-- [A moment exponent](hyp:κ) and [a complex-valued function on the real line](hyp:g) have [nonnegative weighted squared L² energy](goal).
@isnad1 id=le.0h2v.s4.8293f771a07d from=translated src=- shape=eaf3a031 vocab=6450685f
-/
theorem weightedEnergy_nonneg (κ : ℝ) (g : ℝ → ℂ) : 0 ≤ weightedEnergy κ g :=
  integral_nonneg fun v => mul_nonneg (Real.rpow_nonneg (abs_nonneg v) κ) (sq_nonneg _)

/-- [A complex-valued function on the real line](hyp:g) has [weighted energy at exponent zero equal to its ordinary squared L² energy](goal).
@isnad1 id=eq.0h1v.s4.6bc960659c66 from=translated src=- shape=abb51f10 vocab=5475bd06
-/
theorem weightedEnergy_zero (g : ℝ → ℂ) : weightedEnergy 0 g = energy g := by
  simp [weightedEnergy, energy]

/-- [A complex-valued function on the real line](hyp:g) has [weighted energy at exponent two equal to its squared-distance weighted integral](goal).
@isnad1 id=eq.0h1v.s6.84f7852f6d49 from=translated src=- shape=a2b69964 vocab=96414918
-/
theorem weightedEnergy_two (g : ℝ → ℂ) :
    weightedEnergy 2 g = ∫ v, v ^ 2 * ‖g v‖ ^ 2 := by
  simp [weightedEnergy, sq_abs]

end Causalean.Mathlib.Analysis.Fourier
