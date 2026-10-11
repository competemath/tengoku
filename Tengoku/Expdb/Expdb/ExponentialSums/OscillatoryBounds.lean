module

public import Tengoku.Expdb.Expdb.ExponentialSums.FixedExponentialSum
public import Tengoku

import Tengoku.Expdb.Expdb.Mathlib.EulerMaclaurin
import Tengoku.Expdb.Expdb.Mathlib.IteratedDeriv

/-!
# Oscillatory integral and exponential-sum bounds

Calculus for the Fourier character and uniform estimates for `oscillatory F T N`, including a
first-derivative integral bound and Euler–Maclaurin comparisons between oscillatory sums and
integrals.
-/

@[expose] public section

open Filter Topology
open scoped ContDiff Expdb FourierTransform

noncomputable section

namespace Expdb

/-! ## Fourier-character calculus -/

/-- The real Fourier character `x ↦ 𝐞 x`, viewed as complex-valued, is smooth. -/
theorem contDiff_fourierChar : ContDiff ℝ ∞ (𝐞 · : ℝ → ℂ) := by
  rw [show (𝐞 · : ℝ → ℂ) = fun x : ℝ ↦
      Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) by
    funext x
    exact Real.fourierChar_apply x]
  have hreal : ContDiff ℝ ∞ (fun x : ℝ ↦ 2 * Real.pi * x) := by fun_prop
  exact ((Complex.ofRealCLM.contDiff.comp hreal).mul contDiff_const).cexp

/-- The `n`th derivative of the real Fourier character is
`(2πi)ⁿ 𝐞 x`. -/
theorem iteratedDeriv_fourierChar (n : ℕ) (x : ℝ) :
    iteratedDeriv n (𝐞 · : ℝ → ℂ) x =
      ((2 * Real.pi : ℂ) * Complex.I) ^ n * 𝐞 x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [iteratedDeriv_succ']
      have hderiv : deriv (𝐞 · : ℝ → ℂ) =
          fun y ↦ ((2 * Real.pi : ℂ) * Complex.I) * 𝐞 y := by
        funext y
        exact Real.deriv_fourierChar y
      rw [hderiv, iteratedDeriv_const_mul _
        (contDiff_fourierChar.contDiffAt.of_le
          (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)), ih]
      ring

/-! ## Derivative bounds for oscillatory phases -/

/-- A smooth phase remains smooth after rescaling and composition with the Fourier character. -/
theorem contDiffOn_oscillatory
    {F : ℝ → ℝ} {s : Set ℝ} {T N : ℝ} {n : ℕ}
    (hF : ContDiffOn ℝ n F phaseInterval)
    (hmap : Set.MapsTo (N⁻¹ * ·) s phaseInterval) :
    ContDiffOn ℝ n (oscillatory F T N) s := by
  have hscale : ContDiffOn ℝ n (N⁻¹ * ·) s := by fun_prop
  have hFscale : ContDiffOn ℝ n (fun x ↦ F (N⁻¹ * x)) s := by
    change ContDiffOn ℝ n (F ∘ fun x ↦ N⁻¹ * x) s
    exact hF.comp hscale hmap
  have hinner : ContDiffOn ℝ n (fun x ↦ T * F (N⁻¹ * x)) s :=
    contDiffOn_const.mul hFscale
  have heq : oscillatory F T N =
      (𝐞 · : ℝ → ℂ) ∘ fun x ↦ T * F (N⁻¹ * x) := by
    funext x
    simp only [oscillatory, Function.comp_apply, div_eq_mul_inv]
    rw [mul_comm x N⁻¹]
  rw [heq]
  exact (contDiff_fourierChar.of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).comp_contDiffOn hinner

/-! ## A first-derivative estimate for the phase integral -/

/-! ## Euler–Maclaurin bounds for oscillatory sums -/

private def oscillatoryErrorConstant (s : ℕ) : ℝ :=
  1 +
    (∑ m ∈ Finset.range s, |EulerMaclaurin.saw (m + 2) 0| *
      (2 * (((m + 1).factorial : ℝ) * (2 * Real.pi + 1) ^ (m + 1)))) +
    EulerMaclaurin.sawBound (s + 1) *
      (((s + 1).factorial : ℝ) * (2 * Real.pi + 1) ^ (s + 1))

private def oscillatorySumConstant (s : ℕ) (K c : ℝ) : ℝ :=
  oscillatoryErrorConstant s + (2 / c + K / c ^ 2)

end Expdb

end
