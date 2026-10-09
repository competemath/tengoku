module
public import Tengoku.Causalean.Causalean.Mathlib.Analysis.Fourier.AngularFourier
public import Tengoku.Causalean.Causalean.Mathlib.Analysis.Fourier.AngularFourierWeakDerivative

/-!
# Angular Fourier Sobolev energies

This module combines angular Plancherel with weak coordinate multipliers to identify the
zero- and first-order Fourier energies of compactly supported functions. It includes the
real slice interface, finite energy bounds, and exact dimension-two specializations.
-/

public section

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Causalean.Mathlib.Analysis.Fourier
variable {p : ℕ}

/-- The first-order angular density of an L1 function is a nonnegative
measurable real function. -/
@[fun_prop]
theorem firstEnergy_density_measurable (G : Space p → ℂ) (hG : Integrable G volume) :
    Measurable (fun w => ‖angularFourier G w‖ ^ 2 * (1 + ‖w‖ ^ 2 / (p : ℝ))) := by
  have hF := angularFourier_measurable G hG
  fun_prop

/-- The first-order angular energy splits into zero-order energy plus the
dimensionally averaged sum of coordinate-weighted energies, including infinite
energies; only L1 and positive dimension are needed for this splitting.

Use `norm_sq_eq_sum_coordinates` and distribute multiplication by the squared
transform norm. Convert the pointwise nonnegative identity with
`ENNReal.ofReal_add`, `ENNReal.ofReal_mul`, and
`ENNReal.ofReal_sum_of_nonneg`. Commute the finite sum and integral with
`lintegral_finsetSum`, the constant with `lintegral_const_mul'`, and the
addition with `lintegral_add_left`. Continuity from L1 supplies every
measurability premise. Do not require finite energies for this splitting.
-/
theorem firstEnergy_eq_coordinate_sum (hp : 1 ≤ p) (G : Space p → ℂ)
    (hG : Integrable G volume) :
    firstEnergy G = zeroEnergy G + ENNReal.ofReal ((p : ℝ)⁻¹) *
      ∑ r : Fin p, ∫⁻ w, ENNReal.ofReal (‖angularFourier G w‖ ^ 2 * (w r) ^ 2) := by
  classical
  have hF := angularFourier_measurable G hG
  have hzero : Measurable (fun w => ENNReal.ofReal (‖angularFourier G w‖ ^ 2)) := by
    fun_prop
  have hcoord (r : Fin p) : Measurable (fun w : Space p =>
      ENNReal.ofReal (‖angularFourier G w‖ ^ 2 * (w r) ^ 2)) := by
    fun_prop
  have hdensity (w : Space p) :
      ‖angularFourier G w‖ ^ 2 * (1 + ‖w‖ ^ 2 / (p : ℝ)) =
      ‖angularFourier G w‖ ^ 2 + (p : ℝ)⁻¹ *
        ∑ r : Fin p, ‖angularFourier G w‖ ^ 2 * (w r) ^ 2 := by
    rw [norm_sq_eq_sum_coordinates, ← Finset.mul_sum]
    ring
  have henn (w : Space p) :
      ENNReal.ofReal (‖angularFourier G w‖ ^ 2 * (1 + ‖w‖ ^ 2 / (p : ℝ))) =
      ENNReal.ofReal (‖angularFourier G w‖ ^ 2) + ENNReal.ofReal ((p : ℝ)⁻¹) *
        ∑ r : Fin p, ENNReal.ofReal (‖angularFourier G w‖ ^ 2 * (w r) ^ 2) := by
    rw [hdensity, ENNReal.ofReal_add (sq_nonneg _) (by positivity),
      ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_sum_of_nonneg (fun r _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))]
  unfold firstEnergy zeroEnergy l2Energy
  simp_rw [henn]
  rw [lintegral_add_left hzero,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_finsetSum Finset.univ (fun r _ => hcoord r)]

variable {p : ℕ}

end Causalean.Mathlib.Analysis.Fourier
