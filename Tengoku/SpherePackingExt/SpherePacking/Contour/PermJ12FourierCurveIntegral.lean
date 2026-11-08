module

public import Tengoku.Seed.Analysis.Distribution.SchwartzSpace.Fourier
public import Tengoku.Seed.MeasureTheory.Integral.CurveIntegral.Basic

import Tengoku.Seed.MeasureTheory.Integral.Prod

public import Tengoku.SpherePackingExt.SpherePacking.ForMathlib.ScalarOneForm
public import Tengoku.SpherePackingExt.SpherePacking.Contour.Segments
public import Tengoku.SpherePackingExt.SpherePacking.Integration.Measure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Fourier transform as a curve integral (template lemmas)

These lemmas implement the common Fubini argument used in the `perm_J1/J2` developments (both
Dim8 and Dim24):
1. rewrite `𝓕 Jⱼ` using `fourier_eq'`;
2. express the radial profile as a `t`-integral of a kernel;
3. swap the order of integration via `MeasureTheory.integral_integral_swap`;
4. evaluate the inner `x`-integral to obtain a function of the segment parameter `t`;
5. identify the resulting `t`-integral with a curve integral on a segment.

The dimension-specific files only need to provide:
- the "phase * radial profile = t-integral of the kernel" bridge lemma;
- an `Integrable` hypothesis for Fubini; and
- a lemma identifying the `t`-integral with the desired curve integral.
-/

open scoped FourierTransform RealInnerProductSpace Complex
open MeasureTheory
open MagicFunction

namespace SpherePacking.Contour

noncomputable section

private lemma cexp_neg_two_pi_inner_mul_I
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (x w : V) :
    cexp (-(2 * (↑Real.pi : ℂ) * (↑⟪x, w⟫ : ℂ) * Complex.I)) =
      cexp (↑(-2 * Real.pi * ⟪x, w⟫) * Complex.I) := by
  simp [mul_assoc]

/-! ### `μIoc01` segment integral helpers -/

end

end SpherePacking.Contour
