module
public import Tengoku.SpherePackingExt.SpherePacking.ForMathlib.IntegrablePowMulExp
public import Tengoku.SpherePackingExt.SpherePacking.ForMathlib.DerivHelpers
public import Tengoku.Seed.Analysis.Complex.RealDeriv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Integrability for `J₆'`-type integrands

This file provides a reusable integrability lemma for the `J₆'`-type integrands on `Ici 1`.
-/

namespace SpherePacking.Integration

noncomputable section

open Complex Real Set MeasureTheory Filter

/-- The `n`-th `x`-derivative integrand appearing in `J₆'`-type formulas.-/
@[expose] public def gN_J6_integrand (f : ℝ → ℂ) (n : ℕ) (x : ℝ) : ℝ → ℂ :=
  fun t : ℝ =>
    ((-Real.pi * t : ℂ) ^ n) *
      ((Complex.I : ℂ) * (f t * cexp ((x : ℂ) * (-Real.pi * t : ℂ))))

end

end SpherePacking.Integration
