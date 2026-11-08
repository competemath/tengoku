module

public import Tengoku.Seed.Init
public import Tengoku.Seed.Analysis.Calculus.ParametricIntegral
import Tengoku.Seed.Analysis.Complex.RealDeriv
import Tengoku.Seed.Tactic.GCongr
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.NormNum
import Tengoku.Seed.Tactic.Positivity
import Tengoku.Seed.Tactic.Ring
public import Tengoku.SpherePackingExt.SpherePacking.Integration.Measure
import Tengoku.SpherePackingExt.SpherePacking.ForMathlib.DerivHelpers
import Tengoku.SpherePackingExt.SpherePacking.ForMathlib.IntegrablePowMulExp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Differentiation under the integral sign on `Ici 1`

This file provides a reusable dominated-differentiation lemma for integrals over `Ici 1`.
It is used in several magic-function developments (e.g. the `I₆'` and `J₆'` smoothness proofs).
-/

namespace SpherePacking.Integration.SmoothIntegralIciOne
noncomputable section

open scoped Topology
open Complex Real Set MeasureTheory Filter

open SpherePacking.Integration (μIciOne)

/-- The coefficient function used in the exponential weight.-/
@[expose] public def coeff (t : ℝ) : ℂ := (-Real.pi * t : ℂ)

/-- The basic integrand `t ↦ I * (hf t * exp (x * coeff t))`.-/
@[expose] public def g (hf : ℝ → ℂ) (x t : ℝ) : ℂ :=
  (Complex.I : ℂ) * (hf t * cexp ((x : ℂ) * coeff t))

/-- The auxiliary integrand `gN n`, corresponding to the `n`-th derivative in `x`.-/
@[expose] public def gN (hf : ℝ → ℂ) (n : ℕ) (x t : ℝ) : ℂ :=
  (coeff t) ^ n * g (hf := hf) x t

/-- Norm of `coeff t` on `Ici 1`.-/
public lemma coeff_norm (t : ℝ) (ht : t ∈ Set.Ici (1 : ℝ)) : ‖coeff t‖ = Real.pi * t := by
  simp [coeff, Complex.norm_real, abs_of_nonneg Real.pi_pos.le,
    abs_of_nonneg (zero_le_one.trans (by simpa [Set.mem_Ici] using ht))]

end

end SpherePacking.Integration.SmoothIntegralIciOne
