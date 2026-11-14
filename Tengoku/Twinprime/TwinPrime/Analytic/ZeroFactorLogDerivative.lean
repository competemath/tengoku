import Tengoku.Twinprime.TwinPrime.Analytic.HolomorphicZeroRemoval
import Tengoku.Seed.Analysis.Calculus.LogDeriv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Logarithmic derivatives after removing the actual zeros

Finite divisor support turns the factorized rational function into a finite
product. Its logarithmic derivative is the sum of the actual multiplicities
divided by the displacement from each zero. The identity then applies to
the exact holomorphic zero-removal factorization.
-/

noncomputable section

open Finset Function MeromorphicOn Filter
open scoped Topology

namespace TwinPrime.Analytic

theorem logDeriv_sub_const_zpow (u z : ℂ) (m : ℤ) :
    logDeriv (fun w : ℂ => (w - u) ^ m) z = (m : ℂ) / (z - u) := by
  have hd : HasDerivAt (fun w : ℂ => w - u) 1 z := (hasDerivAt_id z).sub_const u
  rw [logDeriv_fun_zpow hd.differentiableAt m, logDeriv_apply, hd.deriv]
  ring

/-- The finite zero-factor function is analytic at any point where its
totalized value is nonzero, even without assuming nonnegative exponents.-/
theorem analyticAt_zeroFactorPolynomial_of_ne_zero (f : ℂ → ℂ) (K : Set ℂ)
    (hK : IsCompact K) (z : ℂ) (hP : zeroFactorPolynomial f K z ≠ 0) :
    AnalyticAt ℂ (zeroFactorPolynomial f K) z := by
  have hd : (divisor f K).support.Finite := (divisor f K).finiteSupport hK
  have hdz : divisor f K z = 0 := by
    by_contra hdz
    have hfactor := congrFun (Function.FactorizedRational.extractFactor z hd) z
    apply hP
    simpa only [zeroFactorPolynomial, Pi.mul_apply, Pi.pow_apply, sub_self,
      zero_zpow _ hdz, zero_mul] using hfactor
  exact Function.FactorizedRational.analyticAt (by rw [hdz])

end TwinPrime.Analytic
