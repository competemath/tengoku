import Tengoku.Twinprime.TwinPrime.Analytic.MiddlePrimeSieveThreshold
import Tengoku.Twinprime.TwinPrime.Analytic.MiddlePrimeSieveAsymptotic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The actual power-cutoff middle-prime sieve

The explicit integer thresholds satisfy the geometric conditions of the
finite sieve. The entire weighted remainder is negligible, and the
remaining normalized upper bound has one explicit prime main sum.
-/

noncomputable section

open Finset Filter Topology

namespace TwinPrime.Analytic

def middlePrimePowerMainSum (a v : ℝ) (X : ℕ) : ℝ :=
  ∑ q ∈ (Ioc (primaryCutoff X) (middlePrimePowerCutoff v X)).filter Nat.Prime,
    Real.log ((2 * X : ℝ) / q) /
      ((Nat.totient q : ℝ) * Real.log (middlePrimeSieveThreshold a X q))

/--
@isnad1 id=le.2h2v.s5.c66f1f8bd4c0 from=translated src=- shape=9946dde9 vocab=64b7bcb6
-/
theorem middlePrimePowerCutoff_le_input (v : ℝ) (hv : v ≤ 1)
    (X : ℕ) (hX : 1 ≤ X) : middlePrimePowerCutoff v X ≤ X := by
  apply Nat.floor_le_of_le
  exact Real.rpow_le_self_of_one_le (by exact_mod_cast hX) hv

end TwinPrime.Analytic
