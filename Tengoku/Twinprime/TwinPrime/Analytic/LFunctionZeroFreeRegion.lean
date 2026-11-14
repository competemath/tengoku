import Tengoku.Twinprime.TwinPrime.Analytic.LFunctionQuadraticZeroFree
import Tengoku.Twinprime.TwinPrime.Analytic.LFunctionNearOneZeros

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A primitive L-function zero-free region with a possible real exception

The budget combines both character-square cases and the near-one rectangle.
The remaining zero, if present, is quadratic, real, simple, and unique for
the given primitive character. No lower bound for its distance from one
is asserted here.
-/

noncomputable section

open Metric MeromorphicOn

namespace TwinPrime.Analytic

def primitiveZeroFreeBudget (q : ℕ) (t : ℝ) : ℝ :=
  nonquadraticZeroFreeBudget q t + quadraticZeroFreeBudget q t + 4 * nearOneZeroBudget q

def primitiveZeroFreeWidth (q : ℕ) (t : ℝ) : ℝ := 1 / (40 * primitiveZeroFreeBudget q t)

/--
@isnad1 id=and.0h2v.s5.66a53802ea9e from=translated src=- shape=4ae7e106 vocab=304c2296
-/
theorem primitiveZeroFreeBudget_bounds (q : ℕ) (t : ℝ) :
    120 ≤ primitiveZeroFreeBudget q t ∧
      nonquadraticZeroFreeBudget q t ≤ primitiveZeroFreeBudget q t ∧
      quadraticZeroFreeBudget q t ≤ primitiveZeroFreeBudget q t ∧
      4 * nearOneZeroBudget q ≤ primitiveZeroFreeBudget q t := by
  have hn := nonquadraticZeroFreeBudget_ge q t
  have hq := quadraticZeroFreeBudget_ge q t
  have hK := primitiveLFunctionLogBudget_nonneg q 0
  have hnear : 40 ≤ nearOneZeroBudget q := by unfold nearOneZeroBudget; linarith
  unfold primitiveZeroFreeBudget
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/--
@isnad1 id=lt.0h2v.s4.b2c3ab686d2d from=translated src=- shape=787c1379 vocab=11b839bc
-/
theorem primitiveZeroFreeWidth_pos (q : ℕ) (t : ℝ) :
    0 < primitiveZeroFreeWidth q t := by
  have h := (primitiveZeroFreeBudget_bounds q t).1
  unfold primitiveZeroFreeWidth
  positivity

/--
@isnad1 id=le.0h2v.s5.d0474692a422 from=translated src=- shape=c12cb093 vocab=0cc02aaa
-/
theorem primitiveZeroFreeWidth_le_nonquadratic (q : ℕ) (t : ℝ) :
    primitiveZeroFreeWidth q t ≤ 1 / (20 * nonquadraticZeroFreeBudget q t) := by
  have hn := nonquadraticZeroFreeBudget_ge q t
  have hR := (primitiveZeroFreeBudget_bounds q t).2.1
  unfold primitiveZeroFreeWidth
  apply one_div_le_one_div_of_le (by linarith : 0 < 20 * nonquadraticZeroFreeBudget q t)
  linarith

/--
@isnad1 id=le.0h2v.s3.38aad81462a8 from=translated src=- shape=7c82f523 vocab=99911928
-/
theorem primitiveZeroFreeWidth_le_nearOne (q : ℕ) (t : ℝ) :
    primitiveZeroFreeWidth q t ≤ nearOneZeroWidth q := by
  have hK := primitiveLFunctionLogBudget_nonneg q 0
  have hnear : 40 ≤ nearOneZeroBudget q := by unfold nearOneZeroBudget; linarith
  have hR := (primitiveZeroFreeBudget_bounds q t).2.2.2
  unfold primitiveZeroFreeWidth nearOneZeroWidth
  apply one_div_le_one_div_of_le (by linarith : 0 < 16 * nearOneZeroBudget q)
  linarith

/--
@isnad1 id=le.0h2v.s5.227b6c7f0c82 from=translated src=- shape=8b746c74 vocab=bd3624fd
-/
theorem primitiveZeroFreeHeight_le_nearOne (q : ℕ) (t : ℝ) :
    1 / (4 * primitiveZeroFreeBudget q t) ≤ nearOneZeroWidth q := by
  have hK := primitiveLFunctionLogBudget_nonneg q 0
  have hnear : 40 ≤ nearOneZeroBudget q := by unfold nearOneZeroBudget; linarith
  have hR := (primitiveZeroFreeBudget_bounds q t).2.2.2
  unfold nearOneZeroWidth
  apply one_div_le_one_div_of_le (by linarith : 0 < 16 * nearOneZeroBudget q)
  linarith

end TwinPrime.Analytic
