/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Tengoku.Causalean.Causalean.Mathlib.Analysis.Duality.MomentPrior.Basic
public import Tengoku

/-!
# Approximation duality and symmetric moment-matched priors

This module packages the Hahn--Banach/Riesz extremal certificate for best
uniform approximation of absolute value and converts its positive and negative
parts into two symmetric probability measures.  The resulting structure is the
consumer-facing moment-matched-prior API.
-/

@[expose] public section

open MeasureTheory Set

namespace Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality

/-- For [a Borel measure on the real line](hyp:ν), [symmetry about zero](goal) means that reflecting every point through zero leaves the measure unchanged. -/
def IsSymmetric (ν : Measure ℝ) : Prop :=
  Measure.map (fun x : ℝ => -x) ν = ν

/-- For [a measure on the real line](hyp:ν), [support on the unit interval](goal) means that the complement of the closed interval from −1 to 1 has measure zero. -/
def IsSupportedOnUnitInterval (ν : Measure ℝ) : Prop :=
  ν (symmUnitIntervalᶜ) = 0

private noncomputable def dualAbs : C(symmUnitInterval, ℝ) :=
  ⟨fun x => |(x : ℝ)|, by fun_prop⟩

private noncomputable def dualPow (j : ℕ) : C(symmUnitInterval, ℝ) :=
  ⟨fun x => (x : ℝ) ^ j, by fun_prop⟩

private noncomputable def dualPolynomials (K : ℕ) :
    Submodule ℝ C(symmUnitInterval, ℝ) :=
  ((Polynomial.toContinuousMapOnAlgHom symmUnitInterval).toLinearMap.domRestrict
    (Polynomial.degreeLT ℝ (K + 1))).range

private noncomputable def symmPush (μ : Measure symmUnitInterval) : Measure ℝ :=
  (1 / 2 : ENNReal) •
    (Measure.map (Subtype.val : symmUnitInterval → ℝ) μ +
      Measure.map ((fun x : ℝ => -x) ∘ (Subtype.val : symmUnitInterval → ℝ)) μ)

/-- An extremal certificate given by two finite measures on the real line, labelled positive and
negative.  Each has mass `1/2`, is symmetric and supported on `[-1,1]`; their
degree-`K` moments agree, while their absolute first moments differ by `E_K`.

The structure is a certificate made of two finite measures; it does not require them to be
mutually singular, so it records a decomposition of the kind produced by the normalized Jordan
decomposition of the norm-one separating functional without asserting that it is one.  Multiplying
each measure by two gives probability measures and the gap `2 E_K`.
-/
structure AbsExtremalDecomposition (K : ℕ) where
  positive : Measure ℝ
  negative : Measure ℝ
  finite_positive : IsFiniteMeasure positive
  finite_negative : IsFiniteMeasure negative
  positive_mass : positive Set.univ = (1 / 2 : ENNReal)
  negative_mass : negative Set.univ = (1 / 2 : ENNReal)
  positive_supported : IsSupportedOnUnitInterval positive
  negative_supported : IsSupportedOnUnitInterval negative
  positive_symmetric : IsSymmetric positive
  negative_symmetric : IsSymmetric negative
  moments_eq : ∀ j : ℕ, j ≤ K →
    ∫ x : ℝ, x ^ j ∂positive = ∫ x : ℝ, x ^ j ∂negative
  abs_gap :
    (∫ x : ℝ, |x| ∂positive) - (∫ x : ℝ, |x| ∂negative) =
      bestUniformApproxErrorAbs K

/-- Two symmetric probability measures on `[-1,1]` whose moments match through
degree `K` and whose absolute first moments have the oriented gap `2 E_K`. -/
structure AbsMomentMatchedPriors (K : ℕ) where
  ν₀ : Measure ℝ
  ν₁ : Measure ℝ
  probability₀ : IsProbabilityMeasure ν₀
  probability₁ : IsProbabilityMeasure ν₁
  supported₀ : IsSupportedOnUnitInterval ν₀
  supported₁ : IsSupportedOnUnitInterval ν₁
  symmetric₀ : IsSymmetric ν₀
  symmetric₁ : IsSymmetric ν₁
  moments_eq : ∀ j : ℕ, j ≤ K →
    ∫ x : ℝ, x ^ j ∂ν₀ = ∫ x : ℝ, x ^ j ∂ν₁
  abs_gap :
    (∫ x : ℝ, |x| ∂ν₁) - (∫ x : ℝ, |x| ∂ν₀) =
      2 * bestUniformApproxErrorAbs K

/-- For [a nonnegative moment-degree limit](hyp:K) and [an absolute-value extremal decomposition at that limit](hyp:D), [the associated pair of moment-matched priors](goal) has [first prior equal to twice the decomposition's negative measure](step:1) and second prior equal to twice its positive measure.

Doubling the two already oriented Jordan parts of an extremal decomposition produces the symmetric probability-prior pair. -/
noncomputable def AbsExtremalDecomposition.toMomentMatchedPriors
    {K : ℕ} (D : AbsExtremalDecomposition K) : AbsMomentMatchedPriors K := by
  let ν₀ : Measure ℝ := (2 : ENNReal) • D.negative
  let ν₁ : Measure ℝ := (2 : ENNReal) • D.positive
  refine
    { ν₀ := ν₀
      ν₁ := ν₁
      probability₀ := ?_
      probability₁ := ?_
      supported₀ := ?_
      supported₁ := ?_
      symmetric₀ := ?_
      symmetric₁ := ?_
      moments_eq := ?_
      abs_gap := ?_ }
  · constructor
    simp only [ν₀, Measure.smul_apply, D.negative_mass]
    simpa [smul_eq_mul, div_eq_inv_mul] using
      (ENNReal.mul_inv_cancel (a := (2 : ENNReal)) (by norm_num) (by norm_num))
  · constructor
    simp only [ν₁, Measure.smul_apply, D.positive_mass]
    simpa [smul_eq_mul, div_eq_inv_mul] using
      (ENNReal.mul_inv_cancel (a := (2 : ENNReal)) (by norm_num) (by norm_num))
  · dsimp only [IsSupportedOnUnitInterval, ν₀]
    rw [Measure.smul_apply, D.negative_supported]
    simp
  · dsimp only [IsSupportedOnUnitInterval, ν₁]
    rw [Measure.smul_apply, D.positive_supported]
    simp
  · simpa [IsSymmetric, ν₀, Measure.map_smul] using
      congrArg ((2 : ENNReal) • ·) D.negative_symmetric
  · simpa [IsSymmetric, ν₁, Measure.map_smul] using
      congrArg ((2 : ENNReal) • ·) D.positive_symmetric
  · intro j hj
    simp only [ν₀, ν₁, integral_smul_measure, ENNReal.toReal_ofNat]
    rw [D.moments_eq j hj]
  · simp only [ν₀, ν₁, integral_smul_measure, ENNReal.toReal_ofNat, smul_eq_mul]
    linarith [D.abs_gap]

/-- For [a packaged prior pair](hyp:K,P), [its first prior is a probability measure](goal).

 The first prior in a packaged pair is a probability measure. -/
theorem priorZero_isProbabilityMeasure {K : ℕ} (P : AbsMomentMatchedPriors K) :
    IsProbabilityMeasure P.ν₀ :=
  P.probability₀

/-- For [a packaged prior pair](hyp:K,P), [its second prior is a probability measure](goal).

 The second prior in a packaged pair is a probability measure. -/
theorem priorOne_isProbabilityMeasure {K : ℕ} (P : AbsMomentMatchedPriors K) :
    IsProbabilityMeasure P.ν₁ :=
  P.probability₁

/-- For [a packaged prior pair](hyp:K,P), [its first prior has total mass one](goal).

 The first prior has total mass one. -/
theorem priorZero_mass {K : ℕ} (P : AbsMomentMatchedPriors K) :
    P.ν₀ Set.univ = 1 := by
  exact P.probability₀.measure_univ

/-- For [a packaged prior pair](hyp:K,P), [its second prior has total mass one](goal).

 The second prior has total mass one. -/
theorem priorOne_mass {K : ℕ} (P : AbsMomentMatchedPriors K) :
    P.ν₁ Set.univ = 1 := by
  exact P.probability₁.measure_univ

/-- For [a packaged prior pair](hyp:K,P), [its first prior is supported on the unit interval](goal).

 The first prior is supported on `[-1,1]`. -/
theorem priorZero_supported {K : ℕ} (P : AbsMomentMatchedPriors K) :
    IsSupportedOnUnitInterval P.ν₀ :=
  P.supported₀

/-- For [a packaged prior pair](hyp:K,P), [its second prior is supported on the unit interval](goal).

 The second prior is supported on `[-1,1]`. -/
theorem priorOne_supported {K : ℕ} (P : AbsMomentMatchedPriors K) :
    IsSupportedOnUnitInterval P.ν₁ :=
  P.supported₁

/-- For [a packaged prior pair](hyp:K,P), [its first prior is symmetric about zero](goal).

 The first prior is symmetric about zero. -/
theorem priorZero_symmetric {K : ℕ} (P : AbsMomentMatchedPriors K) :
    IsSymmetric P.ν₀ :=
  P.symmetric₀

/-- For [a packaged prior pair](hyp:K,P), [its second prior is symmetric about zero](goal).

 The second prior is symmetric about zero. -/
theorem priorOne_symmetric {K : ℕ} (P : AbsMomentMatchedPriors K) :
    IsSymmetric P.ν₁ :=
  P.symmetric₁

/-- For [a packaged prior pair](hyp:K,P) and [a moment order no larger than the degree limit](hyp:j,hj), [the two priors have equal moments of that order](goal).

 The two priors have equal `j`-th moments for every `j ≤ K`. -/
theorem prior_moments_eq {K : ℕ} (P : AbsMomentMatchedPriors K)
    {j : ℕ} (hj : j ≤ K) :
    ∫ x : ℝ, x ^ j ∂P.ν₀ = ∫ x : ℝ, x ^ j ∂P.ν₁ :=
  P.moments_eq j hj

/-- For [a packaged prior pair](hyp:K,P), [the oriented difference in absolute first moments is twice the best approximation error](goal).

 The oriented difference of the priors' absolute first moments is exactly
`2 E_K`. -/
theorem prior_absMoment_gap {K : ℕ} (P : AbsMomentMatchedPriors K) :
    (∫ x : ℝ, |x| ∂P.ν₁) - (∫ x : ℝ, |x| ∂P.ν₀) =
      2 * bestUniformApproxErrorAbs K :=
  P.abs_gap

end Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality
