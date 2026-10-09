module
public import Tengoku.Causalean.Causalean.Mathlib.Probability.Poisson.FinitePartition.Basic
public import Tengoku.Causalean.Causalean.Mathlib.InformationTheory.KLBind
public import Tengoku.Causalean.Causalean.Mathlib.InformationTheory.ProductKLLeCam
public import Tengoku

/-!
# Relative entropy of finite Poisson experiments

This file packages a finite measure as a Poisson count with mean equal to its
mass times a scalar intensity and conditionally i.i.d. points from its
normalisation.  It states the extended-real KL identity for two equal-mass
finite intensity measures and the monotone upper-bound form used in testing
arguments.  A shared independent real mark law is carried throughout.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

variable {X : Type*} [MeasurableSpace X]

private noncomputable def finiteSampleKernel
    (P : Measure X) [IsProbabilityMeasure P] : Kernel ℕ (FiniteSample X) where
  toFun n := Measure.map (fixedSizeEmbed n) (Measure.pi fun _ : Fin n ↦ P)
  measurable' := Measurable.of_discrete

/-- Given [a finite measure](hyp:ν), its [finite-measure mass](goal) is its total mass on the
observation space, represented as a nonnegative real number. -/
noncomputable def finiteMeasureMass (ν : Measure X) [IsFiniteMeasure ν] : ℝ≥0 :=
  (ν Set.univ).toNNReal

/-- Given [a finite measure](hyp:ν) and [a fallback probability law](hyp:P₀), the
[normalized finite measure](goal) is the fallback when the measure is zero and otherwise is the
measure divided by its total mass. -/
noncomputable def normalizedFiniteMeasure (ν : Measure X) [IsFiniteMeasure ν]
    (P₀ : Measure X) [IsProbabilityMeasure P₀] : Measure X := by
  classical
  exact if h : ν = 0 then P₀ else (ν Set.univ)⁻¹ • ν

/-- [Normalizing a finite measure produces a probability measure](goal) on
[a measurable observation space](hyp:X), using [the finite measure](hyp:ν) and
[a fallback probability law](hyp:P₀).

The normalisation uses the explicit fallback probability measure when the finite measure is zero. -/
instance normalizedFiniteMeasure_isProbabilityMeasure
    (ν : Measure X) [IsFiniteMeasure ν]
    (P₀ : Measure X) [IsProbabilityMeasure P₀] :
    IsProbabilityMeasure (normalizedFiniteMeasure ν P₀) := by
  classical
  rw [normalizedFiniteMeasure]
  split_ifs with hν
  · infer_instance
  · rw [isProbabilityMeasure_iff, Measure.smul_apply _ _ Set.univ]
    have hmass : ν Set.univ ≠ 0 := by
      exact fun h ↦ hν (Measure.measure_univ_eq_zero.mp h)
    exact ENNReal.inv_mul_cancel hmass (ne_of_lt (measure_lt_top ν Set.univ))

/-- Given [a finite intensity measure](hyp:ν), [a fallback probability law](hyp:P₀),
[a real-valued mark law](hyp:R), and [a nonnegative scalar intensity](hyp:lam), the
[finite-measure marked Poisson law](goal) normalizes the intensity measure and uses a Poisson mean
equal to the scalar intensity times its total mass. -/
noncomputable def finiteMeasureMarkedPoissonLaw
    (ν : Measure X) [IsFiniteMeasure ν]
    (P₀ : Measure X) [IsProbabilityMeasure P₀]
    (R : Measure ℝ) [IsProbabilityMeasure R] (lam : ℝ≥0) :
    Measure (FiniteSample (X × ℝ)) :=
  finiteMarkedPoissonSampleLaw (normalizedFiniteMeasure ν P₀) R
    (lam * finiteMeasureMass ν)

/-- For [a finite intensity measure](hyp:ν), [a fallback probability law](hyp:P₀),
[a real-valued mark law](hyp:R), and [a nonnegative scalar intensity](hyp:lam),
[the count is Poisson with mean equal to the scaled total intensity mass](goal). -/
lemma finiteMeasureMarkedPoissonLaw_map_count
    (ν : Measure X) [IsFiniteMeasure ν]
    (P₀ : Measure X) [IsProbabilityMeasure P₀]
    (R : Measure ℝ) [IsProbabilityMeasure R] (lam : ℝ≥0) :
    Measure.map FiniteSample.count (finiteMeasureMarkedPoissonLaw ν P₀ R lam) =
      poissonMeasure (lam * finiteMeasureMass ν) := by
  exact finiteMarkedPoissonSampleLaw_map_count
    (normalizedFiniteMeasure ν P₀) R (lam * finiteMeasureMass ν)

end Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
