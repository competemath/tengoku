/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.PointwiseSupportProcessTightness

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite representations of evaluation functionals

Every element of `FiniteEvaluationDual T` is represented explicitly by a
finite family of points and coefficients.  This removes the opacity of
membership in a submodule span and makes finite-dimensional convergence
theorems directly usable for arbitrary finite-evaluation projections.

The second part of the file packages the continuous-mapping step.  Weak
convergence of the law of a finite evaluation vector implies weak convergence
of the law of any represented finite evaluation functional.
-/

open Filter MeasureTheory Set WithLp
open scoped BigOperators Topology ProbabilityTheory

noncomputable section

namespace RandomSetTheory

variable (T : Type*) [MetricSpace T]

/-- Every finite-evaluation functional is a finite linear combination of
point-evaluation continuous linear maps.  The case `k = 0` represents the
zero functional.-/
theorem FiniteEvaluationDual.exists_fin_sum_evalCLM
    (w : FiniteEvaluationDual T) :
    ∃ (k : ℕ) (a : Fin k → ℝ) (t : Fin k → T),
      ∑ j, a j • ContinuousMap.evalCLM ℝ (t j) = w.1 := by
  obtain ⟨k, a, g, hg⟩ := Submodule.mem_span_set'.1 w.2
  let t : Fin k → T := fun j ↦ (g j).2.choose
  have ht (j : Fin k) : ContinuousMap.evalCLM ℝ (t j) = (g j).1 :=
    (g j).2.choose_spec
  refine ⟨k, a, t, ?_⟩
  calc
    ∑ j, a j • ContinuousMap.evalCLM ℝ (t j) =
        ∑ j, a j • ((g j).1 : StrongDual ℝ C(T, ℝ)) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [ht j]
    _ = w.1 := hg

/-- Pointwise form of `FiniteEvaluationDual.exists_fin_sum_evalCLM`:
`w(f)` is a finite weighted sum of values of `f`.-/
theorem FiniteEvaluationDual.exists_apply_eq_fin_sum
    (w : FiniteEvaluationDual T) :
    ∃ (k : ℕ) (a : Fin k → ℝ) (t : Fin k → T),
      ∀ f : C(T, ℝ),
        (w.1 : StrongDual ℝ C(T, ℝ)) f = ∑ j, a j * f (t j) := by
  obtain ⟨k, a, t, hw⟩ :=
    FiniteEvaluationDual.exists_fin_sum_evalCLM T w
  refine ⟨k, a, t, fun f ↦ ?_⟩
  have happly := congrArg
    (fun L : StrongDual ℝ C(T, ℝ) ↦ L f) hw
  simpa only [sum_apply, smul_apply,
    ContinuousMap.evalCLM_apply, smul_eq_mul] using happly.symm

/-- The continuous linear map which records a finite vector of point
evaluations.-/
def finiteEvaluationVectorCLM {k : ℕ} (t : Fin k → T) :
    C(T, ℝ) →L[ℝ] EuclideanSpace ℝ (Fin k) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin k ↦ ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j ↦ ContinuousMap.evalCLM ℝ (t j))

@[simp]
theorem finiteEvaluationVectorCLM_apply {k : ℕ} (t : Fin k → T)
    (f : C(T, ℝ)) (j : Fin k) :
    finiteEvaluationVectorCLM T t f j = f (t j) := rfl

/-- The continuous scalar linear functional associated with a vector of
coefficients.-/
def finiteLinearCombinationCLM {k : ℕ} (a : Fin k → ℝ) :
    EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ :=
  innerSL ℝ (toLp 2 a)

@[simp]
theorem finiteLinearCombinationCLM_apply {k : ℕ} (a : Fin k → ℝ)
    (x : EuclideanSpace ℝ (Fin k)) :
    finiteLinearCombinationCLM a x = ∑ j, a j * x j := by
  simp [finiteLinearCombinationCLM, PiLp.inner_apply, mul_comm]

/-- A representation by point evaluations factors the corresponding
functional through its finite evaluation vector.-/
theorem finiteLinearCombinationCLM_comp_finiteEvaluationVectorCLM
    {k : ℕ} (a : Fin k → ℝ) (t : Fin k → T)
    (w : FiniteEvaluationDual T)
    (hw : ∑ j, a j • ContinuousMap.evalCLM ℝ (t j) = w.1) :
    (finiteLinearCombinationCLM a).comp (finiteEvaluationVectorCLM T t) = w.1 := by
  ext f
  have happly := congrArg
    (fun L : StrongDual ℝ C(T, ℝ) ↦ L f) hw
  simpa only [ContinuousLinearMap.comp_apply,
    finiteLinearCombinationCLM_apply, finiteEvaluationVectorCLM_apply,
    sum_apply, smul_apply,
    ContinuousMap.evalCLM_apply, smul_eq_mul] using happly

section ProbabilityMeasures

variable [CompactSpace T]
variable [MeasurableSpace C(T, ℝ)] [BorelSpace C(T, ℝ)]
variable {iota : Type*} {l : Filter iota}

/-- Continuous-mapping bridge for a fixed finite representation.  If the
finite evaluation-vector laws converge to `rho`, then the law of the
represented finite-evaluation functional converges to the image of `rho` by
the corresponding scalar linear form.-/
theorem ProbabilityMeasure.tendsto_map_finiteEvaluationDual_of_vector
    {k : ℕ} (a : Fin k → ℝ) (t : Fin k → T)
    (w : FiniteEvaluationDual T)
    (hw : ∑ j, a j • ContinuousMap.evalCLM ℝ (t j) = w.1)
    (mu : iota → ProbabilityMeasure C(T, ℝ))
    (rho : ProbabilityMeasure (EuclideanSpace ℝ (Fin k)))
    (hvec : Tendsto
      (fun i ↦ ProbabilityMeasure.map (mu i)
        (finiteEvaluationVectorCLM T t).measurable.aemeasurable)
      l
      (nhds rho)) :
    Tendsto
      (fun i ↦ ProbabilityMeasure.map (mu i)
        w.1.continuous.measurable.aemeasurable)
      l
      (nhds (ProbabilityMeasure.map rho
        (finiteLinearCombinationCLM a).measurable.aemeasurable)) := by
  let evalMap := finiteEvaluationVectorCLM T t
  let linearMap := finiteLinearCombinationCLM a
  have hfactor : linearMap.comp evalMap = w.1 := by
    exact finiteLinearCombinationCLM_comp_finiteEvaluationVectorCLM T a t w hw
  have hmapped := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun i ↦ ProbabilityMeasure.map (mu i) evalMap.measurable.aemeasurable)
    rho hvec linearMap.continuous
  have hmap_map (i : iota) :
      ProbabilityMeasure.map
          (ProbabilityMeasure.map (mu i) evalMap.measurable.aemeasurable)
          linearMap.measurable.aemeasurable =
        ProbabilityMeasure.map (mu i)
          w.1.continuous.measurable.aemeasurable := by
    apply ProbabilityMeasure.toMeasure_injective
    simp only [ProbabilityMeasure.toMeasure_map]
    rw [Measure.map_map linearMap.measurable evalMap.measurable]
    rw [show linearMap ∘ evalMap = w.1 from by
      funext f
      exact DFunLike.congr_fun hfactor f]
  simpa only [evalMap, linearMap, hmap_map] using hmapped

/-- Every `w : FiniteEvaluationDual T` admits finite data for which the
continuous-mapping bridge is available.  This is the form intended for
instantiating process tightness results from a finite-dimensional CLT.-/
theorem ProbabilityMeasure.exists_fin_tendsto_map_finiteEvaluationDual_bridge
    (w : FiniteEvaluationDual T)
    (mu : iota → ProbabilityMeasure C(T, ℝ)) :
    ∃ (k : ℕ) (a : Fin k → ℝ) (t : Fin k → T),
      (∑ j, a j • ContinuousMap.evalCLM ℝ (t j) = w.1) ∧
      ∀ (rho : ProbabilityMeasure (EuclideanSpace ℝ (Fin k))),
        Tendsto
          (fun i ↦ ProbabilityMeasure.map (mu i)
            (finiteEvaluationVectorCLM T t).measurable.aemeasurable)
          l
          (nhds rho) →
        Tendsto
          (fun i ↦ ProbabilityMeasure.map (mu i)
            w.1.continuous.measurable.aemeasurable)
          l
          (nhds (ProbabilityMeasure.map rho
            (finiteLinearCombinationCLM a).measurable.aemeasurable)) := by
  obtain ⟨k, a, t, hw⟩ :=
    FiniteEvaluationDual.exists_fin_sum_evalCLM T w
  refine ⟨k, a, t, hw, ?_⟩
  intro rho hvec
  exact ProbabilityMeasure.tendsto_map_finiteEvaluationDual_of_vector
    T a t w hw mu rho hvec

end ProbabilityMeasures

end RandomSetTheory
