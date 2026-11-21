/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.FiniteEvaluationRepresentation
import Tengoku.Randomsettheory.RandomSetTheory.TightProcessLimitExistence
import Tengoku.Seed.Probability.Distributions.Gaussian.IsGaussianProcess.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Canonical process limits from finite evaluation vectors

On a compact second-countable metric index space, tightness together with
weak convergence of every finite vector of point evaluations constructs a
unique law on `C(T, ℝ)`.  The limiting law realizes all the prescribed
finite-vector laws.

The proof selects a finite representation of each element of
`FiniteEvaluationDual T`, pushes the corresponding prescribed vector law
through its scalar linear combination, and applies
`ProbabilityMeasure.existsUnique_tendsto_of_tight_of_finiteEvaluationProjectionLimits`.
Continuity of every finite evaluation-vector map then identifies all vector
marginals of the resulting process law.
-/

open Filter MeasureTheory ProbabilityTheory Set WithLp
open scoped BigOperators Topology ProbabilityTheory

noncomputable section

namespace RandomSetTheory

variable (T : Type*) [MetricSpace T] [CompactSpace T] [SecondCountableTopology T]
variable [MeasurableSpace C(T, ℝ)] [BorelSpace C(T, ℝ)]

omit [SecondCountableTopology T] in
/-- If all finite evaluation-vector marginals of a continuous-path law are
Gaussian, then the canonical coordinate process is a Gaussian process.

This lemma performs the finite reindexing explicitly: a finite set `I` is
enumerated by `Fin I.card`; its Euclidean (`PiLp`) evaluation vector is then
mapped continuously back to the ordinary function space `I → ℝ` used in
the definition of `IsGaussianProcess`.
@isnad1 id=isgaussi.2h3v.s10.52882928954c from=translated src=- shape=1313770e vocab=43410bcd
-/
theorem isGaussianProcess_canonical_of_finiteEvaluationVector_isGaussian
    (mu0 : ProbabilityMeasure C(T, ℝ))
    (rho : ∀ k : ℕ, (Fin k → T) →
      ProbabilityMeasure (EuclideanSpace ℝ (Fin k)))
    (hvector : ∀ (k : ℕ) (t : Fin k → T),
      ProbabilityMeasure.map mu0
        (finiteEvaluationVectorCLM T t).measurable.aemeasurable = rho k t)
    (hgaussian : ∀ (k : ℕ) (t : Fin k → T),
      IsGaussian ((rho k t : ProbabilityMeasure
        (EuclideanSpace ℝ (Fin k))) : Measure (EuclideanSpace ℝ (Fin k)))) :
    IsGaussianProcess (fun q (f : C(T, ℝ)) ↦ f q) (mu0 : Measure C(T, ℝ)) := by
  classical
  refine ⟨?_⟩
  intro I
  let e : I ≃ Fin I.card := Finset.equivFin I
  let t : Fin I.card → T := fun j ↦ (e.symm j).1
  let evalMap := finiteEvaluationVectorCLM T t
  let reindex : EuclideanSpace ℝ (Fin I.card) →L[ℝ] (I → ℝ) :=
    { toFun := fun x i ↦ x (e i)
      map_add' := by
        intro x y
        ext i
        simp
      map_smul' := by
        intro c x
        ext i
        simp
      cont := by fun_prop }
  have hfun :
      (fun f : C(T, ℝ) ↦ I.restrict (fun q ↦ f q)) = reindex ∘ evalMap := by
    funext f i
    simp [reindex, evalMap, t, e]
  have hlaw :
      (mu0 : Measure C(T, ℝ)).map evalMap =
        (rho I.card t : Measure (EuclideanSpace ℝ (Fin I.card))) := by
    simpa only [evalMap, ProbabilityMeasure.toMeasure_map] using
      congrArg ProbabilityMeasure.toMeasure (hvector I.card t)
  letI : IsGaussian
      (rho I.card t : Measure (EuclideanSpace ℝ (Fin I.card))) :=
    hgaussian I.card t
  refine ⟨?_⟩
  rw [hfun, ← Measure.map_map reindex.measurable evalMap.measurable, hlaw]
  infer_instance

end RandomSetTheory
