/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Randomsettheory.RandomSetTheory.L2LipschitzPathMeasurability
import Tengoku.Randomsettheory.RandomSetTheory.MeasurableSize
import Tengoku.Randomsettheory.RandomSetTheory.TightFiniteEvaluationVectorLimit
import Tengoku.Randomsettheory.RandomSetTheory.SupportProcessClosedStructure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Pointwise random-set CLT under a square-integrable radius envelope

This file assembles the complete process-level argument behind the pointwise
random-set CLT.  An Effros-measurable compact convex random set whose radius
has a square-integrable envelope gives a tight centered support process on the
unit ball.  The iid finite-direction CLT identifies all of its finite
evaluation vectors, and Prokhorov uniqueness then constructs the canonical
continuous Gaussian process law.  The continuous-mapping theorem finally
gives the symmetric Hausdorff distance and both directed distances.

No process weak limit and no chaining certificate are assumed.
-/
namespace Tengoku.Randomsettheory end Tengoku.Randomsettheory open Tengoku.Randomsettheory
open Filter MeasureTheory Metric ProbabilityTheory Real Set WithLp
open scoped BigOperators InnerProductSpace ProbabilityTheory Topology

noncomputable section

namespace RandomSetTheory

variable {Omega Z E : Type*} [MeasurableSpace Omega] [MeasurableSpace Z]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Equality of the two set presentations of the closed unit ball.-/
theorem euclideanUnitBall_set_eq_closedBall :
    {x : E | ‖x‖ ≤ 1} = Metric.closedBall (0 : E) 1 := by
  ext x
  simp [Metric.mem_closedBall, dist_zero_right]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The two unit-ball index types used by the chaining and support-process
APIs are propositionally equal.-/
theorem euclideanUnitBall_eq_closedBall :
    EuclideanUnitBall E = Metric.closedBall (0 : E) 1 :=
  congrArg (fun s : Set E ↦ (s : Type _))
    (euclideanUnitBall_set_eq_closedBall (E := E))

/-- Canonical homeomorphism between the two unit-ball index presentations.-/
def euclideanUnitBallHomeomorphClosedBall :
    EuclideanUnitBall E ≃ₜ Metric.closedBall (0 : E) 1 :=
  Homeomorph.setCongr (euclideanUnitBall_set_eq_closedBall (E := E))

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
@[simp]
theorem euclideanUnitBallHomeomorphClosedBall_coe
    (u : EuclideanUnitBall E) :
    ((euclideanUnitBallHomeomorphClosedBall (E := E) u :
      Metric.closedBall (0 : E) 1) : E) = (u : E) := rfl

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
@[simp]
theorem euclideanUnitBallHomeomorphClosedBall_symm_coe
    (u : Metric.closedBall (0 : E) 1) :
    ((euclideanUnitBallHomeomorphClosedBall (E := E).symm u :
      EuclideanUnitBall E) : E) = (u : E) := rfl

/-- In finite dimension the Euclidean unit ball is compact.-/
noncomputable instance instCompactSpaceEuclideanUnitBall :
    CompactSpace (EuclideanUnitBall E) :=
  isCompact_iff_compactSpace.mp (by
    apply Metric.isCompact_of_isClosed_isBounded
    · exact isClosed_le continuous_norm continuous_const
    · exact (isBounded_iff_forall_norm_le.mpr ⟨1, fun _v hv ↦ hv⟩))

/-- Reindex a continuous path from the norm-predicate unit ball to the
metric closed-ball presentation.-/
def unitBallPathToClosedBall
    (f : C(EuclideanUnitBall E, ℝ)) :
    C(Metric.closedBall (0 : E) 1, ℝ) :=
  f.comp (euclideanUnitBallHomeomorphClosedBall (E := E).symm)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
@[simp]
theorem unitBallPathToClosedBall_apply
    (f : C(EuclideanUnitBall E, ℝ))
    (u : Metric.closedBall (0 : E) 1) :
    unitBallPathToClosedBall f u =
      f (euclideanUnitBallHomeomorphClosedBall (E := E).symm u) := rfl

/-- Reindexing along the unit-ball homeomorphism is continuous for the
uniform path norms.-/
theorem continuous_unitBallPathToClosedBall :
    Continuous (unitBallPathToClosedBall (E := E)) := by
  apply (LipschitzWith.of_dist_le_mul (K := 1) ?_).continuous
  intro f g
  simp only [NNReal.coe_one, one_mul]
  rw [ContinuousMap.dist_le_iff_of_nonempty]
  intro u
  exact ContinuousMap.dist_apply_le_dist (f := f) (g := g)
    (euclideanUnitBallHomeomorphClosedBall (E := E).symm u)

omit [MeasurableSpace Z] [FiniteDimensional ℝ E] in
/-- A pointwise radius envelope is a Lipschitz envelope for support
functions.-/
theorem abs_supportFunction_sub_le_radiusEnvelope
    (F : Z → Set E) (hFcompact : ∀ z, IsCompact (F z))
    (hFne : ∀ z, (F z).Nonempty) (R : Z → ℝ)
    (hRbound : ∀ z x, x ∈ F z → ‖x‖ ≤ R z) :
    ∀ z s t,
      |supportFunction (F z) s - supportFunction (F z) t| ≤
        R z * dist s t := by
  intro z s t
  simpa only [dist_eq_norm] using
    abs_supportFunction_sub_le
      (hFcompact z) (hFne z) (hRbound z) s t

omit [MeasurableSpace Z] [FiniteDimensional ℝ E] in
/-- Support functions are continuous whenever their random compact set has a
finite radius envelope.-/
theorem continuous_supportFunction_of_radiusEnvelope
    (F : Z → Set E) (hFcompact : ∀ z, IsCompact (F z))
    (hFne : ∀ z, (F z).Nonempty) (R : Z → ℝ)
    (hR : ∀ z, 0 ≤ R z)
    (hRbound : ∀ z x, x ∈ F z → ‖x‖ ≤ R z) :
    ∀ z, Continuous (supportFunction (F z)) := by
  intro z
  apply (LipschitzWith.of_dist_le_mul (K := ⟨R z, hR z⟩) ?_).continuous
  intro s t
  exact abs_supportFunction_sub_le_radiusEnvelope
    F hFcompact hFne R hRbound z s t

/-- Canonical untruncated centered support process used by the `L²`
tightness theorem.-/
def centeredSupportEmpiricalContinuousMap
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (X : ℕ → Omega → Z) (hX : ∀ i, Measurable (X i))
    (F : Z → Set E) (hF : RandomSet.IsEffrosMeasurable F)
    (hFcompact : ∀ z, IsCompact (F z))
    (hFne : ∀ z, (F z).Nonempty)
    (R : Z → ℝ) (hR : ∀ z, 0 ≤ R z)
    (hRbound : ∀ z x, x ∈ F z → ‖x‖ ≤ R z)
    (hRL2 : ∀ i, MemLp (fun omega ↦ R (X i omega)) 2 mu)
    (n : ℕ) (omega : Omega) : C(EuclideanUnitBall E, ℝ) :=
  ProbabilityTheory.centeredAnchoredEmpiricalContinuousMap (mu := mu)
    (fun z u ↦ supportFunction (F z) u) R X hX
    (fun u ↦ measurable_supportFunction hF hFcompact hFne u)
    (continuous_supportFunction_of_radiusEnvelope
      F hFcompact hFne R hR hRbound)
    hR (abs_supportFunction_sub_le_radiusEnvelope
      F hFcompact hFne R hRbound) hRL2 n omega

/-- Canonical square-root-truncated centered support process.-/
def centeredTruncatedSupportEmpiricalContinuousMap
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (X : ℕ → Omega → Z) (hX : ∀ i, Measurable (X i))
    (F : Z → Set E) (hF : RandomSet.IsEffrosMeasurable F)
    (hFcompact : ∀ z, IsCompact (F z))
    (hFne : ∀ z, (F z).Nonempty)
    (R : Z → ℝ) (hRmeas : Measurable R)
    (hR : ∀ z, 0 ≤ R z)
    (hRbound : ∀ z x, x ∈ F z → ‖x‖ ≤ R z)
    (n : ℕ) (omega : Omega) : C(EuclideanUnitBall E, ℝ) :=
  ProbabilityTheory.centeredTruncatedEmpiricalContinuousMap (mu := mu)
    (fun z u ↦ supportFunction (F z) u) R (a := 1) (by norm_num) X hX
    (fun u ↦ measurable_supportFunction hF hFcompact hFne u)
    (continuous_supportFunction_of_radiusEnvelope
      F hFcompact hFne R hR hRbound)
    hRmeas hR (abs_supportFunction_sub_le_radiusEnvelope
      F hFcompact hFne R hRbound) n omega

/-- Effros measurability in every direction and path continuity make the
canonical untruncated support process measurable as a path-valued random
variable.-/
theorem measurable_centeredSupportEmpiricalContinuousMap
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [MeasurableSpace C(EuclideanUnitBall E, ℝ)]
    [BorelSpace C(EuclideanUnitBall E, ℝ)]
    (X : ℕ → Omega → Z) (hX : ∀ i, Measurable (X i))
    (F : Z → Set E) (hF : RandomSet.IsEffrosMeasurable F)
    (hFcompact : ∀ z, IsCompact (F z))
    (hFne : ∀ z, (F z).Nonempty)
    (R : Z → ℝ) (hR : ∀ z, 0 ≤ R z)
    (hRbound : ∀ z x, x ∈ F z → ‖x‖ ≤ R z)
    (hRL2 : ∀ i, MemLp (fun omega ↦ R (X i omega)) 2 mu)
    (n : ℕ) :
    Measurable (centeredSupportEmpiricalContinuousMap (mu := mu)
      X hX F hF hFcompact hFne R hR hRbound hRL2 n) := by
  exact ProbabilityTheory.measurable_centeredAnchoredEmpiricalContinuousMap
    (fun z u ↦ supportFunction (F z) u) R X hX
      (fun u ↦ measurable_supportFunction hF hFcompact hFne u)
      (continuous_supportFunction_of_radiusEnvelope
        F hFcompact hFne R hR hRbound)
      hR (abs_supportFunction_sub_le_radiusEnvelope
        F hFcompact hFne R hRbound) hRL2 n

/-- The same automatic path measurability holds after square-root
truncation.-/
theorem measurable_centeredTruncatedSupportEmpiricalContinuousMap
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [MeasurableSpace C(EuclideanUnitBall E, ℝ)]
    [BorelSpace C(EuclideanUnitBall E, ℝ)]
    (X : ℕ → Omega → Z) (hX : ∀ i, Measurable (X i))
    (F : Z → Set E) (hF : RandomSet.IsEffrosMeasurable F)
    (hFcompact : ∀ z, IsCompact (F z))
    (hFne : ∀ z, (F z).Nonempty)
    (R : Z → ℝ) (hRmeas : Measurable R)
    (hR : ∀ z, 0 ≤ R z)
    (hRbound : ∀ z x, x ∈ F z → ‖x‖ ≤ R z)
    (n : ℕ) :
    Measurable (centeredTruncatedSupportEmpiricalContinuousMap (mu := mu)
      X hX F hF hFcompact hFne R hRmeas hR hRbound n) := by
  exact ProbabilityTheory.measurable_centeredTruncatedEmpiricalContinuousMap
    (fun z u ↦ supportFunction (F z) u) R (a := 1) (by norm_num) X hX
      (fun u ↦ measurable_supportFunction hF hFcompact hFne u)
      (continuous_supportFunction_of_radiusEnvelope
        F hFcompact hFne R hR hRbound)
      hRmeas hR (abs_supportFunction_sub_le_radiusEnvelope
        F hFcompact hFne R hRbound) n

omit [FiniteDimensional ℝ E] in
/-- A square-integrable radius envelope gives the `L²` hypothesis required
by every finite-direction support CLT.-/
theorem memLp_finiteDirectionalSupportDeviation_of_radiusEnvelope
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (X : ℕ → Omega → Z)
    (hX : ∀ i, Measurable (X i))
    (F : Z → Set E) (hF : RandomSet.IsEffrosMeasurable F)
    (hFcompact : ∀ z, IsCompact (F z))
    (hFne : ∀ z, (F z).Nonempty)
    (L : Set E) (R : Z → ℝ)
    (hRbound : ∀ z x, x ∈ F z → ‖x‖ ≤ R z)
    (hRL2 : MemLp (fun omega ↦ R (X 0 omega)) 2 mu)
    {k : ℕ} (t : Fin k → EuclideanUnitBall E) :
    MemLp
      (finiteDirectionalSupportDeviation
        (fun i omega ↦ F (X i omega)) L (fun j ↦ (t j : E)) 0)
      2 mu := by
  apply MemLp.of_eval_piLp
  intro j
  have hsuppMeas : Measurable
    (fun omega ↦ supportFunction (F (X 0 omega)) (t j : E)) :=
    (measurable_supportFunction hF hFcompact hFne (t j : E)).comp
      (hX 0)
  have hsuppL2 : MemLp
      (fun omega ↦ supportFunction (F (X 0 omega)) (t j : E)) 2 mu := by
    apply hRL2.mono' hsuppMeas.aestronglyMeasurable
    filter_upwards [] with omega
    simpa only [Real.norm_eq_abs] using
      abs_supportFunction_le_radius
        (hFcompact (X 0 omega)) (hFne (X 0 omega))
        (hRbound (X 0 omega)) (t j).property
  exact hsuppL2.sub (memLp_const (supportFunction L (t j : E)))

omit [FiniteDimensional ℝ E] in
/-- The generic anchored empirical process is exactly the square-root-scaled
support difference between the empirical Minkowski average and its population
target.  The `n + 1` convention avoids the empty empirical average.-/
theorem centeredAnchoredEmpiricalContinuousMap_supportFunction_apply
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (X : ℕ → Omega → Z) (hX : ∀ i, Measurable (X i))
    (hident : ∀ i, IdentDistrib (X i) (X 0) mu mu)
    (F : Z → Set E)
    (hFcompact : ∀ z, IsCompact (F z))
    (hFne : ∀ z, (F z).Nonempty)
    (L : Set E) (R : Z → ℝ)
    (hHmeas : ∀ t, Measurable (fun z ↦ supportFunction (F z) t))
    (hHcont : ∀ z, Continuous (supportFunction (F z)))
    (hR : ∀ z, 0 ≤ R z)
    (hLip : ∀ z s t,
      |supportFunction (F z) s - supportFunction (F z) t| ≤
        R z * dist s t)
    (hRL2 : ∀ i, MemLp (fun omega ↦ R (X i omega)) 2 mu)
    (hLsupport : ∀ u,
      supportFunction L u =
        ∫ omega, supportFunction (F (X 0 omega)) u ∂mu)
    (n : ℕ) (omega : Omega) (t : EuclideanUnitBall E) :
    ProbabilityTheory.centeredAnchoredEmpiricalContinuousMap (mu := mu)
        (fun z u ↦ supportFunction (F z) u) R X hX hHmeas hHcont
        hR hLip hRL2 n omega t =
      √((n + 1 : ℕ) : ℝ) *
        (supportFunction
            (minkowskiAverage (Finset.range (n + 1))
              (fun i ↦ F (X i omega))) (t : E) -
          supportFunction L (t : E)) := by
  rw [ProbabilityTheory.centeredAnchoredEmpiricalContinuousMap_apply]
  unfold ProbabilityTheory.centeredAnchoredEmpiricalProcess
  simp only [ProbabilityTheory.lipschitzIncrement,
    supportFunction_zero (hFcompact _) (hFne _), sub_zero]
  have hint : ∀ i,
      ∫ xi, supportFunction (F (X i xi)) (t : E) ∂mu =
        ∫ xi, supportFunction (F (X 0 xi)) (t : E) ∂mu := by
    intro i
    exact ((hident i).comp (hHmeas (t : E))).integral_eq
  simp_rw [hint]
  rw [← hLsupport (t : E)]
  rw [supportFunction_minkowskiAverage
    (Finset.range (n + 1)) (fun i ↦ F (X i omega))
    (fun i _ ↦ hFcompact (X i omega))
    (fun i _ ↦ hFne (X i omega))]
  simp only [Finset.card_range, Finset.sum_sub_distrib,
    Finset.sum_const, nsmul_eq_mul]
  have hn : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hsqrt : √((n + 1 : ℕ) : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hn)
  norm_num [Nat.cast_add, Nat.cast_one] at hn hsqrt ⊢
  field_simp
  rw [Real.sq_sqrt hn.le]

section CanonicalBorel

local instance : MeasurableSpace C(EuclideanUnitBall E, ℝ) :=
  borel C(EuclideanUnitBall E, ℝ)

local instance : BorelSpace C(EuclideanUnitBall E, ℝ) := ⟨rfl⟩

local instance : MeasurableSpace C(Metric.closedBall (0 : E) 1, ℝ) :=
  borel C(Metric.closedBall (0 : E) 1, ℝ)

local instance : BorelSpace C(Metric.closedBall (0 : E) 1, ℝ) := ⟨rfl⟩

end CanonicalBorel

end RandomSetTheory
-- Tengoku: root names of this library moved to Tengoku.Randomsettheory so they do not collide with other libraries (generated)
