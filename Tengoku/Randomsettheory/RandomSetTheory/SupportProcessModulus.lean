/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.Geometry
import Tengoku.Randomsettheory.RandomSetTheory.UnitBallNets

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Directional modulus of empirical support processes

The empirical support process attached to a finite Minkowski average is the
difference between two support functions, multiplied by a deterministic
scale (for a central limit theorem this scale is `sqrt n`).  Radius bounds
give an explicit pathwise Lipschitz modulus in the support direction.

This file records that deterministic ingredient and its finite-net
consequence.  In particular, a deviation somewhere on the unit ball forces a
slightly smaller deviation at a point of any prescribed finite net.  These
results do not assert stochastic equicontinuity or a functional central limit
theorem; they isolate the geometric estimate needed before those genuinely
probabilistic arguments.
-/

open Real Set Metric
open scoped BigOperators InnerProductSpace

noncomputable section

namespace RandomSetTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The support process of a finite Minkowski average, centred at a
deterministic target and multiplied by an arbitrary real scale.-/
def scaledCenteredSupportProcess {I : Type*} (c : ℝ) (s : Finset I)
    (K : I → Set E) (L : Set E) (u : E) : ℝ :=
  c * (supportFunction (minkowskiAverage s K) u - supportFunction L u)

/-- A radius-based Lipschitz constant for `scaledCenteredSupportProcess`.
Absolute values make the definition meaningful without redundant sign
hypotheses on the supplied radius bounds or on the scale.-/
def supportProcessDirectionConstant {I : Type*} (c : ℝ) (s : Finset I)
    (R : I → ℝ) (RL : ℝ) : ℝ :=
  |c| * (|(s.card : ℝ)⁻¹ * ∑ i ∈ s, R i| + |RL|)

/--
@isnad1 id=le.0h5v.s4.88d03a316aac from=translated src=- shape=44c9b96a vocab=acfdb43e
-/
@[simp]
theorem supportProcessDirectionConstant_nonneg {I : Type*} (c : ℝ)
    (s : Finset I) (R : I → ℝ) (RL : ℝ) :
    0 ≤ supportProcessDirectionConstant c s R RL := by
  exact mul_nonneg (abs_nonneg c) (add_nonneg (abs_nonneg _) (abs_nonneg RL))

/-- Radius control makes the centred and scaled empirical support process
Lipschitz in its direction.  The estimate is pathwise and therefore applies
equally to deterministic sets and to every realization of random sets.
@isnad1 id=le.6h10v.s7.b06565c3791b from=translated src=- shape=85d6c834 vocab=304aca3c
-/
theorem abs_scaledCenteredSupportProcess_sub_le
    {I : Type*} (c : ℝ) (s : Finset I) (K : I → Set E) (L : Set E)
    (R : I → ℝ) (RL : ℝ)
    (hKcompact : ∀ i ∈ s, IsCompact (K i))
    (hKne : ∀ i ∈ s, (K i).Nonempty)
    (hLcompact : IsCompact L) (hLne : L.Nonempty)
    (hR : ∀ i ∈ s, ∀ x ∈ K i, ‖x‖ ≤ R i)
    (hRL : ∀ x ∈ L, ‖x‖ ≤ RL) (u v : E) :
    |scaledCenteredSupportProcess c s K L u -
        scaledCenteredSupportProcess c s K L v| ≤
      supportProcessDirectionConstant c s R RL * ‖u - v‖ := by
  let Rbar : ℝ := (s.card : ℝ)⁻¹ * ∑ i ∈ s, R i
  have hAvgCompact : IsCompact (minkowskiAverage s K) :=
    isCompact_minkowskiAverage s K hKcompact
  have hAvgNe : (minkowskiAverage s K).Nonempty :=
    nonempty_minkowskiAverage s K hKne
  have hAvgRadius : ∀ x ∈ minkowskiAverage s K, ‖x‖ ≤ Rbar := by
    intro x hx
    exact norm_le_average_radius_of_mem_minkowskiAverage s K R hR hx
  have hbase := abs_supportFunctionDifference_sub_le
    hAvgCompact hLcompact hAvgNe hLne hAvgRadius hRL u v
  have hrad : Rbar + RL ≤ |Rbar| + |RL| :=
    add_le_add (le_abs_self Rbar) (le_abs_self RL)
  calc
    |scaledCenteredSupportProcess c s K L u -
        scaledCenteredSupportProcess c s K L v| =
        |c| * |(supportFunction (minkowskiAverage s K) u -
          supportFunction L u) -
          (supportFunction (minkowskiAverage s K) v -
            supportFunction L v)| := by
      rw [scaledCenteredSupportProcess, scaledCenteredSupportProcess]
      rw [← mul_sub, abs_mul]
    _ ≤ |c| * ((Rbar + RL) * ‖u - v‖) :=
      mul_le_mul_of_nonneg_left hbase (abs_nonneg c)
    _ ≤ |c| * ((|Rbar| + |RL|) * ‖u - v‖) := by
      gcongr
    _ = supportProcessDirectionConstant c s R RL * ‖u - v‖ := by
      simp only [supportProcessDirectionConstant, Rbar]
      ring

/-- The preceding pointwise estimate packaged as a genuine global
`LipschitzWith` statement.  In particular, every realization of the scaled
support process has a continuous sample path in the direction variable.
@isnad1 id=lipschit.6h8v.s7.ac3399d41550 from=translated src=- shape=347ed11a vocab=eb12e05a
-/
theorem lipschitzWith_scaledCenteredSupportProcess
    {I : Type*} (c : ℝ) (s : Finset I) (K : I → Set E) (L : Set E)
    (R : I → ℝ) (RL : ℝ)
    (hKcompact : ∀ i ∈ s, IsCompact (K i))
    (hKne : ∀ i ∈ s, (K i).Nonempty)
    (hLcompact : IsCompact L) (hLne : L.Nonempty)
    (hR : ∀ i ∈ s, ∀ x ∈ K i, ‖x‖ ≤ R i)
    (hRL : ∀ x ∈ L, ‖x‖ ≤ RL) :
    LipschitzWith
      ⟨supportProcessDirectionConstant c s R RL,
        supportProcessDirectionConstant_nonneg c s R RL⟩
      (scaledCenteredSupportProcess c s K L) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  change dist (scaledCenteredSupportProcess c s K L u)
      (scaledCenteredSupportProcess c s K L v) ≤
    supportProcessDirectionConstant c s R RL * dist u v
  simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs] using
    abs_scaledCenteredSupportProcess_sub_le
      c s K L R RL hKcompact hKne hLcompact hLne hR hRL u v

/-- In finite dimension the absolute scaled support process attains its
maximum on the unit sphere.  Thus the supremum occurring in pointwise
random-set limit statements is an actual finite maximum for every sample.
@isnad1 id=ex.6h8v.s8.8b116bc24c37 from=translated src=- shape=3c26099c vocab=9595f433
-/
theorem exists_unitSphere_isMax_abs_scaledCenteredSupportProcess
    {I : Type*} [FiniteDimensional ℝ E] [Nontrivial E]
    (c : ℝ) (s : Finset I) (K : I → Set E) (L : Set E)
    (R : I → ℝ) (RL : ℝ)
    (hKcompact : ∀ i ∈ s, IsCompact (K i))
    (hKne : ∀ i ∈ s, (K i).Nonempty)
    (hLcompact : IsCompact L) (hLne : L.Nonempty)
    (hR : ∀ i ∈ s, ∀ x ∈ K i, ‖x‖ ≤ R i)
    (hRL : ∀ x ∈ L, ‖x‖ ≤ RL) :
    ∃ u ∈ Metric.sphere (0 : E) 1,
      ∀ v ∈ Metric.sphere (0 : E) 1,
        |scaledCenteredSupportProcess c s K L v| ≤
          |scaledCenteredSupportProcess c s K L u| := by
  have hcont : Continuous
      (fun u : E ↦ |scaledCenteredSupportProcess c s K L u|) :=
    (lipschitzWith_scaledCenteredSupportProcess
      c s K L R RL hKcompact hKne hLcompact hLne hR hRL).continuous.abs
  obtain ⟨u, hu, humax⟩ :=
    (isCompact_sphere (0 : E) 1).exists_isMaxOn
      (NormedSpace.sphere_nonempty.mpr zero_le_one) hcont.continuousOn
  exact ⟨u, hu, fun v hv ↦ humax hv⟩

/-- Stability of the support process when both the empirical average and its
centering target are changed.  The hypotheses may come from arbitrary
support-function estimates; the next theorem supplies them automatically
from Hausdorff distances.
@isnad1 id=le.2h11v.s7.8c8d21d8e131 from=translated src=- shape=7ab75599 vocab=69fff529
-/
theorem abs_scaledCenteredSupportProcess_change_sets_le
    {I : Type*} (c : ℝ) (s : Finset I)
    (K K' : I → Set E) (L L' : Set E) (u : E) {a b : ℝ}
    (hK : |supportFunction (minkowskiAverage s K) u -
      supportFunction (minkowskiAverage s K') u| ≤ a)
    (hL : |supportFunction L u - supportFunction L' u| ≤ b) :
    |scaledCenteredSupportProcess c s K L u -
        scaledCenteredSupportProcess c s K' L' u| ≤
      |c| * (a + b) := by
  calc
    |scaledCenteredSupportProcess c s K L u -
        scaledCenteredSupportProcess c s K' L' u| =
        |c| * |(supportFunction (minkowskiAverage s K) u -
          supportFunction (minkowskiAverage s K') u) -
          (supportFunction L u - supportFunction L' u)| := by
      rw [scaledCenteredSupportProcess, scaledCenteredSupportProcess]
      rw [← mul_sub, abs_mul]
      congr 2
      ring
    _ ≤ |c| *
        (|supportFunction (minkowskiAverage s K) u -
            supportFunction (minkowskiAverage s K') u| +
          |supportFunction L u - supportFunction L' u|) := by
      gcongr
      exact abs_sub _ _
    _ ≤ |c| * (a + b) := by
      gcongr

/-- Hausdorff perturbation bound for the centred and scaled support process.
It controls changes in a parameter whenever the empirical averages and the
population targets are Hausdorff-continuous in that parameter.
@isnad1 id=le.8h9v.s8.42a32f68d321 from=translated src=- shape=57361aab vocab=8d423732
-/
theorem abs_scaledCenteredSupportProcess_change_sets_le_hausdorffDist
    {I : Type*} (c : ℝ) (s : Finset I)
    (K K' : I → Set E) (L L' : Set E)
    (hKcompact : ∀ i ∈ s, IsCompact (K i))
    (hKne : ∀ i ∈ s, (K i).Nonempty)
    (hK'compact : ∀ i ∈ s, IsCompact (K' i))
    (hK'ne : ∀ i ∈ s, (K' i).Nonempty)
    (hLcompact : IsCompact L) (hLne : L.Nonempty)
    (hL'compact : IsCompact L') (hL'ne : L'.Nonempty) (u : E) :
    |scaledCenteredSupportProcess c s K L u -
        scaledCenteredSupportProcess c s K' L' u| ≤
      |c| * ‖u‖ *
        (hausdorffDist (minkowskiAverage s K) (minkowskiAverage s K') +
          hausdorffDist L L') := by
  have hAvgCompact : IsCompact (minkowskiAverage s K) :=
    isCompact_minkowskiAverage s K hKcompact
  have hAvgNe : (minkowskiAverage s K).Nonempty :=
    nonempty_minkowskiAverage s K hKne
  have hAvg'Compact : IsCompact (minkowskiAverage s K') :=
    isCompact_minkowskiAverage s K' hK'compact
  have hAvg'Ne : (minkowskiAverage s K').Nonempty :=
    nonempty_minkowskiAverage s K' hK'ne
  have h := abs_scaledCenteredSupportProcess_change_sets_le
    c s K K' L L' u
    (abs_supportFunction_sub_le_hausdorffDist
      hAvgCompact hAvg'Compact hAvgNe hAvg'Ne u)
    (abs_supportFunction_sub_le_hausdorffDist
      hLcompact hL'compact hLne hL'ne u)
  calc
    |scaledCenteredSupportProcess c s K L u -
        scaledCenteredSupportProcess c s K' L' u| ≤
        |c| * (‖u‖ *
          hausdorffDist (minkowskiAverage s K) (minkowskiAverage s K') +
          ‖u‖ * hausdorffDist L L') := h
    _ = |c| * ‖u‖ *
        (hausdorffDist (minkowskiAverage s K) (minkowskiAverage s K') +
          hausdorffDist L L') := by ring

/-- Finite-net interpolation for the scaled support process.  If its
absolute value is at most `t` on an `eps`-net of the unit ball, it is at most
`t + C * eps` everywhere on the unit ball, where `C` is the explicit
pathwise directional modulus.
@isnad1 id=le.9h12v.s8.b6221276e1b4 from=translated src=- shape=6f0c8f15 vocab=627002cc
-/
theorem abs_scaledCenteredSupportProcess_le_of_finset_net
    {I : Type*} (c : ℝ) (s : Finset I) (K : I → Set E) (L : Set E)
    (R : I → ℝ) (RL eps t : ℝ) (N : Finset E)
    (hKcompact : ∀ i ∈ s, IsCompact (K i))
    (hKne : ∀ i ∈ s, (K i).Nonempty)
    (hLcompact : IsCompact L) (hLne : L.Nonempty)
    (hR : ∀ i ∈ s, ∀ x ∈ K i, ‖x‖ ≤ R i)
    (hRL : ∀ x ∈ L, ‖x‖ ≤ RL)
    (hnet : ∀ u : E, ‖u‖ ≤ 1 → ∃ v ∈ N, dist u v ≤ eps)
    (hN : ∀ v ∈ N, |scaledCenteredSupportProcess c s K L v| ≤ t) :
    ∀ u : E, ‖u‖ ≤ 1 →
      |scaledCenteredSupportProcess c s K L u| ≤
        t + supportProcessDirectionConstant c s R RL * eps := by
  intro u hu
  obtain ⟨v, hvN, huv⟩ := hnet u hu
  have hmod := abs_scaledCenteredSupportProcess_sub_le
    c s K L R RL hKcompact hKne hLcompact hLne hR hRL u v
  have hdist : ‖u - v‖ ≤ eps := by
    simpa only [dist_eq_norm] using huv
  have hmod' :
      |scaledCenteredSupportProcess c s K L u -
        scaledCenteredSupportProcess c s K L v| ≤
        supportProcessDirectionConstant c s R RL * eps :=
    hmod.trans <| mul_le_mul_of_nonneg_left hdist
      (supportProcessDirectionConstant_nonneg c s R RL)
  calc
    |scaledCenteredSupportProcess c s K L u| =
        |scaledCenteredSupportProcess c s K L v +
          (scaledCenteredSupportProcess c s K L u -
            scaledCenteredSupportProcess c s K L v)| := by
      congr 1
      ring
    _ ≤ |scaledCenteredSupportProcess c s K L v| +
        |scaledCenteredSupportProcess c s K L u -
          scaledCenteredSupportProcess c s K L v| := abs_add_le _ _
    _ ≤ t + supportProcessDirectionConstant c s R RL * eps :=
      add_le_add (hN v hvN) hmod'

/-- Contrapositive form of finite-net interpolation: a deviation above the
interpolated threshold somewhere on the unit ball is witnessed above `t` at
one of the net points.  This is the exact deterministic inclusion used by
finite-net probability bounds.
@isnad1 id=ex.8h11v.s8.672640f0dfce from=translated src=- shape=3ea394aa vocab=90a10425
-/
theorem exists_finset_gt_of_exists_unitBall_gt_scaledCenteredSupportProcess
    {I : Type*} (c : ℝ) (s : Finset I) (K : I → Set E) (L : Set E)
    (R : I → ℝ) (RL eps t : ℝ) (N : Finset E)
    (hKcompact : ∀ i ∈ s, IsCompact (K i))
    (hKne : ∀ i ∈ s, (K i).Nonempty)
    (hLcompact : IsCompact L) (hLne : L.Nonempty)
    (hR : ∀ i ∈ s, ∀ x ∈ K i, ‖x‖ ≤ R i)
    (hRL : ∀ x ∈ L, ‖x‖ ≤ RL)
    (hnet : ∀ u : E, ‖u‖ ≤ 1 → ∃ v ∈ N, dist u v ≤ eps)
    (hlarge : ∃ u : E, ‖u‖ ≤ 1 ∧
      t + supportProcessDirectionConstant c s R RL * eps <
        |scaledCenteredSupportProcess c s K L u|) :
    ∃ v ∈ N, t < |scaledCenteredSupportProcess c s K L v| := by
  by_contra hsmall
  have hN : ∀ v ∈ N,
      |scaledCenteredSupportProcess c s K L v| ≤ t := by
    intro v hv
    exact le_of_not_gt fun hvt ↦ hsmall ⟨v, hv, hvt⟩
  obtain ⟨u, hu, hult⟩ := hlarge
  have hule := abs_scaledCenteredSupportProcess_le_of_finset_net
    c s K L R RL eps t N hKcompact hKne hLcompact hLne hR hRL hnet hN u hu
  exact (not_lt_of_ge hule) hult

end RandomSetTheory
