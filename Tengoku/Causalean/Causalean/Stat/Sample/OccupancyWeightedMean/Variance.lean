/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Tengoku.Causalean.Causalean.Stat.Sample.OccupancyWeightedMean.MomentBounds

/-!
# Weak-moment variance bound for occupancy-weighted residual means

This module represents the occupancy-weighted statistic as a finite sum of
supported residuals, proves its square integrability, and bounds its second
moment by expected reciprocal usable occupancy. Outcomes need only supported
arm/group second moments; all empirical zero-count cases are totalized.
-/

@[expose] public section

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

variable {Omega kappa : Type*} [MeasurableSpace Omega]
  [Fintype kappa] [DecidableEq kappa]
  [MeasurableSpace kappa] [MeasurableSingletonClass kappa]

private noncomputable def occupancyResidualWeight {n : Nat}
    (d : Fin n → kappa × Bool) (a : Bool) (k : kappa) : Real := by
  classical
  exact if 0 < usableGroupTotal Prod.fst Prod.snd d then
      (usableGroupTotal Prod.fst Prod.snd d : Real)⁻¹ *
        if usableGroup Prod.fst Prod.snd d k then
          (groupCount Prod.fst Prod.snd d k : Real) *
            (if a then (groupArmCount Prod.fst Prod.snd d true k : Real)⁻¹
              else -(groupArmCount Prod.fst Prod.snd d false k : Real)⁻¹)
        else 0
    else 0

/-- If [group labels, arm labels, and outcomes are measurable](hyp:hgroup,harm,hY)
and [every arm/group-supported residual has a finite second moment](hyp:hmem),
[the zero-safe occupancy-weighted residual has a finite second moment under
every finite independent product sample](goal).
@isnad1 id=memlp.4h8v.s7.368c53585b59 from=translated src=- shape=43e06588 vocab=5ba7cf26
-/
theorem occupancyWeightedResidual_memLp_two
    {n : Nat} (mu : Measure Omega) [IsProbabilityMeasure mu]
    (group : Omega -> kappa) (arm : Omega -> Bool) (Y : Omega -> Real)
    (center : Bool -> kappa -> Real)
    (hgroup : Measurable group) (harm : Measurable arm) (hY : Measurable Y)
    (hmem : ∀ a k,
      MemLp (supportedArmGroupResidual group arm Y center a k) 2 mu) :
    MemLp (occupancyWeightedResidual (n := n) mu group arm Y center) 2
      (Measure.pi (fun _ : Fin n => mu)) := by
  -- Expand the statistic as a finite sum of supported residual coordinates.
  -- Its design coefficients range over a finite set, hence are bounded;
  -- close under finite sums and bounded scalar multiplication in `MemLp`.
  classical
  let weight : (Fin n → kappa × Bool) → Bool → kappa → Real :=
    occupancyResidualWeight
  let bound : Real := ∑ d : Fin n → kappa × Bool, ∑ a : Bool, ∑ k : kappa, |weight d a k|
  have hweight_bound (d : Fin n → kappa × Bool) (a : Bool) (k : kappa) :
      |weight d a k| ≤ bound := by
    dsimp [bound]
    calc
      |weight d a k| ≤ ∑ k' : kappa, |weight d a k'| :=
        Finset.single_le_sum (fun k' _ => abs_nonneg (weight d a k')) (Finset.mem_univ k)
      _ ≤ ∑ a' : Bool, ∑ k' : kappa, |weight d a' k'| :=
        Finset.single_le_sum
          (fun a' _ => Finset.sum_nonneg fun k' _ => abs_nonneg (weight d a' k'))
          (Finset.mem_univ a)
      _ ≤ ∑ d' : Fin n → kappa × Bool,
          ∑ a' : Bool, ∑ k' : kappa, |weight d' a' k'| :=
        Finset.single_le_sum
          (fun d' _ => Finset.sum_nonneg fun a' _ =>
            Finset.sum_nonneg fun k' _ => abs_nonneg (weight d' a' k'))
          (Finset.mem_univ d)
  have hterm (i : Fin n) (a : Bool) (k : kappa) :
      MemLp (fun z : Fin n → Omega =>
        weight (sampleDesign group arm z) a k *
          supportedArmGroupResidual group arm Y center a k (z i)) 2
        (Measure.pi (fun _ : Fin n => mu)) := by
    have hr := (hmem a k).comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin n => mu) i)
    have hw : Measurable (fun d : Fin n → kappa × Bool => weight d a k) :=
      Measurable.of_discrete
    apply hr.of_le_mul
    · have hm : AEStronglyMeasurable
          (((fun d : Fin n → kappa × Bool => weight d a k) ∘
              sampleDesign group arm) *
            (supportedArmGroupResidual group arm Y center a k ∘ fun z => z i))
          (Measure.pi (fun _ : Fin n => mu)) :=
        ((hw.comp (measurable_sampleDesign group arm hgroup harm)).mul
          ((measurable_supportedArmGroupResidual group arm Y center
            hgroup harm hY a k).comp (measurable_pi_apply i))).aestronglyMeasurable
      refine hm.congr ?_
      filter_upwards [] with z
      rfl
    · filter_upwards [] with z
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hweight_bound _ _ _) (abs_nonneg _)
  have hsum : MemLp (fun z : Fin n → Omega =>
      ∑ k : kappa, ∑ a : Bool, ∑ i : Fin n,
        weight (sampleDesign group arm z) a k *
          supportedArmGroupResidual group arm Y center a k (z i)) 2
      (Measure.pi (fun _ : Fin n => mu)) := by
    exact memLp_finsetSum Finset.univ fun k _ =>
      memLp_finsetSum Finset.univ fun a _ =>
        memLp_finsetSum Finset.univ fun i _ => hterm i a k
  convert hsum using 1
  funext z
  unfold occupancyWeightedResidual
  dsimp [weight, occupancyResidualWeight]
  change (if 0 < usableGroupTotal group arm z then
      (usableGroupTotal group arm z : Real)⁻¹ *
        ∑ k, if usableGroup group arm z k then
          (groupCount group arm z k : Real) *
            (armResidualMean group arm Y center z true k -
              armResidualMean group arm Y center z false k)
        else 0
    else 0) =
    ∑ k : kappa, ∑ a : Bool, ∑ i : Fin n,
      (if 0 < usableGroupTotal group arm z then
        (usableGroupTotal group arm z : Real)⁻¹ *
          if usableGroup group arm z k then
            (groupCount group arm z k : Real) *
              (if a then (groupArmCount group arm z true k : Real)⁻¹
                else -(groupArmCount group arm z false k : Real)⁻¹)
          else 0
      else 0) * supportedArmGroupResidual group arm Y center a k (z i)
  split_ifs with htotal
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases huk : usableGroup group arm z k
    · have hf : 0 < groupArmCount group arm z false k := huk.1
      have ht : 0 < groupArmCount group arm z true k := huk.2
      simp only [huk, ite_eq_left, Fintype.sum_bool, armResidualMean,
        armResidualSum, hf, ht]
      simp only [Bool.false_eq_true, ite_false]
      rw [mul_sub]
      simp_rw [Finset.mul_sum]
      ring_nf
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_neg_distrib]
      ring_nf
    · simp [huk]
  · simp

end Causalean.Stat
