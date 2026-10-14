/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Endgame.CutoffMorrey
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology

/-!
# Causal bounded multipliers for linear heat sources

Indicated input measurability suffices for a supported product after
truncation to the past. Uniform multiplier bounds control its Morrey norm.
The improved velocity exponent supplies the linear velocity terms, while
a cutoff of absolute value at most one preserves pressure-gradient bounds.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey

noncomputable section

namespace CKN.Core.Endgame

/-- A scalar product restricted to nonpositive times. -/
def pastMultiplierSource (a f : ParabolicPoint → ℝ) : ParabolicPoint → ℝ :=
  {z : ParabolicPoint | z.2 ≤ 0}.indicator (fun z => a z * f z)

/-- The support of the past product lies in the intermediate cylinder.
@isnad1 id=eq.2h3v.s7.bd7c79c11a09 from=translated src=- shape=8700adac vocab=2c6112c3
-/
theorem pastMultiplierSource_zero_outside_intermediate
    {a f : ParabolicPoint → ℝ}
    (hsupp : ∀ z, z.2 ≤ 0 → z ∉ parabolicCylinder (0 : Vec3) 0 (5 / 8) → a z = 0)
    {z : ParabolicPoint} (hz : z ∉ parabolicCylinder (0 : Vec3) 0 (5 / 8)) :
    pastMultiplierSource a f z = 0 := by
  unfold pastMultiplierSource
  by_cases ht : z ∈ {w : ParabolicPoint | w.2 ≤ 0}
  · rw [indicator_of_mem ht, hsupp z ht hz, zero_mul]
  · exact indicator_of_notMem ht _

/-- The causal product is measurable without a global measurability
assumption on the original input.
@isnad1 id=aemeasur.3h2v.s7.32cc10977733 from=translated src=- shape=83dde968 vocab=aaef16cf
-/
theorem pastMultiplierSource_aemeasurable
    {a f : ParabolicPoint → ℝ}
    (ha : AEMeasurable a volume)
    (hf : AEMeasurable ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator f) volume)
    (hsupp : ∀ z, z.2 ≤ 0 → z ∉ parabolicCylinder (0 : Vec3) 0 (5 / 8) → a z = 0) :
    AEMeasurable (pastMultiplierSource a f) volume := by
  have hPast : MeasurableSet {z : ParabolicPoint | z.2 ≤ 0} :=
    (isClosed_le continuous_snd_parabolicPoint continuous_const).measurableSet
  have heq : pastMultiplierSource a f =
      {z : ParabolicPoint | z.2 ≤ 0}.indicator
        (fun z => a z * (parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator f z) := by
    funext z
    unfold pastMultiplierSource
    by_cases ht : z ∈ {w : ParabolicPoint | w.2 ≤ 0}
    · rw [indicator_of_mem ht, indicator_of_mem ht]
      by_cases hz : z ∈ parabolicCylinder (0 : Vec3) 0 (5 / 8)
      · rw [indicator_of_mem hz]
      · rw [indicator_of_notMem hz, hsupp z ht hz, zero_mul, mul_zero]
    · rw [indicator_of_notMem ht, indicator_of_notMem ht]
  rw [heq]
  exact (ha.mul hf).indicator hPast

/-- A bounded past multiplier preserves a Morrey exponent pair with its
explicit multiplier factor.
@isnad1 id=le.4h5v.s7.b3bd1a93b9af from=translated src=- shape=1a9fc559 vocab=6324aca8
-/
theorem pastMultiplierSource_morrey_le
    (P τ C : ℝ) (hP : 0 < P) (hC : 0 ≤ C)
    (a f : ParabolicPoint → ℝ)
    (hbound : ∀ z, z.2 ≤ 0 → |a z| ≤ C)
    (hsupp : ∀ z, z.2 ≤ 0 → z ∉ parabolicCylinder (0 : Vec3) 0 (5 / 8) → a z = 0) :
    morreyNorm P τ (pastMultiplierSource a f) ≤
      ENNReal.ofReal C * morreyNorm P τ
        ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator f) := by
  let b := {z : ParabolicPoint | z.2 ≤ 0}.indicator a
  have hb : ∀ z, |b z| ≤ C := by
    intro z
    by_cases ht : z ∈ {w : ParabolicPoint | w.2 ≤ 0}
    · simpa only [b, indicator_of_mem ht] using hbound z ht
    · simpa only [b, indicator_of_notMem ht, abs_zero] using hC
  have hbs : ∀ z ∉ parabolicCylinder (0 : Vec3) 0 (5 / 8), b z = 0 := by
    intro z hz
    by_cases ht : z ∈ {w : ParabolicPoint | w.2 ≤ 0}
    · simpa only [b, indicator_of_mem ht] using hsupp z ht hz
    · exact indicator_of_notMem ht _
  have heq : pastMultiplierSource a f = fun z => b z * f z := by
    funext z
    by_cases ht : z ∈ {w : ParabolicPoint | w.2 ≤ 0}
    · simp only [pastMultiplierSource, b, indicator_of_mem ht]
    · simp only [pastMultiplierSource, b, indicator_of_notMem ht, zero_mul]
  rw [heq]
  exact morrey_norm_mul_le_indicator P τ C hP hC
    (parabolicCylinder (0 : Vec3) 0 (5 / 8)) b f hb hbs

/-- A cutoff of absolute value at most one preserves the pressure-gradient
source exponent and its numerical bound.
@isnad1 id=and.5h4v.s8.3adcc0555f95 from=translated src=- shape=2464fb6a vocab=6c06f52b
-/
theorem causal_linear_pressure_source_morrey_le
    (q : ℝ) (KP : ℝ≥0∞) (a f : ParabolicPoint → ℝ)
    (ha : AEMeasurable a volume)
    (hf : AEMeasurable ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator f) volume)
    (hbound : ∀ z, z.2 ≤ 0 → |a z| ≤ 1)
    (hsupp : ∀ z, z.2 ≤ 0 → z ∉ parabolicCylinder (0 : Vec3) 0 (5 / 8) → a z = 0)
    (hN : morreyNorm (6 / 5) (min q (25 / 9 : ℝ))
      ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator f) ≤ KP) :
    AEMeasurable (pastMultiplierSource a f) volume ∧
      morreyNorm (6 / 5) (min q (25 / 9 : ℝ)) (pastMultiplierSource a f) ≤ KP := by
  refine ⟨pastMultiplierSource_aemeasurable ha hf hsupp, ?_⟩
  have hproduct := pastMultiplierSource_morrey_le (6 / 5) (min q (25 / 9)) 1
    (by norm_num) (by norm_num) a f hbound hsupp
  simp only [ENNReal.ofReal_one, one_mul] at hproduct
  exact hproduct.trans hN

end CKN.Core.Endgame
