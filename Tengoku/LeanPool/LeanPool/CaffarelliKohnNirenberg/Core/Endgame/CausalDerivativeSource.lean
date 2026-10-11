/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Endgame.CutoffMorrey
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Endgame.OneSidedCutoff
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Step4.SourceMorreyGradient
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Setting.ScalingInvarianceTests

/-!
# The concrete causal differentiated cutoff source

The paper source `-2 ∂ⱼφ uᵢ`, truncated to the past, is measurable using
only local suitable-solution data. Its support and Morrey bound follow
from the cutoff support, its derivative bound, and initial velocity norms.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.Step3

noncomputable section

namespace CKN.Core.Endgame

/-- A scalar component of the differentiated cutoff source in the past. -/
def causalDerivativeComponent (φ : Vec3 × ℝ → ℝ) (u : ParabolicPoint → Vec3)
    (j i : Fin 3) : ParabolicPoint → ℝ :=
  {z : ParabolicPoint | z.2 ≤ 0}.indicator
    (fun z => CKN.Core.Step4.localizedGradientSourceH φ u j z i)

private theorem spatialPartial_zero_on_past_outside_intermediate
    {φ : Vec3 × ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hsupp : ∀ z ∈ tsupport φ, z.2 ≤ 0 →
      parabolicHomeomorph.symm z ∈ parabolicCylinder (0 : Vec3) 0 (5 / 8))
    (j : Fin 3) (z : ParabolicPoint) (ht : z.2 ≤ 0)
    (hz : z ∉ parabolicCylinder (0 : Vec3) 0 (5 / 8)) : spatialPartial φ j z = 0 := by
  apply spatialPartial_zero_of_not_mem_tsupport_public hφ _ j
  intro hmem
  exact hz (hsupp (z.1, z.2) hmem ht)

/-- The causal differentiated source vanishes outside the intermediate
cylinder, including at future times. -/
theorem causalDerivativeComponent_zero_outside_intermediate
    {φ : Vec3 × ℝ → ℝ} {u : ParabolicPoint → Vec3}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hsupp : ∀ z ∈ tsupport φ, z.2 ≤ 0 →
      parabolicHomeomorph.symm z ∈ parabolicCylinder (0 : Vec3) 0 (5 / 8))
    (j i : Fin 3) {z : ParabolicPoint}
    (hz : z ∉ parabolicCylinder (0 : Vec3) 0 (5 / 8)) :
    causalDerivativeComponent φ u j i z = 0 := by
  unfold causalDerivativeComponent
  by_cases ht : z ∈ {w : ParabolicPoint | w.2 ≤ 0}
  · rw [indicator_of_mem ht]
    change (-2 * spatialPartial φ j z) * u z i = 0
    rw [spatialPartial_zero_on_past_outside_intermediate hφ hsupp j z ht hz,
      mul_zero, zero_mul]
  · exact indicator_of_notMem ht _

/-- The causal differentiated source is globally measurable once the
indicated velocity component is measurable. No global velocity assumption
is required. -/
theorem causalDerivativeComponent_aemeasurable
    {φ : Vec3 × ℝ → ℝ} {u : ParabolicPoint → Vec3}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hsupp : ∀ z ∈ tsupport φ, z.2 ≤ 0 →
      parabolicHomeomorph.symm z ∈ parabolicCylinder (0 : Vec3) 0 (5 / 8))
    (j i : Fin 3)
    (hu : AEMeasurable ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator
      (fun z => u z i)) volume) :
    AEMeasurable (causalDerivativeComponent φ u j i) volume := by
  have hpartial : Continuous (fun z : ParabolicPoint => spatialPartial φ j z) :=
    (spatialPartial_contDiff hφ j).continuous.comp continuous_parabolicPoint_to_prod
  have hPast : MeasurableSet {z : ParabolicPoint | z.2 ≤ 0} :=
    (isClosed_le continuous_snd_parabolicPoint continuous_const).measurableSet
  have heq : causalDerivativeComponent φ u j i =
      {z : ParabolicPoint | z.2 ≤ 0}.indicator
        (fun z => (-2 * spatialPartial φ j z) *
          (parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator (fun w => u w i) z) := by
    funext z
    unfold causalDerivativeComponent
    by_cases ht : z ∈ {w : ParabolicPoint | w.2 ≤ 0}
    · rw [indicator_of_mem ht, indicator_of_mem ht]
      by_cases hz : z ∈ parabolicCylinder (0 : Vec3) 0 (5 / 8)
      · rw [indicator_of_mem hz]
        rfl
      · rw [indicator_of_notMem hz, mul_zero]
        change (-2 * spatialPartial φ j z) * u z i = 0
        rw [spatialPartial_zero_on_past_outside_intermediate hφ hsupp j z ht hz,
          mul_zero, zero_mul]
    · rw [indicator_of_notMem ht, indicator_of_notMem ht]
  rw [heq]
  exact ((aemeasurable_const.mul hpartial.aemeasurable).mul hu).indicator hPast

end CKN.Core.Endgame
