import Tengoku
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.OrbitUnknottingFramedCircleTube

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Relative support for generic framed-circle displacement extensions

The generic tube engine extends a periodic displacement by a radial bump.
This file supplies the compactness step needed in relative applications: if
an open set contains the core circle, the bump can be chosen so that its
entire compact support core lies in that open set.  Consequently the induced
small ambient isotopy fixes every set disjoint from the chosen support region.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace

namespace Submission
namespace SmoothFramedPeriodicCircle

variable {n : ℕ} (F : SmoothFramedPeriodicCircle n)

local notation "E" => EuclideanSpace ℝ (Fin (n + 1))
local notation "N" => EuclideanSpace ℝ (Fin n)
local notation "C" => AddCircle (1 : ℝ)

/-- A sufficiently thin closed tube about the zero section lies in every
prescribed open neighborhood of the core circle.-/
theorem exists_closedTube_subset_open {U : Set E}
    (hUopen : IsOpen U) (hcircle : Set.range F.circle ⊆ U) :
    ∃ r : ℝ, 0 < r ∧
      F.tube '' ((Set.univ : Set C) ×ˢ Metric.closedBall (0 : N) r) ⊆ U := by
  let T : Set (C × N) := F.tube ⁻¹' U
  have hTopen : IsOpen T := hUopen.preimage F.continuous_tube
  have hzero : (Set.univ : Set C) ×ˢ ({0} : Set N) ⊆ T := by
    rintro ⟨a, z⟩ ⟨-, hz⟩
    rw [Set.mem_singleton_iff] at hz
    change z = 0 at hz
    subst z
    exact hcircle ⟨a, F.tube_zero a |>.symm⟩
  obtain ⟨A, W, hAopen, hWopen, hCA, hzeroW, hAWT⟩ :=
    generalized_tube_lemma (X := C) (Y := N)
      isCompact_univ isCompact_singleton hTopen hzero
  have hzero_mem_W : (0 : N) ∈ W := hzeroW (Set.mem_singleton 0)
  rcases (Metric.isOpen_iff.mp hWopen) 0 hzero_mem_W with
    ⟨R, hR, hballW⟩
  let r : ℝ := R / 2
  have hr : 0 < r := by dsimp [r]; linarith
  have hrR : r < R := by dsimp [r]; linarith
  refine ⟨r, hr, ?_⟩
  rintro x ⟨q, hq, rfl⟩
  exact hAWT ⟨hCA (Set.mem_univ q.1),
    hballW (Metric.closedBall_subset_ball hrR hq.2)⟩

/-- A radial bump whose compact tube support lies inside the prescribed open
neighborhood, and also strictly inside the injective tube radius.-/
theorem exists_radialBump_supportCore_subset {U : Set E}
    (hUopen : IsOpen U) (hcircle : Set.range F.circle ⊆ U) :
    ∃ b : ContDiffBump (0 : N),
      b.rOut < F.globalSmoothTube.radius ∧
      F.tube '' ((Set.univ : Set C) ×ˢ
        Metric.closedBall (0 : N) b.rOut) ⊆ U := by
  obtain ⟨r, hr, hrU⟩ := F.exists_closedTube_subset_open hUopen hcircle
  let ρ : ℝ := min r F.globalSmoothTube.radius
  have hρ : 0 < ρ := lt_min hr F.globalSmoothTube.radius_pos
  let b : ContDiffBump (0 : N) := {
    rIn := ρ / 3
    rOut := ρ / 2
    rIn_pos := by linarith
    rIn_lt_rOut := by linarith
  }
  have hbρ : b.rOut < ρ := by dsimp [b]; linarith
  have hbr : b.rOut < r := hbρ.trans_le (min_le_left _ _)
  have hbTube : b.rOut < F.globalSmoothTube.radius :=
    hbρ.trans_le (min_le_right _ _)
  refine ⟨b, hbTube, ?_⟩
  intro x hx
  apply hrU
  exact Set.image_mono (Set.prod_mono_right
    (Metric.closedBall_subset_closedBall hbr.le)) hx

namespace PeriodicDisplacementExtensionData

variable {F : SmoothFramedPeriodicCircle n}
variable (D : F.PeriodicDisplacementExtensionData)

/-- If the compact support core was placed in `U`, the ambient field
vanishes pointwise outside `U`.-/
theorem ambientField_eq_zero_of_supportCore_subset {U : Set E}
    (hcore : D.supportCore ⊆ U) {x : E} (hx : x ∉ U) :
    D.ambientField x = 0 := by
  apply D.ambientField_eq_zero_of_not_mem_supportCore
  exact fun hxs => hx (hcore hxs)

/-- Feed an unscaled extension with a Lipschitz constant below one into the
global ambient-isotopy primitive.-/
def toSmallAmbientDisplacement (K : ℝ≥0) (hK : K < 1)
    (hLip : LipschitzWith K D.ambientField) :
    SmallAmbientDisplacement n where
  field := D.ambientField
  smooth := D.contDiff_ambientField
  K := K
  K_lt_one := hK
  lipschitz := hLip

/-- Scaling a supported extension preserves all support properties and is
small whenever the scaled Lipschitz constant is below one.-/
def toScaledSmallAmbientDisplacement (r : ℝ) (K : ℝ≥0)
    (hLip : LipschitzWith K D.ambientField)
    (hsmall : ‖r‖₊ * K < 1) : SmallAmbientDisplacement n where
  field := fun x => r • D.ambientField x
  smooth := D.contDiff_ambientField.const_smul r
  K := ‖r‖₊ * K
  K_lt_one := hsmall
  lipschitz := by
    simpa [Function.comp_def] using (lipschitzWith_smul r).comp hLip

end PeriodicDisplacementExtensionData
end SmoothFramedPeriodicCircle
end Submission
