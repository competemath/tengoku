import Tengoku.OpenaiMath.OAI.Analysis.SegmentLenses.LawRecovery

namespace OAI

/-!
# Common finite norming tests and head localization
-/

noncomputable section

open scoped BigOperators
open Finset

namespace SegmentLenses

theorem exists_norming_unitBall {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E →L[ℝ] ℝ) :
    ∃ p : E, ‖p‖ ≤ 1 ∧ f p = ‖f‖ := by
  obtain ⟨p, hp, hmax⟩ := (isCompact_closedBall (0 : E) (1 : ℝ)).exists_isMaxOn
    (by exact ⟨0, by simp⟩) f.continuous.continuousOn
  have hpn : ‖p‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hp
  have hpos : 0 ≤ f p := by
    have h := hmax (by simp : (0 : E) ∈ Metric.closedBall 0 1)
    simpa only [Set.mem_ofPred_eq, map_zero] using h
  have hupper : ‖f‖ ≤ f p := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm hpos
    intro v hv
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor
    · have h := hmax (show -v ∈ Metric.closedBall (0 : E) 1 by
        simp only [Metric.mem_closedBall, dist_zero_right, norm_neg, hv, le_refl])
      change f (-v) ≤ f p at h
      rw [map_neg] at h
      linarith
    · exact hmax (by simpa only [Metric.mem_closedBall, dist_zero_right, hv] using le_rfl)
  have hlower : f p ≤ ‖f‖ := calc
    f p ≤ |f p| := le_abs_self _
    _ ≤ ‖f‖ * ‖p‖ := f.le_opNorm p
    _ ≤ ‖f‖ := mul_le_of_le_one_right (norm_nonneg _) hpn
  exact ⟨p, hpn, le_antisymm hlower hupper⟩

section HeadTests
variable {V : Type*} [decidableEqV : DecidableEq V] [SegmentSystem V]

def headTestSpace (H : Finset V) : Submodule ℝ (Test V) where
  carrier := {u | ∀ v ∉ H, u.coeff v = 0}
  zero_mem' := by intro v hv; rfl
  add_mem' := by intro u v hu hv w hw; exact (show u.coeff w + v.coeff w = 0 by rw [hu w hw, hv w hw, add_zero])
  smul_mem' := by intro a u hu w hw; exact (show a * u.coeff w = 0 by rw [hu w hw, mul_zero])

def restrictDual (H : Finset V) (x : FullDual V) : headTestSpace H →L[ℝ] ℝ :=
  x.comp ((UniformSpace.Completion.toComplL : Test V →L[ℝ] Primal V).comp (headTestSpace H).subtypeL)

end HeadTests

section NormingTest
variable {V : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V] [TreeOrder V]
  [SegmentSystem V] [IntervalSegments V]

end NormingTest

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]

theorem nonempty (μ : FiniteLaw Ω) : Nonempty Ω := by
  by_contra hn
  let : IsEmpty Ω := ⟨fun ω => hn ⟨ω⟩⟩
  have ht := μ.total
  simp at ht

theorem abs_mean_le (μ : FiniteLaw Ω) (f : Ω → ℝ) :
    |μ.mean f| ≤ μ.mean (fun ω => |f ω|) := by
  simpa only [expect_scalar, Real.norm_eq_abs] using μ.norm_expect_le f

theorem mean_mul_right (μ : FiniteLaw Ω) (f : Ω → ℝ) (c : ℝ) :
    μ.mean (fun ω => f ω * c) = μ.mean f * c := by
  simpa only [mul_comm] using μ.mean_mul c f

end FiniteLaw

section ConeReconstruction
variable {V Ω : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V] [TreeOrder V]
  [SegmentSystem V] [IntervalSegments V] [Fintype Ω]

end ConeReconstruction

end SegmentLenses

end

end OAI
