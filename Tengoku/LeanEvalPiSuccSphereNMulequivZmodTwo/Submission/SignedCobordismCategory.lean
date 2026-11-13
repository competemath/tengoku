import Tengoku
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.FiberSign

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Identity and reversal for signed framed cobordisms

Composition was constructed in `FiberSign`.  The identity cylinder and time
reversal complete the elementary categorical operations needed to splice local
Morse birth and saddle models into arbitrary finite traces.  In particular,
death and saddle-split realizations can be obtained by reversing birth and
merge realizations.
-/

noncomputable section

namespace Submission

open Set Function Metric
open scoped Topology RealInnerProductSpace ContDiff

variable {n : ℕ}

namespace FramedLevelCobordism

/-- Reverse the time coordinate by `t ↦ 1 - t`.-/
def reverseMap (C : FramedLevelCobordism n)
    (v : EuclideanSpace ℝ (Fin (n + 1 + 1))) : EuclideanSpace ℝ (Fin n) :=
  C.G (reparamMap n (-1) 1 v)

lemma contDiff_reverseMap (C : FramedLevelCobordism n) :
    ContDiff ℝ ∞ C.reverseMap :=
  C.smooth.comp (contDiff_reparamMap (-1) 1)

/-- Reversing time exchanges the source and target presentations.-/
def reverse (C : FramedLevelCobordism n) : FramedLevelCobordism n where
  X₀ := C.X₁
  X₁ := C.X₀
  G := C.reverseMap
  smooth := C.contDiff_reverseMap
  spatial_bounded := by
    obtain ⟨R, hR⟩ := C.spatial_bounded
    refine ⟨R, ?_⟩
    intro v hv
    have h := hR (reparamMap n (-1) 1 v) hv
    rw [reparamMap, initCLM_spaceTime] at h
    exact h
  regular := by
    intro v hv
    have hGd : HasFDerivAt C.G
        (fderiv ℝ C.G (reparamMap n (-1) 1 v))
        (reparamMap n (-1) 1 v) :=
      (C.smooth.differentiable infty_ne_zero _).hasFDerivAt
    have hfd : fderiv ℝ C.reverseMap v =
        (fderiv ℝ C.G (reparamMap n (-1) 1 v)).comp (reparamCLM n (-1)) := by
      exact (hGd.comp v (hasFDerivAt_reparamMap (-1) 1 v)).fderiv
    rw [hfd, ContinuousLinearMap.coe_comp]
    exact (C.regular _ hv).comp (surjective_reparamCLM (by norm_num))
  collar_zero := by
    intro x t ht
    change C.G (reparamMap n (-1) 1 (spaceTime x t)) = C.X₁.g x
    rw [reparamMap, initCLM_spaceTime, vertC_spaceTime]
    exact C.collar_one x (-1 * t + 1) (by linarith)
  collar_one := by
    intro x t ht
    change C.G (reparamMap n (-1) 1 (spaceTime x t)) = C.X₀.g x
    rw [reparamMap, initCLM_spaceTime, vertC_spaceTime]
    exact C.collar_zero x (-1 * t + 1) (by linarith)

@[simp] lemma reverse_X₀ (C : FramedLevelCobordism n) : C.reverse.X₀ = C.X₁ := rfl

@[simp] lemma reverse_X₁ (C : FramedLevelCobordism n) : C.reverse.X₁ = C.X₀ := rfl

end FramedLevelCobordism

namespace SignedFramedLevelCobordism

variable {X₀ X₁ : FramedLevelSet n} {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}

/-- The signed identity cylinder.-/
def refl (S : FiberSign X₀) : SignedFramedLevelCobordism S S where
  cobordism := FramedLevelCobordism.refl X₀
  source_eq := rfl
  target_eq := rfl
  toFun v := S (initCLM (n + 1) v)
  continuous := S.continuous.comp (initCLM (n + 1)).continuous
  nonzero := by
    intro v hv
    exact S.nonzero (initCLM (n + 1) v) hv
  collar_zero := by
    intro x t ht
    rw [initCLM_spaceTime]
  collar_one := by
    intro x t ht
    rw [initCLM_spaceTime]

/-- Time reversal of a signed cobordism.-/
def reverse (C : SignedFramedLevelCobordism S₀ S₁) :
    SignedFramedLevelCobordism S₁ S₀ where
  cobordism := C.cobordism.reverse
  source_eq := C.target_eq
  target_eq := C.source_eq
  toFun v := C (reparamMap n (-1) 1 v)
  continuous := C.continuous.comp (contDiff_reparamMap (-1) 1).continuous
  nonzero := by
    intro v hv
    exact C.nonzero (reparamMap n (-1) 1 v) hv
  collar_zero := by
    intro x t ht
    rw [reparamMap, initCLM_spaceTime, vertC_spaceTime]
    exact C.collar_one x (-1 * t + 1) (by linarith)
  collar_one := by
    intro x t ht
    rw [reparamMap, initCLM_spaceTime, vertC_spaceTime]
    exact C.collar_zero x (-1 * t + 1) (by linarith)

/-- Nonempty signed cobordism is a reflexive relation.-/
theorem nonempty_refl (S : FiberSign X₀) :
    Nonempty (SignedFramedLevelCobordism S S) :=
  ⟨refl S⟩

/-- Nonempty signed cobordism is symmetric.-/
theorem nonempty_symm
    (h : Nonempty (SignedFramedLevelCobordism S₀ S₁)) :
    Nonempty (SignedFramedLevelCobordism S₁ S₀) := by
  obtain ⟨C⟩ := h
  exact ⟨C.reverse⟩

/-- Nonempty signed cobordisms compose.-/
theorem nonempty_trans {X₂ : FramedLevelSet n} {S₂ : FiberSign X₂}
    (h₀₁ : Nonempty (SignedFramedLevelCobordism S₀ S₁))
    (h₁₂ : Nonempty (SignedFramedLevelCobordism S₁ S₂)) :
    Nonempty (SignedFramedLevelCobordism S₀ S₂) := by
  obtain ⟨C₀₁⟩ := h₀₁
  obtain ⟨C₁₂⟩ := h₁₂
  exact ⟨C₀₁.trans C₁₂⟩

end SignedFramedLevelCobordism

end Submission
