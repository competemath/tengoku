import Tengoku.Seed.Analysis.Normed.Operator.Mul
import Tengoku.Seed.Analysis.Normed.Operator.LinearIsometry

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Scalar coordinates on rigid endomorphism algebras

If every bounded endomorphism of a nontrivial normed space `E` is a scalar, then `T ↦ s` is a
multiplicative linear isometry `(E →L[K] E) ≃ K`.
-/

noncomputable section

namespace AlternatingAnalytic.RigidDenseSource

variable {K E : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup E] [NormedSpace K E] [Nontrivial E]

/-- `s ↦ s • id` is a linear isometry `K → (E →L[K] E)`.-/
def scalarActionIsometry : K →ₗᵢ[K] (E →L[K] E) where
  toLinearMap := (ContinuousLinearMap.lsmul K K).toLinearMap
  norm_map' s := ContinuousLinearMap.opNorm_lsmul_apply K K (a := s)

@[simp]
theorem scalarActionIsometry_apply (s : K) :
    scalarActionIsometry (E := E) s = s • ContinuousLinearMap.id K E := by
  ext x
  rfl

variable (hr : ∀ T : E →L[K] E, ∃ s : K, ∀ x, T x = s • x)

/-- The isometry `(E →L[K] E) ≃ K` when every endomorphism is a scalar.-/
def endScalarEquivOfRigidity : (E →L[K] E) ≃ₗᵢ[K] K :=
  (LinearIsometryEquiv.ofSurjective (scalarActionIsometry (K := K) (E := E))
    (fun T => by
      obtain ⟨s, hs⟩ := hr T
      exact ⟨s, ContinuousLinearMap.ext (fun x => (hs x).symm)⟩)).symm

@[simp]
theorem endScalarEquivOfRigidity_symm_apply (s : K) :
    (endScalarEquivOfRigidity hr).symm s = s • ContinuousLinearMap.id K E := by
  change scalarActionIsometry s = _
  exact scalarActionIsometry_apply s

theorem endScalarEquivOfRigidity_apply (T : E →L[K] E) (x : E) :
    T x = endScalarEquivOfRigidity hr T • x := by
  have h := (endScalarEquivOfRigidity hr).symm_apply_apply T
  rw [endScalarEquivOfRigidity_symm_apply] at h
  exact (congrArg (fun U : E →L[K] E => U x) h).symm

@[simp]
theorem norm_endScalarEquivOfRigidity (T : E →L[K] E) :
    ‖endScalarEquivOfRigidity hr T‖ = ‖T‖ :=
  (endScalarEquivOfRigidity hr).norm_map T

@[simp]
theorem endScalarEquivOfRigidity_id :
    endScalarEquivOfRigidity hr (ContinuousLinearMap.id K E) = 1 := by
  apply (endScalarEquivOfRigidity hr).symm.injective
  simp

@[simp]
theorem endScalarEquivOfRigidity_comp (T U : E →L[K] E) :
    endScalarEquivOfRigidity hr (T.comp U) =
      endScalarEquivOfRigidity hr T * endScalarEquivOfRigidity hr U := by
  apply (endScalarEquivOfRigidity hr).symm.injective
  simp only [LinearIsometryEquiv.symm_apply_apply, endScalarEquivOfRigidity_symm_apply]
  ext x
  simp only [ContinuousLinearMap.comp_apply, _root_.smul_apply,
    ContinuousLinearMap.id_apply]
  rw [endScalarEquivOfRigidity_apply hr T, endScalarEquivOfRigidity_apply hr U,
    mul_smul]

end AlternatingAnalytic.RigidDenseSource
