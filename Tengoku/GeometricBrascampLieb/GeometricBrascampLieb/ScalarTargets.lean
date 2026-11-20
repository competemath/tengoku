import Tengoku.GeometricBrascampLieb.GeometricBrascampLieb.FrameDatum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Scalar targets and restriction to real scalars

A norm-one real or complex functional is a coisometry. Restricting scalars
commutes with adjoints for any real inner product inducing the same norm;
this avoids replacing the existing real inner product or volume instance.
-/

noncomputable section
open scoped InnerProduct

namespace GeometricBrascampLieb

section Scalar
variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/--
@isnad1 id=eq.0h3v.s9.347f1881bd46 from=translated src=- shape=1bdd5e36 vocab=eadd3740
-/
theorem norm_scalar_source (A : 𝕜 →L[𝕜] E) : ‖A‖ = ‖A 1‖ := by
  apply le_antisymm
  · apply A.opNorm_le_bound (norm_nonneg _)
    intro z
    calc
      ‖A z‖ = ‖A (z • (1 : 𝕜))‖ := by rw [smul_eq_mul, mul_one]
      _ = ‖z‖ * ‖A 1‖ := by rw [map_smul, norm_smul]
      _ ≤ ‖A 1‖ * ‖z‖ := le_of_eq (mul_comm _ _)
  · simpa only [norm_one, mul_one] using A.le_opNorm (1 : 𝕜)

/--
@isnad1 id=eq.1h3v.s12.a69182151c8c from=translated src=- shape=ce0648db vocab=4705a148
-/
theorem scalar_coisometry_of_norm_one [CompleteSpace E]
    (B : E →L[𝕜] 𝕜) (hB : ‖B‖ = 1) :
    B.comp B.adjoint = ContinuousLinearMap.id 𝕜 𝕜 := by
  have hunit : ‖B.adjoint 1‖ = 1 := by
    rw [← norm_scalar_source, ContinuousLinearMap.adjoint.norm_map, hB]
  have hiso : ∀ z : 𝕜, ‖B.adjoint z‖ = ‖z‖ := by
    intro z
    calc
      ‖B.adjoint z‖ = ‖B.adjoint (z • (1 : 𝕜))‖ := by rw [smul_eq_mul, mul_one]
      _ = ‖z‖ := by rw [map_smul, norm_smul, hunit, mul_one]
  simpa only [ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.one_def] using
    B.adjoint.norm_map_iff_adjoint_comp_self.mp hiso

end Scalar

section RestrictScalars
variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [InnerProductSpace ℝ F]

/-- Polarization identifies the real inner product without changing its instance.
@isnad1 id=eq.0h4v.s7.a9208a556226 from=translated src=- shape=c6cc4c2f vocab=808bc567
-/
theorem real_inner_eq_re_of_same_norm (x y : E) :
    inner ℝ x y = RCLike.re (inner 𝕜 x y) := by
  rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
    re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two]

variable [CompleteSpace E] [CompleteSpace F]
  [IsScalarTower ℝ 𝕜 E] [IsScalarTower ℝ 𝕜 F]

/--
@isnad1 id=eq.0h4v.s12.84c4f442e853 from=translated src=- shape=a8bc9740 vocab=4f27a639
-/
theorem adjoint_restrictScalars (B : E →L[𝕜] F) :
    (B.restrictScalars ℝ).adjoint = B.adjoint.restrictScalars ℝ := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  change inner ℝ (B.adjoint x) y = inner ℝ x (B y)
  rw [real_inner_eq_re_of_same_norm (𝕜 := 𝕜),
    real_inner_eq_re_of_same_norm (𝕜 := 𝕜), ContinuousLinearMap.adjoint_inner_left]

/--
@isnad1 id=eq.1h4v.s12.9da194ccd32d from=translated src=- shape=50279ee1 vocab=cea226c0
-/
theorem coisometry_restrictScalars (B : E →L[𝕜] F)
    (hB : B.comp B.adjoint = ContinuousLinearMap.id 𝕜 F) :
    (B.restrictScalars ℝ).comp (B.restrictScalars ℝ).adjoint =
      ContinuousLinearMap.id ℝ F := by
  rw [adjoint_restrictScalars]
  ext x
  exact congrArg (fun A : F →L[𝕜] F => A x) hB

end RestrictScalars
end GeometricBrascampLieb
