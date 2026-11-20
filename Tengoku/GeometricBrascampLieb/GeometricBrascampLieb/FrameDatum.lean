import Tengoku.GeometricBrascampLieb.GeometricBrascampLieb.Geometry
import Tengoku.Seed.Tactic.Linarith

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Constructing geometric data from a quadratic frame identity

Applications often supply a weighted identity of squared norms. Polarization
converts this to the operator resolution required by `Datum`.
-/

noncomputable section
open scoped BigOperators InnerProduct

namespace GeometricBrascampLieb

variable {ι E : Type*} {F : ι → Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℝ (F i)]
  [∀ i, CompleteSpace (F i)]

omit [CompleteSpace E] [∀ i, CompleteSpace (F i)] in
/--
@isnad1 id=eq.1h7v.s9.3990ad0ac1cc from=translated src=- shape=eca415e7 vocab=b8b995bf
-/
theorem sum_weight_inner_of_norm_sq
    (B : ∀ i, E →L[ℝ] F i) (c : ι → ℝ)
    (hframe : ∀ x, ∑ i, c i * ‖B i x‖ ^ 2 = ‖x‖ ^ 2) (x y : E) :
    ∑ i, c i * inner ℝ (B i x) (B i y) = inner ℝ x y := by
  have h := hframe (x + y)
  simp_rw [map_add, norm_add_sq_real, mul_add, Finset.sum_add_distrib] at h
  have hcross : (∑ i, c i * (2 * inner ℝ (B i x) (B i y))) =
      2 * ∑ i, c i * inner ℝ (B i x) (B i y) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hframe x, hframe y, hcross] at h
  linarith

/--
@isnad1 id=eq.1h5v.s12.2fb4d7fce0d6 from=translated src=- shape=75c6c2b4 vocab=a0fa638f
-/
theorem resolution_of_norm_sq
    (B : ∀ i, E →L[ℝ] F i) (c : ι → ℝ)
    (hframe : ∀ x, ∑ i, c i * ‖B i x‖ ^ 2 = ‖x‖ ^ 2) :
    ∑ i, c i • (B i).adjoint.comp (B i) = ContinuousLinearMap.id ℝ E := by
  ext x
  apply ext_inner_right ℝ
  intro y
  simpa only [sum_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, sum_inner,
    real_inner_smul_left, ContinuousLinearMap.adjoint_inner_left] using
    sum_weight_inner_of_norm_sq B c hframe x y

/-- A quadratic frame identity and the coisometry conditions supply geometric data.-/
def Datum.ofNormSq
    (B : ∀ i, E →L[ℝ] F i) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hco : ∀ i, (B i).comp (B i).adjoint = ContinuousLinearMap.id ℝ (F i))
    (hframe : ∀ x, ∑ i, c i * ‖B i x‖ ^ 2 = ‖x‖ ^ 2) : Datum ι E F where
  weight := c
  weight_nonneg := hc
  map := B
  coisometry := hco
  resolution := resolution_of_norm_sq B c hframe

end GeometricBrascampLieb
