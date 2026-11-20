import Tengoku.GeometricBrascampLieb.GeometricBrascampLieb.GaussianIntegrability
import Tengoku.Seed.Analysis.InnerProductSpace.Trace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Continuous trace and spatial regularity of the heat functional -/

noncomputable section
open scoped BigOperators

namespace GeometricBrascampLieb

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def operatorTrace : (E →L[ℝ] E) →L[ℝ] ℝ :=
  ∑ i, (innerSL ℝ (stdOrthonormalBasis ℝ E i)).comp
    (ContinuousLinearMap.apply ℝ E (stdOrthonormalBasis ℝ E i))

/--
@isnad1 id=eq.0h2v.s10.1f577858169b from=translated src=- shape=76ad10c2 vocab=4a7f3917
-/
theorem operatorTrace_apply (A : E →L[ℝ] E) :
    operatorTrace A = LinearMap.trace ℝ E A.toLinearMap := by
  simpa only [operatorTrace, sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply, innerSL_apply_apply, ContinuousLinearMap.coe_coe] using
    (LinearMap.trace_eq_sum_inner A.toLinearMap (stdOrthonormalBasis ℝ E)).symm

/--
@isnad1 id=le.0h2v.s10.b0f37bf0506a from=translated src=- shape=449b4f8b vocab=034eb8ae
-/
theorem norm_trace_le (A : E →L[ℝ] E) :
    ‖LinearMap.trace ℝ E A.toLinearMap‖ ≤ ‖operatorTrace (E := E)‖*‖A‖ := by
  rw [← operatorTrace_apply]
  exact ContinuousLinearMap.le_opNorm _ _

namespace Datum

variable {ι : Type*} {F : ι → Type*} [Fintype ι] [CompleteSpace E]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℝ (F i)]
  [∀ i, CompleteSpace (F i)] [∀ i, FiniteDimensional ℝ (F i)]
  (D : Datum ι E F) (U : ∀ i, LogHeatFlow (F i))

omit [FiniteDimensional ℝ E] in
/--
@isnad1 id=continuo.1h6v.s7.9488d236dfb1 from=translated src=- shape=3db7a1c7 vocab=f9471e44
-/
theorem heatProduct_continuous {t : ℝ} (ht : 0 < t) : Continuous (D.heatProduct U t) :=
  continuous_iff_continuousAt.mpr fun x => (D.heatProduct_hasFDerivAt U ht x).continuousAt

omit [FiniteDimensional ℝ E] in
/--
@isnad1 id=continuo.1h6v.s7.fb09588661a1 from=translated src=- shape=6403f79a vocab=e85726e4
-/
theorem score_continuous {t : ℝ} (ht : 0 < t) : Continuous (D.score U t) :=
  continuous_iff_continuousAt.mpr fun x => (D.score_hasFDerivAt U ht x).continuousAt

omit [FiniteDimensional ℝ E] in
/--
@isnad1 id=continuo.1h6v.s9.8d357ba6dd3c from=translated src=- shape=7d9abade vocab=c1ae8906
-/
theorem scoreDerivative_continuous (t : ℝ) (hH : ∀ i, Continuous ((U i).hessian t)) :
    Continuous (D.scoreDerivative U t) := by
  change Continuous (fun x => ∑ i, D.weight i • (D.map i).adjoint.comp (((U i).hessian t (D.map i x)).comp (D.map i)))
  apply continuous_finsetSum
  intro i _
  exact (continuous_const : Continuous (fun _ : E => D.weight i)).smul ((((hH i).comp (D.map i).continuous).clm_comp_const
    (D.map i)).const_clm_comp (D.map i).adjoint)

omit [FiniteDimensional ℝ E] in
/--
@isnad1 id=continuo.2h6v.s8.0fba4221b133 from=translated src=- shape=a9c2c173 vocab=026a0c8c
-/
theorem timeRate_continuous {t : ℝ} (ht : 0 < t) (hH : ∀ i, Continuous ((U i).hessian t)) :
    Continuous (D.timeRate U t) := by
  change Continuous (fun x => ∑ i, D.weight i * (LinearMap.trace ℝ (F i) ((U i).hessian t (D.map i x)).toLinearMap + ‖(U i).gradient t (D.map i x)‖^2))
  apply continuous_finsetSum
  intro i _
  have hg : Continuous ((U i).gradient t) :=
    continuous_iff_continuousAt.mpr fun y => ((U i).gradient_deriv t ht y).continuousAt
  have htr := (operatorTrace (E := F i)).continuous.comp ((hH i).comp (D.map i).continuous)
  change Continuous (fun x => operatorTrace ((U i).hessian t (D.map i x))) at htr
  simp_rw [operatorTrace_apply] at htr
  exact continuous_const.mul (htr.add (((hg.comp (D.map i).continuous).norm).pow 2))

omit [FiniteDimensional ℝ E] in
/--
@isnad1 id=continuo.2h6v.s9.3f78e0000e3a from=translated src=- shape=b542a27d vocab=b3baadef
-/
theorem fluxDerivative_continuous {t : ℝ} (ht : 0 < t) (hH : ∀ i, Continuous ((U i).hessian t)) :
    Continuous (D.fluxDerivative U t) := by
  have hQ := D.heatProduct_continuous U ht
  have hS := D.score_continuous U ht
  have hT := ((ContinuousLinearMap.smulRightL ℝ E E).continuous.comp
    (hQ.smul ((innerSL ℝ).continuous.comp hS))).clm_apply hS
  exact hT.add (hQ.smul (D.scoreDerivative_continuous U t hH))

end Datum
end GeometricBrascampLieb
