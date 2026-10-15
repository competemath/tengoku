import Tengoku.NavierStokesEuler.Euler.MeanBoundaryOperator

/-! The curl of a differentiable field has support inside the support of that
field. This elementary locality fact does not assume spatial norm bounds. -/

namespace EulerMeanCutoffCurl

open EulerSmoothLimit EulerMeanBoundary

/--
@isnad1 id=le.1h1v.s9.96ee213fd19e from=translated src=- shape=bc7532c3 vocab=fbf7f0d0
-/
theorem tsupport_vectorCurl_subset (f : Space → Space) (hf : Differentiable ℝ f) :
    tsupport (vectorCurl f) ⊆ tsupport f := by
  have hcurl : vectorCurl f = curlMatrix ∘ fderiv ℝ f :=
    funext (fun x => vectorCurl_eq_matrix f x (hf x))
  have hzero : curlMatrix 0 = 0 := by
    ext i
    simp [curlMatrix]
  rw [hcurl]
  exact (tsupport_comp_subset hzero (fderiv ℝ f)).trans (tsupport_fderiv_subset ℝ)

end EulerMeanCutoffCurl
