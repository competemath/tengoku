import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Analysis.LiftCriterion

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Lifts from a retraction

A bounded linear retraction `r` of multilinear maps onto alternating maps gives a multilinear
lift `(u₁, …, uₙ) ↦ (m ↦ r (m ∘ (u₁, …, uₙ)))` of the precomposition action, of norm at most
`‖r‖`. This is the first part of Proposition 4.1; here only the case `‖r‖ ≤ 1` is stated.
-/

noncomputable section

namespace AlternatingAnalytic

open scoped BigOperators

variable {K E E' F : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup E] [NormedSpace K E]
  [NormedAddCommGroup E'] [NormedSpace K E']
  [NormedAddCommGroup F] [NormedSpace K F]

noncomputable local instance contractingRetractionLiftNorm (n : ℕ) :
    Norm ((E →L[K] E') [×n]→L[K]
      ((E' [⋀^Fin n]→L[K] F) →L[K] (E [⋀^Fin n]→L[K] F))) :=
  ContinuousMultilinearMap.hasOpNorm
    (𝕜 := K) (E := fun _ : Fin n => E →L[K] E')
    (G := (E' [⋀^Fin n]→L[K] F) →L[K] (E [⋀^Fin n]→L[K] F))

/-- The lift `(u₁, …, uₙ) ↦ (m ↦ r (m ∘ (u₁, …, uₙ)))` built from a retraction `r`.-/
def contractingRetractionLift (n : ℕ)
    (r : (E [×n]→L[K] F) →L[K] (E [⋀^Fin n]→L[K] F)) :
    (E →L[K] E') [×n]→L[K]
      ((E' [⋀^Fin n]→L[K] F) →L[K] (E [⋀^Fin n]→L[K] F)) :=
  (r.postcomp (E' [⋀^Fin n]→L[K] F)).compContinuousMultilinearMap
    (LiftCriterion.ambLift K (Fin n) E E' F)

/--
@isnad1 id=eq.0h8v.s13.fa3d93d837fc from=translated src=- shape=c2d726e0 vocab=dbb4609b
-/
theorem contractingRetractionLift_apply (n : ℕ)
    (r : (E [×n]→L[K] F) →L[K] (E [⋀^Fin n]→L[K] F))
    (f : Fin n → E →L[K] E') (m : E' [⋀^Fin n]→L[K] F) :
    contractingRetractionLift n r f m =
      r (m.toContinuousMultilinearMap.compContinuousLinearMap f) := rfl

/--
@isnad1 id=eq.1h7v.s13.933e5b413f1e from=translated src=- shape=900a4375 vocab=dc97aa5b
-/
theorem contractingRetractionLift_diag (n : ℕ)
    (r : (E [×n]→L[K] F) →L[K] (E [⋀^Fin n]→L[K] F))
    (hr : ∀ m : E [⋀^Fin n]→L[K] F, r m.toContinuousMultilinearMap = m)
    (f : E →L[K] E') :
    contractingRetractionLift n r (fun _ => f) = LiftCriterion.Q K (Fin n) E E' F f := by
  ext m v
  exact congrArg (fun a : E [⋀^Fin n]→L[K] F => a v) (hr (m.compContinuousLinearMap f))

/--
@isnad1 id=le.1h6v.s12.8f2a72f79cdb from=translated src=- shape=7908b494 vocab=a8f4d5e9
-/
theorem norm_contractingRetractionLift_le (n : ℕ)
    (r : (E [×n]→L[K] F) →L[K] (E [⋀^Fin n]→L[K] F)) (hr : ‖r‖ ≤ 1) :
    ‖contractingRetractionLift (E' := E') n r‖ ≤ 1 := by
  apply ContinuousMultilinearMap.opNorm_le_bound zero_le_one
  intro f
  rw [one_mul]
  apply ContinuousLinearMap.opNorm_le_bound _ (Finset.prod_nonneg fun i _ => norm_nonneg _)
  intro m
  rw [contractingRetractionLift_apply]
  calc
    ‖r (m.toContinuousMultilinearMap.compContinuousLinearMap f)‖ ≤
        ‖m.toContinuousMultilinearMap.compContinuousLinearMap f‖ := by
      simpa using r.le_of_opNorm_le hr (m.toContinuousMultilinearMap.compContinuousLinearMap f)
    _ ≤ ‖m.toContinuousMultilinearMap‖ * ∏ i, ‖f i‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = (∏ i, ‖f i‖) * ‖m‖ := by rw [ContinuousAlternatingMap.norm_toContinuousMultilinearMap, mul_comm]

end AlternatingAnalytic
