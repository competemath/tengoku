import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Analysis.SortedBasisLift

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Norm of the lift from a bounded retraction

The lift `contractingRetractionLift` built from a bounded retraction `ρ` of multilinear
onto alternating maps has norm at most `‖ρ‖` (Proposition 4.1).
-/

noncomputable section

namespace AlternatingAnalytic

open scoped BigOperators

variable {K E E' F : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup E] [NormedSpace K E]
  [NormedAddCommGroup E'] [NormedSpace K E']
  [NormedAddCommGroup F] [NormedSpace K F]

noncomputable local instance boundedRetractionLiftNorm (n : ℕ) :
    Norm ((E →L[K] E') [×n]→L[K]
      ((E' [⋀^Fin n]→L[K] F) →L[K] (E [⋀^Fin n]→L[K] F))) :=
  ContinuousMultilinearMap.hasOpNorm
    (𝕜 := K) (E := fun _ : Fin n => E →L[K] E')
    (G := (E' [⋀^Fin n]→L[K] F) →L[K] (E [⋀^Fin n]→L[K] F))

/-- The lift has norm at most the norm of the retraction.-/
theorem norm_contractingRetractionLift_le_norm (n : ℕ)
    (r : (E [×n]→L[K] F) →L[K] (E [⋀^Fin n]→L[K] F)) :
    ‖contractingRetractionLift (E' := E') n r‖ ≤ ‖r‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (show 0 ≤ ‖r‖ from norm_nonneg r)
  intro f
  apply ContinuousLinearMap.opNorm_le_bound _
    (show 0 ≤ ‖r‖ * ∏ i, ‖f i‖ from
      mul_nonneg (norm_nonneg r) (Finset.prod_nonneg fun i _ => norm_nonneg (f i)))
  intro m
  rw [contractingRetractionLift_apply]
  calc
    ‖r (m.toContinuousMultilinearMap.compContinuousLinearMap f)‖ ≤
        ‖r‖ * ‖m.toContinuousMultilinearMap.compContinuousLinearMap f‖ := r.le_opNorm _
    _ ≤ ‖r‖ * (‖m.toContinuousMultilinearMap‖ * ∏ i, ‖f i‖) :=
      mul_le_mul_of_nonneg_left
        (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _) (norm_nonneg r)
    _ = (‖r‖ * ∏ i, ‖f i‖) * ‖m‖ := by
      rw [ContinuousAlternatingMap.norm_toContinuousMultilinearMap]
      ring

/-- Pointwise bound for the lift.-/
theorem norm_contractingRetractionLift_apply_le (n : ℕ)
    (r : (E [×n]→L[K] F) →L[K] (E [⋀^Fin n]→L[K] F))
    (f : Fin n → E →L[K] E') (m : E' [⋀^Fin n]→L[K] F) (x : Fin n → E) :
    ‖contractingRetractionLift n r f m x‖ ≤
      ‖r‖ * ‖m‖ * (∏ i, ‖f i‖) * ∏ i, ‖x i‖ := by
  calc
    ‖contractingRetractionLift n r f m x‖ ≤
        ‖contractingRetractionLift n r f m‖ * ∏ i, ‖x i‖ :=
      (contractingRetractionLift n r f m).le_opNorm x
    _ ≤ (‖contractingRetractionLift n r f‖ * ‖m‖) * ∏ i, ‖x i‖ :=
      mul_le_mul_of_nonneg_right ((contractingRetractionLift n r f).le_opNorm m)
        (Finset.prod_nonneg fun i _ => norm_nonneg _)
    _ ≤ ((‖r‖ * ∏ i, ‖f i‖) * ‖m‖) * ∏ i, ‖x i‖ := by
      gcongr
      apply ContinuousLinearMap.opNorm_le_bound _
        (show 0 ≤ ‖r‖ * ∏ i, ‖f i‖ from
          mul_nonneg (norm_nonneg r) (Finset.prod_nonneg fun i _ => norm_nonneg (f i)))
      intro a
      rw [contractingRetractionLift_apply]
      calc
        ‖r (a.toContinuousMultilinearMap.compContinuousLinearMap f)‖ ≤
            ‖r‖ * ‖a.toContinuousMultilinearMap.compContinuousLinearMap f‖ := r.le_opNorm _
        _ ≤ ‖r‖ * (‖a.toContinuousMultilinearMap‖ * ∏ i, ‖f i‖) :=
          mul_le_mul_of_nonneg_left
            (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _) (norm_nonneg r)
        _ = _ := by
          rw [ContinuousAlternatingMap.norm_toContinuousMultilinearMap]
          ring
    _ = _ := by ring

end AlternatingAnalytic
