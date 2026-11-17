import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Analysis.AnalyticFamilies
import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Analysis.FiniteCoordinateReflection
import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Analysis.LiftCriterion
import Tengoku.Seed.Analysis.Analytic.CPolynomial
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Analytic alternating families over finite-coordinate parameters

The joint action `(f, g) ↦ (m ↦ g ∘ m ∘ (f, …, f))`, followed by the closed isometric
inclusion that forgets alternation, is the diagonal of a bounded `(k + 1)`-linear map
(Proposition 2.2). Reflecting through that inclusion with Theorem 4.4 shows that every
analytic family over a finite-coordinate parameter space is admissible. This is the
finite-coordinate case of Corollary 4.6, in every characteristic and degree.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace AlternatingAnalytic

variable {K E E' F F' P : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup E] [NormedSpace K E]
  [NormedAddCommGroup E'] [NormedSpace K E']
  [NormedAddCommGroup F] [NormedSpace K F]
  [NormedAddCommGroup F'] [NormedSpace K F']
  [NormedAddCommGroup P] [NormedSpace K P]

/-- Forget alternation in the values of an operator on alternating maps.-/
def alternatingMapActionInclusion (k : ℕ) :
    ((E [⋀^Fin k]→L[K] F) →L[K] (E' [⋀^Fin k]→L[K] F')) →ₗᵢ[K]
      ((E [⋀^Fin k]→L[K] F) →L[K]
        ContinuousMultilinearMap K (fun _ : Fin k => E') F') :=
  (ContinuousAlternatingMap.toContinuousMultilinearMapLI
    (𝕜 := K) (ι := Fin k) (E := E') (F := F')).postcomp

@[simp]
theorem alternatingMapActionInclusion_apply (k : ℕ)
    (T : (E [⋀^Fin k]→L[K] F) →L[K] (E' [⋀^Fin k]→L[K] F'))
    (m : E [⋀^Fin k]→L[K] F) (x : Fin k → E') :
    alternatingMapActionInclusion (K := K) (E := E) (E' := E') (F := F) (F' := F') k
      T m x = T m x := rfl

/-- The bounded `(k + 1)`-linear map `H` of Proposition 2.2.-/
def ambientAlternatingMapAction (k : ℕ) :
    ContinuousMultilinearMap K (fun _ : Fin (k + 1) => (E' →L[K] E) × (F →L[K] F'))
      ((E [⋀^Fin k]→L[K] F) →L[K] ContinuousMultilinearMap K (fun _ : Fin k => E') F') := by
  let post : ((E' →L[K] E) × (F →L[K] F')) →L[K]
      ContinuousMultilinearMap K (fun _ : Fin k => E') F →L[K]
      ContinuousMultilinearMap K (fun _ : Fin k => E') F' :=
    (ContinuousLinearMap.compContinuousMultilinearMapL K (fun _ : Fin k => E') F F').comp
      (ContinuousLinearMap.snd K _ _)
  let postOp := (ContinuousLinearMap.compL K (E [⋀^Fin k]→L[K] F)
    (ContinuousMultilinearMap K (fun _ : Fin k => E') F)
    (ContinuousMultilinearMap K (fun _ : Fin k => E') F')).comp post
  let curried : ContinuousMultilinearMap K
      (fun _ : Fin k => (E' →L[K] E) × (F →L[K] F'))
      (((E' →L[K] E) × (F →L[K] F')) →L[K]
        ((E [⋀^Fin k]→L[K] F) →L[K] ContinuousMultilinearMap K (fun _ : Fin k => E') F')) :=
    postOp.flip.compContinuousMultilinearMap
      ((LiftCriterion.ambLift K (Fin k) E' E F).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.fst K (E' →L[K] E) (F →L[K] F')))
  exact ContinuousMultilinearMap.uncurryRight
    (𝕜 := K) (G := (E [⋀^Fin k]→L[K] F) →L[K]
      ContinuousMultilinearMap K (fun _ : Fin k => E') F')
    (Ei := fun _ : Fin (k + 1) => (E' →L[K] E) × (F →L[K] F')) curried

@[simp]
theorem ambientAlternatingMapAction_apply (k : ℕ)
    (h : Fin (k + 1) → (E' →L[K] E) × (F →L[K] F'))
    (m : E [⋀^Fin k]→L[K] F) (x : Fin k → E') :
    ambientAlternatingMapAction (K := K) (E := E) (E' := E') (F := F) (F' := F') k h m x =
      (h (Fin.last k)).2 (m fun i => (h i.castSucc).1 (x i)) := rfl

/-- The pointwise estimate for `ambientAlternatingMapAction`.-/
theorem ambientAlternatingMapAction_bound (k : ℕ)
    (h : Fin (k + 1) → (E' →L[K] E) × (F →L[K] F'))
    (m : E [⋀^Fin k]→L[K] F) (x : Fin k → E') :
    ‖ambientAlternatingMapAction (K := K) (E := E) (E' := E') (F := F) (F' := F') k h m x‖ ≤
      (∏ i, ‖h i‖) * ‖m‖ * ∏ i, ‖x i‖ := by
  rw [ambientAlternatingMapAction_apply]
  calc
    ‖(h (Fin.last k)).2 (m fun i => (h i.castSucc).1 (x i))‖ ≤
        ‖h (Fin.last k)‖ * (‖m‖ * ∏ i, (‖h i.castSucc‖ * ‖x i‖)) := by
      apply le_trans ((h (Fin.last k)).2.le_opNorm _)
      gcongr
      · exact norm_snd_le _
      · apply m.le_opNorm_mul_prod_of_le
        intro i
        exact ((h i.castSucc).1.le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (norm_fst_le _) (norm_nonneg _))
    _ = (∏ i, ‖h i‖) * ‖m‖ * ∏ i, ‖x i‖ := by
      rw [Finset.prod_mul_distrib, Fin.prod_univ_castSucc]
      ring

-- Fix the standard operator norm for the nested operator codomain.
local instance ambientAlternatingMapActionNorm (k : ℕ) :
    Norm (ContinuousMultilinearMap K
      (fun _ : Fin (k + 1) => (E' →L[K] E) × (F →L[K] F'))
      ((E [⋀^Fin k]→L[K] F) →L[K]
        ContinuousMultilinearMap K (fun _ : Fin k => E') F')) :=
  ContinuousMultilinearMap.hasOpNorm
    (𝕜 := K) (E := fun _ : Fin (k + 1) => (E' →L[K] E) × (F →L[K] F'))
    (G := (E [⋀^Fin k]→L[K] F) →L[K]
      ContinuousMultilinearMap K (fun _ : Fin k => E') F')

/-- The ambient representative has operator norm at most one.-/
theorem norm_ambientAlternatingMapAction_le (k : ℕ) :
    ‖ambientAlternatingMapAction (K := K) (E := E) (E' := E') (F := F) (F' := F') k‖ ≤ 1 := by
  apply ContinuousMultilinearMap.opNorm_le_bound zero_le_one
  intro h
  rw [one_mul]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro m
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro x
  exact ambientAlternatingMapAction_bound k h m x

/-- The diagonal of `ambientAlternatingMapAction` is continuously polynomial.-/
theorem cpolynomialAt_ambientAlternatingMapAction_diagonal (k : ℕ)
    (h : (E' →L[K] E) × (F →L[K] F')) :
    CPolynomialAt K
      (fun h : (E' →L[K] E) × (F →L[K] F') =>
        ambientAlternatingMapAction (K := K) (E := E) (E' := E') (F := F) (F' := F') k
          (fun _ => h)) h := by
  let diagonal : ((E' →L[K] E) × (F →L[K] F')) →L[K]
      (Fin (k + 1) → (E' →L[K] E) × (F →L[K] F')) :=
    ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id K _
  exact (ContinuousMultilinearMap.cpolynomialAt
    (𝕜 := K)
    (F := (E [⋀^Fin k]→L[K] F) →L[K]
      ContinuousMultilinearMap K (fun _ : Fin k => E') F')
    (f := ambientAlternatingMapAction
      (K := K) (E := E) (E' := E') (F := F) (F' := F') k)).comp
      (diagonal.cpolynomialAt h)

/-- The diagonal of `ambientAlternatingMapAction` is analytic.-/
theorem analyticAt_ambientAlternatingMapAction_diagonal (k : ℕ)
    (h : (E' →L[K] E) × (F →L[K] F')) :
    AnalyticAt K
      (fun h : (E' →L[K] E) × (F →L[K] F') =>
        ambientAlternatingMapAction (K := K) (E := E) (E' := E') (F := F) (F' := F') k
          (fun _ => h)) h := by
  exact (cpolynomialAt_ambientAlternatingMapAction_diagonal k h).analyticAt

/-- The diagonal of `ambientAlternatingMapAction` is the joint action followed by
the inclusion that forgets alternation.-/
theorem ambientAlternatingMapAction_diag (k : ℕ)
    (h : (E' →L[K] E) × (F →L[K] F')) :
    ambientAlternatingMapAction (K := K) (E := E) (E' := E') (F := F) (F' := F') k
      (fun _ => h) =
    alternatingMapActionInclusion (K := K) (E := E) (E' := E') (F := F) (F' := F') k
      (alternatingMapAction k h) := by
  ext m x
  rfl

/-- The joint action is continuously polynomial after forgetting alternation.-/
theorem cpolynomialAt_ambient_alternatingMapAction (k : ℕ)
    (h : (E' →L[K] E) × (F →L[K] F')) :
    CPolynomialAt K
      (alternatingMapActionInclusion (K := K) (E := E) (E' := E') (F := F) (F' := F') k ∘
        alternatingMapAction k) h := by
  simpa only [Function.comp_def, ambientAlternatingMapAction_diag] using
    cpolynomialAt_ambientAlternatingMapAction_diagonal k h

/-- The joint action is analytic after forgetting alternation.-/
theorem analyticAt_ambient_alternatingMapAction (k : ℕ)
    (h : (E' →L[K] E) × (F →L[K] F')) :
    AnalyticAt K (fun h : (E' →L[K] E) × (F →L[K] F') =>
      alternatingMapActionInclusion (K := K) (E := E) (E' := E') (F := F) (F' := F') k
        (alternatingMapAction k h)) h := by
  exact (cpolynomialAt_ambient_alternatingMapAction k h).analyticAt

end AlternatingAnalytic
