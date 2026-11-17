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

/--
@isnad1 id=eq.0h9v.s13.ff8a154690bd from=translated src=- shape=d3555078 vocab=a2acb06e
-/
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

/--
@isnad1 id=eq.0h9v.s13.95e177fe37d3 from=translated src=- shape=ad9b82d9 vocab=de8d5fdf
-/
@[simp]
theorem ambientAlternatingMapAction_apply (k : ℕ)
    (h : Fin (k + 1) → (E' →L[K] E) × (F →L[K] F'))
    (m : E [⋀^Fin k]→L[K] F) (x : Fin k → E') :
    ambientAlternatingMapAction (K := K) (E := E) (E' := E') (F := F) (F' := F') k h m x =
      (h (Fin.last k)).2 (m fun i => (h i.castSucc).1 (x i)) := rfl

/-- The pointwise estimate for `ambientAlternatingMapAction`.
@isnad1 id=le.0h9v.s13.60cd6e32502d from=translated src=- shape=6463b010 vocab=4636c4ea
-/
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

/-- The ambient representative has operator norm at most one.
@isnad1 id=le.0h6v.s12.9c05ef323d5c from=translated src=- shape=b609de0b vocab=14ec0ee5
-/
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

/-- The diagonal of `ambientAlternatingMapAction` is continuously polynomial.
@isnad1 id=cpolynom.0h7v.s13.608d536c3b6b from=translated src=- shape=46d97992 vocab=906ffc26
-/
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

/-- The diagonal of `ambientAlternatingMapAction` is analytic.
@isnad1 id=analytic.0h7v.s13.8f2ca2199ee0 from=translated src=- shape=46d97992 vocab=abe9cb22
-/
theorem analyticAt_ambientAlternatingMapAction_diagonal (k : ℕ)
    (h : (E' →L[K] E) × (F →L[K] F')) :
    AnalyticAt K
      (fun h : (E' →L[K] E) × (F →L[K] F') =>
        ambientAlternatingMapAction (K := K) (E := E) (E' := E') (F := F) (F' := F') k
          (fun _ => h)) h := by
  exact (cpolynomialAt_ambientAlternatingMapAction_diagonal k h).analyticAt

/-- The diagonal of `ambientAlternatingMapAction` is the joint action followed by
the inclusion that forgets alternation.
@isnad1 id=eq.0h7v.s14.37e7e6722827 from=translated src=- shape=fc4d6a47 vocab=8ef36263
-/
theorem ambientAlternatingMapAction_diag (k : ℕ)
    (h : (E' →L[K] E) × (F →L[K] F')) :
    ambientAlternatingMapAction (K := K) (E := E) (E' := E') (F := F) (F' := F') k
      (fun _ => h) =
    alternatingMapActionInclusion (K := K) (E := E) (E' := E') (F := F) (F' := F') k
      (alternatingMapAction k h) := by
  ext m x
  rfl

/-- The joint action is continuously polynomial after forgetting alternation.
@isnad1 id=cpolynom.0h7v.s13.f693ef6db405 from=translated src=- shape=34601752 vocab=512b3b57
-/
theorem cpolynomialAt_ambient_alternatingMapAction (k : ℕ)
    (h : (E' →L[K] E) × (F →L[K] F')) :
    CPolynomialAt K
      (alternatingMapActionInclusion (K := K) (E := E) (E' := E') (F := F) (F' := F') k ∘
        alternatingMapAction k) h := by
  simpa only [Function.comp_def, ambientAlternatingMapAction_diag] using
    cpolynomialAt_ambientAlternatingMapAction_diagonal k h

/-- The joint action is analytic after forgetting alternation.
@isnad1 id=analytic.0h7v.s13.0eb4c5717f33 from=translated src=- shape=4e34eff3 vocab=42fc0506
-/
theorem analyticAt_ambient_alternatingMapAction (k : ℕ)
    (h : (E' →L[K] E) × (F →L[K] F')) :
    AnalyticAt K (fun h : (E' →L[K] E) × (F →L[K] F') =>
      alternatingMapActionInclusion (K := K) (E := E) (E' := E') (F := F) (F' := F') k
        (alternatingMapAction k h)) h := by
  exact (cpolynomialAt_ambient_alternatingMapAction k h).analyticAt

end AlternatingAnalytic
