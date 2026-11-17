import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Analysis.AnalyticFamilies

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Degree-zero alternating-map action

The isometry `constOfIsEmptyLIE` identifies a degree-zero alternating map with
its constant value. Under this identification the action of `(u, v)` is `v`,
and `u` has no effect.
-/

noncomputable section

namespace AlternatingAnalytic

variable {K : Type*} [NontriviallyNormedField K]
  {E E' F F' : Type*}
  [NormedAddCommGroup E] [NormedSpace K E]
  [NormedAddCommGroup E'] [NormedSpace K E']
  [NormedAddCommGroup F] [NormedSpace K F]
  [NormedAddCommGroup F'] [NormedSpace K F']

/-- In degree zero, the action sends the constant with value `y` to the
constant with value `v y`.-/
@[simp]
theorem alternatingMapAction_zero_const (u : E' →L[K] E) (v : F →L[K] F') (y : F) :
    alternatingMapAction 0 (u, v)
        (ContinuousAlternatingMap.constOfIsEmptyLIE K E F (Fin 0) y) =
      ContinuousAlternatingMap.constOfIsEmptyLIE K E' F' (Fin 0) (v y) := by
  ext x
  rfl

/-- After the degree-zero identification, the action sends `y` to `v y`.-/
@[simp]
theorem alternatingMapAction_zero_conjugate_apply
    (u : E' →L[K] E) (v : F →L[K] F') (y : F) :
    (ContinuousAlternatingMap.constOfIsEmptyLIE K E' F' (Fin 0)).symm
        (alternatingMapAction 0 (u, v)
          (ContinuousAlternatingMap.constOfIsEmptyLIE K E F (Fin 0) y)) = v y := by
  rw [alternatingMapAction_zero_const]
  exact (ContinuousAlternatingMap.constOfIsEmptyLIE K E' F' (Fin 0)).symm_apply_apply _

/-- The degree-zero action, conjugated by `constOfIsEmptyLIE`, is `v`.-/
theorem alternatingMapAction_zero_conjugate (u : E' →L[K] E) (v : F →L[K] F') :
    ((ContinuousAlternatingMap.constOfIsEmptyLIE K E' F' (Fin 0)).symm :
      (E' [⋀^Fin 0]→L[K] F') →L[K] F').comp
        ((alternatingMapAction 0 (u, v)).comp
          (ContinuousAlternatingMap.constOfIsEmptyLIE K E F (Fin 0) :
            F →L[K] (E [⋀^Fin 0]→L[K] F))) =
      v := by
  ext y
  exact alternatingMapAction_zero_conjugate_apply u v y

/-- A formula for the degree-zero action.-/
theorem alternatingMapAction_zero_eq (u : E' →L[K] E) (v : F →L[K] F') :
    alternatingMapAction 0 (u, v) =
      (ContinuousAlternatingMap.constOfIsEmptyLIE K E' F' (Fin 0) :
        F' →L[K] (E' [⋀^Fin 0]→L[K] F')).comp
        (v.comp
          ((ContinuousAlternatingMap.constOfIsEmptyLIE K E F (Fin 0)).symm :
            (E [⋀^Fin 0]→L[K] F) →L[K] F)) := by
  ext m x
  change v (m (fun i => u (x i))) = v (m 0)
  exact congrArg (fun z => v (m z)) (Subsingleton.elim _ _)

/-- The contravariant morphism has no effect in degree zero.-/
theorem alternatingMapAction_zero_independent (u₁ u₂ : E' →L[K] E) (v : F →L[K] F') :
    alternatingMapAction 0 (u₁, v) = alternatingMapAction 0 (u₂, v) := by
  rw [alternatingMapAction_zero_eq u₁ v, alternatingMapAction_zero_eq u₂ v]

/-- The degree-zero action has the same norm as `v`.-/
@[simp]
theorem norm_alternatingMapAction_zero (u : E' →L[K] E) (v : F →L[K] F') :
    ‖alternatingMapAction 0 (u, v)‖ = ‖v‖ := by
  rw [alternatingMapAction_zero_eq]
  exact (ContinuousLinearMap.opNorm_linearIsometryEquiv_comp _ _).trans
    (ContinuousLinearMap.opNorm_comp_linearIsometryEquiv _ _)

/-- Summary of the degree-zero action: the formula, independence from `u`, and the norm.-/
theorem alternatingMapAction_zero (u : E' →L[K] E) (v : F →L[K] F') :
    (∀ y : F, alternatingMapAction 0 (u, v)
        (ContinuousAlternatingMap.constOfIsEmptyLIE K E F (Fin 0) y) =
      ContinuousAlternatingMap.constOfIsEmptyLIE K E' F' (Fin 0) (v y)) ∧
    ((ContinuousAlternatingMap.constOfIsEmptyLIE K E' F' (Fin 0)).symm :
      (E' [⋀^Fin 0]→L[K] F') →L[K] F').comp
        ((alternatingMapAction 0 (u, v)).comp
          (ContinuousAlternatingMap.constOfIsEmptyLIE K E F (Fin 0) :
            F →L[K] (E [⋀^Fin 0]→L[K] F))) = v ∧
    (∀ u' : E' →L[K] E, alternatingMapAction 0 (u, v) = alternatingMapAction 0 (u', v)) ∧
    ‖alternatingMapAction 0 (u, v)‖ = ‖v‖ :=
  ⟨alternatingMapAction_zero_const u v, alternatingMapAction_zero_conjugate u v,
    (fun u' => alternatingMapAction_zero_independent u u' v),
    norm_alternatingMapAction_zero u v⟩

end AlternatingAnalytic
