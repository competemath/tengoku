import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.FullNegativeEndpoint

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Explicit failure of weak `(1,1)` for both quadratic Carleson operators

The identity Young function is explicitly allowed by the paper's definition.
Its growth is strictly below `t log₂ t`, so the checked negative endpoint
theorem excludes the ordinary weak `(1,1)` distribution estimate as well.
-/

open Filter MeasureTheory Set Asymptotics
open scoped ENNReal Topology

namespace QuadraticCarleson.NegativeWeakOneOneCorollary

set_option autoImplicit false

/-- The exceptional linear Young function explicitly included in the paper.-/
def identityYoungFunction : YoungFunction where
  toFun := id
  continuousOn_nonneg := continuous_id.continuousOn
  convexOn_nonneg := convexOn_id (convex_Ici 0)
  strictMonoOn_nonneg := strictMono_id.strictMonoOn (Ici 0)
  map_zero := rfl
  identity_or_superlinear := Or.inl (fun _ _ ↦ rfl)

/--
@isnad1 id=eq.0h1v.s3.5c72ff9c1e0f from=translated src=- shape=29edb2d9 vocab=59e8172c
-/
@[simp] theorem identityYoungFunction_apply (t : ℝ) : identityYoungFunction t = t := rfl

/-- Every fixed number of the paper's iterated logarithms tends to infinity.
@isnad1 id=tendsto.0h1v.s3.831ea62cd1fa from=translated src=- shape=74931b86 vocab=1d1aed78
-/
theorem tendsto_paperLog_atTop (n : ℕ) : Tendsto (paperLog n) atTop atTop := by
  induction n with
  | zero => exact tendsto_id
  | succ n ih =>
      exact Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_left atTop 10 ih)

/-- Linear growth is little-o of the negative endpoint growth.
@isnad1 id=growsslo.0h0v.s1.e9719471e274 from=translated src=- shape=49959d42 vocab=2a29ab11
-/
theorem identityYoungFunction_growsSlowerThanEndpoint :
    GrowsSlowerThanEndpoint identityYoungFunction := by
  have hlog : (fun _ : ℝ ↦ (1 : ℝ)) =o[atTop] (paperLog 2) :=
    (isLittleO_one_left_iff ℝ).mpr
      (tendsto_norm_atTop_atTop.comp (tendsto_paperLog_atTop 2))
  have hmul := (isBigO_refl (fun t : ℝ ↦ t) atTop).mul_isLittleO hlog
  simpa only [GrowsSlowerThanEndpoint, identityYoungFunction_apply, mul_one] using hmul

/-- The usual `α · |{T f > α}| ≤ C ‖f‖₁` bound implies the modular
estimate for the identity Young function, with the same constant.
@isnad1 id=hasfunct.1h1v.s7.5550c06f94ec from=translated src=- shape=45894206 vocab=7ca99651
-/
theorem hasFunctionPhiModularEstimate_identity_of_weakOneOne
    {T : L0Infinity → ℝ → ℝ≥0∞}
    (hweak : ∃ C : ℝ, 0 < C ∧ ∀ (f : L0Infinity) (α : ℝ), 0 < α →
      ENNReal.ofReal α * volume (functionOperatorLevelSet T f α) ≤
        ENNReal.ofReal C * ∫⁻ x, ‖f x‖ₑ) :
    HasFunctionPhiModularEstimate identityYoungFunction T := by
  obtain ⟨C, hC, hbound⟩ := hweak
  refine ⟨C, hC, fun f α hα ↦ ?_⟩
  have hα0 : ENNReal.ofReal α ≠ 0 := (ENNReal.ofReal_pos.mpr hα).ne'
  have hmass : (∫⁻ x, ENNReal.ofReal (identityYoungFunction (‖f x‖ / α))) =
      (ENNReal.ofReal α)⁻¹ * ∫⁻ x, ‖f x‖ₑ := by
    simp_rw [identityYoungFunction_apply, ENNReal.ofReal_div_of_pos hα,
      ofReal_norm, div_eq_mul_inv, mul_comm _ ((ENNReal.ofReal α)⁻¹)]
    exact lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hα0)
  rw [hmass]
  have h := mul_le_mul' (le_refl ((ENNReal.ofReal α)⁻¹)) (hbound f α hα)
  rw [ENNReal.inv_mul_cancel_left hα0 ENNReal.ofReal_ne_top] at h
  simpa only [mul_left_comm] using h

/-- The concrete lacunary quadratic operator is not of weak type `(1,1)`
on the paper's bounded compactly supported measurable test domain.
@isnad1 id=not.0h0v.s7.a7cb0baaf37a from=translated src=- shape=b7c714a5 vocab=6b651611
-/
theorem lacunaryQuadraticCarlesonL0_not_weakOneOne :
    ¬∃ C : ℝ, 0 < C ∧ ∀ (f : L0Infinity) (α : ℝ), 0 < α →
      ENNReal.ofReal α * volume {x | ENNReal.ofReal α <
        lacunaryQuadraticCarlesonL0 f x} ≤
          ENNReal.ofReal C * ∫⁻ x, ‖f x‖ₑ := by
  intro hweak
  apply negativeEndpoint_not_hasPhiModularEstimate identityYoungFunction
    identityYoungFunction_growsSlowerThanEndpoint
  exact (hasFunctionPhiModularEstimate_iff identityYoungFunction lacunaryL0Operator).mp
    (hasFunctionPhiModularEstimate_identity_of_weakOneOne hweak)

/-- The full real-modulation quadratic operator likewise fails weak `(1,1)`.
@isnad1 id=not.0h0v.s7.7409cbedc678 from=translated src=- shape=b7c714a5 vocab=e4fd02d8
-/
theorem quadraticCarlesonL0_not_weakOneOne :
    ¬∃ C : ℝ, 0 < C ∧ ∀ (f : L0Infinity) (α : ℝ), 0 < α →
      ENNReal.ofReal α * volume {x | ENNReal.ofReal α < quadraticCarlesonL0 f x} ≤
        ENNReal.ofReal C * ∫⁻ x, ‖f x‖ₑ := by
  intro hweak
  exact fullNegativeEndpoint_not_hasPhiModularEstimate identityYoungFunction
    identityYoungFunction_growsSlowerThanEndpoint
    (hasFunctionPhiModularEstimate_identity_of_weakOneOne hweak)

end QuadraticCarleson.NegativeWeakOneOneCorollary
