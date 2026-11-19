/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.CounterexampleErrorBudget
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.L0LacunaryOperator

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Failure of sub-`L log₂ L` modular estimates

This file closes the negative-endpoint counterexample.  It first proves the
linear-in-`N` level-set lower bound for the canonical distributional
lacunary quadratic Carleson operator on the paper's smooth compactly
supported counterexamples.  The abstract modular contradiction then gives
failure for every Young function growing strictly slower than `t log₂ t`,
together with the normalized unit-height witnesses stated in the paper.
-/

open Filter MeasureTheory Set
open scoped ENNReal SchwartzMap

namespace QuadraticCarleson

set_option autoImplicit false

/-- The paper's analytic counterexample estimate, now for the actual
distributionally defined lacunary quadratic Carleson operator.
@isnad1 id=eventual.0h0v.s5.61d45f837e14 from=translated src=- shape=4a18d1d9 vocab=cd546717
-/
theorem eventually_lacunary_counterexample_level_volume_ge :
    ∀ᶠ N : ℕ in atTop,
      ENNReal.ofReal (negativeEndpointDelta * (N : ℝ)) ≤
        volume {x | ENNReal.ofReal
            (counterexampleHeight negativeEndpointHeightConstant N) ≤
          lacunaryQuadraticCarlesonSchwartz (counterexampleSchwartz N) x} := by
  filter_upwards [eventually_ge_atTop 100,
      eventually_paperAmplitude_pos,
      eventually_paper_window_start,
      eventually_paper_negative_endpoint_error_budget]
      with N hN hA hwindow hbudget
  apply lacunary_counterexample_level_volume_ge_of_pointwise hN hwindow
  exact paperTranslatedBohrSet_pointwise_of_error_budget
    hN hA (paperExponentShift_rpow_eq_amplitude hA) hbudget

/-- The first headline conclusion, on the exact compactly supported Schwartz
test class used by the counterexample: no modular estimate can hold below
`L log₂ L`.
@isnad1 id=not.1h1v.s3.89be348b15d5 from=translated src=- shape=2d03b771 vocab=1d75875f
-/
theorem negativeEndpoint_not_hasSchwartzPhiModularEstimate
    (Phi : YoungFunction) (hPhi : GrowsSlowerThanEndpoint Phi) :
    ¬HasSchwartzPhiModularEstimate Phi lacunarySchwartzOperator := by
  exact not_hasSchwartzPhiModularEstimate_lacunary_of_counterexample_lower_bound
    Phi hPhi negativeEndpointHeightConstant_pos negativeEndpointDelta_pos
      eventually_lacunary_counterexample_level_volume_ge

/-- The paper's normalized `f_kappa` conclusion.  The formal statement is
slightly stronger in allowing every `kappa > 0`, rather than additionally
requiring `kappa < 1`.
@isnad1 id=ex.2h2v.s8.b85e50c2459f from=translated src=- shape=a8fe596f vocab=504783d4
-/
theorem negativeEndpoint_exists_unit_schwartz_modular_witness
    (Phi : YoungFunction) (hPhi : GrowsSlowerThanEndpoint Phi)
    {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ g : 𝓢(ℝ, ℂ), HasCompactSupport (g : ℝ → ℂ) ∧
      (∫⁻ x : ℝ, ENNReal.ofReal (Phi (‖g x‖))) <
        ENNReal.ofReal kappa *
          volume {x | 1 < lacunaryQuadraticCarlesonSchwartz g x} := by
  exact exists_unit_schwartz_modular_witness_lacunary_of_counterexample_lower_bound
    Phi hPhi negativeEndpointHeightConstant_pos negativeEndpointDelta_pos
      eventually_lacunary_counterexample_level_volume_ge hkappa

/-- Any measurable operator on the paper's full `L0Infinity` domain that
agrees with the canonical lacunary principal values on compactly supported
Schwartz functions inherits the negative endpoint theorem.
@isnad1 id=not.2h2v.s6.756e45d39144 from=translated src=- shape=ca2e36b5 vocab=88bf83b5
-/
theorem negativeEndpoint_not_hasPhiModularEstimate_of_agrees_on_schwartz
    (Phi : YoungFunction) (hPhi : GrowsSlowerThanEndpoint Phi)
    (T : NonnegativeOperator)
    (hagree : ∀ (f : 𝓢(ℝ, ℂ)) (hf : HasCompactSupport (f : ℝ → ℂ)) (x : ℝ),
      T (compactSchwartzToL0Infinity f hf) x =
        lacunarySchwartzOperator f x) :
    ¬HasPhiModularEstimate Phi T := by
  exact not_hasPhiModularEstimate_of_schwartz_restriction
    Phi T lacunarySchwartzOperator hagree
      (negativeEndpoint_not_hasSchwartzPhiModularEstimate Phi hPhi)

/-- The paper's first headline theorem on its full bounded,
compactly-supported measurable test domain.
@isnad1 id=not.1h1v.s3.36922df6b5b7 from=translated src=- shape=2d03b771 vocab=9effcf1a
-/
theorem negativeEndpoint_not_hasPhiModularEstimate
    (Phi : YoungFunction) (hPhi : GrowsSlowerThanEndpoint Phi) :
    ¬HasPhiModularEstimate Phi lacunaryL0Operator := by
  exact negativeEndpoint_not_hasPhiModularEstimate_of_agrees_on_schwartz
    Phi hPhi lacunaryL0Operator lacunaryL0Operator_agrees_on_compactSchwartz

/-- The full-domain form of the paper's `f_kappa` conclusion.
@isnad1 id=ex.2h2v.s6.27dd7cd49e8e from=translated src=- shape=93420976 vocab=5642a61c
-/
theorem negativeEndpoint_exists_unit_modular_witness
    (Phi : YoungFunction) (hPhi : GrowsSlowerThanEndpoint Phi)
    {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ f : L0Infinity,
      (∫⁻ x : ℝ, ENNReal.ofReal (Phi (‖f x‖))) <
        ENNReal.ofReal kappa *
          volume (operatorLevelSet lacunaryL0Operator f 1) := by
  obtain ⟨g, hg, hbound⟩ :=
    negativeEndpoint_exists_unit_schwartz_modular_witness Phi hPhi hkappa
  let f : L0Infinity := compactSchwartzToL0Infinity g hg
  refine ⟨f, ?_⟩
  have hlevel :
      {x | 1 < lacunaryQuadraticCarlesonSchwartz g x} =
        operatorLevelSet lacunaryL0Operator f 1 := by
    ext x
    change 1 < lacunaryQuadraticCarlesonSchwartz g x ↔
      ENNReal.ofReal 1 < lacunaryL0Operator f x
    rw [ENNReal.ofReal_one]
    change 1 < lacunaryQuadraticCarlesonSchwartz g x ↔
      1 < lacunaryQuadraticCarlesonL0 f x
    rw [show f = compactSchwartzToL0Infinity g hg by rfl,
      lacunaryQuadraticCarlesonL0_compactSchwartz]
  rw [← hlevel]
  simpa only [f, compactSchwartzToL0Infinity_apply] using hbound

/-- The normalized witness with the paper's printed range `0 < κ < 1`.
The preceding theorem proves the stronger fact that the upper restriction on
`κ` is unnecessary.
@isnad1 id=ex.2h2v.s6.f14eddf31358 from=translated src=- shape=ff9d8d31 vocab=5642a61c
-/
theorem negativeEndpoint_exists_paper_modular_witness
    (Phi : YoungFunction) (hPhi : GrowsSlowerThanEndpoint Phi)
    {kappa : ℝ} (hkappa : 0 < kappa ∧ kappa < 1) :
    ∃ f : L0Infinity,
      (∫⁻ x : ℝ, ENNReal.ofReal (Phi (‖f x‖))) <
        ENNReal.ofReal kappa *
          volume (operatorLevelSet lacunaryL0Operator f 1) :=
  negativeEndpoint_exists_unit_modular_witness Phi hPhi hkappa.1

/-- Every measurable operator which pointwise dominates the lacunary
quadratic operator also fails the same modular estimate.  Instantiating `T`
with the full quadratic supremum gives the “therefore `C₂` as well” clause of
the paper.
@isnad1 id=not.2h2v.s4.60b8ca4bb93f from=translated src=- shape=852efb70 vocab=47b24e68
-/
theorem negativeEndpoint_not_hasPhiModularEstimate_of_dominates_lacunary
    (Phi : YoungFunction) (hPhi : GrowsSlowerThanEndpoint Phi)
    (T : NonnegativeOperator)
    (hdom : ∀ f x, lacunaryL0Operator f x ≤ T f x) :
    ¬HasPhiModularEstimate Phi T := by
  intro hT
  exact negativeEndpoint_not_hasPhiModularEstimate Phi hPhi
    (hT.of_pointwise_le Phi lacunaryL0Operator T hdom)

/-- The normalized witnesses also transfer to every pointwise larger
operator.
@isnad1 id=ex.3h3v.s6.70c98ff83dbe from=translated src=- shape=a6eb81d0 vocab=a8d5d315
-/
theorem negativeEndpoint_exists_paper_modular_witness_of_dominates_lacunary
    (Phi : YoungFunction) (hPhi : GrowsSlowerThanEndpoint Phi)
    (T : NonnegativeOperator)
    (hdom : ∀ f x, lacunaryL0Operator f x ≤ T f x)
    {kappa : ℝ} (hkappa : 0 < kappa ∧ kappa < 1) :
    ∃ f : L0Infinity,
      (∫⁻ x : ℝ, ENNReal.ofReal (Phi (‖f x‖))) <
        ENNReal.ofReal kappa * volume (operatorLevelSet T f 1) := by
  obtain ⟨f, hf⟩ := negativeEndpoint_exists_paper_modular_witness Phi hPhi hkappa
  refine ⟨f, hf.trans_le ?_⟩
  gcongr
  intro x hx
  exact hx.trans_le (hdom f x)

end QuadraticCarleson
