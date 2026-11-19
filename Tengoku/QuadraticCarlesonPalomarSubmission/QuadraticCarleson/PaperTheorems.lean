import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.NegativePrincipalValueEndpoints
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.LacunaryEndpointDirectResolved
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.FiniteModulationDirectBlockResolved
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.PositiveFullMaximalMeasurability
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.NegativeWeakOneOneCorollary

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Paper-facing headline statements

Review entry point for arXiv:2609.04101v1. These explicit theorem types retain
the source test domain, strict level sets, modulars, and quantifier order.
Both negative and positive endpoints use the same genuine principal-value
operators. The definitions and proofs live in the individually imported files.

This review-facing statement map identifies the claims formalized here. It does
not assert that every auxiliary result cited by the article is formalized in
this repository.
-/

open MeasureTheory
open scoped ENNReal

namespace QuadraticCarleson.PaperTheorems

open PositivePrincipalValueEndpoints

set_option autoImplicit false

/-- Theorem `t:loglogfail`: lacunary failure below `t log₂ t`.
@isnad1 id=not.1h1v.s3.942b29ee45bf from=translated src=- shape=2d03b771 vocab=f4339b06
-/
theorem lacunary_sub_log2_modular_failure
    (Phi : YoungFunction) (hPhi : GrowsSlowerThanEndpoint Phi) :
    ¬HasFunctionPhiModularEstimate Phi lacunaryPrincipalValueMaximal :=
  NegativePrincipalValueEndpoints.lacunary_not_hasPhiModularEstimate Phi hPhi

/-- Theorem `t:loglogfail`, full-modulation consequence.
@isnad1 id=not.1h1v.s3.95c938a324a5 from=translated src=- shape=2d03b771 vocab=90b0fe5a
-/
theorem full_sub_log2_modular_failure
    (Phi : YoungFunction) (hPhi : GrowsSlowerThanEndpoint Phi) :
    ¬HasFunctionPhiModularEstimate Phi fullPrincipalValueMaximal :=
  NegativePrincipalValueEndpoints.full_not_hasPhiModularEstimate Phi hPhi

/-- Theorem `t:loglogfail`: the printed unit-height witness for `0 < κ < 1`.
@isnad1 id=ex.2h2v.s6.79c9de1ceec9 from=translated src=- shape=34a26d2f vocab=20e35bd0
-/
theorem lacunary_counterexample_at_unit_height
    (Phi : YoungFunction) (hPhi : GrowsSlowerThanEndpoint Phi)
    {kappa : ℝ} (hkappa : 0 < kappa ∧ kappa < 1) :
    ∃ f : L0Infinity,
      (∫⁻ x : ℝ, ENNReal.ofReal (Phi (‖f x‖))) <
        ENNReal.ofReal kappa * volume {x | 1 < lacunaryPrincipalValueMaximal f x} :=
  NegativePrincipalValueEndpoints.lacunary_exists_paper_modular_witness Phi hPhi hkappa

/-- The same printed witness range for the full real-modulation operator.
@isnad1 id=ex.2h2v.s6.3e30f0533bab from=translated src=- shape=34a26d2f vocab=c966238b
-/
theorem full_counterexample_at_unit_height
    (Phi : YoungFunction) (hPhi : GrowsSlowerThanEndpoint Phi)
    {kappa : ℝ} (hkappa : 0 < kappa ∧ kappa < 1) :
    ∃ f : L0Infinity,
      (∫⁻ x : ℝ, ENNReal.ofReal (Phi (‖f x‖))) <
        ENNReal.ofReal kappa * volume {x | 1 < fullPrincipalValueMaximal f x} :=
  NegativePrincipalValueEndpoints.full_exists_paper_modular_witness Phi hPhi hkappa

/-- Theorem `t:LlogL`, first bound: full-modulation `L log₁ L`, with one
constant for all inputs and all positive thresholds.
@isnad1 id=ex.0h0v.s7.7b334c37f33c from=translated src=- shape=b2ef0b34 vocab=d13a4f4d
-/
theorem full_LlogL_endpoint :
    ∃ K : ℝ≥0∞, K < ∞ ∧ ∀ f : L0Infinity,
      (∀ᵐ x, ∀ lam : ℝ,
        HasQuadraticPrincipalValue lam f x (principalValueRepresentative lam f x)) ∧
      ∀ α : ℝ, 0 < α →
        volume {x | ENNReal.ofReal α < fullPrincipalValueMaximal f x} ≤
          K * ∫⁻ x, ENNReal.ofReal ((‖f x‖ / α) * paperLog 1 (‖f x‖ / α)) :=
  HilbertMaximalWeakResolved.full_principalValue_endpoint

/-- Theorem `t:LlogL`, second bound: lacunary `L (log₂ L)² log₄ L`, with
one constant for all inputs and all positive thresholds.
@isnad1 id=ex.0h0v.s7.c2669c74e918 from=translated src=- shape=4c8e40fa vocab=572751fb
-/
theorem lacunary_log2_squared_log4_endpoint :
    ∃ K : ℝ≥0∞, K < ∞ ∧ ∀ f : L0Infinity,
      (∀ᵐ x, ∀ m : ℤ, HasQuadraticPrincipalValue (dyadicModulation m) f x
        (principalValueRepresentative (dyadicModulation m) f x)) ∧
      ∀ α : ℝ, 0 < α →
        volume {x | ENNReal.ofReal α < lacunaryPrincipalValueMaximal f x} ≤
          K * ∫⁻ x, ENNReal.ofReal
            ((‖f x‖ / α) * paperLog 2 (‖f x‖ / α) ^ 2 * paperLog 4 (‖f x‖ / α)) :=
  LacunaryEndpointDirectResolved.lacunary_principalValue_endpoint

/-- Introduction's weak `(1,1)` failure, for the same lacunary PV operator.
@isnad1 id=not.0h0v.s7.7e2e07f9c565 from=translated src=- shape=b7c714a5 vocab=03d4fea4
-/
theorem lacunary_not_weakOneOne :
    ¬∃ C : ℝ, 0 < C ∧ ∀ (f : L0Infinity) (α : ℝ), 0 < α →
      ENNReal.ofReal α * volume {x | ENNReal.ofReal α < lacunaryPrincipalValueMaximal f x} ≤
        ENNReal.ofReal C * ∫⁻ x, ‖f x‖ₑ := by
  intro hweak
  exact lacunary_sub_log2_modular_failure NegativeWeakOneOneCorollary.identityYoungFunction
    NegativeWeakOneOneCorollary.identityYoungFunction_growsSlowerThanEndpoint
    (NegativeWeakOneOneCorollary.hasFunctionPhiModularEstimate_identity_of_weakOneOne hweak)

/-- Introduction's weak `(1,1)` failure, for the same full PV operator.
@isnad1 id=not.0h0v.s7.a1f093db86ac from=translated src=- shape=b7c714a5 vocab=3742682c
-/
theorem full_not_weakOneOne :
    ¬∃ C : ℝ, 0 < C ∧ ∀ (f : L0Infinity) (α : ℝ), 0 < α →
      ENNReal.ofReal α * volume {x | ENNReal.ofReal α < fullPrincipalValueMaximal f x} ≤
        ENNReal.ofReal C * ∫⁻ x, ‖f x‖ₑ := by
  intro hweak
  exact full_sub_log2_modular_failure NegativeWeakOneOneCorollary.identityYoungFunction
    NegativeWeakOneOneCorollary.identityYoungFunction_growsSlowerThanEndpoint
    (NegativeWeakOneOneCorollary.hasFunctionPhiModularEstimate_identity_of_weakOneOne hweak)

/-- Both actual headline level-set operators are a.e.-measurable.
@isnad1 id=and.0h1v.s4.13bf815d71a7 from=translated src=- shape=d64805b2 vocab=973ddbe8
-/
theorem principalValueMaxima_aemeasurable (f : L0Infinity) :
    AEMeasurable (fullPrincipalValueMaximal f) volume ∧
      AEMeasurable (lacunaryPrincipalValueMaximal f) volume :=
  ⟨PositiveFullMaximalMeasurability.aemeasurable_fullPrincipalValueMaximal f,
    PositiveFullMaximalMeasurability.aemeasurable_lacunaryPrincipalValueMaximal f⟩

/-- Corollary `c:finitemodulationsweak11`: arbitrary signed nonzero finite
modulations, uniformly over `B`. This does not put the supremum over `B`
inside the operator.
@isnad1 id=le.2h5v.s7.73d7848129be from=translated src=- shape=5117f199 vocab=273fd68f
-/
theorem finite_modulation_blocks_weakOneOne
    {N : ℕ} (B : ℕ) (lam : Fin N → ℝ) (hlam : ∀ i, lam i ≠ 0)
    (f : L0Infinity) {α : ℝ} (hα : 0 < α) :
    ENNReal.ofReal α * volume
        {x | ENNReal.ofReal α <
          FiniteModulationDirectBlockResolved.finitePaperBlockMaxEnorm B lam hlam f x} ≤
      ENNReal.ofReal
          (FiniteModulationDirectBlockResolved.finiteBlockWeakConstant * paperLog 1 N ^ 2) *
        ∫⁻ x, ‖f x‖ₑ :=
  FiniteModulationDirectBlockResolved.finiteModulationBlock_weak_bound B lam hlam f hα

end QuadraticCarleson.PaperTheorems
