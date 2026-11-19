import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.FullNegativeEndpoint
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.HilbertMaximalWeakResolved

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Negative endpoints for the genuine principal-value operators

The negative counterexamples and positive estimates use the same principal-value
representatives. The transfer uses equality on a common conull set, including
before the uncountable full-modulation supremum is taken.
-/

open MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson

set_option autoImplicit false

/-- Almost-everywhere equal operator outputs have the same strict level-set
outer measures; no extra measurability structure is required.
@isnad1 id=eq.1h4v.s6.d008679d1fb5 from=translated src=- shape=db240f21 vocab=2f74a06f
-/
theorem functionOperatorLevelSet_measure_congr_ae
    {T S : L0Infinity → ℝ → ℝ≥0∞} {f : L0Infinity}
    (hTS : T f =ᵐ[volume] S f) (α : ℝ) :
    volume (functionOperatorLevelSet T f α) =
      volume (functionOperatorLevelSet S f α) := by
  apply measure_congr
  filter_upwards [hTS] with x hx
  change (ENNReal.ofReal α < T f x) = (ENNReal.ofReal α < S f x)
  rw [hx]

/-- The source modular bound is unchanged under a.e. replacement of each
operator output.
@isnad1 id=hasfunct.2h3v.s5.4b20270638b2 from=translated src=- shape=63c94417 vocab=cc3f1a97
-/
theorem HasFunctionPhiModularEstimate.congr_ae
    {Phi : YoungFunction} {T S : L0Infinity → ℝ → ℝ≥0∞}
    (hT : HasFunctionPhiModularEstimate Phi T)
    (hTS : ∀ f, T f =ᵐ[volume] S f) : HasFunctionPhiModularEstimate Phi S := by
  obtain ⟨C, hC, hbound⟩ := hT
  refine ⟨C, hC, fun f α hα ↦ ?_⟩
  rw [← functionOperatorLevelSet_measure_congr_ae (hTS f) α]
  exact hbound f α hα

/--
@isnad1 id=iff.1h3v.s5.7699b1a48a12 from=translated src=- shape=bce271ed vocab=cc3f1a97
-/
theorem hasFunctionPhiModularEstimate_congr_ae
    (Phi : YoungFunction) {T S : L0Infinity → ℝ → ℝ≥0∞}
    (hTS : ∀ f, T f =ᵐ[volume] S f) :
    HasFunctionPhiModularEstimate Phi T ↔ HasFunctionPhiModularEstimate Phi S :=
  ⟨fun h ↦ h.congr_ae hTS, fun h ↦ h.congr_ae (fun f ↦ (hTS f).symm)⟩

namespace NegativePrincipalValueEndpoints

open PositivePrincipalValueEndpoints

/-- Unconditional common-conull-set identification for the lacunary supremum.
@isnad1 id=eventual.0h1v.s4.52c9676e2011 from=translated src=- shape=1b1fd463 vocab=1a36802c
-/
theorem lacunaryPrincipalValueMaximal_ae_eq (f : L0Infinity) :
    lacunaryPrincipalValueMaximal f =ᵐ[volume] lacunaryQuadraticCarlesonL0 f :=
  PositivePrincipalValueEndpoints.lacunaryPrincipalValueMaximal_ae_eq
    HilbertMaximalWeakResolved.hasUniformHilbertMaximalWeakBound f

/-- Unconditional common-conull-set identification for the full real supremum.
@isnad1 id=eventual.0h1v.s4.158ae1bdacb7 from=translated src=- shape=1b1fd463 vocab=329a1cdd
-/
theorem fullPrincipalValueMaximal_ae_eq (f : L0Infinity) :
    fullPrincipalValueMaximal f =ᵐ[volume] quadraticCarlesonL0 f :=
  PositivePrincipalValueEndpoints.fullPrincipalValueMaximal_ae_eq
    HilbertMaximalWeakResolved.hasUniformHilbertMaximalWeakBound f

/-- The negative headline for exactly the lacunary principal-value operator
occurring in the positive endpoint theorem.
@isnad1 id=not.1h1v.s3.942b29ee45bf from=translated src=- shape=2d03b771 vocab=f4339b06
-/
theorem lacunary_not_hasPhiModularEstimate
    (Phi : YoungFunction) (hPhi : GrowsSlowerThanEndpoint Phi) :
    ¬HasFunctionPhiModularEstimate Phi lacunaryPrincipalValueMaximal := by
  intro hPV
  have hlim := hPV.congr_ae lacunaryPrincipalValueMaximal_ae_eq
  exact negativeEndpoint_not_hasPhiModularEstimate Phi hPhi
    ((hasFunctionPhiModularEstimate_iff Phi lacunaryL0Operator).mp hlim)

/-- The full-real-modulation negative conclusion for exactly the same
principal-value operator as in the positive full endpoint.
@isnad1 id=not.1h1v.s3.95c938a324a5 from=translated src=- shape=2d03b771 vocab=90b0fe5a
-/
theorem full_not_hasPhiModularEstimate
    (Phi : YoungFunction) (hPhi : GrowsSlowerThanEndpoint Phi) :
    ¬HasFunctionPhiModularEstimate Phi fullPrincipalValueMaximal := by
  intro hPV
  exact fullNegativeEndpoint_not_hasPhiModularEstimate Phi hPhi
    (hPV.congr_ae fullPrincipalValueMaximal_ae_eq)

/-- The source's unit-level lacunary witness, with its printed `0 < κ < 1`
range and the genuine principal-value maximal operator.
@isnad1 id=ex.2h2v.s6.79c9de1ceec9 from=translated src=- shape=34a26d2f vocab=20e35bd0
-/
theorem lacunary_exists_paper_modular_witness
    (Phi : YoungFunction) (hPhi : GrowsSlowerThanEndpoint Phi)
    {kappa : ℝ} (hkappa : 0 < kappa ∧ kappa < 1) :
    ∃ f : L0Infinity,
      (∫⁻ x : ℝ, ENNReal.ofReal (Phi (‖f x‖))) <
        ENNReal.ofReal kappa * volume {x | 1 < lacunaryPrincipalValueMaximal f x} := by
  obtain ⟨f, hf⟩ := negativeEndpoint_exists_paper_modular_witness Phi hPhi hkappa
  refine ⟨f, ?_⟩
  have hlevel := functionOperatorLevelSet_measure_congr_ae
    (lacunaryPrincipalValueMaximal_ae_eq f) 1
  simp only [functionOperatorLevelSet, ENNReal.ofReal_one] at hlevel
  rw [hlevel]
  simpa only [operatorLevelSet, ENNReal.ofReal_one, lacunaryL0Operator] using hf

/-- The same source witness statement for the full real-modulation
principal-value operator.
@isnad1 id=ex.2h2v.s6.3e30f0533bab from=translated src=- shape=34a26d2f vocab=c966238b
-/
theorem full_exists_paper_modular_witness
    (Phi : YoungFunction) (hPhi : GrowsSlowerThanEndpoint Phi)
    {kappa : ℝ} (hkappa : 0 < kappa ∧ kappa < 1) :
    ∃ f : L0Infinity,
      (∫⁻ x : ℝ, ENNReal.ofReal (Phi (‖f x‖))) <
        ENNReal.ofReal kappa * volume {x | 1 < fullPrincipalValueMaximal f x} := by
  obtain ⟨f, hf⟩ := fullNegativeEndpoint_exists_paper_modular_witness Phi hPhi hkappa
  refine ⟨f, ?_⟩
  have hlevel := functionOperatorLevelSet_measure_congr_ae
    (fullPrincipalValueMaximal_ae_eq f) 1
  simp only [functionOperatorLevelSet, ENNReal.ofReal_one] at hlevel
  rw [hlevel]
  simpa only [functionOperatorLevelSet, ENNReal.ofReal_one] using hf

end NegativePrincipalValueEndpoints
end QuadraticCarleson
