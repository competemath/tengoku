/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.SharpAumannRepresentation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Joint-law and conditional-kernel representations

An observationally compatible complete-data law is most cleanly represented
as a coupling on `O × X`: its first marginal is the observed law and it gives
full mass to the graph of the feasible completion correspondence.  This file
proves that the moments attainable by such couplings are exactly the moments
attainable by supported conditional Markov kernels.

The equivalence itself uses only standard-Borel disintegration.  Atomlessness
enters later, when the sharp Aumann theorem purifies conditional barycentres.
-/
namespace Tengoku.Randomsettheory end Tengoku.Randomsettheory open Tengoku.Randomsettheory
open MeasureTheory Set
open scoped ProbabilityTheory

noncomputable section

namespace RandomSetTheory

variable {O X E : Type*} [MeasurableSpace O] [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Moments attainable by probability couplings whose observed marginal is
`mu` and whose latent coordinate belongs almost surely to `S o`.-/
def jointLawAttainableMoments (mu : Measure O) (S : O → Set X)
    (phi : O × X → E) : Set E :=
  {y | ∃ rho : Measure (O × X),
      ∃ _hrho : IsProbabilityMeasure rho,
        rho.fst = mu ∧
          rho {p | p.2 ∈ S p.1} = 1 ∧
            Integrable phi rho ∧ ∫ p, phi p ∂rho = y}

/-- Supported conditional kernels and compatible joint-law couplings generate
exactly the same moments.  This is the precise disintegration bridge behind
the report's notation `P(do,dx) = P_obs(do) K(dx|o)`.
@isnad1 id=eq.2h6v.s6.537d3a214cba from=translated src=- shape=c2bae277 vocab=17aefe00
-/
theorem jointLawAttainableMoments_eq_kernelAttainableMoments
    [StandardBorelSpace X] [Nonempty X]
    {mu : Measure O} [IsProbabilityMeasure mu]
    {S : O → Set X}
    (hgraph : MeasurableSet {p : O × X | p.2 ∈ S p.1})
    (hSmeas : ∀ o, MeasurableSet (S o))
    {phi : O × X → E} :
    jointLawAttainableMoments mu S phi =
      kernelAttainableMoments mu S phi := by
  apply Set.Subset.antisymm
  · rintro y ⟨rho, hrho, hfst, hrhoSupp, hphiInt, rfl⟩
    letI : IsProbabilityMeasure rho := hrho
    let kappa : ProbabilityTheory.Kernel O X := rho.condKernel
    letI : ProbabilityTheory.IsMarkovKernel kappa := by
      dsimp only [kappa]
      infer_instance
    have hkappaSuppFst : KernelSupportedOn rho.fst S kappa :=
      condKernel_supportedOn_of_jointLaw hgraph hSmeas hrhoSupp
    have hkappaSupp : KernelSupportedOn mu S kappa := by
      simpa only [hfst] using hkappaSuppFst
    have hdis : (rho.fst ⊗ₘ kappa) = rho :=
      Measure.disintegrate rho kappa
    have hprod : (mu ⊗ₘ kappa) = rho := by
      rw [← hfst]
      exact hdis
    refine ⟨kappa, inferInstance, hkappaSupp, ?_, ?_⟩
    · rwa [hprod]
    · rw [hprod]
  · rintro y ⟨kappa, hkappa, hkappaSupp, hphiInt, rfl⟩
    letI : ProbabilityTheory.IsMarkovKernel kappa := hkappa
    let rho : Measure (O × X) := mu ⊗ₘ kappa
    letI : IsProbabilityMeasure rho := by
      dsimp only [rho]
      infer_instance
    have hfst : rho.fst = mu := by
      dsimp only [rho]
      exact Measure.fst_compProd mu kappa
    have hfiber : ∀ᵐ o ∂mu, ∀ᵐ x ∂(kappa o), x ∈ S o := by
      filter_upwards [hkappaSupp] with o ho
      exact (mem_ae_iff_prob_eq_one (hSmeas o)).2 ho
    have hjoint : ∀ᵐ p ∂rho, p.2 ∈ S p.1 := by
      dsimp only [rho]
      exact Measure.ae_compProd_of_ae_ae hgraph hfiber
    have hrhoSupp : rho {p | p.2 ∈ S p.1} = 1 :=
      (mem_ae_iff_prob_eq_one hgraph).1 hjoint
    refine ⟨rho, inferInstance, hfst, hrhoSupp, ?_, rfl⟩
    simpa only [rho] using hphiInt

/-- Sharp Aumann representation stated directly for compatible joint laws.
On a finite atomless observed base and in a finite-dimensional target, no
extra closedness or purification hypothesis remains.
@isnad1 id=eq.10h7v.s8.db190bb9c2f7 from=translated src=- shape=37cd585a vocab=63d43e33
-/
theorem jointLawAttainableMoments_eq_aumannExpectation_of_atomless
    {H : Type*}
    [MetricSpace X] [CompleteSpace X] [BorelSpace X]
    [SecondCountableTopology X] [Nonempty X]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    [FiniteDimensional ℝ H]
    {mu : Measure O} [IsProbabilityMeasure mu]
    (hmu : IsAtomlessMeasure mu)
    {S : O → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    (hgraph : MeasurableSet {p : O × X | p.2 ∈ S p.1})
    (hSmeas : ∀ o, MeasurableSet (S o))
    (hcompact : ∀ o, IsCompact (S o)) (hne : ∀ o, (S o).Nonempty)
    {phi : O × X → H} (hphiMeas : Measurable phi)
    (hphiCont : ∀ o, Continuous fun x => phi (o, x))
    {g : O → ℝ} (hg : Integrable g mu)
    (hdom : ∀ o, ∀ x ∈ S o, ‖phi (o, x)‖ ≤ g o) :
    jointLawAttainableMoments mu S phi =
      aumannExpectation mu (fun o => (fun x => phi (o, x)) '' S o) := by
  rw [jointLawAttainableMoments_eq_kernelAttainableMoments hgraph hSmeas]
  exact kernelAttainableMoments_eq_aumannExpectation_of_atomless
    hmu hS hSmeas hcompact hne hphiMeas hphiCont hg hdom

end RandomSetTheory
-- Tengoku: root names of this library moved to Tengoku.Randomsettheory so they do not collide with other libraries (generated)
