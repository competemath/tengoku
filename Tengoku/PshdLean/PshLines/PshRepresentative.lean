import Tengoku.PshdLean.PshLines.PlurisubharmonicAE
import Tengoku.PshdLean.PshLines.GermPshLeviPositivity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Genuine PSH representatives of distributions

The representative is an actual extended-real PSH function, finite almost
everywhere on its domain. Local integrability and equality with the specified
distribution are part of what it means to represent that distribution, not
assumptions about every distribution. Existence is a separate theorem.
-/

noncomputable section

open Set MeasureTheory TopologicalSpace
open scoped Distributions

namespace PshLines

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
variable (μ : Measure E) {Ω : Opens E}

/-- A genuine PSH representative of a distribution on its open domain.
Almost-everywhere finiteness prevents confusing the `toReal` of `⊥` with zero.-/
def IsPshRepresentative (T : 𝓓'(Ω, ℝ)) (u : E → EReal) : Prop :=
  PlurisubharmonicOn u Ω ∧
  (∀ᵐ x ∂μ.restrict Ω, u x ≠ ⊤ ∧ u x ≠ ⊥) ∧
  ∃ hu : LocallyIntegrableOn (fun x => (u x).toReal) Ω μ,
    T = regularDistribution μ (fun x => (u x).toReal) hu

variable {μ} [μ.IsAddHaarMeasure] {T : 𝓓'(Ω, ℝ)} {u v : E → EReal}

/-- Genuine PSH representatives are unique on the open domain, without a
connectedness assumption. No uniqueness outside that domain is asserted.
@isnad1 id=eqon.2h6v.s8.9e3b820611d7 from=translated src=- shape=165ccb43 vocab=a6ab16b9
-/
theorem IsPshRepresentative.unique (hu : IsPshRepresentative μ T u)
    (hv : IsPshRepresentative μ T v) : EqOn u v Ω := by
  obtain ⟨huP, huF, huL, huT⟩ := hu
  obtain ⟨hvP, hvF, hvL, hvT⟩ := hv
  exact huP.eqOn_of_regularDistribution_eq hvP μ huL hvL
    (huF.mono (fun _ hx => EReal.coe_toReal hx.1 hx.2))
    (hvF.mono (fun _ hx => EReal.coe_toReal hx.1 hx.2))
    (huT.symm.trans hvT)

/-- Every genuinely represented PSH distribution has nonnegative Levi
derivatives. The converse must construct a representative rather than assume it.
@isnad1 id=hasnonne.1h5v.s8.532b2dc6a39c from=translated src=- shape=c287e555 vocab=76f4ed49
-/
theorem IsPshRepresentative.hasNonnegativeDistributionalLevi
    (hu : IsPshRepresentative μ T u) : HasNonnegativeDistributionalLevi T := by
  obtain ⟨huP, huF, huL, rfl⟩ := hu
  exact huP.hasNonnegativeDistributionalLevi_of_locallyIntegrable huL huF

end PshLines
