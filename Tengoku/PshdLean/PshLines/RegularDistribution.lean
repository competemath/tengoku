import Tengoku.Seed.Analysis.Distribution.Distribution

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Regular distributions and distributional Levi operators

These are genuine continuous linear functionals on smooth compactly supported
test functions. Constructing a regular distribution requires an explicit local
integrability proof; no assertion that arbitrary PSH functions are locally
integrable is built into these definitions.
-/

noncomputable section

open Set MeasureTheory TopologicalSpace
open scoped Distributions

namespace PshLines

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Ω : Opens E}

/-- Positivity is tested against every nonnegative smooth test function.-/
def PositiveDistribution (T : 𝓓'(Ω, ℝ)) : Prop :=
  ∀ φ : 𝓓(Ω, ℝ), (∀ x, 0 ≤ φ x) → 0 ≤ T φ

/--
@isnad1 id=positive.2h4v.s8.e8b3128d452f from=translated src=- shape=bef1e16c vocab=4cc2a57e
-/
theorem PositiveDistribution.add {S T : 𝓓'(Ω, ℝ)}
    (hS : PositiveDistribution S) (hT : PositiveDistribution T) :
    PositiveDistribution (S + T) := by
  intro φ hφ
  exact add_nonneg (hS φ hφ) (hT φ hφ)

/--
@isnad1 id=positive.2h4v.s8.b4cfd8c69d35 from=translated src=- shape=6f9af835 vocab=58a8231f
-/
theorem PositiveDistribution.smul {T : 𝓓'(Ω, ℝ)} (hT : PositiveDistribution T)
    {c : ℝ} (hc : 0 ≤ c) : PositiveDistribution (c • T) := by
  intro φ hφ
  exact mul_nonneg hc (hT φ hφ)

section Regular

variable [MeasurableSpace E] [OpensMeasurableSpace E]

/-- The distribution induced by a real locally integrable density. The proof
argument rules out mathlib's zero fallback for a nonintegrable density.-/
def regularDistribution (μ : Measure E) (u : E → ℝ)
    (_hu : LocallyIntegrableOn u Ω μ) : 𝓓'(Ω, ℝ) :=
  TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.mul ℝ ℝ) μ u

/--
@isnad1 id=eq.1h5v.s9.523387617214 from=translated src=- shape=cde4bc90 vocab=ed15b82e
-/
theorem regularDistribution_apply (μ : Measure E) (u : E → ℝ)
    (hu : LocallyIntegrableOn u Ω μ) (φ : 𝓓(Ω, ℝ)) :
    regularDistribution μ u hu φ = ∫ x, φ x * u x ∂μ :=
  TestFunction.integralAgainstBilinCLM_eq_integral hu

/--
@isnad1 id=eq.3h5v.s7.4ab947d8a02d from=translated src=- shape=32a19057 vocab=b32e59ce
-/
theorem regularDistribution_congr_ae {μ : Measure E} {u w : E → ℝ}
    (hu : LocallyIntegrableOn u Ω μ) (hw : LocallyIntegrableOn w Ω μ)
    (heq : u =ᵐ[μ] w) : regularDistribution μ u hu = regularDistribution μ w hw := by
  ext φ
  rw [regularDistribution_apply, regularDistribution_apply]
  exact integral_congr_ae (heq.mono (fun x hx => congrArg (φ x * ·) hx))

/-- A nonnegative locally integrable density defines a positive distribution.
@isnad1 id=positive.2h4v.s7.56c6839e2dd8 from=translated src=- shape=4554ed28 vocab=1afde27f
-/
theorem positive_regularDistribution {μ : Measure E} {u : E → ℝ}
    (hu : LocallyIntegrableOn u Ω μ) (hpos : ∀ᵐ x ∂μ, 0 ≤ u x) :
    PositiveDistribution (regularDistribution μ u hu) := by
  intro φ hφ
  rw [regularDistribution_apply]
  exact integral_nonneg_of_ae (hpos.mono (fun x hx => mul_nonneg (hφ x) hx))

end Regular

section Levi

variable [NormedSpace ℂ E]

/-- The real directional Levi operator on distributions, with the same factor
one quarter as the classical real-Hessian definition. The derivatives have
order parameter `⊤`, so no finite-order fallback can occur.-/
def distributionalLeviCLM (v : E) : 𝓓'(Ω, ℝ) →L[ℝ] 𝓓'(Ω, ℝ) :=
  (1 / 4 : ℝ) •
    ((Distribution.lineDerivCLM (n := ⊤) (k := ⊤) v).comp
        (Distribution.lineDerivCLM (n := ⊤) (k := ⊤) v) +
      (Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (Complex.I • v)).comp
        (Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (Complex.I • v)))

/-- Two distributional derivatives cancel the two integration-by-parts signs.
@isnad1 id=eq.0h5v.s12.1e4f7a31f1d9 from=translated src=- shape=051f32cb vocab=ef984d53
-/
theorem distributionalLeviCLM_apply (T : 𝓓'(Ω, ℝ)) (v : E) (φ : 𝓓(Ω, ℝ)) :
    distributionalLeviCLM v T φ = (1 / 4 : ℝ) *
      (T (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v
          (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v φ)) +
       T (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (Complex.I • v)
         (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (Complex.I • v) φ))) := by
  simp [distributionalLeviCLM, Distribution.lineDerivCLM_apply, mul_add]

/-- Nonnegativity of every constant complex-direction Levi distribution.
The equivalence with a canonical PSH representative remains a separate theorem.-/
def HasNonnegativeDistributionalLevi (T : 𝓓'(Ω, ℝ)) : Prop :=
  ∀ v, PositiveDistribution (distributionalLeviCLM v T)

/--
@isnad1 id=hasnonne.2h4v.s8.91e6266e4952 from=translated src=- shape=aa1b1dff vocab=80277551
-/
theorem HasNonnegativeDistributionalLevi.add {S T : 𝓓'(Ω, ℝ)}
    (hS : HasNonnegativeDistributionalLevi S)
    (hT : HasNonnegativeDistributionalLevi T) :
    HasNonnegativeDistributionalLevi (S + T) := by
  intro v
  rw [map_add]
  exact (hS v).add (hT v)

/--
@isnad1 id=hasnonne.2h4v.s8.05d7eaec4047 from=translated src=- shape=e7df97ea vocab=2ea11553
-/
theorem HasNonnegativeDistributionalLevi.smul {T : 𝓓'(Ω, ℝ)}
    (hT : HasNonnegativeDistributionalLevi T) {c : ℝ} (hc : 0 ≤ c) :
    HasNonnegativeDistributionalLevi (c • T) := by
  intro v
  rw [map_smul]
  exact (hT v).smul hc

end Levi

end PshLines
