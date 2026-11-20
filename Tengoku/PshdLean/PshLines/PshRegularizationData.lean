import Tengoku.PshdLean.PshLines.PshRepresentative

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Distribution restriction and decreasing smooth PSH approximation data

These definitions describe actual continuous test functionals and actual smooth
functions. They assert no existence of a regularization or PSH representative.
The existence and limit arguments live in the regularization modules.
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Distributions Topology ContDiff

namespace PshLines

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Ω U : Opens E}

/-- Restriction by the continuous inclusion of test functions. The explicit
domain inclusion excludes the zero fallback of `TestFunction.monoCLM`.-/
def restrictDistribution (T : 𝓓'(Ω, ℝ)) (_hUΩ : U ≤ Ω) : 𝓓'(U, ℝ) :=
  T.comp (TestFunction.monoCLM ℝ)

/-- Inclusion into a larger open domain does not change a test function's values.
@isnad1 id=eq.1h4v.s10.0cf0fa60fa7b from=translated src=- shape=ae6da7bb vocab=e89cc7f9
-/
theorem testFunction_inclusion_coe (hUΩ : U ≤ Ω) (φ : 𝓓(U, ℝ)) :
    ((TestFunction.monoCLM ℝ φ : 𝓓(Ω, ℝ)) : E → ℝ) = φ := by
  simp only [TestFunction.monoCLM_apply, le_refl, hUΩ, and_self, ite_true]

/--
@isnad1 id=eq.1h5v.s10.1cd153a691d0 from=translated src=- shape=5c98356e vocab=1920807c
-/
theorem restrictDistribution_apply (T : 𝓓'(Ω, ℝ)) (hUΩ : U ≤ Ω)
    (φ : 𝓓(U, ℝ)) :
    restrictDistribution T hUΩ φ = T (TestFunction.monoCLM ℝ φ) := rfl

/--
@isnad1 id=eq.0h3v.s6.fd04fed56dc3 from=translated src=- shape=44618994 vocab=3a98661d
-/
theorem restrictDistribution_self (T : 𝓓'(Ω, ℝ)) :
    restrictDistribution T le_rfl = T := by
  ext φ
  rw [restrictDistribution_apply]
  congr 1
  apply TestFunction.ext
  intro x
  exact congrFun (testFunction_inclusion_coe le_rfl φ) x

/-- Restriction of distributions is transitive.  Although the bundled test
functions are included in two stages on the left, both inclusions have the
same underlying function as the direct inclusion on the right.
@isnad1 id=eq.2h5v.s7.92403f01252e from=translated src=- shape=2f8ea105 vocab=2d758495
-/
theorem restrictDistribution_trans {V : Opens E} (T : 𝓓'(Ω, ℝ))
    (hVU : V ≤ U) (hUΩ : U ≤ Ω) :
    restrictDistribution (restrictDistribution T hUΩ) hVU =
      restrictDistribution T (hVU.trans hUΩ) := by
  ext φ
  simp only [restrictDistribution_apply]
  congr 1
  apply TestFunction.ext
  intro x
  calc
    ((TestFunction.monoCLM ℝ (TestFunction.monoCLM ℝ φ) : 𝓓(Ω, ℝ)) : E → ℝ) x =
        ((TestFunction.monoCLM ℝ φ : 𝓓(U, ℝ)) : E → ℝ) x :=
      congrFun (testFunction_inclusion_coe hUΩ (TestFunction.monoCLM ℝ φ)) x
    _ = φ x := congrFun (testFunction_inclusion_coe hVU φ) x
    _ = ((TestFunction.monoCLM ℝ φ : 𝓓(Ω, ℝ)) : E → ℝ) x :=
      (congrFun (testFunction_inclusion_coe (hVU.trans hUΩ) φ) x).symm

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] in
/-- Restricting a regular distribution gives the regular distribution of the
same density on the smaller open set.
@isnad1 id=eq.2h5v.s7.c35419a08e91 from=translated src=- shape=f7209c8e vocab=5501d12c
-/
theorem restrictDistribution_regularDistribution (μ : Measure E)
    {u : E → ℝ} (hu : LocallyIntegrableOn u Ω μ) (hUΩ : U ≤ Ω) :
    restrictDistribution (regularDistribution μ u hu) hUΩ =
      regularDistribution μ u (hu.mono_set hUΩ) := by
  ext φ
  rw [restrictDistribution_apply, regularDistribution_apply,
    regularDistribution_apply]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change (TestFunction.monoCLM ℝ φ : 𝓓(Ω, ℝ)) x * u x = φ x * u x
    rw [congrFun (testFunction_inclusion_coe hUΩ φ) x]

omit [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] in
/-- A genuine PSH representative remains a representative after restricting
both its distribution and its open domain.
@isnad1 id=ispshrep.2h6v.s7.82b1c84e06a7 from=translated src=- shape=102b4cc4 vocab=fcf4894f
-/
theorem IsPshRepresentative.restrict (μ : Measure E) {T : 𝓓'(Ω, ℝ)}
    {u : E → EReal} (hu : IsPshRepresentative μ T u) (hUΩ : U ≤ Ω) :
    IsPshRepresentative μ (restrictDistribution T hUΩ) u := by
  obtain ⟨huPsh, huFinite, huLocal, huT⟩ := hu
  have huLocalU := huLocal.mono_set hUΩ
  refine ⟨huPsh.mono hUΩ,
    ae_restrict_of_ae_restrict_of_subset hUΩ huFinite, huLocalU, ?_⟩
  calc
    restrictDistribution T hUΩ =
        restrictDistribution (regularDistribution μ (fun x => (u x).toReal) huLocal) hUΩ :=
      congrArg (fun S : 𝓓'(Ω, ℝ) => restrictDistribution S hUΩ) huT
    _ = regularDistribution μ (fun x => (u x).toReal) huLocalU :=
      restrictDistribution_regularDistribution μ huLocal hUΩ

/-- A decreasing smooth PSH approximation to an actual distribution, with weak
convergence tested against every smooth compactly supported test function.
Smoothness is global, whereas PSH and monotonicity are asserted only on Ω.-/
def IsDecreasingSmoothPshApproximation (μ : Measure E) (T : 𝓓'(Ω, ℝ))
    (f : ℕ → E → ℝ) : Prop :=
  (∀ n, ContDiff ℝ (⊤ : ℕ∞) (f n)) ∧
  (∀ n, DiscPshOn (fun x => (f n x : EReal)) Ω) ∧
  (∀ x ∈ Ω, Antitone (fun n => f n x)) ∧
  ∀ φ : 𝓓(Ω, ℝ),
    Tendsto (fun n => ∫ x, φ x * f n x ∂μ) atTop (𝓝 (T φ))

end PshLines
