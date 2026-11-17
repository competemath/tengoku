import Tengoku.SingularityCompleteLean.Singularity.CocompactHaarAverages
import Tengoku.SingularityCompleteLean.Singularity.CompactActionContraction
import Tengoku.SingularityCompleteLean.Singularity.HyperbolicTraceNormalization
import Tengoku.SingularityCompleteLean.Singularity.StableProductRigidity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# One-sided product rigidity on the actual compact quotient

A diagonal-invariant probability covered by horocycle product charts equals
the normalized Haar quotient probability if its transverse marginals are
absolutely continuous relative to the reference transverse marginals. The
marginals along the contracting horocycles can be arbitrary.

The finite invariant quotient lift of the Naïm current is constructed in
`GeometricNaimQuotient`. The actual one-sided application, including the
off-diagonal endpoint product transfer, is proved in `OneSidedNaimRigidity`.
-/

noncomputable section
open Set MeasureTheory MeasureTheory.Measure Filter
open scoped MatrixGroups UpperHalfPlane Topology

namespace Singularity

/-- A product chart obtained by moving a transverse section along lower horocycles.-/
def lowerShearQuotientChart {B : Type*} (Γ : Subgroup SL(2, ℝ))
    (σ : B → SL(2, ℝ) ⧸ Γ) (p : ℝ × B) : SL(2, ℝ) ⧸ Γ :=
  lowerShearMatrix p.1 • σ p.2

/-- Measurability requires only measurability of the transverse section.
@isnad1 id=measurab.1h3v.s10.e0f287250205 from=translated src=- shape=f7a2bf2a vocab=791f99b4
-/
theorem measurable_lowerShearQuotientChart {B : Type*} [MeasurableSpace B]
    [MeasurableSpace SL(2, ℝ)] [BorelSpace SL(2, ℝ)]
    (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ] (σ : B → SL(2, ℝ) ⧸ Γ) (hσ : Measurable σ) :
    Measurable (lowerShearQuotientChart Γ σ) := by
  let := slTwo_polishSpace
  exact (continuous_lowerShearMatrix.measurable.comp measurable_fst).smul (hσ.comp measurable_snd)

/-- Changing the first chart coordinate is exactly a lower-shear translation.
@isnad1 id=eq.0h6v.s10.8223ed133f8c from=translated src=- shape=6aecb444 vocab=ecb6c847
-/
theorem lowerShearQuotientChart_change {B : Type*} (Γ : Subgroup SL(2, ℝ))
    (σ : B → SL(2, ℝ) ⧸ Γ) (u v : ℝ) (b : B) :
    lowerShearQuotientChart Γ σ (v, b) =
      lowerShearMatrix (v - u) • lowerShearQuotientChart Γ σ (u, b) := by
  simp only [lowerShearQuotientChart, ← mul_smul, ← lowerShearMatrix_add, sub_add_cancel]

/-- Actual quotient rigidity for arbitrary measurable coordinates along contracting
horocycles; the first coordinate need not be the additive shear parameter.
@isnad1 id=eq.7h12v.s12.a8af4f947c4c from=translated src=- shape=531e9e52 vocab=c3fd3236
-/
theorem cocompact_invariant_probability_eq_haar_of_stable_charts
    {A B I : Type*} [MeasurableSpace A] [MeasurableSpace B] [Countable I]
    [MeasurableSpace SL(2, ℝ)] [BorelSpace SL(2, ℝ)]
    (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
    (ν : Measure SL(2, ℝ)) [IsHaarMeasure ν]
    (m : Measure (SL(2, ℝ) ⧸ Γ)) [IsProbabilityMeasure m]
    (τ : ℝ) (hτ : 0 < τ)
    (hinv : MeasurePreserving (fun x : SL(2, ℝ) ⧸ Γ => dilationMatrix τ • x) m m)
    (α α' : I → Measure A) (β β' : I → Measure B)
    [∀ i, NeZero (α i)] [∀ i, SFinite (β i)] [∀ i, SFinite (β' i)]
    (hβ : ∀ i, β' i ≪ β i)
    (Φ : I → A × B → SL(2, ℝ) ⧸ Γ) (hΦ : ∀ i, Measurable (Φ i))
    (href : ∀ i, ((α i).prod (β i)).map (Φ i) ≪
      cocompactHaarQuotientProbability Γ ν)
    (hcover : m ≪ Measure.sum (fun i =>
      ((α' i).prod (β' i)).map (Φ i)))
    (hfibre : ∀ i a a' b, ∃ u : ℝ, Φ i (a', b) = lowerShearMatrix u • Φ i (a, b)) :
    m = cocompactHaarQuotientProbability Γ ν := by
  let := slTwo_polishSpace
  let := slTwo_locallyCompactSpace
  let := cocompact_slTwo_quotient Γ
  let := cocompactHaarQuotientProbability_probability Γ ν
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  obtain ⟨ns, hns, hlim⟩ := cocompactHaar_birkhoffAverage_subsequence Γ ν τ hτ f
    f.continuous.measurable ‖f‖ (norm_nonneg _) f.norm_coe_le_norm
  let T : (SL(2, ℝ) ⧸ Γ) → (SL(2, ℝ) ⧸ Γ) := fun x => dilationMatrix τ • x
  let c : ℝ := ∫ x, f x ∂cocompactHaarQuotientProbability Γ ν
  have hset : MeasurableSet {x | Tendsto (fun k => birkhoffAverage ℝ T f (ns k) x)
      atTop (𝓝 c)} := by
    exact measurableSet_tendsto _ (fun k => measurable_real_birkhoffAverage T
      (measurable_const_smul _) f f.continuous.measurable (ns k))
  have hlim' : ∀ᵐ x ∂m, Tendsto (fun k => birkhoffAverage ℝ T f (ns k) x) atTop (𝓝 c) := by
    apply hcover.ae_le
    apply ae_sum_iff.mpr
    intro i
    have hchart := hΦ i
    apply (ae_map_iff hchart.aemeasurable hset).mpr
    apply ae_product_of_fibre_saturation (α i) (α' i) (β i) (β' i) (hβ i)
      _ (hset.preimage hchart)
    · intro a a' b ha
      obtain ⟨u, hu⟩ := hfibre i a a' b
      rw [hu]
      exact compact_lowerShear_average_limit τ hτ u _ f f.continuous
        ns hns.tendsto_atTop c ha
    · exact ae_of_ae_map hchart.aemeasurable ((href i).ae_le hlim)
  exact integral_eq_of_birkhoffAverage_subsequence m T hinv f f.continuous.measurable
    ‖f‖ (norm_nonneg _) f.norm_coe_le_norm ns hns.tendsto_atTop c hlim'

/-- Actual quotient rigidity under explicit one-sided horocycle chart hypotheses.
@isnad1 id=eq.6h11v.s12.46f874366091 from=translated src=- shape=d2f08296 vocab=15d55973
-/
theorem cocompact_invariant_probability_eq_haar_of_horocycle_charts
    {B I : Type*} [MeasurableSpace B] [Countable I]
    [MeasurableSpace SL(2, ℝ)] [BorelSpace SL(2, ℝ)]
    (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
    (ν : Measure SL(2, ℝ)) [IsHaarMeasure ν]
    (m : Measure (SL(2, ℝ) ⧸ Γ)) [IsProbabilityMeasure m]
    (τ : ℝ) (hτ : 0 < τ)
    (hinv : MeasurePreserving (fun x : SL(2, ℝ) ⧸ Γ => dilationMatrix τ • x) m m)
    (α α' : I → Measure ℝ) (β β' : I → Measure B)
    [∀ i, NeZero (α i)] [∀ i, SFinite (β i)] [∀ i, SFinite (β' i)]
    (hβ : ∀ i, β' i ≪ β i)
    (σ : I → B → SL(2, ℝ) ⧸ Γ) (hσ : ∀ i, Measurable (σ i))
    (href : ∀ i, ((α i).prod (β i)).map (lowerShearQuotientChart Γ (σ i)) ≪
      cocompactHaarQuotientProbability Γ ν)
    (hcover : m ≪ Measure.sum (fun i =>
      ((α' i).prod (β' i)).map (lowerShearQuotientChart Γ (σ i)))) :
    m = cocompactHaarQuotientProbability Γ ν := by
  exact cocompact_invariant_probability_eq_haar_of_stable_charts Γ ν m τ hτ hinv
    α α' β β' hβ (fun i => lowerShearQuotientChart Γ (σ i))
    (fun i => measurable_lowerShearQuotientChart Γ (σ i) (hσ i)) href hcover
    (fun i u v b => ⟨v - u, lowerShearQuotientChart_change Γ (σ i) u v b⟩)

end Singularity
