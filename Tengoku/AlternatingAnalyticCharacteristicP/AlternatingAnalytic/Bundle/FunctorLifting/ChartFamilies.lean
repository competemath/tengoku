import Tengoku.Seed.Geometry.Manifold.ContMDiff.NormedSpace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Families parametrized by open subsets of the model space

On a manifold modelled on a normed space `P` without boundary, a map into a normed space is `Cⁿ`
on an open set exactly when all its expressions in extended charts are `Cⁿ` on the corresponding
open subsets of `P`. Consequently, a map between normed spaces that preserves `Cⁿ` families
parametrized by open subsets of `P` also preserves `Cⁿ` families parametrized by open subsets of
the manifold. This is the chart step in the familywise form of Theorem 2.1.
-/

open Set
open scoped Manifold ContDiff

namespace AlternatingAnalytic.FunctorLifting

variable {K P M G H : Type*} [NontriviallyNormedField K] [NormedAddCommGroup P] [NormedSpace K P]
  [TopologicalSpace M] [ChartedSpace P M] {n : ℕ∞ω}
  [NormedAddCommGroup G] [NormedSpace K G] [NormedAddCommGroup H] [NormedSpace K H]

/-- The chart domains cut out by an open set are open in the model space.
@isnad1 id=isopen.1h5v.s7.baa9ab98b358 from=translated src=- shape=de8227dc vocab=ded7ce18
-/
theorem isOpen_extChartAt_target_inter_preimage {U : Set M} (hU : IsOpen U) (x : M) :
    IsOpen ((extChartAt 𝓘(K, P) x).target ∩ (extChartAt 𝓘(K, P) x).symm ⁻¹' U) :=
  (continuousOn_extChartAt_symm x).isOpen_inter_preimage (isOpen_extChartAt_target x) hU

/-- The open-chart criterion for `Cⁿ` maps into a normed space, at every order.
@isnad1 id=iff.1h7v.s8.73ceec90d24c from=translated src=- shape=3d2dc41a vocab=f27d5f2d
-/
theorem contMDiffOn_iff_contDiffOn_extChartAt [IsManifold 𝓘(K, P) n M] {U : Set M}
    (hU : IsOpen U) {γ : M → G} :
    ContMDiffOn 𝓘(K, P) 𝓘(K, G) n γ U ↔
      ∀ x : M, ContDiffOn K n (γ ∘ (extChartAt 𝓘(K, P) x).symm)
        ((extChartAt 𝓘(K, P) x).target ∩ (extChartAt 𝓘(K, P) x).symm ⁻¹' U) := by
  constructor
  · intro hγ x
    simpa [chartAt_self_eq, mfld_simps] using (contMDiffOn_iff.mp hγ).2 x 0
  · intro hγ x hx
    have hxV : extChartAt 𝓘(K, P) x x ∈
        (extChartAt 𝓘(K, P) x).target ∩ (extChartAt 𝓘(K, P) x).symm ⁻¹' U := by
      simpa only [mfld_simps] using hx
    have hc : ContMDiffOn 𝓘(K, P) 𝓘(K, G) n (γ ∘ (extChartAt 𝓘(K, P) x).symm)
        ((extChartAt 𝓘(K, P) x).target ∩ (extChartAt 𝓘(K, P) x).symm ⁻¹' U) :=
      contMDiffOn_iff_contDiffOn.mpr (hγ x)
    apply ContMDiffAt.contMDiffWithinAt
    apply contMDiffAt_iff_source.mpr
    exact (hc.contMDiffAt ((isOpen_extChartAt_target_inter_preimage hU x).mem_nhds hxV))
      |>.contMDiffWithinAt

/-- A map preserving `Cⁿ` families on open subsets of the model space `P` preserves `Cⁿ`
families on open subsets of the manifold.
@isnad1 id=contmdif.3h9v.s8.bf672658d80b from=translated src=- shape=fbea93d0 vocab=233a5999
-/
theorem contMDiffOn_comp_of_preservesFamilies [IsManifold 𝓘(K, P) n M] {Φ : H → G}
    (hΦ : ∀ U : Set P, IsOpen U → ∀ γ : P → H, ContDiffOn K n γ U →
      ContDiffOn K n (fun t ↦ Φ (γ t)) U)
    {U : Set M} (hU : IsOpen U) {γ : M → H} (hγ : ContMDiffOn 𝓘(K, P) 𝓘(K, H) n γ U) :
    ContMDiffOn 𝓘(K, P) 𝓘(K, G) n (fun x ↦ Φ (γ x)) U := by
  rw [contMDiffOn_iff_contDiffOn_extChartAt hU] at hγ ⊢
  exact fun x ↦ hΦ _ (isOpen_extChartAt_target_inter_preimage hU x) _ (hγ x)

end AlternatingAnalytic.FunctorLifting
