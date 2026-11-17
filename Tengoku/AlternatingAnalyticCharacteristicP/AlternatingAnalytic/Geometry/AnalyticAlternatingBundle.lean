import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Geometry.FiniteCoordinateManifoldFamilies
import Tengoku.Seed.Geometry.Manifold.VectorBundle.Basic
import Tengoku.Seed.Topology.VectorBundle.ContinuousAlternatingMap

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Analytic alternating bundles over finite-coordinate manifolds

Mathlib's bundle of continuous alternating maps `x ↦ Alt^k(E₁ x; E₂ x)` is `C^n`
whenever the model action `alternatingMapAction` takes `C^n` families on open subsets
of the base to `C^n` families. Over an analytic manifold whose model has continuous
linear coordinates `P ≃L[K] K^d`, this holds for every degree, so the bundle is
analytic. This is the object part of Corollary 4.6 in the finite-coordinate setting;
morphisms are in `AnalyticAlternatingBundleMorphism.lean`.

## Main results

- `contMDiffVectorBundle_alternating_of_family`: the bundle is `C^n` if the model action
  preserves `C^n` families.
- `coordChangeL_continuousAlternatingMap_eq_alternatingMapAction`: the transition
  formula.
- `contMDiffVectorBundle_alternating_of_finiteCoordinates`: the bundle is analytic over
  a finite-coordinate base.
-/

noncomputable section

open Bundle Set
open scoped Bundle Manifold ContDiff

namespace AlternatingAnalytic

variable {K M F₁ F₂ : Type*} [NontriviallyNormedField K] [TopologicalSpace M]
  [NormedAddCommGroup F₁] [NormedSpace K F₁]
  [NormedAddCommGroup F₂] [NormedSpace K F₂]
  {E₁ E₂ : M → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module K (E₁ x)]
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module K (E₂ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [TopologicalSpace (TotalSpace F₂ E₂)]

section Transitions

variable (k : ℕ)
  (e₁ e₁' : Trivialization F₁ (π F₁ E₁))
  (e₂ e₂' : Trivialization F₂ (π F₂ E₂))
  [e₁.IsLinear K] [e₁'.IsLinear K] [e₂.IsLinear K] [e₂'.IsLinear K]

/-- The alternating transition is the model action of the reverse source transition and
the forward target transition.
@isnad1 id=eq.0h12v.s10.c1a479caea5b from=translated src=- shape=9d634f0a vocab=f9e161ce
-/
theorem continuousAlternatingMapCoordChange_eq_alternatingMapAction (b : M) :
    Pretrivialization.continuousAlternatingMapCoordChange K (Fin k) e₁ e₁' e₂ e₂' b =
      alternatingMapAction k
        ((e₁'.coordChangeL K e₁ b : F₁ →L[K] F₁),
          (e₂.coordChangeL K e₂' b : F₂ →L[K] F₂)) := by
  simp only [Pretrivialization.continuousAlternatingMapCoordChange,
    ContinuousLinearEquiv.coe_continuousAlternatingMapCongr,
    ContinuousLinearEquiv.symm_symm, alternatingMapAction]

variable [∀ x, TopologicalSpace (E₁ x)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₁ E₁] [FiberBundle F₂ E₂]

/-- On the common domain, the model action computes the change of pretrivialization.
@isnad1 id=eq.1h13v.s11.25998d26ab5b from=translated src=- shape=401de70a vocab=89cf7dba
-/
theorem alternatingMapAction_coordChange_apply (b : M)
    (hb : b ∈ e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet))
    (L : F₁ [⋀^Fin k]→L[K] F₂) :
    alternatingMapAction k
        ((e₁'.coordChangeL K e₁ b : F₁ →L[K] F₁),
          (e₂.coordChangeL K e₂' b : F₂ →L[K] F₂)) L =
      (Pretrivialization.continuousAlternatingMap K (Fin k) e₁' e₂'
        ⟨b, (Pretrivialization.continuousAlternatingMap K (Fin k) e₁ e₂).symm b L⟩).2 := by
  rw [← continuousAlternatingMapCoordChange_eq_alternatingMapAction]
  exact Pretrivialization.continuousAlternatingMapCoordChange_apply b hb L

end Transitions

variable [∀ x, TopologicalSpace (E₁ x)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₁ E₁] [VectorBundle K F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle K F₂ E₂]

section Assembly

variable {P H : Type*} [NormedAddCommGroup P] [NormedSpace K P]
  [TopologicalSpace H] [ChartedSpace H M] {I : ModelWithCorners K P H} {n : ℕ∞ω}
  [ContMDiffVectorBundle n F₁ E₁ I] [ContMDiffVectorBundle n F₂ E₂ I]
  (k : ℕ)
  (hfamily : ∀ {U : Set M}, IsOpen U →
    ∀ {γ : M → (F₁ →L[K] F₁) × (F₂ →L[K] F₂)},
      ContMDiffOn I 𝓘(K, (F₁ →L[K] F₁) × (F₂ →L[K] F₂)) n γ U →
      ContMDiffOn I 𝓘(K, (F₁ [⋀^Fin k]→L[K] F₂) →L[K] (F₁ [⋀^Fin k]→L[K] F₂))
        n (alternatingMapAction k ∘ γ) U)

include hfamily

/-- If the model action preserves `C^n` families, the alternating transitions are `C^n`
on the four-way overlap.
@isnad1 id=contmdif.1h15v.s15.efc9abc0bcb3 from=translated src=- shape=d84b6c99 vocab=33de44ec
-/
theorem contMDiffOn_continuousAlternatingMapCoordChange_of_family
    (e₁ e₁' : Trivialization F₁ (π F₁ E₁))
    (e₂ e₂' : Trivialization F₂ (π F₂ E₂))
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₁']
    [MemTrivializationAtlas e₂] [MemTrivializationAtlas e₂'] :
    ContMDiffOn I 𝓘(K, (F₁ [⋀^Fin k]→L[K] F₂) →L[K] (F₁ [⋀^Fin k]→L[K] F₂)) n
      (Pretrivialization.continuousAlternatingMapCoordChange K (Fin k) e₁ e₁' e₂ e₂')
      (e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)) := by
  have h₁ := contMDiffOn_coordChangeL (IB := I) (n := n) e₁' e₁
  have h₂ := contMDiffOn_coordChangeL (IB := I) (n := n) e₂ e₂'
  have hpair := (h₁.mono (show
      e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet) ⊆
        e₁'.baseSet ∩ e₁.baseSet from fun _ h ↦ ⟨h.2.1, h.1.1⟩)).prodMk_space
    (h₂.mono (fun _ h ↦ ⟨h.1.2, h.2.2⟩))
  have h := hfamily
    ((e₁.open_baseSet.inter e₂.open_baseSet).inter
      (e₁'.open_baseSet.inter e₂'.open_baseSet)) hpair
  exact h.congr fun b _ ↦
    continuousAlternatingMapCoordChange_eq_alternatingMapAction k e₁ e₁' e₂ e₂' b

variable [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul K (E₂ x)]

/-- If the model action preserves `C^n` families, the alternating prebundle is `C^n`.
@isnad1 id=iscontmd.1h11v.s14.dd5c97edcb25 from=translated src=- shape=2a68ce4b vocab=b2333e93
-/
theorem alternatingVectorPrebundle_isContMDiff_of_family :
    (Bundle.ContinuousAlternatingMap.vectorPrebundle K (Fin k) F₁ E₁ F₂ E₂).IsContMDiff
      I n where
  exists_contMDiffCoordChange := by
    rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩ _ ⟨e₁', e₂', he₁', he₂', rfl⟩
    exact ⟨Pretrivialization.continuousAlternatingMapCoordChange K (Fin k) e₁ e₁' e₂ e₂',
      contMDiffOn_continuousAlternatingMapCoordChange_of_family k hfamily e₁ e₁' e₂ e₂',
      Pretrivialization.continuousAlternatingMapCoordChange_apply⟩

/-- If the model action preserves `C^n` families, the alternating bundle is `C^n`.
@isnad1 id=contmdif.1h11v.s14.13730cb2d8e8 from=translated src=- shape=abafa4ad vocab=706f1a22
-/
theorem contMDiffVectorBundle_alternating_of_family :
    ContMDiffVectorBundle n (F₁ [⋀^Fin k]→L[K] F₂)
      (fun x ↦ E₁ x [⋀^Fin k]→L[K] E₂ x) I := by
  let := alternatingVectorPrebundle_isContMDiff_of_family (E₁ := E₁) (E₂ := E₂) k hfamily
  exact VectorPrebundle.contMDiffVectorBundle I
    (Bundle.ContinuousAlternatingMap.vectorPrebundle K (Fin k) F₁ E₁ F₂ E₂)

end Assembly

section BundleTransitions

variable [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul K (E₂ x)]

/-- On a common trivializing domain, the coordinate change of the alternating bundle is
the model action of the reverse source and forward target transitions.
@isnad1 id=eq.1h12v.s11.ac4f4210e5ec from=translated src=- shape=d2a35c5b vocab=50a05ca2
-/
theorem coordChangeL_continuousAlternatingMap_eq_alternatingMapAction (k : ℕ)
    (e₁ e₁' : Trivialization F₁ (π F₁ E₁))
    (e₂ e₂' : Trivialization F₂ (π F₂ E₂))
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₁']
    [MemTrivializationAtlas e₂] [MemTrivializationAtlas e₂'] (b : M)
    (hb : b ∈ e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)) :
    ((e₁.continuousAlternatingMap K (Fin k) e₂).coordChangeL K
        (e₁'.continuousAlternatingMap K (Fin k) e₂') b :
        (F₁ [⋀^Fin k]→L[K] F₂) →L[K] (F₁ [⋀^Fin k]→L[K] F₂)) =
      alternatingMapAction k
        ((e₁'.coordChangeL K e₁ b : F₁ →L[K] F₁),
          (e₂.coordChangeL K e₂' b : F₂ →L[K] F₂)) := by
  ext L v
  change (e₁.continuousAlternatingMap K (Fin k) e₂).coordChangeL K
      (e₁'.continuousAlternatingMap K (Fin k) e₂') b L v = _
  rw [Trivialization.coordChangeL_apply _ _ hb]
  exact congrArg (fun m ↦ m v)
    (alternatingMapAction_coordChange_apply k e₁ e₁' e₂ e₂' b hb L).symm

end BundleTransitions

section FiniteCoordinates

variable [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul K (E₂ x)]

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace K P]
  [ChartedSpace P M] [IsManifold 𝓘(K, P) ω M]
  [ContMDiffVectorBundle ω F₁ E₁ 𝓘(K, P)]
  [ContMDiffVectorBundle ω F₂ E₂ 𝓘(K, P)]
  {d : ℕ} (c : P ≃L[K] (Fin d → K)) (k : ℕ)

include c

end FiniteCoordinates

end AlternatingAnalytic
