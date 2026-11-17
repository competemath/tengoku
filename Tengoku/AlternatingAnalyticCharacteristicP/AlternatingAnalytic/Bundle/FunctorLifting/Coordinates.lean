import Tengoku.Seed.Geometry.Manifold.VectorBundle.ContMDiffSection
import Tengoku.Seed.Geometry.Manifold.VectorBundle.Hom

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Operator coordinates of bundle morphisms

For a fiberwise operator `φ : E₁ x →L E₂ x`, the local expression in the trivializations at `x`
and the local expression in the trivializations at another point `x₀` differ by the transition
operators. Local expressions at the point itself preserve identities and composition. The
local expressions of a `Cⁿ` section of the Hom bundle in the trivializations at a fixed point are
`Cⁿ` on every open subset of the common base set.
-/

open Bundle Set
open scoped Bundle Manifold ContDiff

namespace AlternatingAnalytic.FunctorLifting

variable {K P M : Type*} [NontriviallyNormedField K] [NormedAddCommGroup P] [NormedSpace K P]
  [TopologicalSpace M] {F₁ F₂ F₃ : Type*}
  [NormedAddCommGroup F₁] [NormedSpace K F₁] [NormedAddCommGroup F₂] [NormedSpace K F₂]
  [NormedAddCommGroup F₃] [NormedSpace K F₃]
  {E₁ E₂ E₃ : M → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module K (E₁ x)] [∀ x, TopologicalSpace (E₁ x)]
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module K (E₂ x)] [∀ x, TopologicalSpace (E₂ x)]
  [∀ x, AddCommGroup (E₃ x)] [∀ x, Module K (E₃ x)] [∀ x, TopologicalSpace (E₃ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [FiberBundle F₁ E₁] [VectorBundle K F₁ E₁]
  [TopologicalSpace (TotalSpace F₂ E₂)] [FiberBundle F₂ E₂] [VectorBundle K F₂ E₂]
  [TopologicalSpace (TotalSpace F₃ E₃)] [FiberBundle F₃ E₃] [VectorBundle K F₃ E₃]

/-- Changing the base point of the trivializations conjugates the local expression of an
operator by the transition operators.-/
theorem coordChangeL_comp_inCoordinates_comp {x₀ x : M}
    (h₁ : x ∈ (trivializationAt F₁ E₁ x₀).baseSet) (h₂ : x ∈ (trivializationAt F₂ E₂ x₀).baseSet)
    (φ : E₁ x →L[K] E₂ x) :
    ((trivializationAt F₂ E₂ x).coordChangeL K (trivializationAt F₂ E₂ x₀) x :
        F₂ →L[K] F₂).comp
      ((ContinuousLinearMap.inCoordinates F₁ E₁ F₂ E₂ x x x x φ).comp
        ((trivializationAt F₁ E₁ x₀).coordChangeL K (trivializationAt F₁ E₁ x) x :
          F₁ →L[K] F₁)) =
      ContinuousLinearMap.inCoordinates F₁ E₁ F₂ E₂ x₀ x x₀ x φ := by
  have hx₁ := mem_baseSet_trivializationAt F₁ E₁ x
  have hx₂ := mem_baseSet_trivializationAt F₂ E₂ x
  ext v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inCoordinates,
    ContinuousLinearEquiv.coe_coe]
  rw [Trivialization.coordChangeL_apply (R := K) _ _ ⟨h₁, hx₁⟩, Trivialization.symmL_apply _ hx₁,
    Trivialization.symm_apply_apply_mk _ hx₁,
    Trivialization.continuousLinearMapAt_apply_of_mem (R := K) (hb := hx₂),
    Trivialization.coordChangeL_apply (R := K) _ _ ⟨hx₂, h₂⟩,
    Trivialization.symm_apply_apply_mk _ hx₂,
    Trivialization.continuousLinearMapAt_apply_of_mem (R := K) (hb := h₂),
    Trivialization.symmL_apply _ h₁]

/-- The local expression of the identity at its own base point is the identity.-/
theorem inCoordinates_self_id (x : M) :
    ContinuousLinearMap.inCoordinates F₁ E₁ F₁ E₁ x x x x (ContinuousLinearMap.id K (E₁ x)) =
      ContinuousLinearMap.id K F₁ := by
  have hx := mem_baseSet_trivializationAt F₁ E₁ x
  ext v
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply]
  exact (trivializationAt F₁ E₁ x).continuousLinearMapAt_symmL hx v

/-- Local expressions at a common base point preserve composition.-/
theorem inCoordinates_self_comp (x : M) (f : E₁ x →L[K] E₂ x) (g : E₂ x →L[K] E₃ x) :
    ContinuousLinearMap.inCoordinates F₁ E₁ F₃ E₃ x x x x (g.comp f) =
      (ContinuousLinearMap.inCoordinates F₂ E₂ F₃ E₃ x x x x g).comp
        (ContinuousLinearMap.inCoordinates F₁ E₁ F₂ E₂ x x x x f) := by
  have hx := mem_baseSet_trivializationAt F₂ E₂ x
  ext v
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply]
  rw [(trivializationAt F₂ E₂ x).symmL_continuousLinearMapAt hx]

variable [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul K (E₂ x)] {n : ℕ∞ω}
  [ChartedSpace P M] [ContMDiffVectorBundle n F₁ E₁ 𝓘(K, P)]
  [ContMDiffVectorBundle n F₂ E₂ 𝓘(K, P)]

/-- The local expressions of a `Cⁿ` Hom section in the trivializations at a fixed point are
`Cⁿ` on open subsets of the common base set.-/
theorem contMDiffOn_inCoordinates_of_section
    (s : ContMDiffSection 𝓘(K, P) (F₁ →L[K] F₂) n (fun x ↦ E₁ x →L[K] E₂ x)) (x₀ : M)
    {U : Set M} (hU : IsOpen U)
    (hU' : U ⊆ (trivializationAt F₁ E₁ x₀).baseSet ∩ (trivializationAt F₂ E₂ x₀).baseSet) :
    ContMDiffOn 𝓘(K, P) 𝓘(K, F₁ →L[K] F₂) n
      (fun x ↦ ContinuousLinearMap.inCoordinates F₁ E₁ F₂ E₂ x₀ x x₀ x (s x)) U :=
  (((trivializationAt F₁ E₁ x₀).continuousLinearMap (RingHom.id K)
    (trivializationAt F₂ E₂ x₀)).contMDiffOn_section_iff hU hU').mp s.contMDiff.contMDiffOn

end AlternatingAnalytic.FunctorLifting
