/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Tengoku.LanaOka.Oka.Analysis.LocallyConvex.Schwartz
import Tengoku.LanaOka.Oka.Topology.Sheaves.Cohomology.CechDegreeOne
import Tengoku.LanaOka.Oka.Topology.Sheaves.SectionModel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finiteness of Čech cohomology in degree one from a Fréchet section model

Let `M` be a section model of the abelian sheaf `F` (`TopCat.Sheaf.SectionModel`) by Fréchet
spaces, indexed by a countable type. Čech cochains of a finite family of opens are then
identified with the Fréchet spaces `TopCat.Sheaf.SectionModel.Cochain` of families of model
sections, the Čech differential and refinement with continuous linear maps
(`TopCat.Sheaf.SectionModel.dL`, `TopCat.Sheaf.SectionModel.refineL`).

**Cartan–Serre argument** (`TopCat.Sheaf.SectionModel.finiteDimensional_of_cech`). Let `U`, `V`
be finite families of opens with `V i` of compact closure inside `U i`, such that every Čech
`1`-cocycle of `V` is the refinement of a cocycle of `U` up to a coboundary. If restriction to
relatively compact opens is compact on the model, then the map
`Z¹(U) × C⁰(V) → Z¹(V)`, `(z, c) ↦ z|_V + d c` is surjective and differs from `(z, c) ↦ d c` by a
compact operator, so by Schwartz's theorem the cokernel `Z¹(V) / B¹(V)` is finite dimensional.
Consequently every `ℂ`-linear quotient of the cocycles of `V` vanishing on coboundaries (such as
`H¹(X, F)`) is finite dimensional.
-/

universe u v

open CategoryTheory TopologicalSpace Opposite Topology Filter Set TopCat.Presheaf

namespace TopCat.Sheaf.SectionModel

variable {X : TopCat.{u}} {F : AbSheaf X} {𝒬 : Type u} {E : 𝒬 → Type v}
  [∀ q, AddCommGroup (E q)] [∀ q, Module ℂ (E q)]

section Basic

variable [∀ q, UniformSpace (E q)] [∀ q, IsUniformAddGroup (E q)] [∀ q, ContinuousSMul ℂ (E q)]
  (M : SectionModel F E) {ι : Type u} (U : ι → Opens X)

/-- Čech `n`-cochains of the family `U`, read in the model. -/
abbrev Cochain (n : ℕ) : Type _ := ∀ σ : Fin (n + 1) → ι, M.sub (cechOpen U σ)

/-- Čech cochains of `F` are cochains in the model. -/
noncomputable def cochainEquiv (n : ℕ) : CechCochain U F.obj n ≃+ M.Cochain U n :=
  AddEquiv.piCongrRight fun σ ↦ M.sectionsEquiv (cechOpen U σ)

omit [∀ q, IsUniformAddGroup (E q)] [∀ q, ContinuousSMul ℂ (E q)] in
lemma cochainEquiv_apply (n : ℕ) (c : CechCochain U F.obj n) (σ : Fin (n + 1) → ι) :
    M.cochainEquiv U n c σ = M.sectionsEquiv _ (c σ) :=
  rfl

/-- The Čech differential on model cochains. -/
noncomputable def dL (n : ℕ) : M.Cochain U n →L[ℂ] M.Cochain U (n + 1) :=
  ContinuousLinearMap.pi fun τ ↦ ∑ j : Fin (n + 2), ((-1 : ℂ) ^ (j : ℕ)) •
    (M.subRes (cechOpen_le_comp U τ j.succAbove)).comp
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun σ : Fin (n + 1) → ι ↦ M.sub (cechOpen U σ))
        (τ ∘ j.succAbove))

section Refine

variable {V : ι → Opens X} (hVU : ∀ i, V i ≤ U i)

/-- Refinement of model cochains along `V i ≤ U i`. -/
noncomputable def refineL (n : ℕ) : M.Cochain U n →L[ℂ] M.Cochain V n :=
  ContinuousLinearMap.pi fun σ ↦ (M.subRes (cechOpen_le_cechOpen_comp U hVU σ)).comp
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun σ : Fin (n + 1) → ι ↦ M.sub (cechOpen U σ)) σ)

omit [∀ q, IsUniformAddGroup (E q)] [∀ q, ContinuousSMul ℂ (E q)] in
lemma refineL_apply (n : ℕ) (c : M.Cochain U n) (σ : Fin (n + 1) → ι) :
    M.refineL U hVU n c σ = M.subRes (cechOpen_le_cechOpen_comp U hVU σ) (c σ) :=
  rfl

omit [∀ q, IsUniformAddGroup (E q)] [∀ q, ContinuousSMul ℂ (E q)] in
/-- The model refinement is the Čech refinement. -/
lemma cochainEquiv_cechRefine (n : ℕ) (c : CechCochain U F.obj n) :
    M.cochainEquiv V n (cechRefine U (τ := id) hVU F.obj n c) =
      M.refineL U hVU n (M.cochainEquiv U n c) := by
  funext σ
  rw [cochainEquiv_apply, cechRefine_apply, refineL_apply, cochainEquiv_apply,
    sectionsEquiv_map]
  rfl

end Refine

omit [∀ q, IsUniformAddGroup (E q)] [∀ q, ContinuousSMul ℂ (E q)] in
/-- The model cochain of the image of a cochain under `smulHom c` is `c •` the model cochain. -/
lemma cochainEquiv_smulHom (n : ℕ) (c : ℂ) (z : CechCochain U F.obj n) :
    M.cochainEquiv U n (cechCochainMap U (M.smulHom c).hom n z) =
      c • M.cochainEquiv U n z := by
  funext σ
  ext q
  simp only [cochainEquiv_apply, Pi.smul_apply, Submodule.coe_smul, sectionsEquiv_apply_coe]
  change (M.ε q.1).symm (F.obj.map _ ((M.smulHom c).hom.app _ (z σ))) = _
  rw [← ConcreteCategory.comp_apply, ← (M.smulHom c).hom.naturality,
    ConcreteCategory.comp_apply]
  apply (M.ε q.1).injective
  rw [M.ε_smul, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

end Basic

section Frechet

variable [∀ q, UniformSpace (E q)] [∀ q, IsUniformAddGroup (E q)] [∀ q, ContinuousSMul ℂ (E q)]
  [∀ q, T2Space (E q)] [∀ q, FirstCountableTopology (E q)] [∀ q, CompleteSpace (E q)]
  [∀ q, LocallyConvexSpace ℝ (E q)] [Countable 𝒬]
  (M : SectionModel F E) {ι : Type u} [Finite ι]

/-- Čech `1`-cocycles of the family `U`, read in the model: a closed subspace of the model
cochains. -/
noncomputable abbrev Z1 (U : ι → Opens X) : Submodule ℂ (M.Cochain U 1) :=
  LinearMap.ker (M.dL U 1 : M.Cochain U 1 →ₗ[ℂ] M.Cochain U 2)

omit [∀ q, FirstCountableTopology (E q)] [∀ q, CompleteSpace (E q)]
  [∀ q, LocallyConvexSpace ℝ (E q)] [Countable 𝒬] [Finite ι] in
lemma isClosed_Z1 (U : ι → Opens X) : IsClosed (M.Z1 U : Set (M.Cochain U 1)) :=
  (M.dL U 1).isClosed_ker

omit [∀ q, LocallyConvexSpace ℝ (E q)] in
/-- If `V i` has compact closure inside `U i` for all `i`, refinement of model cochains is a
compact operator. -/
lemma isCompactOperator_refineL
    (hK : ∀ (W : Opens X) (x : X), x ∈ W → ∃ (q q' : 𝒬) (h : M.Q q' ≤ M.Q q),
      x ∈ M.Q q' ∧ M.Q q ≤ W ∧ IsCompactOperator (M.resL q q' h))
    (U : ι → Opens X) {V : ι → Opens X} (hVU : ∀ i, V i ≤ U i)
    (hVc : ∀ i, IsCompact (closure (V i : Set X))) (hVcl : ∀ i, closure (V i : Set X) ⊆ U i)
    (n : ℕ) : IsCompactOperator (M.refineL U hVU n) := by
  refine IsCompactOperator.piMap (f := fun σ ↦ M.subRes (cechOpen_le_cechOpen_comp U hVU σ))
    fun σ ↦ M.isCompactOperator_subRes hK _ ?_ ?_
  · refine (hVc (σ 0)).of_isClosed_subset isClosed_closure (closure_mono ?_)
    exact (iInf_le (fun a ↦ V (σ a)) 0 : cechOpen V σ ≤ V (σ 0))
  · intro x hx
    change x ∈ ((⨅ a, U (σ a) : Opens X) : Set X)
    rw [Opens.coe_iInf, mem_iInter]
    exact fun a ↦ hVcl (σ a) (closure_mono (iInf_le (fun a ↦ V (σ a)) a) hx)

end Frechet

end TopCat.Sheaf.SectionModel
