import Tengoku.Seed.LinearAlgebra.Matrix.Trace
import Tengoku.Seed.LinearAlgebra.Matrix.ToLin
import Tengoku.Seed.LinearAlgebra.Trace
import Tengoku.Seed.LinearAlgebra.FiniteDimensional.Lemmas
import Tengoku.Seed.LinearAlgebra.Basis.VectorSpace
import Tengoku.Seed.RingTheory.SimpleModule.Basic
import Tengoku.Seed.RepresentationTheory.Irreducible
import Tengoku.Seed.Algebra.Module.Projective
import Tengoku.Seed.LinearAlgebra.FreeModule.Finite.Matrix
import Tengoku.Seed.Algebra.Lie.OfAssociative
import Tengoku.Seed.Algebra.Algebra.Rat

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Representation_span_range_eq_top_of_isIrreducible.lean`: wrote out 7 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 4 `p2m_export`, 2 `p2m_open`, 1 `p2m_open_scoped`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Representation_span_range_eq_top_of_isIrreducible

set_option autoImplicit false

open Module LinearMap

section Burnside

variable {k A V : Type*} [CommRing k] [Ring A] [Algebra k A] [AddCommGroup V] [Module k V]
  [Module A V] [IsScalarTower k A V]

namespace IsSimpleModule export _root_.IsSimpleModule (nontrivial algebraMap_end_bijective_of_isAlgClosed) end IsSimpleModule
open scoped _root_.IsSimpleModule in

private theorem IsSimpleModule.surjective_toModuleEnd_of_surjective_algebraMap_end
    [Module.Free k V] [Module.Finite k V] [IsSimpleModule A V]
    (hcomm : Function.Surjective (algebraMap k (Module.End A V))) :
    Function.Surjective (Module.toModuleEnd k V : A →+* Module.End k V) := by
  classical
  intro f₀

  have hsmul : ∀ (φ : Module.End A V) (v : V), f₀ (φ • v) = φ • (f₀ v) := by
    intro φ v
    obtain ⟨c, rfl⟩ := hcomm φ
    rw [Module.End.smul_def, Module.End.smul_def, Module.algebraMap_end_apply,
      Module.algebraMap_end_apply, map_smul]
  let F : Module.End (Module.End A V) V :=
    { toFun := f₀
      map_add' := f₀.map_add
      map_smul' := hsmul }

  let b := Module.Free.chooseBasis k V
  obtain ⟨a, ha⟩ := jacobson_density (R := A) (M := V) F (Finset.univ.image b)
  refine ⟨a, b.ext fun i ↦ ?_⟩
  have := ha (b i) (Finset.mem_image_of_mem b (Finset.mem_univ i))
  have h__af := this.symm
  simp at h__af ⊢
  exact h__af

end Burnside

namespace Representation
export _root_.Representation (free asModule asModuleEquiv irreducible_iff_isSimpleModule_asModule asAlgebraHom IsIrreducible asAlgebraHom_single asAlgebraHom_single_one asModuleEquiv_map_smul)
open _root_.Representation

section Dictionary

variable {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]

private theorem range_asAlgebraHom_toLinearMap (ρ : Representation k G V) :
    LinearMap.range ρ.asAlgebraHom.toLinearMap = Submodule.span k (Set.range ⇑ρ) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨r, rfl⟩
    show ρ.asAlgebraHom r ∈ _
    induction r using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | single g a =>
      rw [asAlgebraHom_single]
      exact Submodule.smul_mem _ a (Submodule.subset_span ⟨g, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    exact ⟨MonoidAlgebra.single g 1, ρ.asAlgebraHom_single_one g⟩

private theorem span_range_eq_top_iff_surjective_asAlgebraHom (ρ : Representation k G V) :
    Submodule.span k (Set.range ⇑ρ) = ⊤ ↔ Function.Surjective ρ.asAlgebraHom := by
  rw [← range_asAlgebraHom_toLinearMap]
  exact LinearMap.range_eq_top

private theorem trace_asAlgebraHom_eq_of_forall_trace_eq {V₂ : Type*} [AddCommGroup V₂] [Module k V₂]
    (ρ₁ : Representation k G V) (ρ₂ : Representation k G V₂)
    (htr : ∀ g, trace k V (ρ₁ g) = trace k V₂ (ρ₂ g)) (r : MonoidAlgebra k G) :
    trace k V (ρ₁.asAlgebraHom r) = trace k V₂ (ρ₂.asAlgebraHom r) := by
  induction r using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single g a => rw [asAlgebraHom_single, asAlgebraHom_single, map_smul, map_smul, htr g]

end Dictionary

end Representation

namespace Representation
export _root_.Representation (free asModule asModuleEquiv irreducible_iff_isSimpleModule_asModule asAlgebraHom IsIrreducible asAlgebraHom_single asAlgebraHom_single_one asModuleEquiv_map_smul)
open _root_.Representation

section Burnside

variable {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

set_option backward.isDefEq.respectTransparency false in

private theorem _root_.Representation.span_range_eq_top_of_isIrreducible [IsAlgClosed k] (ρ : Representation k G V)
    [ρ.IsIrreducible] : Submodule.span k (Set.range ⇑ρ) = ⊤ := by
  rw [span_range_eq_top_iff_surjective_asAlgebraHom]
  haveI : IsSimpleModule (MonoidAlgebra k G) ρ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance

  have hcomm : Function.Surjective (algebraMap k (Module.End (MonoidAlgebra k G) ρ.asModule)) :=
    (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed k).surjective

  have hact := IsSimpleModule.surjective_toModuleEnd_of_surjective_algebraMap_end
    (k := k) (A := MonoidAlgebra k G) (V := ρ.asModule) hcomm

  intro f
  obtain ⟨r, hr⟩ := hact (ρ.asModuleEquiv.symm.toLinearMap ∘ₗ f ∘ₗ ρ.asModuleEquiv.toLinearMap)
  refine ⟨r, LinearMap.ext fun v ↦ ?_⟩

  have happ : (r • (ρ.asModuleEquiv.symm v) : ρ.asModule)
      = (ρ.asModuleEquiv.symm.toLinearMap ∘ₗ f ∘ₗ ρ.asModuleEquiv.toLinearMap)
          (ρ.asModuleEquiv.symm v) :=
    LinearMap.congr_fun hr (ρ.asModuleEquiv.symm v)

  have hdict : ρ.asAlgebraHom r v = ρ.asModuleEquiv (r • ρ.asModuleEquiv.symm v) := by
    rw [asModuleEquiv_map_smul, LinearEquiv.apply_symm_apply]
  rw [hdict, happ]
  simp

export _root_.Representation (span_range_eq_top_of_isIrreducible)

end Burnside

end Representation

/--
@isnad1 id=eq.0h4v.s9.6f0cc205c04c from=translated src=- shape=59c1523d vocab=78281620
-/
theorem solution
    {k G V : Type*} [Field k] [IsAlgClosed k] [Monoid G] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (ρ : Representation k G V) [ρ.IsIrreducible] :
    Submodule.span k (Set.range ⇑ρ) = ⊤ :=
  ρ.span_range_eq_top_of_isIrreducible
