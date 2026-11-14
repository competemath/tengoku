import Tengoku.TdaLib.TDA.Persistence.FiniteTranslation
import Tengoku.TdaLib.TDA.Persistence.FiniteDecomposition
import Tengoku.Seed.Algebra.Category.ModuleCat.Abelian
import Tengoku.Seed.CategoryTheory.Limits.FunctorCategory.EpiMono
import Tengoku.Seed.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite-chain kernels and translation-triviality

Evaluation identifies the categorical kernel with the component linear kernel.
Its inclusion and naturality detect exactly when a kernel structure map vanishes.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence

open CategoryTheory CategoryTheory.Limits

variable {s : ℕ} {k : Type u} [Field k]
variable {M N : PModule.{u,0,u} k (Fin s)}

/-- The kernel in the category of finite-chain persistence modules.-/
noncomputable abbrev finiteKernel (f : M ⟶ N) : PModule.{u,0,u} k (Fin s) := kernel f

/-- Evaluation of the kernel identifies its fiber with the component kernel.-/
noncomputable def finiteKernelFiberIso (f : M ⟶ N) (i : Fin s) :
    (finiteKernel f).obj i ≅ ModuleCat.of k (LinearMap.ker (f.app i).hom) :=
  PreservesKernel.iso ((evaluation (Fin s) (ModuleCat k)).obj i) f ≪≫
    ModuleCat.kernelIsoKer (f.app i)

/-- The fiber identification takes the kernel inclusion to the subtype map.
@isnad1 id=eq.0h6v.s13.702e969ce452 from=translated src=- shape=69824ba6 vocab=0aad73fa
-/
theorem finiteKernel_ι_fiberIso (f : M ⟶ N) (i : Fin s) :
    (finiteKernelFiberIso f i).inv ≫ (kernel.ι f).app i =
      ModuleCat.ofHom (LinearMap.ker (f.app i).hom).subtype := by
  simp only [finiteKernelFiberIso, Iso.trans_inv]
  have hp := PreservesKernel.iso_inv_ι ((evaluation (Fin s) (ModuleCat k)).obj i) f
  change (PreservesKernel.iso ((evaluation (Fin s) (ModuleCat k)).obj i) f).inv ≫
    (kernel.ι f).app i = kernel.ι (f.app i) at hp
  rw [Category.assoc, hp, ModuleCat.kernelIsoKer_inv_kernel_ι]

/-- The kernel inclusion has precisely the component linear kernel as its range.
@isnad1 id=eq.0h6v.s10.bbae946d2ea9 from=translated src=- shape=eab1a815 vocab=1ed749da
-/
theorem finiteKernel_ι_range (f : M ⟶ N) (i : Fin s) :
    LinearMap.range ((kernel.ι f).app i).hom = LinearMap.ker (f.app i).hom := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    have h := congrArg (fun g : finiteKernel f ⟶ N => (g.app i).hom z) (kernel.condition f)
    exact h
  · intro hx
    refine ⟨(finiteKernelFiberIso f i).inv.hom ⟨x, hx⟩, ?_⟩
    exact congrArg (fun g : ModuleCat.of k (LinearMap.ker (f.app i).hom) ⟶ M.obj i =>
      g.hom ⟨x, hx⟩) (finiteKernel_ι_fiberIso f i)

/-- Kernel maps vanish exactly when the source transition kills the component kernel.
@isnad1 id=iff.1h7v.s10.90f48fd1c0f0 from=translated src=- shape=21dd4d12 vocab=540449df
-/
theorem finiteKernel_map_eq_zero_iff (f : M ⟶ N) {a b : Fin s} (h : a ≤ b) :
    structureMap (finiteKernel f) h = 0 ↔
      LinearMap.ker (f.app a).hom ≤ LinearMap.ker (structureMapLinear M h) := by
  have hn := (kernel.ι f).naturality (homOfLE h)
  change structureMap (finiteKernel f) h ≫ (kernel.ι f).app b =
    (kernel.ι f).app a ≫ structureMap M h at hn
  constructor
  · intro hz x hx
    rw [← finiteKernel_ι_range f a] at hx
    obtain ⟨z, rfl⟩ := hx
    have he := congrArg (fun g : (finiteKernel f).obj a ⟶ M.obj b => g.hom z) hn
    rw [hz, zero_comp] at he
    exact he.symm
  · intro hk
    apply (cancel_mono ((kernel.ι f).app b)).mp
    rw [zero_comp, hn]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact hk (by rw [← finiteKernel_ι_range f a]; exact ⟨z, rfl⟩)

/-- Shortness of the kernel is equivalent to the component kernel-killing condition.
@isnad1 id=iff.1h6v.s10.b168621e220e from=translated src=- shape=b32df0cb vocab=a873ab11
-/
theorem kernel_translationTrivial_iff (theta : Fin s →o Fin s)
    (hTheta : ∀ i, i ≤ theta i) (f : M ⟶ N) :
    TranslationTrivial theta hTheta (finiteKernel f) ↔
      ∀ i, LinearMap.ker (f.app i).hom ≤ LinearMap.ker (structureMapLinear M (hTheta i)) :=
  forall_congr' (fun i => finiteKernel_map_eq_zero_iff f (hTheta i))

end TDA.Persistence
