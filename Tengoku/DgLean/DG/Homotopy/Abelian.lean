import Tengoku.Seed.Algebra.Homology.HomologicalComplexAbelian
import Tengoku.Seed.Algebra.Homology.ShortComplex.ModuleCat
import Tengoku.Seed.Algebra.Homology.ShortComplex.ShortExact
import Tengoku.Seed.CategoryTheory.Abelian.Basic
import Tengoku.Seed.CategoryTheory.Limits.Preserves.Shapes.AbelianImages
import Tengoku.Seed.CategoryTheory.Preadditive.LeftExact
import Tengoku.DgLean.DG.Homotopy.Forget
import Tengoku.DgLean.DG.Module.SubQuotient

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The abelian category of dg modules

For a dg ring `A`, the category `DG.DGModuleCat A` of dg `A`-modules is abelian, and for a dg
`R`-algebra `A` the forgetful functor `DG.DGModuleCat.forget R A` to cochain complexes of
`R`-modules is exact (and faithful, `DG.DGModuleCat.forget_faithful`).

* Kernels: the kernel dg submodule `DG.DGModuleHom.ker` (`DG.DGModuleCat.kernelIsLimit`).
* Cokernels: the quotient by the image, `N ⧸ f.range` (`DG.DGModuleCat.cokernelIsColimit`).
* Monomorphisms are the injective morphisms and epimorphisms the surjective ones
  (`DG.DGModuleCat.mono_iff_injective`, `DG.DGModuleCat.epi_iff_surjective`).
* The forgetful functor preserves kernels and cokernels, which are computed degreewise
  (`DG.DGModuleCat.forget_preservesKernel`, `DG.DGModuleCat.forget_preservesCokernel`), hence
  finite limits and finite colimits.
* `DG.DGModuleCat.abelian`: since the forgetful functor to `CochainComplex (ModuleCat ℤ) ℤ`
  preserves kernels and cokernels and reflects isomorphisms, the coimage-image comparison
  morphisms are isomorphisms (`CategoryTheory.Abelian.ofCoimageImageComparisonIsIso`).
* A short complex of dg modules is exact, resp. short exact, if and only if it is so as a
  sequence of abelian groups (`DG.DGModuleCat.exact_iff_function_exact`,
  `DG.DGModuleCat.shortExact_iff`), and the forgetful functor maps short exact sequences to
  short exact sequences of cochain complexes (`DG.DGModuleCat.shortExact_map_forget`).
-/

open scoped DG

open CategoryTheory CategoryTheory.Limits

universe v u w

noncomputable section

namespace DG

namespace DGModuleCat

variable {A : Type u} [Ring A] [DGAddCommGroup A]

/-! ### Kernels and cokernels -/

section KernelCokernel

variable {M N : DGModuleCat.{v} A} (f : M ⟶ N)

/-- The inclusion of the kernel dg submodule composed with `f` is zero.
@isnad1 id=eq.0h4v.s11.080a1c49428a from=translated src=- shape=0dbe8a00 vocab=59c1a413
-/
theorem ker_subtype_comp : (ofHom f.hom.ker.subtype : of A f.hom.ker ⟶ M) ≫ f = 0 :=
  hom_ext_apply fun (x : f.hom.ker) => x.2

/-- The kernel fork of a morphism of dg modules given by the kernel dg submodule.-/
def kernelFork : KernelFork f :=
  KernelFork.ofι _ (ker_subtype_comp f)

/--
@isnad1 id=eq.0h4v.s9.b9a86938b428 from=translated src=- shape=bcec7f50 vocab=758dca01
-/
@[simp]
theorem kernelFork_ι : (kernelFork f).ι = ofHom f.hom.ker.subtype := rfl

/-- The kernel dg submodule is a kernel in `DGModuleCat A`.-/
def kernelIsLimit : IsLimit (kernelFork f) :=
  KernelFork.IsLimit.ofι _ (ker_subtype_comp f)
    (fun {W} g hg => ofHom (DGSubmodule.codRestrict g.hom fun x =>
      show f (g x) = 0 from congrArg (fun φ : W ⟶ N => φ x) hg))
    (fun _ _ => rfl)
    (fun _ _ _ hm => hom_ext_apply fun x => Subtype.ext (congrArg (fun φ => φ x) hm))

/-- `f` composed with the quotient map by its image is zero.
@isnad1 id=eq.0h4v.s11.6044456e0993 from=translated src=- shape=1c53aec9 vocab=3507dce0
-/
theorem comp_range_mkQ :
    f ≫ (ofHom f.hom.range.mkQ : N ⟶ of A (N ⧸ f.hom.range.toSubmodule)) = 0 :=
  hom_ext_apply fun x => f.hom.range.mkQ_eq_zero_iff.mpr ⟨x, rfl⟩

/-- The cokernel cofork of a morphism of dg modules given by the quotient by the image.-/
def cokernelCofork : CokernelCofork f :=
  CokernelCofork.ofπ _ (comp_range_mkQ f)

/--
@isnad1 id=eq.0h4v.s9.cc8997e0924a from=translated src=- shape=27c65c18 vocab=6764735b
-/
@[simp]
theorem cokernelCofork_π : (cokernelCofork f).π = ofHom f.hom.range.mkQ := rfl

/-- The quotient by the image is a cokernel in `DGModuleCat A`.-/
def cokernelIsColimit : IsColimit (cokernelCofork f) :=
  CokernelCofork.IsColimit.ofπ _ (comp_range_mkQ f)
    (fun {W} g hg => ofHom (DGSubmodule.liftQ g.hom (by
      rintro _ ⟨x, rfl⟩
      exact congrArg (fun φ : M ⟶ W => φ x) hg)))
    (fun _ _ => rfl)
    (fun _ _ _ hm => hom_ext (DGSubmodule.quotient_ext (congrArg Hom.hom hm)))

/--
@isnad1 id=haskerne.0h1v.s5.9670a1f775eb from=translated src=- shape=9499e9bc vocab=f9db0da6
-/
instance hasKernels : HasKernels (DGModuleCat.{v} A) :=
  ⟨fun f => HasLimit.mk ⟨_, kernelIsLimit f⟩⟩

/--
@isnad1 id=hascoker.0h1v.s5.4d02a03d6dc0 from=translated src=- shape=9499e9bc vocab=3bb43080
-/
instance hasCokernels : HasCokernels (DGModuleCat.{v} A) :=
  ⟨fun f => HasColimit.mk ⟨_, cokernelIsColimit f⟩⟩

end KernelCokernel

/-! ### Monomorphisms and epimorphisms -/

section MonoEpi

variable {M N : DGModuleCat.{v} A} (f : M ⟶ N)

/-- A monomorphism of dg modules is injective.
@isnad1 id=injectiv.0h4v.s8.5980d166a3ff from=translated src=- shape=791898ff vocab=7601ffaa
-/
theorem injective_of_mono [Mono f] : Function.Injective f := by
  have h : ofHom f.hom.ker.subtype = 0 :=
    (cancel_mono f).1 ((kernelFork f).condition.trans zero_comp.symm)
  intro x y hxy
  have hxy' : x - y ∈ f.hom.ker := by
    change f (x - y) = 0
    rw [map_sub, hxy, sub_self]
  rw [← sub_eq_zero]
  exact congrArg (fun φ : of A f.hom.ker ⟶ M => φ ⟨x - y, hxy'⟩) h

/-- An epimorphism of dg modules is surjective.
@isnad1 id=surjecti.0h4v.s8.56d48c169a56 from=translated src=- shape=791898ff vocab=44dd1c02
-/
theorem surjective_of_epi [Epi f] : Function.Surjective f := by
  have h : ofHom f.hom.range.mkQ = 0 :=
    (cancel_epi f).1 ((cokernelCofork f).condition.trans comp_zero.symm)
  intro y
  exact f.hom.range.mkQ_eq_zero_iff.mp (congrArg (fun φ => φ y) h)

/-- A morphism of dg modules is a monomorphism if and only if it is injective.
@isnad1 id=iff.0h4v.s8.416ddbd03a0d from=translated src=- shape=c373b4f3 vocab=7601ffaa
-/
theorem mono_iff_injective : Mono f ↔ Function.Injective f :=
  ⟨fun _ => injective_of_mono f, ConcreteCategory.mono_of_injective f⟩

/-- A morphism of dg modules is an epimorphism if and only if it is surjective.
@isnad1 id=iff.0h4v.s8.0442c251f3df from=translated src=- shape=c373b4f3 vocab=44dd1c02
-/
theorem epi_iff_surjective : Epi f ↔ Function.Surjective f :=
  ⟨fun _ => surjective_of_epi f, ConcreteCategory.epi_of_surjective f⟩

/-- A morphism of dg modules commutes with taking homogeneous components.
@isnad1 id=eq.0h6v.s12.68b1190aab39 from=translated src=- shape=6ab76743 vocab=6ea48f81
-/
theorem decompose_apply (x : M) (n : ℤ) :
    (DirectSum.decompose (grading (M := N)) (f x) n : N) =
      f (DirectSum.decompose (grading (M := M)) x n) :=
  coe_decompose_map_of_map_mem f.hom.toLinearMap.toAddMonoidHom (fun h => f.hom.map_mem h) x n

end MonoEpi

/-! ### The forgetful functor to cochain complexes, degreewise -/

section Forget

open DGModuleCat.Algebra

variable (R : Type w) [CommRing R] [Algebra R A] [DGRing A] [DGAlgebra R A]

/-- The image of an injective morphism under the forgetful functor is a monomorphism.
@isnad1 id=mono.1h5v.s9.232dc86d981a from=translated src=- shape=cf455dda vocab=c364c218
-/
theorem mono_forget_map_of_injective {M N : DGModuleCat.{v} A} (f : M ⟶ N)
    (hf : Function.Injective f) : Mono ((forget R A).map f) :=
  HomologicalComplex.mono_of_mono_f _ fun _ => (ModuleCat.mono_iff_injective _).2
    fun _ _ h => Subtype.ext (hf (congrArg Subtype.val h))

/-- The image of a surjective morphism under the forgetful functor is an epimorphism.
@isnad1 id=epi.1h5v.s9.2ccd62af07ca from=translated src=- shape=cf455dda vocab=613352f2
-/
theorem epi_forget_map_of_surjective {M N : DGModuleCat.{v} A} (f : M ⟶ N)
    (hf : Function.Surjective f) : Epi ((forget R A).map f) :=
  HomologicalComplex.epi_of_epi_f _ fun n => (ModuleCat.epi_iff_surjective _).2
    fun (y : DGModule.gradingSubmodule R A N n) => by
    obtain ⟨x, hx⟩ := hf (y : N)
    refine ⟨⟨_, (DirectSum.decompose (grading (M := M)) x n).2⟩, Subtype.ext ?_⟩
    change f (DirectSum.decompose (grading (M := M)) x n : M) = y
    rw [← decompose_apply, hx, DirectSum.decompose_of_mem_same (grading (M := N)) y.2]

/-- A short complex of dg modules which is exact as a sequence of abelian groups is mapped to
an exact short complex of cochain complexes.
@isnad1 id=exact.1h3v.s10.b93e4412c01d from=translated src=- shape=bf26d0c5 vocab=b884289c
-/
theorem exact_map_forget_of_exact (S : ShortComplex (DGModuleCat.{v} A))
    (hS : Function.Exact S.f S.g) : (S.map (forget R A)).Exact := by
  rw [HomologicalComplex.exact_iff_degreewise_exact]
  intro n
  rw [ShortComplex.moduleCat_exact_iff]
  intro (y : DGModule.gradingSubmodule R A S.X₂ n) hy
  obtain ⟨x, hx⟩ := (hS (y : S.X₂)).mp (congrArg Subtype.val hy)
  refine ⟨⟨_, (DirectSum.decompose (grading (M := S.X₁)) x n).2⟩, Subtype.ext ?_⟩
  change S.f (DirectSum.decompose (grading (M := S.X₁)) x n : S.X₁) = y
  rw [← decompose_apply, hx, DirectSum.decompose_of_mem_same (grading (M := S.X₂)) y.2]

/-- A short complex of dg modules which is mapped to an exact short complex of cochain
complexes is exact as a sequence of abelian groups.
@isnad1 id=exact.1h3v.s10.1c3aac1f2674 from=translated src=- shape=53ddba02 vocab=b884289c
-/
theorem exact_of_exact_map_forget (S : ShortComplex (DGModuleCat.{v} A))
    (hS : (S.map (forget R A)).Exact) : Function.Exact S.f S.g := by
  classical
  rw [HomologicalComplex.exact_iff_degreewise_exact] at hS
  intro y
  constructor
  · intro hy
    suffices h : y ∈ LinearMap.range S.f.hom.toLinearMap by
      obtain ⟨x, hx⟩ := h
      exact ⟨x, hx⟩
    rw [← DirectSum.sum_support_decompose (grading (M := S.X₂)) y]
    refine sum_mem fun n _ => ?_
    have hyn : S.g (DirectSum.decompose (grading (M := S.X₂)) y n : S.X₂) = 0 := by
      rw [← decompose_apply, hy, DirectSum.decompose_zero, DirectSum.zero_apply,
        ZeroMemClass.coe_zero]
    obtain ⟨⟨x, _⟩, hx⟩ := (ShortComplex.moduleCat_exact_iff _).mp (hS n)
      ⟨_, (DirectSum.decompose (grading (M := S.X₂)) y n).2⟩ (Subtype.ext hyn)
    exact ⟨x, congrArg Subtype.val hx⟩
  · rintro ⟨x, rfl⟩
    exact congrArg (fun φ => φ x) S.zero

/-- The forgetful functor preserves kernels.
@isnad1 id=preserve.0h5v.s7.04cbfe019bb1 from=translated src=- shape=41788196 vocab=08837a2d
-/
instance forget_preservesKernel {M N : DGModuleCat.{v} A} (f : M ⟶ N) :
    PreservesLimit (parallelPair f 0) (forget R A) := by
  have h : ((ShortComplex.mk _ _ (kernelFork f).condition).map (forget R A)).Exact :=
    exact_map_forget_of_exact R _ fun y =>
      ⟨fun hy => ⟨⟨y, hy⟩, rfl⟩, fun ⟨x, hx⟩ => hx ▸ x.2⟩
  have : Mono ((ShortComplex.mk _ _ (kernelFork f).condition).map (forget R A)).f :=
    mono_forget_map_of_injective R _ Subtype.val_injective
  exact preservesLimit_of_preserves_limit_cone (kernelIsLimit f)
    ((KernelFork.isLimitMapConeEquiv _ _).symm h.fIsKernel)

/-- The forgetful functor preserves cokernels.
@isnad1 id=preserve.0h5v.s7.ea4dcc19908a from=translated src=- shape=41788196 vocab=e9fc4042
-/
instance forget_preservesCokernel {M N : DGModuleCat.{v} A} (f : M ⟶ N) :
    PreservesColimit (parallelPair f 0) (forget R A) := by
  have h : ((ShortComplex.mk _ _ (cokernelCofork f).condition).map (forget R A)).Exact :=
    exact_map_forget_of_exact R _ fun _ => f.hom.range.mkQ_eq_zero_iff
  have : Epi ((ShortComplex.mk _ _ (cokernelCofork f).condition).map (forget R A)).g :=
    epi_forget_map_of_surjective R _ f.hom.range.mkQ_surjective
  exact preservesColimit_of_preserves_colimit_cocone (cokernelIsColimit f)
    ((CokernelCofork.isColimitMapCoconeEquiv _ _).symm h.gIsCokernel)

end Forget

/-! ### The abelian structure -/

section Abelian

variable [DGRing A]

/-- The coimage-image comparison morphisms in `DGModuleCat A` are isomorphisms: they are
mapped to those of cochain complexes of abelian groups by a functor preserving kernels and
cokernels and reflecting isomorphisms.
@isnad1 id=isiso.0h4v.s7.cc78c47d319f from=translated src=- shape=ccceadbf vocab=2bbb832a
-/
instance isIso_coimageImageComparison {M N : DGModuleCat.{v} A} (f : M ⟶ N) :
    IsIso (Abelian.coimageImageComparison f) := by
  have : IsIso ((forget ℤ A).map (Abelian.coimageImageComparison f)) :=
    ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
      (Abelian.PreservesCoimageImageComparison.iso (forget ℤ A) f)).2
      (inferInstanceAs (IsIso (Abelian.coimageImageComparison _)))
  exact isIso_of_reflects_iso _ (forget ℤ A)

/-- The category of dg modules is abelian.-/
instance abelian : Abelian (DGModuleCat.{v} A) :=
  Abelian.ofCoimageImageComparisonIsIso

end Abelian

/-! ### Exactness of the forgetful functor -/

section Exact

open DGModuleCat.Algebra

variable (R : Type w) [CommRing R] [Algebra R A] [DGRing A] [DGAlgebra R A]

/-- The forgetful functor to cochain complexes is left exact.
@isnad1 id=preserve.0h2v.s7.a0bf120f8730 from=translated src=- shape=ee33eeb0 vocab=3d0fb634
-/
instance forget_preservesFiniteLimits : PreservesFiniteLimits (forget.{v} R A) :=
  Functor.preservesFiniteLimits_of_preservesKernels _

/-- The forgetful functor to cochain complexes is right exact.
@isnad1 id=preserve.0h2v.s7.920604a1efce from=translated src=- shape=ee33eeb0 vocab=46916df7
-/
instance forget_preservesFiniteColimits : PreservesFiniteColimits (forget.{v} R A) :=
  Functor.preservesFiniteColimits_of_preservesCokernels _

variable {R} in
/-- A short complex of dg modules is exact if and only if it is exact as a sequence of
abelian groups.
@isnad1 id=iff.0h2v.s10.357314ce3f13 from=translated src=- shape=3dbf6c3e vocab=01c223a7
-/
theorem exact_iff_function_exact (S : ShortComplex (DGModuleCat.{v} A)) :
    S.Exact ↔ Function.Exact S.f S.g := by
  rw [← S.exact_map_iff_of_faithful (forget ℤ A)]
  exact ⟨exact_of_exact_map_forget ℤ S, exact_map_forget_of_exact ℤ S⟩

/-- A short complex of dg modules is short exact if and only if `0 → X₁ → X₂ → X₃ → 0` is an
exact sequence of abelian groups.
@isnad1 id=iff.0h2v.s11.f513e26dd578 from=translated src=- shape=22cdc8fc vocab=40931c6f
-/
theorem shortExact_iff (S : ShortComplex (DGModuleCat.{v} A)) :
    S.ShortExact ↔ Function.Injective S.f ∧ Function.Exact S.f S.g ∧ Function.Surjective S.g :=
  ⟨fun h => by
      have := h.mono_f
      have := h.epi_g
      exact ⟨injective_of_mono S.f, (exact_iff_function_exact S).1 h.exact, surjective_of_epi S.g⟩,
    fun ⟨h₁, h₂, h₃⟩ => by
      have := (mono_iff_injective S.f).2 h₁
      have := (epi_iff_surjective S.g).2 h₃
      exact ⟨(exact_iff_function_exact S).2 h₂⟩⟩

/-- The forgetful functor maps short exact sequences of dg modules to short exact sequences of
cochain complexes.
@isnad1 id=shortexa.1h3v.s8.6a06b3fdcec6 from=translated src=- shape=d5668175 vocab=cbbdb4fc
-/
theorem shortExact_map_forget {S : ShortComplex (DGModuleCat.{v} A)} (hS : S.ShortExact) :
    (S.map (forget R A)).ShortExact :=
  hS.map_of_exact _

end Exact

end DGModuleCat

end DG
