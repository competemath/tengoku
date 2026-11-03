import Tengoku.Seed.Algebra.Homology.HomologicalComplex
import Tengoku.Seed.Algebra.Homology.Additive
import Tengoku.Seed.Algebra.Homology.Linear
import Tengoku.Seed.Algebra.Category.ModuleCat.Basic
import Tengoku.Seed.CategoryTheory.ConcreteCategory.EpiMono
import Tengoku.DgLean.DG.Homotopy.ModuleCat

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The underlying cochain complex of a dg module

For a dg `R`-algebra `A` and a dg `A`-module `M`, the homogeneous components `Mⁿ` are
`R`-submodules and `d : Mⁿ → Mⁿ⁺¹` is `R`-linear, so `M` has an underlying cochain complex
of `R`-modules, `DG.DGModuleCat.toComplex R M : CochainComplex (ModuleCat R) ℤ`. This is the
object map of the forgetful functor

  `DG.DGModuleCat.forget R A : DGModuleCat A ⥤ CochainComplex (ModuleCat R) ℤ`,

which is additive, `R`-linear, faithful and reflects isomorphisms. The forgetful functor to
cochain complexes of abelian groups, `DG.DGModuleCat.forgetToAddCommGrp A`, is the case `R = ℤ`
composed with the forgetful functor `ModuleCat ℤ ⥤ AddCommGrpCat`.

## Implementation notes

The `R`-module structure on the carrier of an object `M : DGModuleCat A` is
`Module.compHom M (algebraMap R A)`, i.e. `r • m = algebraMap R A r • m`. It is a scoped instance
in the namespace `DG.DGModuleCat.Algebra`, as for `ModuleCat.Algebra` in Mathlib; it is needed
to state that `(toComplex R M).X n` is `ModuleCat.of R (DGModule.gradingSubmodule R A M n)`.
-/

open scoped DG

open CategoryTheory CategoryTheory.Limits

universe v u w

/-- A faithful additive functor induces a faithful functor on homological complexes.
@isnad1 id=faithful.0h5v.s6.7e2d1ff1b1b9 from=translated src=- shape=30c47730 vocab=5b10dad0
-/
instance CategoryTheory.Functor.mapHomologicalComplex_faithful {C D : Type*} [Category C]
    [Category D] [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive] [F.Faithful]
    {ι : Type*} (c : ComplexShape ι) : (F.mapHomologicalComplex c).Faithful where
  map_injective h := HomologicalComplex.hom_ext _ _ fun n =>
    F.map_injective (congrArg (fun φ => φ.f n) h)

namespace DG

namespace DGModuleCat

variable (R : Type w) {A : Type u} [CommRing R] [Ring A] [DGAddCommGroup A] [Algebra R A]

namespace Algebra

/-- The carrier of a dg `A`-module is an `R`-module through `algebraMap R A`.-/
scoped instance instModule (M : DGModuleCat.{v} A) : Module R M :=
  Module.compHom M (algebraMap R A)

/--
@isnad1 id=isscalar.0h3v.s8.2404ead4f044 from=translated src=- shape=efebf98b vocab=ae2e078c
-/
scoped instance instIsScalarTower (M : DGModuleCat.{v} A) : IsScalarTower R A M where
  smul_assoc r a m := by
    change (r • a) • m = algebraMap R A r • a • m
    rw [Algebra.smul_def, mul_smul]

end Algebra

open DG.DGModuleCat.Algebra

variable [DGRing A] [DGAlgebra R A]

section Object

variable (M : DGModuleCat.{v} A)

/-- The differential `Mⁿ → Mⁿ⁺¹` as an `R`-linear map.-/
def dRestrict (n : ℤ) :
    DGModule.gradingSubmodule R A M n →ₗ[R] DGModule.gradingSubmodule R A M (n + 1) :=
  (DGModule.dLinear R A M).restrict fun _ hm => d_mem hm

/--
@isnad1 id=eq.0h5v.s11.750d94b2e2b1 from=translated src=- shape=94d57f49 vocab=a0d41d59
-/
@[simp]
theorem coe_dRestrict_apply (n : ℤ) (m : DGModule.gradingSubmodule R A M n) :
    (dRestrict R M n m : M) = d (m : M) := rfl

/-- The underlying cochain complex of `R`-modules of a dg `A`-module.-/
def toComplex : CochainComplex (ModuleCat.{v} R) ℤ :=
  CochainComplex.of (fun n => ModuleCat.of R (DGModule.gradingSubmodule R A M n))
    (fun n => ModuleCat.ofHom (dRestrict R M n)) fun n => by
      ext m
      exact d_d (m : M)

/--
@isnad1 id=eq.0h4v.s8.7544ce3b963e from=translated src=- shape=34b442dc vocab=b2a21f36
-/
@[simp]
theorem toComplex_X (n : ℤ) :
    (toComplex R M).X n = ModuleCat.of R (DGModule.gradingSubmodule R A M n) := rfl

/--
@isnad1 id=eq.0h4v.s9.fab5d45f6f97 from=translated src=- shape=416f1ab3 vocab=2775807c
-/
@[simp]
theorem toComplex_d (n : ℤ) :
    (toComplex R M).d n (n + 1) = ModuleCat.ofHom (dRestrict R M n) :=
  CochainComplex.of_d (fun n => ModuleCat.of R (DGModule.gradingSubmodule R A M n))
    (fun n => ModuleCat.ofHom (dRestrict R M n)) n

end Object

section Morphism

variable {M N P : DGModuleCat.{v} A}

/-- A morphism of dg modules restricted to the homogeneous components of degree `n`, as an
`R`-linear map.-/
def homRestrict (f : M ⟶ N) (n : ℤ) :
    DGModule.gradingSubmodule R A M n →ₗ[R] DGModule.gradingSubmodule R A N n :=
  (f.hom.toLinearMap.restrictScalars R).restrict fun _ hm => f.hom.map_mem hm

/--
@isnad1 id=eq.0h7v.s11.ef7ce03d4bff from=translated src=- shape=0650682b vocab=eea733e0
-/
@[simp]
theorem coe_homRestrict_apply (f : M ⟶ N) (n : ℤ) (m : DGModule.gradingSubmodule R A M n) :
    (homRestrict R f n m : N) = f m := rfl

/-- The morphism of cochain complexes underlying a morphism of dg modules.-/
def toComplexMap (f : M ⟶ N) : toComplex R M ⟶ toComplex R N :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (homRestrict R f n)) fun n => by
    rw [toComplex_d, toComplex_d]
    ext m
    exact Subtype.ext (f.hom.map_d m.1).symm

/--
@isnad1 id=eq.0h6v.s9.60c459e93098 from=translated src=- shape=6feb0e13 vocab=9e4227b2
-/
@[simp]
theorem toComplexMap_f (f : M ⟶ N) (n : ℤ) :
    (toComplexMap R f).f n = ModuleCat.ofHom (homRestrict R f n) := rfl

variable (A) in
/-- The forgetful functor from dg `A`-modules to cochain complexes of `R`-modules.-/
@[simps]
def forget : DGModuleCat.{v} A ⥤ CochainComplex (ModuleCat.{v} R) ℤ where
  obj M := toComplex R M
  map f := toComplexMap R f
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

/--
@isnad1 id=additive.0h2v.s7.e2534c1a1dcb from=translated src=- shape=6e7442fe vocab=a5867363
-/
instance forget_additive : (forget R A).Additive where
  map_add := by intros; ext; rfl

/--
@isnad1 id=eq.1h6v.s9.7cc762372b64 from=translated src=- shape=9130370e vocab=c677983e
-/
theorem forget_map_injective {f g : M ⟶ N} (h : (forget R A).map f = (forget R A).map g) :
    f = g := by
  refine hom_ext_apply fun m => ?_
  induction m using DG.induction_on with
  | h_zero => rw [map_zero, map_zero]
  | @h_homogeneous n m =>
    have h1 : homRestrict R f n = homRestrict R g n :=
      congrArg (fun φ : toComplex R M ⟶ toComplex R N => ModuleCat.Hom.hom (φ.f n)) h
    exact congrArg Subtype.val (LinearMap.congr_fun h1 ⟨m, m.2⟩)
  | h_add m m' hm hm' => rw [map_add, map_add, hm, hm']

/-- The forgetful functor to cochain complexes is faithful.
@isnad1 id=faithful.0h2v.s7.ffe902cde90a from=translated src=- shape=6e7442fe vocab=a871636c
-/
instance forget_faithful : (forget R A).Faithful where
  map_injective h := forget_map_injective R h

/--
@isnad1 id=bijectiv.0h5v.s9.5d29c2f3f862 from=translated src=- shape=a7ee995f vocab=706ebd5a
-/
theorem bijective_of_forget_map_isIso (f : M ⟶ N) [IsIso ((forget R A).map f)] :
    Function.Bijective f := by
  have hn : ∀ n : ℤ, Function.Bijective (homRestrict R f n) := fun n => by
    have : IsIso (((forget R A).map f).f n) :=
      inferInstanceAs (IsIso ((HomologicalComplex.eval _ _ n).map ((forget R A).map f)))
    exact ConcreteCategory.bijective_of_isIso (((forget R A).map f).f n)
  constructor
  · intro m m' hmm'
    rw [← sub_eq_zero, ← map_sub] at hmm'
    rw [← sub_eq_zero]
    generalize m - m' = x at hmm'
    have h : ∀ n, (DirectSum.decompose (grading (M := M)) x n : M) = 0 := fun n => by
      have h1 : (DirectSum.decompose (grading (M := N)) (f x) n : N) =
          f (DirectSum.decompose (grading (M := M)) x n) :=
        coe_decompose_map_of_map_mem f.hom.toLinearMap.toAddMonoidHom
          (fun h => f.hom.map_mem h) x n
      rw [hmm', DirectSum.decompose_zero, DirectSum.zero_apply, ZeroMemClass.coe_zero] at h1
      have h2 : homRestrict R f n ⟨_, (DirectSum.decompose (grading (M := M)) x n).2⟩ = 0 :=
        Subtype.ext h1.symm
      rw [← map_zero (homRestrict R f n)] at h2
      exact congrArg Subtype.val ((hn n).injective h2)
    rw [← (DirectSum.decompose (grading (M := M))).symm_apply_apply x]
    have : DirectSum.decompose (grading (M := M)) x = 0 := DirectSum.ext fun n =>
      Subtype.ext ((h n).trans (ZeroMemClass.coe_zero _).symm)
    rw [this, DirectSum.decompose_symm_zero]
  · intro y
    induction y using DG.induction_on with
    | h_zero => exact ⟨0, map_zero _⟩
    | h_homogeneous y =>
      obtain ⟨x, hx⟩ := (hn _).surjective ⟨y, y.2⟩
      exact ⟨x, congrArg Subtype.val hx⟩
    | h_add y y' hy hy' =>
      obtain ⟨x, rfl⟩ := hy
      obtain ⟨x', rfl⟩ := hy'
      exact ⟨x + x', map_add _ _ _⟩

/-- The forgetful functor to cochain complexes reflects isomorphisms.
@isnad1 id=reflects.0h2v.s7.d01590eb9328 from=translated src=- shape=6e7442fe vocab=fe3191a0
-/
instance forget_reflectsIsomorphisms : (forget R A).ReflectsIsomorphisms where
  reflects f _ := isIso_of_bijective f (bijective_of_forget_map_isIso R f)

end Morphism

section AddCommGrpCat

variable (A)

/-- The forgetful functor from dg `A`-modules to cochain complexes of abelian groups.-/
noncomputable def forgetToAddCommGrp : DGModuleCat.{v} A ⥤ CochainComplex AddCommGrpCat.{v} ℤ :=
  forget ℤ A ⋙ (forget₂ (ModuleCat.{v} ℤ) AddCommGrpCat.{v}).mapHomologicalComplex _

/--
@isnad1 id=faithful.0h1v.s6.f2d6ff09c2bc from=translated src=- shape=cd0f0cd2 vocab=5601c14c
-/
instance forgetToAddCommGrp_faithful : (forgetToAddCommGrp A).Faithful := by
  unfold forgetToAddCommGrp
  infer_instance

end AddCommGrpCat

end DGModuleCat

end DG
