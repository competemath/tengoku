import Tengoku.TdaLib.TDA.Persistence.SupportInterval
import Tengoku.Seed.Algebra.Category.ModuleCat.EpiMono
import Tengoku.Seed.Algebra.Category.ModuleCat.Limits
import Tengoku.Seed.CategoryTheory.Linear.FunctorCategory
import Tengoku.Seed.CategoryTheory.Limits.FunctorCategory.EpiMono
import Tengoku.Seed.CategoryTheory.Preadditive.Injective.Basic
import Tengoku.Seed.LinearAlgebra.Basis.VectorSpace
import Tengoku.Seed.LinearAlgebra.FiniteDimensional.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Principal-downset injectives

The interval module supported on `Set.Iic p` represents the dual of evaluation
at `p`: a functional extends to every earlier grade by the structure map, and
vanishes outside the downset. Extending functionals along injective linear maps
then proves ordinary categorical injectivity, without finiteness assumptions.

For finite posets with a bottom element these are the rectangles `R_(bottom,p)`
in BOOS, arXiv:2208.00300v3, Lemma 2.4. The direct-sum classification in that
lemma requires additional arguments beyond these individual injectives.
-/

set_option autoImplicit false

universe u v

namespace TDA.Persistence.PrincipalDownsetInjective

open CategoryTheory
open scoped Classical

variable {k : Type u} [Field k] {P : Type v} [Preorder P]

/-- One scalar at every grade below `p`, with the support-interval maps.-/
noncomputable abbrev module (p : P) : PModule.{u,v,u} k P :=
  SupportInterval.module (Set.Iic p) Set.ordConnected_Iic

/-- Read the scalar coefficient of a map at its terminal support grade.-/
noncomputable def evaluation (p : P) (M : PModule.{u,v,u} k P)
    (f : M ⟶ module p) : M.obj p →ₗ[k] k :=
  (SupportInterval.fiber (k := k) (Set.Iic p) p).subtype.comp (f.app p).hom

private noncomputable def extensionLinear (p : P) (M : PModule.{u,v,u} k P)
    (l : M.obj p →ₗ[k] k) (q : P) :
    M.obj q →ₗ[k] SupportInterval.fiber (k := k) (Set.Iic p) q := by
  classical
  exact if h : q ≤ p then
    (l.comp (structureMapLinear M h)).codRestrict _ (by
      intro x
      simp [SupportInterval.fiber, h]) else 0

private theorem extensionLinear_val (p : P) (M : PModule.{u,v,u} k P)
    (l : M.obj p →ₗ[k] k) (q : P) (x : M.obj q) :
    (extensionLinear p M l q x : k) =
      if h : q ≤ p then l (structureMapLinear M h x) else 0 := by
  classical
  by_cases h : q ≤ p <;> simp [extensionLinear, h]

/-- Coextend a functional by transport to `p`, and by zero outside its downset.-/
noncomputable def extension (p : P) (M : PModule.{u,v,u} k P)
    (l : M.obj p →ₗ[k] k) : M ⟶ module p where
  app q := ModuleCat.ofHom (extensionLinear p M l q)
  naturality {q r} f := by
    classical
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (extensionLinear p M l r (structureMapLinear M (leOfHom f) x) : k) =
      (structureMapLinear (module p) (leOfHom f) (extensionLinear p M l q x) : k)
    rw [extensionLinear_val, SupportInterval.structureMap_val, extensionLinear_val]
    by_cases hr : r ≤ p
    · have hq : q ≤ p := (leOfHom f).trans hr
      simp only [hr, hq, Set.mem_Iic, dite_true, ite_true]
      rw [structureMapLinear_comp M (leOfHom f) hr]
      rfl
    · simp [hr]

/-- The coefficient of the coextension at any grade, including the zero boundary.
@isnad1 id=eq.0h7v.s11.eab94f9a18b2 from=translated src=- shape=1567b512 vocab=c8a1042d
-/
theorem extension_app_val (p : P) (M : PModule.{u,v,u} k P)
    (l : M.obj p →ₗ[k] k) (q : P) (x : M.obj q) :
    (((extension p M l).app q).hom x : k) =
      if h : q ≤ p then l (structureMapLinear M h x) else 0 :=
  extensionLinear_val p M l q x

/-- A coextension recovers its functional at the terminal support grade.
@isnad1 id=eq.0h5v.s8.935d3fe5671c from=translated src=- shape=38b48b4f vocab=d13b6e8d
-/
@[simp] theorem evaluation_extension (p : P) (M : PModule.{u,v,u} k P)
    (l : M.obj p →ₗ[k] k) : evaluation p M (extension p M l) = l := by
  ext x
  change (((extension p M l).app p).hom x : k) = l x
  rw [extension_app_val]
  simp

/-- Naturality determines every coefficient from the component at `p`.
@isnad1 id=eq.0h7v.s10.d7d148ec2f0d from=translated src=- shape=c305be10 vocab=4d5b0698
-/
theorem app_val (p : P) (M : PModule.{u,v,u} k P)
    (f : M ⟶ module p) (q : P) (x : M.obj q) :
    ((f.app q).hom x : k) =
      if h : q ≤ p then evaluation p M f (structureMapLinear M h x) else 0 := by
  classical
  by_cases h : q ≤ p
  · have hn := congrArg (fun g => (g.hom x : k)) (f.naturality (homOfLE h))
    change evaluation p M f (structureMapLinear M h x) =
      (structureMapLinear (module p) h ((f.app q).hom x) : k) at hn
    rw [SupportInterval.structureMap_val, ite_eq_left (show p ∈ Set.Iic p from le_rfl)] at hn
    simpa [h] using hn.symm
  · simpa [h] using SupportInterval.val_eq_zero (Set.Iic p) h ((f.app q).hom x)

/-- A morphism into a principal downset is determined by its endpoint functional.
@isnad1 id=eq.1h6v.s8.12d6ecef3647 from=translated src=- shape=65106c89 vocab=d0e96531
-/
@[ext] theorem hom_ext (p : P) (M : PModule.{u,v,u} k P)
    {f g : M ⟶ module p} (h : evaluation p M f = evaluation p M g) : f = g := by
  ext q x
  rw [app_val, app_val, h]

/-- Coextension of the endpoint functional recovers the whole morphism.
@isnad1 id=eq.0h5v.s7.4a22065db002 from=translated src=- shape=a38b5856 vocab=48336671
-/
@[simp] theorem extension_evaluation (p : P) (M : PModule.{u,v,u} k P)
    (f : M ⟶ module p) : extension p M (evaluation p M f) = f := by
  apply hom_ext p M
  exact evaluation_extension p M _

/-- The linear dual of evaluation represents maps into the principal downset.-/
noncomputable def homLinearEquiv (p : P) (M : PModule.{u,v,u} k P) :
    (M ⟶ module p) ≃ₗ[k] (M.obj p →ₗ[k] k) where
  toFun := evaluation p M
  invFun := extension p M
  left_inv := extension_evaluation p M
  right_inv := evaluation_extension p M
  map_add' f g := by ext x; rfl
  map_smul' c f := by ext x; rfl

/-- Evaluation commutes with precomposition by a natural transformation.
@isnad1 id=eq.0h7v.s9.4a9568772660 from=translated src=- shape=83ee45eb vocab=c58631b1
-/
theorem evaluation_precomp (p : P) {M N : PModule.{u,v,u} k P}
    (a : M ⟶ N) (f : N ⟶ module p) :
    evaluation p M (a ≫ f) = (evaluation p N f).comp (a.app p).hom := rfl

/-- Coextension commutes with precomposition by a natural transformation.
@isnad1 id=eq.0h7v.s9.4fa4bbd62de2 from=translated src=- shape=0c61bf9f vocab=1a76d75b
-/
theorem extension_precomp (p : P) {M N : PModule.{u,v,u} k P}
    (a : M ⟶ N) (l : N.obj p →ₗ[k] k) :
    a ≫ extension p N l = extension p M (l.comp (a.app p).hom) := by
  apply hom_ext p M
  simp [evaluation_precomp]

/-- The principal-downset module is injective against arbitrary ambient monos.
@isnad1 id=injectiv.0h3v.s5.479bef4eacdd from=translated src=- shape=6096ae36 vocab=52250427
-/
instance isInjective (p : P) : Injective (module (k := k) p) where
  factors {A B} g f _ := by
    have hinj : Function.Injective (f.app p).hom :=
      (ModuleCat.mono_iff_injective _).mp ((NatTrans.mono_iff_mono_app f).mp inferInstance p)
    obtain ⟨s, hs⟩ := (f.app p).hom.exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.mpr hinj)
    refine ⟨extension p B ((evaluation p A g).comp s), ?_⟩
    apply hom_ext p A
    rw [evaluation_precomp, evaluation_extension, LinearMap.comp_assoc, hs,
      LinearMap.comp_id]

/-- Every principal-downset fiber is finite-dimensional over the arbitrary field.
@isnad1 id=finitedi.0h4v.s7.85c93e21afae from=translated src=- shape=072f6eea vocab=e9934fdb
-/
instance finiteDimensional (p q : P) : FiniteDimensional k ((module (k := k) p).obj q) := by
  change FiniteDimensional k (SupportInterval.fiber (k := k) (Set.Iic p) q)
  infer_instance

end TDA.Persistence.PrincipalDownsetInjective
