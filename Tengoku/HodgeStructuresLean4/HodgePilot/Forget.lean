import Tengoku.HodgeStructuresLean4.HodgePilot.CategoryInstance
import Tengoku.Seed.Algebra.Category.ModuleCat.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # The forgetful functor to `ℚ`-modules

Every pure rational Hodge structure of weight `n` is, in particular, a
finite-dimensional `ℚ`-vector space, and every morphism of Hodge structures is
in particular a `ℚ`-linear map. This packages that observation as a functor

  `toModuleCat : HodgeStructCat n ⥤ ModuleCat ℚ`

sending an object to its underlying module `ModuleCat.of ℚ X.carrier` and a
morphism to its underlying linear map (via `ModuleCat.ofHom`), and records that
this functor is faithful: a morphism of Hodge structures is determined by its
underlying linear map (`HodgeStructCat.hom_ext`). -/

open scoped TensorProduct

open CategoryTheory

noncomputable section

universe u

namespace HodgePilot

namespace HodgeStructCat

variable {n : ℤ}

/-- The forgetful functor from the category of pure rational Hodge structures of
weight `n` to the category of `ℚ`-vector spaces. On objects it forgets the Hodge
structure, retaining only the underlying module `ModuleCat.of ℚ X.carrier`; on
morphisms it forgets the compatibility with the `(p,q)`-decomposition, retaining
only the underlying `ℚ`-linear map.-/
def toModuleCat : HodgeStructCat.{u} n ⥤ ModuleCat.{u} ℚ where
  obj X := ModuleCat.of ℚ X.carrier
  map f := ModuleCat.ofHom f.toLinearMap
  map_id X := by
    -- `(𝟙 X).toLinearMap = LinearMap.id` and `ofHom LinearMap.id = 𝟙 _`.
    simp only [id_toLinearMap, ModuleCat.ofHom_id]
  map_comp f g := by
    -- `(f ≫ g).toLinearMap = g.toLinearMap.comp f.toLinearMap` and
    -- `ofHom` turns composition of linear maps into `≫`.
    simp only [comp_toLinearMap, ModuleCat.ofHom_comp]

@[simp] theorem toModuleCat_obj (X : HodgeStructCat.{u} n) :
    toModuleCat.obj X = ModuleCat.of ℚ X.carrier := rfl

@[simp] theorem toModuleCat_map {X Y : HodgeStructCat.{u} n} (f : X ⟶ Y) :
    toModuleCat.map f = ModuleCat.ofHom f.toLinearMap := rfl

/-- The forgetful functor `toModuleCat` is faithful: a morphism of Hodge
structures is determined by its underlying `ℚ`-linear map, so distinct
morphisms have distinct images.-/
instance : (toModuleCat (n := n)).Faithful where
  map_injective {X Y f g} h := by
    -- `h : ofHom f.toLinearMap = ofHom g.toLinearMap`; extracting the
    -- underlying linear maps is definitional, then the extensionality lemma
    -- for `HodgeStructCat` finishes.
    exact HodgeStructCat.hom_ext (congrArg ModuleCat.Hom.hom h)

end HodgeStructCat

end HodgePilot
