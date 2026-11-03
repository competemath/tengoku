import Tengoku.HodgeStructuresLean4.HodgePilot.Morphisms

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # The category of pure rational Hodge structures of weight `n`

We bundle a finite-dimensional ℚ-vector space together with a
`QHodgeStructure n` on it into a single object type `HodgeStructCat n`, in the
same spirit as `ModuleCat`, and equip it with a `CategoryTheory.Category`
instance whose morphisms are the `HodgeHom`s of `Morphisms.lean`. The category
laws are exactly the `comp_id`/`id_comp`/`comp_assoc` proofs already established
there (all definitional, so `aesop_cat` would also discharge them). -/

open scoped TensorProduct

open CategoryTheory

noncomputable section

universe u

namespace HodgePilot

/-- A bundled object of the category of pure rational Hodge structures of weight
`n`: a finite-dimensional ℚ-vector space `carrier` together with a
`QHodgeStructure n` on it. The module structure is carried as instance fields,
mirroring `ModuleCat`.-/
structure HodgeStructCat (n : ℤ) where
  /-- The underlying ℚ-vector space of the object.-/
  carrier : Type u
  [isAddCommGroup : AddCommGroup carrier]
  [isModule : Module ℚ carrier]
  [isFinite : Module.Finite ℚ carrier]
  /-- The pure rational Hodge structure of weight `n` on the carrier.-/
  str : QHodgeStructure n carrier

attribute [instance] HodgeStructCat.isAddCommGroup HodgeStructCat.isModule
  HodgeStructCat.isFinite

namespace HodgeStructCat

variable {n : ℤ}

instance : CoeSort (HodgeStructCat.{u} n) (Type u) :=
  ⟨HodgeStructCat.carrier⟩

/-- The object associated to a finite-dimensional ℚ-vector space equipped with a
pure rational Hodge structure of weight `n`.-/
def of (V : Type u) [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    (hV : QHodgeStructure n V) : HodgeStructCat.{u} n where
  carrier := V
  str := hV

/-- Morphisms in `HodgeStructCat n` are morphisms of Hodge structures.

Note the diagrammatic order: `CategoryStruct.comp f g` (written `f ≫ g`) sends
`f : X ⟶ Y` and `g : Y ⟶ Z` to `X ⟶ Z`, so it is `HodgeHom.comp g f`.-/
instance category : Category (HodgeStructCat.{u} n) where
  Hom X Y := HodgeHom X.str Y.str
  id X := HodgeHom.id X.str
  comp f g := HodgeHom.comp g f
  id_comp f := HodgeHom.comp_id f
  comp_id f := HodgeHom.id_comp f
  assoc f g h := (HodgeHom.comp_assoc h g f).symm

/-- Two morphisms of Hodge structures are equal when their underlying linear
maps agree (the `maps_pieces` field is a `Prop`, so it is irrelevant).
@isnad1 id=eq.1h7v.s7.5eb6d37cae5f from=translated src=- shape=fede1da9 vocab=c95dfc83
-/
theorem hodgeHom_ext {V W : Type u} [AddCommGroup V] [Module ℚ V]
    [Module.Finite ℚ V] [AddCommGroup W] [Module ℚ W] [Module.Finite ℚ W]
    {hV : QHodgeStructure n V} {hW : QHodgeStructure n W}
    {f g : HodgeHom hV hW} (h : f.toLinearMap = g.toLinearMap) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- Two morphisms in `HodgeStructCat n` are equal when their underlying linear
maps agree.
@isnad1 id=eq.1h5v.s7.10a3f6963ee2 from=translated src=- shape=dedb6fe9 vocab=6383ef1d
-/
@[ext]
theorem hom_ext {X Y : HodgeStructCat.{u} n} {f g : X ⟶ Y}
    (h : f.toLinearMap = g.toLinearMap) : f = g :=
  hodgeHom_ext (hV := X.str) (hW := Y.str) h

/--
@isnad1 id=eq.0h2v.s6.4b342cc42a99 from=translated src=- shape=24bd311c vocab=2c4f6ff6
-/
@[simp] theorem id_toLinearMap (X : HodgeStructCat n) :
    (𝟙 X : X ⟶ X).toLinearMap = LinearMap.id := rfl

/--
@isnad1 id=eq.0h6v.s7.9672ad0aa732 from=translated src=- shape=8d9e82f3 vocab=ba7037a3
-/
@[simp] theorem comp_toLinearMap {X Y Z : HodgeStructCat n}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).toLinearMap = g.toLinearMap.comp f.toLinearMap := rfl

end HodgeStructCat

end HodgePilot
