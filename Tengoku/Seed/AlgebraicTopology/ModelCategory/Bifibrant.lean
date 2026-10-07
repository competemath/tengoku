/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.AlgebraicTopology.ModelCategory.IsCofibrant

/-!
# Bifibrant objects

In this file, we introduce the full subcategories `CofibrantObject C`,
`FibrantObject C` and `BifibrantObject C` of a model category `C` which
respectively consist of cofibrant objects, fibrant objects,
and bifibrant objects, where "bifibrant" means both cofibrant and fibrant.

-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C]

section Cofibrant

variable [CategoryWithCofibrations C] [HasInitial C]

variable (C) in
/-- The property that is satisfied by cofibrant objects.
(This is only introduced in order to consider the full subcategory
`CofibrantObject`. Otherwise, the typeclass `IsCofibrant`
is preferred.) -/
def cofibrantObjects : ObjectProperty C := IsCofibrant

variable (C) in
/-- The full subcategory of cofibrant objects. -/
abbrev CofibrantObject : Type u := (cofibrantObjects C).FullSubcategory

namespace CofibrantObject

/-- Constructor for `CofibrantObject C`. -/
abbrev mk (X : C) [IsCofibrant X] : CofibrantObject C :=
  ⟨X, by assumption⟩

/--
@isnad1 id=ex.0h2v.s5.668fd8b7f458 from=seed src=0 shape=62615caf vocab=a4c50966
-/
lemma mk_surjective (X : CofibrantObject C) :
    ∃ (Y : C) (_ : IsCofibrant Y), X = mk Y := ⟨X.obj, X.property, rfl⟩

/-- Constructor for morphisms in `CofibrantObject C`. -/
abbrev homMk {X Y : C} [IsCofibrant X] [IsCofibrant Y] (f : X ⟶ Y) :
    mk X ⟶ mk Y := ObjectProperty.homMk f

/--
@isnad1 id=ex.0h4v.s7.7f489a188f1f from=seed src=0 shape=9b9157b2 vocab=ca2708f3
-/
lemma homMk_surjective {X Y : C} [IsCofibrant X] [IsCofibrant Y]
    (f : mk X ⟶ mk Y) :
    ∃ (g : X ⟶ Y), f = homMk g := ⟨f.hom, rfl⟩

/--
@isnad1 id=iff.0h4v.s6.fd5a96e95a5b from=seed src=0 shape=57d592f5 vocab=6e768ec1
-/
@[simp]
lemma weakEquivalence_homMk_iff [CategoryWithWeakEquivalences C] {X Y : C}
    [IsCofibrant X] [IsCofibrant Y] (f : X ⟶ Y) :
    WeakEquivalence (homMk f) ↔ WeakEquivalence f := by
  simp only [weakEquivalence_iff]
  rfl

/--
@isnad1 id=eq.0h2v.s6.0250d1777422 from=seed src=0 shape=7e3427e2 vocab=253de7d2
-/
@[simp]
lemma homMk_id (X : C) [IsCofibrant X] : homMk (𝟙 X) = 𝟙 (mk X) := rfl

/--
@isnad1 id=eq.0h6v.s7.91f7006604ed from=seed src=0 shape=adc5b468 vocab=a8d4c500
-/
@[reassoc (attr := simp)]
lemma homMk_homMk {X Y Z : C} [IsCofibrant X] [IsCofibrant Y] [IsCofibrant Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    homMk f ≫ homMk g = homMk (f ≫ g) := rfl

/-- The inclusion functor `CofibrantObject C ⥤ C`. -/
abbrev ι : CofibrantObject C ⥤ C := (cofibrantObjects C).ι

instance (X : CofibrantObject C) : IsCofibrant X.1 := X.2
instance (X : CofibrantObject C) : IsCofibrant (CofibrantObject.ι.obj X) := X.2

end CofibrantObject

end Cofibrant

section Fibrant

variable [CategoryWithFibrations C] [HasTerminal C]

variable (C) in
/-- The property that is satisfied by fibrant objects.
(This is only introduced in order to consider the full subcategory
`FibrantObject`. Otherwise, the typeclass `IsFibrant`
is preferred.) -/
def fibrantObjects : ObjectProperty C := fun X ↦ IsFibrant X

variable (C) in
/-- The full subcategory of fibrant objects. -/
abbrev FibrantObject : Type u := (fibrantObjects C).FullSubcategory

namespace FibrantObject

/-- Constructor for `FibrantObject C`. -/
abbrev mk (X : C) [IsFibrant X] : FibrantObject C :=
  ⟨X, by assumption⟩

/--
@isnad1 id=ex.0h2v.s5.ad3f6ab56c05 from=seed src=0 shape=62615caf vocab=01b644ff
-/
lemma mk_surjective (X : FibrantObject C) :
    ∃ (Y : C) (_ : IsFibrant Y), X = mk Y := ⟨X.obj, X.property, rfl⟩

/-- Constructor for morphisms in `FibrantObject C`. -/
abbrev homMk {X Y : C} [IsFibrant X] [IsFibrant Y] (f : X ⟶ Y) :
    mk X ⟶ mk Y := ObjectProperty.homMk f

/--
@isnad1 id=ex.0h4v.s7.4fa2a03a7f8a from=seed src=0 shape=9b9157b2 vocab=606422c8
-/
lemma homMk_surjective {X Y : C} [IsFibrant X] [IsFibrant Y]
    (f : mk X ⟶ mk Y) :
    ∃ (g : X ⟶ Y), f = homMk g := ⟨f.hom, rfl⟩

/--
@isnad1 id=iff.0h4v.s6.2510d9eafb13 from=seed src=0 shape=57d592f5 vocab=32b3ea9e
-/
@[simp]
lemma weakEquivalence_homMk_iff [CategoryWithWeakEquivalences C] {X Y : C}
    [IsFibrant X] [IsFibrant Y] (f : X ⟶ Y) :
    WeakEquivalence (homMk f) ↔ WeakEquivalence f := by
  simp only [weakEquivalence_iff]
  rfl

/--
@isnad1 id=eq.0h2v.s6.8b89d56c2856 from=seed src=0 shape=7e3427e2 vocab=94e7a632
-/
@[simp]
lemma homMk_id (X : C) [IsFibrant X] : homMk (𝟙 X) = 𝟙 (mk X) := rfl

/--
@isnad1 id=eq.0h6v.s7.2edf4558fa67 from=seed src=0 shape=adc5b468 vocab=a0f00b05
-/
@[reassoc (attr := simp)]
lemma homMk_homMk {X Y Z : C} [IsFibrant X] [IsFibrant Y] [IsFibrant Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    homMk f ≫ homMk g = homMk (f ≫ g) := rfl

/-- The inclusion functor `FibrantObject C ⥤ C`. -/
abbrev ι : FibrantObject C ⥤ C := (fibrantObjects C).ι

instance (X : FibrantObject C) : IsFibrant X.1 := X.2
instance (X : FibrantObject C) : IsFibrant (FibrantObject.ι.obj X) := X.2

end FibrantObject

end Fibrant

section Bifibrant

variable [CategoryWithCofibrations C] [HasInitial C]
  [CategoryWithFibrations C] [HasTerminal C]

variable (C) in
/-- The property that is satisfied by bifibrant objects, i.e. objects
that are both cofibrant and fibrant.
(This is only introduced in order to consider the full subcategory
`BifibrantObject`. Otherwise, the typeclasses `IsCofibrant` and
`IsFibrant` are preferred.) -/
def bifibrantObjects : ObjectProperty C :=
  cofibrantObjects C ⊓ fibrantObjects C

variable (C) in
/--
@isnad1 id=le.0h1v.s5.dde51fd9d4eb from=seed src=0 shape=e54dd848 vocab=564eda0b
-/
lemma bifibrantObjects_le_cofibrantObject :
    bifibrantObjects C ≤ cofibrantObjects C :=
  fun _ h ↦ h.1

variable (C) in
/--
@isnad1 id=le.0h1v.s5.c0028f16902b from=seed src=0 shape=e54dd848 vocab=f242b2a8
-/
lemma bifibrantObjects_le_fibrantObject :
    bifibrantObjects C ≤ fibrantObjects C :=
  fun _ h ↦ h.2

variable (C) in
/-- The full subcategory of bifibrant objects. -/
abbrev BifibrantObject : Type u := (bifibrantObjects C).FullSubcategory

namespace BifibrantObject

/-- Constructor for `BifibrantObject C`. -/
abbrev mk (X : C) [IsCofibrant X] [IsFibrant X] :
    BifibrantObject C :=
  ⟨X, by assumption, by assumption⟩

/--
@isnad1 id=ex.0h2v.s6.f3b85c4eeb6f from=seed src=0 shape=192412f6 vocab=d8c1e399
-/
lemma mk_surjective (X : BifibrantObject C) :
    ∃ (Y : C) (_ : IsCofibrant Y) (_ : IsFibrant Y), X = mk Y :=
  ⟨X.obj, X.property.1, X.property.2, rfl⟩

/-- Constructor for morphisms in `BifibrantObject C`. -/
abbrev homMk {X Y : C} [IsCofibrant X] [IsCofibrant Y]
    [IsFibrant X] [IsFibrant Y] (f : X ⟶ Y) :
    mk X ⟶ mk Y := ObjectProperty.homMk f

/--
@isnad1 id=ex.0h4v.s7.2f4f97c86219 from=seed src=0 shape=dad24261 vocab=64938786
-/
lemma homMk_surjective {X Y : C} [IsCofibrant X] [IsCofibrant Y]
    [IsFibrant X] [IsFibrant Y]
    (f : mk X ⟶ mk Y) :
    ∃ (g : X ⟶ Y), f = homMk g := ⟨f.hom, rfl⟩

/--
@isnad1 id=iff.0h4v.s7.cad83ef84322 from=seed src=0 shape=cb98dbef vocab=a6f0fe95
-/
@[simp]
lemma weakEquivalence_homMk_iff [CategoryWithWeakEquivalences C] {X Y : C}
    [IsCofibrant X] [IsFibrant X] [IsCofibrant Y] [IsFibrant Y] (f : X ⟶ Y) :
    WeakEquivalence (homMk f) ↔ WeakEquivalence f := by
  simp only [weakEquivalence_iff]
  rfl

/--
@isnad1 id=eq.0h2v.s7.7a2902c6bc63 from=seed src=0 shape=ffe6b494 vocab=163a3bd8
-/
@[simp]
lemma homMk_id (X : C) [IsCofibrant X] [IsFibrant X] :
    homMk (𝟙 X) = 𝟙 (mk X) := rfl

/--
@isnad1 id=eq.0h6v.s7.dde9f52549a4 from=seed src=0 shape=8df3abb4 vocab=c60625e1
-/
@[reassoc (attr := simp)]
lemma homMk_homMk {X Y Z : C} [IsCofibrant X] [IsCofibrant Y] [IsCofibrant Z]
    [IsFibrant X] [IsFibrant Y] [IsFibrant Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    homMk f ≫ homMk g = homMk (f ≫ g) := rfl

/-- The inclusion functor `BifibrantObject C ⥤ C`. -/
abbrev ι : BifibrantObject C ⥤ C := (bifibrantObjects C).ι

instance (X : BifibrantObject C) : IsCofibrant X.obj := X.property.1
instance (X : BifibrantObject C) : IsFibrant X.obj := X.property.2
instance (X : BifibrantObject C) : IsCofibrant (BifibrantObject.ι.obj X) := X.property.1
instance (X : BifibrantObject C) : IsFibrant (BifibrantObject.ι.obj X) := X.property.2

/-- The inclusion `BifibrantObject C ⥤ CofibrantObject C`. -/
abbrev ιCofibrantObject : BifibrantObject C ⥤ CofibrantObject C :=
  ObjectProperty.ιOfLE (bifibrantObjects_le_cofibrantObject C)

/-- The inclusion functor `BifibrantObject C ⥤ FibrantObject C`. -/
abbrev ιFibrantObject : BifibrantObject C ⥤ FibrantObject C :=
  ObjectProperty.ιOfLE (bifibrantObjects_le_fibrantObject C)

instance (X : BifibrantObject C) : IsCofibrant (ιFibrantObject.obj X).obj := X.property.1

instance (X : BifibrantObject C) : IsFibrant (ιCofibrantObject.obj X).obj := X.property.2

end BifibrantObject

end Bifibrant

end HomotopicalAlgebra
