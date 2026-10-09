/-
Copyright (c) 2026 Johns Hopkins Category Theory Seminar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johns Hopkins Category Theory Seminar, Arnoud van der Leer
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.AlgebraicTopology.SimplicialSet.CompStruct
public import Tengoku.Seed.CategoryTheory.CodiscreteCategory
public import Tengoku.Seed.AlgebraicTopology.SimplicialSet.Nerve

/-!
# The Coherent Isomorphism

We define the free walking isomorphism `WalkingIso`; the category with objects `zero` and
`one` and unique morphisms `zero ⟶ one` and `one ⟶ zero`. We construct an equivalence
`WalkingIso.equiv` between the type of functors from `WalkingIso` into any category `C` and the type
`Σ (X : C) (Y : C), (X ≅ Y)` of isomorphisms in that category.

The simplicial set `SSet.coherentIso` is defined as the nerve of `WalkingIso`, with
`coherentIso.x₀` and `coherentIso.x₁` the `0`-simplices corresponding to `WalkingIso.zero`
and `WalkingIso.one` respectively, and `coherentIso.hom : Edge x₀ x₁` and
`coherentIso.inv : Edge x₁ x₀` forward and backward edges corresponding to the morphisms in
`WalkingIso`. Given any simplicial set `X`, with a morphism `g : coherentIso ⟶ X`, `0`-simplices
`x₀ x₁: X _⦋0⦌` and an edge between them `f : Edge x₀ x₁`, such that `g` sends `coherentIso.hom` to
`f`, then `f` has an inverse (in the sense of `Edge.InvStruct`), see `invStructOfEqMapHom`.

-/

@[expose] public section

universe w u v

open CategoryTheory

namespace CategoryTheory

/-- This is the free-living isomorphism as the codiscrete category on `Bool`. -/
abbrev WalkingIso : Type w := Codiscrete (ULift Bool)

namespace WalkingIso

/-- The underlying type of `WalkingIso` is equivalent to `Bool`, since they both have 2 elements. -/
def equivBool : WalkingIso.{w} ≃ Bool := codiscreteEquiv.trans Equiv.ulift

section

variable {C : Type u} [Category.{v} C]

/-- The domain of the isomorphism -/
def zero : WalkingIso.{w} := .mk (.up false)

/-- The codomain of the isomorphism -/
def one : WalkingIso.{w} := .mk (.up true)

/-- The isomorphism between `zero` and `one` in `WalkingIso`. -/
def iso : zero.{w} ≅ one := Codiscrete.iso zero one

lemma eq_iso_hom (f : zero.{w} ⟶ one) : f = iso.{w}.hom := Codiscrete.eq_iso_hom f

lemma eq_iso_inv (f : one.{w} ⟶ zero) : f = iso.{w}.inv := Codiscrete.eq_iso_inv f

/-- Functors out of `WalkingIso` define isomorphisms in the target category. -/
@[simps!]
def toIso (F : WalkingIso.{w} ⥤ C) : F.obj zero ≅ F.obj one := F.mapIso iso

section induction

variable {motive : WalkingIso.{u} → Sort*} (zero : motive zero) (one : motive one)

/-- The recursor for WalkingIso, which constructs a term of `∏ (x : WalkingIso), A x` from
a term of `A zero` and a term of `A one`. -/
@[elab_as_elim, induction_eliminator]
protected def rec : ∀ a, motive a
  | .mk (.up false) => zero
  | .mk (.up true) => one

/--
@isnad1 id=eq.0h3v.s4.d17653e5ec31 from=seed src=0 shape=323556e3 vocab=b141e76d
-/
@[simp] lemma rec_zero : WalkingIso.rec zero one .zero = zero := rfl
/--
@isnad1 id=eq.0h3v.s4.11b97d7688e2 from=seed src=0 shape=41d4aa76 vocab=b141e76d
-/
@[simp] lemma rec_one : WalkingIso.rec zero one .one = one := rfl

end induction

set_option backward.isDefEq.respectTransparency false in
/-- From an isomorphism in a category, we can build a functor out of `WalkingIso` to
that category. -/
def fromIso {X Y : C} (e : X ≅ Y) : WalkingIso.{w} ⥤ C where
  obj x := by induction x; exacts [X, Y]
  map {x y} _ := by induction x <;> induction y; exacts [𝟙 X, e.hom, e.inv, 𝟙 Y]
  map_comp {x y z} _ _ := by induction x <;> induction y <;> induction z <;> simp
  map_id {x} := by induction x <;> rfl

section

variable {X Y : C} (e : X ≅ Y)

/--
@isnad1 id=eq.0h4v.s5.944d4724d4c8 from=seed src=0 shape=0fd2f492 vocab=efd211fe
-/
@[simp]
lemma fromIso_zero : (fromIso.{w} e).obj .zero = X := rfl

/--
@isnad1 id=eq.0h4v.s5.7ab03845155b from=seed src=0 shape=ed6449e8 vocab=1b249836
-/
@[simp]
lemma fromIso_one : (fromIso.{w} e).obj .one = Y := rfl

/--
@isnad1 id=eq.0h5v.s6.4c1e17c3e289 from=seed src=0 shape=cbb5939f vocab=db4c0148
-/
@[simp]
lemma fromIso_map_zero_zero (f : zero ⟶ zero) : (fromIso.{w} e).map f = 𝟙 X := rfl

/--
@isnad1 id=eq.0h5v.s6.9e1fdb869753 from=seed src=0 shape=b6de3793 vocab=0cba6c1e
-/
@[simp]
lemma fromIso_hom (f : zero ⟶ one) : (fromIso.{w} e).map f = e.hom := rfl

/--
@isnad1 id=eq.0h5v.s6.565bfd42aff4 from=seed src=0 shape=b6de3793 vocab=ba6ff00a
-/
@[simp]
lemma fromIso_inv (f : one ⟶ zero) : (fromIso.{w} e).map f = e.inv := rfl

/--
@isnad1 id=eq.0h5v.s6.3878828b0aad from=seed src=0 shape=6f5567c7 vocab=375ac559
-/
@[simp]
lemma fromIso_map_one_one (f : one ⟶ one) : (fromIso.{w} e).map f = 𝟙 Y := rfl

end

set_option backward.isDefEq.respectTransparency false in
/-- An equivalence between the type of `WalkingIso`s in `C` and the type of isomorphisms in `C`. -/
@[simps]
def equiv : (WalkingIso.{w} ⥤ C) ≃ Σ (X : C) (Y : C), (X ≅ Y) where
  toFun F := ⟨F.obj zero, F.obj one, toIso F⟩
  invFun p := fromIso p.2.2
  right_inv := fun ⟨X, Y, e⟩ ↦ rfl
  left_inv F := Functor.ext (by rintro (_ | _) <;> rfl) <| by
      intro X Y f
      induction X <;>
      induction Y <;>
      simp [Codiscrete.eq_id] <;>
      rfl

end

end WalkingIso

end CategoryTheory

namespace SSet

open Simplicial

/-- The simplicial set that encodes a single isomorphism.
Its n-simplices are formal compositions of arrows in WalkingIso. -/
abbrev coherentIso : SSet := nerve WalkingIso.{u}

namespace coherentIso

/-- The source vertex of `coherentIso`. -/
def x₀ : coherentIso.{u} _⦋0⦌ :=
  ComposableArrows.mk₀ WalkingIso.zero

/-- The target vertex of `coherentIso`. -/
def x₁ : coherentIso.{u} _⦋0⦌ :=
  ComposableArrows.mk₀ WalkingIso.one

/-- The forwards edge of `coherentIso`. -/
def hom : Edge.{u} x₀ x₁ where
  edge := ComposableArrows.mk₁ WalkingIso.iso.hom
  src_eq := ComposableArrows.ext₀ rfl
  tgt_eq := ComposableArrows.ext₀ rfl

/-- The backwards edge of `coherentIso`. -/
def inv : Edge.{u} x₁ x₀ where
  edge := ComposableArrows.mk₁ WalkingIso.iso.inv
  src_eq := ComposableArrows.ext₀ rfl
  tgt_eq := ComposableArrows.ext₀ rfl

/-- The forwards and backwards edge of `coherentIso` compose to the identity. -/
def homInvId : Edge.CompStruct.{u} hom inv (Edge.id x₀) where
  simplex := ComposableArrows.mk₂ WalkingIso.iso.hom WalkingIso.iso.inv
  d₂ := ComposableArrows.ext₁ rfl rfl rfl
  d₀ := ComposableArrows.ext₁ rfl rfl rfl
  d₁ := ComposableArrows.ext₁ rfl rfl rfl

/-- The backwards and forwards edge of `coherentIso` compose to the identity. -/
def invHomId : Edge.CompStruct.{u} inv hom (Edge.id x₁) where
  simplex := ComposableArrows.mk₂ WalkingIso.iso.inv WalkingIso.iso.hom
  d₂ := ComposableArrows.ext₁ rfl rfl rfl
  d₀ := ComposableArrows.ext₁ rfl rfl rfl
  d₁ := ComposableArrows.ext₁ rfl rfl rfl

/-- The forwards edge of `coherentIso` has an inverse. -/
@[simps]
def invStructHom : Edge.InvStruct.{u} coherentIso.hom where
  inv := inv
  homInvId := homInvId
  invHomId := invHomId

/-- For a simplicial set `X`, if an edge in `X` is equal to the image of `hom`
under a morphism of simplicial sets, this edge has an inverse. -/
abbrev invStructOfEqMapHom {X : SSet.{u}} {x₀ x₁ : X _⦋0⦌}
    {f : Edge x₀ x₁}
    {g : coherentIso ⟶ X}
    (hfg : f.edge = g.app _ hom.edge) :
    f.InvStruct :=
  (invStructHom.map g).ofEq hfg.symm

end coherentIso

end SSet
