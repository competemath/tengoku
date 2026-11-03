/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.Algebra.Homology.DGCategory.NaturalTransformation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Whiskering homogeneous dg natural transformations

A homogeneous dg natural transformation can be precomposed with a dg functor
on the source side and postcomposed with one on the target side.  Both
operations keep the degree, and neither introduces a sign.

## Where the Koszul sign is, and where it is not

It is tempting to expect a sign in `whiskerRight`, because it applies a
functor to a morphism of degree `n`.  There is none: a `DGFunctor` preserves
the graded composition on the nose (`DGFunctor.map_comp` carries no sign), so
transporting `η`'s graded naturality through `K` transports the sign
unchanged.  Likewise `whiskerLeft` is naturality of `η` evaluated at
`F.map p f`, again with `η`'s own sign and no other.

The sign appears one level up, in the **interchange law**.  For
`α : F ⟶ F'` of degree `n` and `β : G ⟶ G'` of degree `m` the two ways of
reading the horizontal composite differ by `(-1)^(m * n)`:

`(α ◁ G) ≫ (F' ▷ β) = (-1)^(m n) • ((F ▷ β) ≫ (α ◁ G'))`.

That is exactly graded naturality of `β` evaluated at the degree-`n` morphism
`α X`, which is why the sign is `β`'s degree times `α`'s and not something
new.  The two horizontal composites agree on the nose exactly when `m * n` is
even.

## Degrees

Whiskering does not change the degree, so both operations are additive in the
transformation and are packaged as `AddMonoidHom`s.  Vertical composition is
where degrees add, and `whiskerLeft_composition` and
`whiskerRight_composition` say whiskering is a homomorphism for it in every
result degree.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u u' u'' u'''

namespace CategoryTheory

open DGCategoryStruct DGCategory

namespace DGFunctor.HomogeneousNatTrans

variable {C : Type u} {D : Type u'} {E : Type u''} {B : Type u'''}
  [DGCategory.{v} C] [DGCategory.{v} D] [DGCategory.{v} E] [DGCategory.{v} B]

/-! ### Left whiskering -/

section WhiskerLeft

variable (F : DGFunctor C D) {G H I : DGFunctor D E} {n m : ℤ}

/-- **Precomposition with a dg functor.**

The component at `X` is `η`'s component at `F.obj X`, and graded naturality is
`η`'s own, evaluated at `F.map p f`.-/
def whiskerLeft (η : HomogeneousNatTrans G H n) :
    HomogeneousNatTrans (F.comp G) (F.comp H) n :=
  ⟨fun X => app η (F.obj X), by
    intro X Y p r hpn hnp f
    exact naturality η p r hpn hnp (F.map p f)⟩

/--
@isnad1 id=eq.0h9v.s9.b26c604c792d from=translated src=- shape=030143cc vocab=9576d382
-/
@[simp]
theorem whiskerLeft_app (η : HomogeneousNatTrans G H n) (X : C) :
    app (whiskerLeft F η) X = app η (F.obj X) :=
  rfl

/--
@isnad1 id=eq.0h7v.s11.2b3b094c71f0 from=translated src=- shape=1f0552b5 vocab=f9058fbb
-/
@[simp]
theorem whiskerLeft_zero :
    whiskerLeft F (0 : HomogeneousNatTrans G H n) = 0 := by
  ext X
  rfl

/--
@isnad1 id=eq.0h9v.s12.34d2e7d57988 from=translated src=- shape=312a3817 vocab=f5c673a6
-/
theorem whiskerLeft_add (η θ : HomogeneousNatTrans G H n) :
    whiskerLeft F (η + θ) = whiskerLeft F η + whiskerLeft F θ := by
  ext X
  rfl

/-- Left whiskering as an additive map.-/
def whiskerLeftHom (G H : DGFunctor D E) (n : ℤ) :
    HomogeneousNatTrans G H n →+ HomogeneousNatTrans (F.comp G) (F.comp H) n :=
  AddMonoidHom.mk' (whiskerLeft F) (whiskerLeft_add F)

/--
@isnad1 id=eq.0h8v.s14.f41db9692d3b from=translated src=- shape=50733e03 vocab=e47ea05b
-/
@[simp]
theorem whiskerLeftHom_apply (η : HomogeneousNatTrans G H n) :
    whiskerLeftHom F G H n η = whiskerLeft F η :=
  rfl

/-- Left whiskering takes the identity transformation to the identity.
@isnad1 id=eq.0h5v.s9.fc320077396b from=translated src=- shape=1e6abef7 vocab=ae8da6ac
-/
@[simp]
theorem whiskerLeft_id (G : DGFunctor D E) :
    whiskerLeft F (id G) = id (F.comp G) :=
  rfl

/-- Left whiskering is a homomorphism for vertical composition, in every
result degree.
@isnad1 id=eq.1h12v.s17.c4c83c0433c7 from=translated src=- shape=c2f30f2c vocab=aaa25281
-/
theorem whiskerLeft_composition (η : HomogeneousNatTrans G H n)
    (θ : HomogeneousNatTrans H I m) (r : ℤ) (h : n + m = r) :
    whiskerLeft F (composition G H I n m r h η θ) =
      composition (F.comp G) (F.comp H) (F.comp I) n m r h
        (whiskerLeft F η) (whiskerLeft F θ) := by
  ext X
  rw [whiskerLeft_app, composition_apply_app, composition_apply_app,
    whiskerLeft_app, whiskerLeft_app]
  rfl

/-- Left whiskering commutes with the pointwise differential.
@isnad1 id=eq.0h8v.s10.acf78f96a7e9 from=translated src=- shape=b805a407 vocab=3a8f00ab
-/
@[simp]
theorem whiskerLeft_differential (η : HomogeneousNatTrans G H n) :
    differential (whiskerLeft F η) = whiskerLeft F (differential η) :=
  rfl

/-- A whiskered closed transformation is closed.
@isnad1 id=isclosed.1h8v.s9.834d309237bc from=translated src=- shape=44402518 vocab=262e9c43
-/
theorem IsClosed.whiskerLeft {η : HomogeneousNatTrans G H n} (hη : IsClosed η) :
    IsClosed (HomogeneousNatTrans.whiskerLeft F η) := by
  ext X
  rw [whiskerLeft_differential, whiskerLeft_app, zero_app]
  exact congrArg (fun σ => app σ (F.obj X)) hη

end WhiskerLeft

/-! ### Right whiskering -/

section WhiskerRight

variable {F G H : DGFunctor C D} {n m : ℤ}

/-- **Postcomposition with a dg functor.**

The component at `X` is `K` applied to `η`'s component, in the same degree
`n`.  No sign appears: `K` preserves the graded composition on the nose, so it
carries `η`'s naturality equation across sign and all.-/
def whiskerRight (η : HomogeneousNatTrans F G n) (K : DGFunctor D E) :
    HomogeneousNatTrans (F.comp K) (G.comp K) n :=
  ⟨fun X => K.map n (app η X), by
    intro X Y p r hpn hnp f
    show dgComp p n r hpn (K.map p (F.map p f)) (K.map n (app η Y)) =
      (n * p).negOnePow •
        dgComp n p r hnp (K.map n (app η X)) (K.map p (G.map p f))
    rw [← K.map_comp p n r hpn, ← K.map_comp n p r hnp,
      naturality η p r hpn hnp f]
    simp [Units.smul_def, map_zsmul]⟩

/--
@isnad1 id=eq.0h9v.s11.2dd92f5707ab from=translated src=- shape=6ea13654 vocab=c66aa5af
-/
@[simp]
theorem whiskerRight_app (η : HomogeneousNatTrans F G n) (K : DGFunctor D E)
    (X : C) :
    app (whiskerRight η K) X = K.map n (app η X) :=
  rfl

/--
@isnad1 id=eq.0h7v.s11.898f197be442 from=translated src=- shape=00141c64 vocab=9f6b9d87
-/
@[simp]
theorem whiskerRight_zero (K : DGFunctor D E) :
    whiskerRight (0 : HomogeneousNatTrans F G n) K = 0 := by
  ext X
  exact map_zero (K.map n)

/--
@isnad1 id=eq.0h9v.s12.17af7f82f4f8 from=translated src=- shape=4fd1e311 vocab=7251b14a
-/
theorem whiskerRight_add (η θ : HomogeneousNatTrans F G n)
    (K : DGFunctor D E) :
    whiskerRight (η + θ) K = whiskerRight η K + whiskerRight θ K := by
  ext X
  exact map_add (K.map n) (app η X) (app θ X)

/-- Right whiskering as an additive map.-/
def whiskerRightHom (F G : DGFunctor C D) (n : ℤ) (K : DGFunctor D E) :
    HomogeneousNatTrans F G n →+ HomogeneousNatTrans (F.comp K) (G.comp K) n :=
  AddMonoidHom.mk' (fun η => whiskerRight η K)
    (fun η θ => whiskerRight_add η θ K)

/--
@isnad1 id=eq.0h8v.s14.aac34f3d1c66 from=translated src=- shape=0f8dc5d6 vocab=1841f7e8
-/
@[simp]
theorem whiskerRightHom_apply (η : HomogeneousNatTrans F G n)
    (K : DGFunctor D E) :
    whiskerRightHom F G n K η = whiskerRight η K :=
  rfl

/-- Right whiskering takes the identity transformation to the identity.  This
is `DGFunctor.map_id`, and it is the one place where right whiskering needs
more than additivity of `K.map`.
@isnad1 id=eq.0h5v.s9.d275f08de717 from=translated src=- shape=21708dc7 vocab=218de98f
-/
@[simp]
theorem whiskerRight_id (F : DGFunctor C D) (K : DGFunctor D E) :
    whiskerRight (id F) K = id (F.comp K) := by
  ext X
  exact K.map_id (F.obj X)

/-- Right whiskering is a homomorphism for vertical composition, in every
result degree.  This is `DGFunctor.map_comp`.
@isnad1 id=eq.1h12v.s17.0900af0db3c6 from=translated src=- shape=8e6558c1 vocab=73a7b2f9
-/
theorem whiskerRight_composition (η : HomogeneousNatTrans F G n)
    (θ : HomogeneousNatTrans G H m) (r : ℤ) (h : n + m = r)
    (K : DGFunctor D E) :
    whiskerRight (composition F G H n m r h η θ) K =
      composition (F.comp K) (G.comp K) (H.comp K) n m r h
        (whiskerRight η K) (whiskerRight θ K) := by
  ext X
  rw [whiskerRight_app, composition_apply_app, composition_apply_app,
    whiskerRight_app, whiskerRight_app, K.map_comp n m r h]
  rfl

/-- Right whiskering commutes with the pointwise differential.  This is
`DGFunctor.map_d`.
@isnad1 id=eq.0h8v.s10.8a0da697aa73 from=translated src=- shape=acecd792 vocab=d222dbea
-/
@[simp]
theorem whiskerRight_differential (η : HomogeneousNatTrans F G n)
    (K : DGFunctor D E) :
    differential (whiskerRight η K) = whiskerRight (differential η) K := by
  ext X
  rw [differential_app, whiskerRight_app, whiskerRight_app, differential_app,
    K.map_d n (n + 1)]
  rfl

/-- A whiskered closed transformation is closed.
@isnad1 id=isclosed.1h8v.s9.93aa9517d132 from=translated src=- shape=26bac6fa vocab=11cf8662
-/
theorem IsClosed.whiskerRight {η : HomogeneousNatTrans F G n} (hη : IsClosed η)
    (K : DGFunctor D E) :
    IsClosed (HomogeneousNatTrans.whiskerRight η K) := by
  ext X
  rw [whiskerRight_differential, whiskerRight_app, zero_app]
  have h := congrArg (fun σ => app σ X) hη
  simp only [zero_app] at h
  rw [h, map_zero]
  rfl

end WhiskerRight

/-! ### Whiskering by a composite

All three laws hold by `rfl`, because `DGFunctor.comp` composes the object maps
and the `AddMonoidHom`s directly.  They are what makes horizontal composition
of dg natural transformations strictly associative. -/

section Compat

variable {F F' : DGFunctor C D} {G G' : DGFunctor D E} {n m : ℤ}

/-- Whiskering twice on the right is whiskering by the composite.
@isnad1 id=eq.0h10v.s10.a44a511c3715 from=translated src=- shape=a7beb49c vocab=9f6b9d87
-/
theorem whiskerRight_whiskerRight (α : HomogeneousNatTrans F F' n)
    (G : DGFunctor D E) (K : DGFunctor E B) :
    whiskerRight (whiskerRight α G) K = whiskerRight α (G.comp K) :=
  rfl

/-- Whiskering twice on the left is whiskering by the composite.
@isnad1 id=eq.0h10v.s10.4e92f277a139 from=translated src=- shape=f4ec669f vocab=f9058fbb
-/
theorem whiskerLeft_whiskerLeft (F : DGFunctor C D) (G : DGFunctor D E)
    {K K' : DGFunctor E B} (β : HomogeneousNatTrans K K' n) :
    whiskerLeft F (whiskerLeft G β) = whiskerLeft (F.comp G) β :=
  rfl

/-- Whiskering on the two sides commutes.
@isnad1 id=eq.0h10v.s10.b9d11320e91c from=translated src=- shape=0a4fede9 vocab=e5bcb6a3
-/
theorem whiskerRight_whiskerLeft (F : DGFunctor C D)
    (β : HomogeneousNatTrans G G' m) (K : DGFunctor E B) :
    whiskerRight (whiskerLeft F β) K = whiskerLeft F (whiskerRight β K) :=
  rfl

end Compat

/-! ### The interchange law -/

section Interchange

variable {F F' : DGFunctor C D} {G G' : DGFunctor D E} {n m : ℤ}

/-- **The Godement interchange law, componentwise.**

Reading the horizontal composite of `α` and `β` in the two possible orders
differs by `(-1)^(m * n)`.  The identity is nothing but graded naturality of
`β` evaluated at the degree-`n` morphism `α X`, which is why the sign is
`β`'s degree times `α`'s and not something new.
@isnad1 id=eq.2h13v.s15.aa6c46573848 from=translated src=- shape=d4d29873 vocab=b8e0afd2
-/
theorem interchange_app (α : HomogeneousNatTrans F F' n)
    (β : HomogeneousNatTrans G G' m) (r : ℤ) (hnm : n + m = r)
    (hmn : m + n = r) (X : C) :
    dgComp n m r hnm (G.map n (app α X)) (app β (F'.obj X)) =
      (m * n).negOnePow •
        dgComp m n r hmn (app β (F.obj X)) (G'.map n (app α X)) :=
  naturality β n r hnm hmn (app α X)

/-- **The Godement interchange law.**

`(α ◁ G) ≫ (F' ▷ β) = (-1)^(m n) • ((F ▷ β) ≫ (α ◁ G'))`, with `n` the degree
of `α` and `m` the degree of `β`.  Both sides are transformations
`F ⋙ G ⟶ F' ⋙ G'` of degree `r`; the two vertical composites are taken in the
two orders, which is why `r` comes with both `n + m = r` and `m + n = r`.
@isnad1 id=eq.2h12v.s18.5381ae7c12ab from=translated src=- shape=14e0e64b vocab=e83c1bac
-/
theorem interchange (α : HomogeneousNatTrans F F' n)
    (β : HomogeneousNatTrans G G' m) (r : ℤ) (hnm : n + m = r)
    (hmn : m + n = r) :
    composition (F.comp G) (F'.comp G) (F'.comp G') n m r hnm
        (whiskerRight α G) (whiskerLeft F' β) =
      (m * n).negOnePow •
        composition (F.comp G) (F.comp G') (F'.comp G') m n r hmn
          (whiskerLeft F β) (whiskerRight α G') := by
  ext X
  rw [composition_apply_app, whiskerRight_app, whiskerLeft_app,
    units_smul_app, composition_apply_app, whiskerLeft_app, whiskerRight_app]
  exact interchange_app α β r hnm hmn X

end Interchange

end DGFunctor.HomogeneousNatTrans

end CategoryTheory
