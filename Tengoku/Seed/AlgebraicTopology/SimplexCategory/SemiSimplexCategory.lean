/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.AlgebraicTopology.SimplexCategory.Basic

/-!
# The semi-simplex category

We define a category `SemiSimplexCategory` so that semi-simplicial objects
can be defined (TODO) as functors from `SemiSimplexCategoryᵒᵖ` similarly
as simplicial objects are functors from `SimplexCategory`.

-/

@[expose] public section

open CategoryTheory Simplicial

/-- The category whose objects are denoted `⦋n⦌ₛ` for `n : ℕ` and
morphisms `⦋n⦌ₛ ⟶ ⦋m⦌ₛ` are order embeddings `Fin (n.len + 1) ↪o Fin (m.len + 1)`.
(This identifies to a wide subcategory of the category `SemiSimplex`, which
has the "same" objects, and morphisms `Fin (n.len + 1) →o Fin (m.len + 1)`,
see the faithful functor `SemiSimplexCategory.toSimplexCategory`.) -/
@[ext]
structure SemiSimplexCategory : Type where
  /-- Constructor `ℕ → SemiSimplexCategory`. -/
  mk ::
  /-- The length of an object in `SemiSimplexCategory` -/
  len : ℕ

namespace SemiSimplexCategory

/-- The object of `SemiSimplexCategory` corresponding to `n : ℕ` is denoted `⦋n⦌ₛ`. -/
scoped[Simplicial] notation "⦋" n "⦌ₛ" => SemiSimplexCategory.mk n

/-- The type of morphisms in the semi-simplex category are order embeddings.
This type is made irreducible: use `SemiSimplexCategory.homEquiv` to make
the conversion. -/
def Hom (n m : SemiSimplexCategory) := Fin (n.len + 1) ↪o Fin (m.len + 1)

instance smallCategory : SmallCategory.{0} SemiSimplexCategory where
  Hom := Hom
  id _ := .refl _
  comp f g := f.trans g

/-- Morphisms `n ⟶ m` in `SemiSimplexCategory` identify to order embeddings
`Fin (n.len + 1) ↪o Fin (m.len + 1)`. -/
def homEquiv {n m : SemiSimplexCategory} :
    (n ⟶ m) ≃ (Fin (n.len + 1) ↪o Fin (m.len + 1)) :=
  .refl _

/--
@isnad1 id=eq.0h1v.s9.ed8b3b09e5ac from=seed src=0 shape=226f6d01 vocab=c2bc7d11
-/
@[simp]
lemma homEquiv_id (a : SemiSimplexCategory) :
    homEquiv (𝟙 a) = .refl _ := rfl

/--
@isnad1 id=eq.0h5v.s10.3a1fb0265886 from=seed src=0 shape=ff2fdd3c vocab=5a68beb1
-/
@[simp]
lemma homEquiv_comp {a b c : SemiSimplexCategory} (f : a ⟶ b) (g : b ⟶ c) :
    homEquiv (f ≫ g) = (homEquiv f).trans (homEquiv g) := rfl

attribute [irreducible] Hom

/--
@isnad1 id=eq.1h4v.s9.aed6e818ba50 from=seed src=0 shape=4fa7ef33 vocab=851989b2
-/
@[ext]
theorem hom_ext {a b : SemiSimplexCategory} {f g : a ⟶ b}
    (h : homEquiv f = homEquiv g) : f = g :=
  homEquiv.injective h

/-- The inclusion functor `SemiSimplexCategory ⥤ SimplexCategory`. -/
def toSimplexCategory : SemiSimplexCategory ⥤ SimplexCategory where
  obj n := ⦋n.len⦌
  map f := SimplexCategory.Hom.mk (homEquiv f).toOrderHom

/--
@isnad1 id=eq.0h1v.s3.385c9c1a7a07 from=seed src=0 shape=19bb8685 vocab=0925e752
-/
@[simp]
lemma toSimplexCategory_obj (n : ℕ) :
    toSimplexCategory.obj ⦋n⦌ₛ = ⦋n⦌ := rfl

instance : toSimplexCategory.Faithful where
  map_injective h := by
    ext : 2
    apply ConcreteCategory.congr_hom h

instance {n m : SemiSimplexCategory} (f : n ⟶ m) : Mono (toSimplexCategory.map f) := by
  rw [SimplexCategory.mono_iff_injective]
  exact (homEquiv f).injective

instance {n m : SemiSimplexCategory} (f : n ⟶ m) : Mono f where
  right_cancellation g₁ g₂ h := by
    apply toSimplexCategory.map_injective
    simp only [← cancel_mono (toSimplexCategory.map f), ← Functor.map_comp, h]

/-- Constructor for morphisms in `SemiSimplexCategory` which takes as an input
a monomorphism in `SimplexCategory`. -/
def homOfMono {n m : SemiSimplexCategory}
    (f : toSimplexCategory.obj n ⟶ toSimplexCategory.obj m) [Mono f] : n ⟶ m :=
  homEquiv.symm (OrderEmbedding.ofStrictMono f.toOrderHom
    ((SimplexCategory.Hom.toOrderHom f).monotone.strictMono_of_injective
      (by rwa [← SimplexCategory.mono_iff_injective])))

/--
@isnad1 id=eq.0h3v.s6.9658be1c6e10 from=seed src=0 shape=191bf337 vocab=bbab0ae1
-/
@[simp]
lemma toSimplexCategory_map_homOfMono {n m : SemiSimplexCategory}
    (f : toSimplexCategory.obj n ⟶ toSimplexCategory.obj m) [Mono f] :
    toSimplexCategory.map (homOfMono f) = f := by
  aesop

end SemiSimplexCategory
