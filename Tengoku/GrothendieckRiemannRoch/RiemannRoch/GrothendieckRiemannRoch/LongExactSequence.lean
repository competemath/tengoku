/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.GrothendieckRiemannRoch.RiemannRoch.GrothendieckRiemannRoch.DerivedPushforward
import Tengoku.GrothendieckRiemannRoch.RiemannRoch.KTheory.ExactCategory

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Long exact sequences and Grothendieck-group witnesses

This file constructs the image short exact sequence attached to two consecutive arrows in an
exact sequence in an abelian category.  It is the categorical input for manufacturing
`LongExactWitness` data from genuine long exact sequences, rather than supplying virtual-class
decompositions by hand.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe u v w

namespace GrothendieckRiemannRoch

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {A B D : C}

/-- The standard short complex `im(f) → B → im(g)` associated to two composable arrows.-/
noncomputable def imageShortComplex (f : A ⟶ B) (g : B ⟶ D) (zero : f ≫ g = 0) :
    ShortComplex C :=
  ShortComplex.mk (Abelian.image.ι f) (Abelian.factorThruImage g) (by
    rw [← cancel_mono (Abelian.image.ι g), Category.assoc, Abelian.image.fac]
    simpa using Abelian.image_ι_comp_eq_zero zero)

/-- Exactness of `A → B → D` makes `im(f) → B → im(g)` short exact.
@isnad1 id=shortexa.2h6v.s7.0be759734721 from=translated src=- shape=6aa46680 vocab=7e356a2f
-/
theorem imageShortComplex_shortExact (f : A ⟶ B) (g : B ⟶ D)
    (zero : f ≫ g = 0) (exact : (ShortComplex.mk f g zero).Exact) :
    (imageShortComplex f g zero).ShortExact := by
  let S : ShortComplex C := ShortComplex.mk f g zero
  let S' : ShortComplex C :=
    ShortComplex.mk (Abelian.image.ι f) g (Abelian.image_ι_comp_eq_zero zero)
  let T : ShortComplex C := imageShortComplex f g zero
  let φ : T ⟶ S' := ShortComplex.homMk (𝟙 _) (𝟙 _) (Abelian.image.ι g)
    (by simp [T, S', imageShortComplex])
    (by simp [T, S', imageShortComplex])
  have hS' : S'.Exact := by
    exact (S.exact_iff_exact_image_ι).mp exact
  letI : Epi φ.τ₁ := by
    change Epi (𝟙 T.X₁)
    infer_instance
  letI : IsIso φ.τ₂ := by
    change IsIso (𝟙 T.X₂)
    infer_instance
  letI : Mono φ.τ₃ := by
    change Mono (Abelian.image.ι g)
    infer_instance
  have hT : T.Exact :=
    (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr hS'
  letI : Mono T.f := by
    dsimp [T, imageShortComplex]
    infer_instance
  letI : Epi T.g := by
    dsimp [T, imageShortComplex]
    infer_instance
  exact { exact := hT }

variable (P : C → Prop)

/-- The Grothendieck-class decomposition associated to two consecutive arrows in an exact
sequence.
@isnad1 id=eq.2h10v.s8.d425ee8124e0 from=translated src=- shape=08a9d3b6 vocab=39452433
-/
theorem subcategoryClassOf_eq_image_add_image
    (f : A ⟶ B) (g : B ⟶ D) (zero : f ≫ g = 0)
    (exact : (ShortComplex.mk f g zero).Exact)
    (hImageF : P (Abelian.image f)) (hB : P B) (hImageG : P (Abelian.image g)) :
    ExactGrothendieck.subcategoryClassOf C P B hB =
      ExactGrothendieck.subcategoryClassOf C P (Abelian.image f) hImageF +
        ExactGrothendieck.subcategoryClassOf C P (Abelian.image g) hImageG := by
  let T := imageShortComplex f g zero
  exact ExactGrothendieck.subcategoryClassOf_middle C P hImageF hB hImageG T.zero
    (imageShortComplex_shortExact f g zero exact)

/-- A bounded portion of a genuine long exact sequence in an abelian category, together with
membership of every term and every successive image in the chosen exact subcategory.-/
structure BoundedLongExactData (n : ℕ) where
  /-- Left term in each cohomological degree.-/
  a : ℕ → C
  /-- Middle term in each cohomological degree.-/
  b : ℕ → C
  /-- Right term in each cohomological degree.-/
  c : ℕ → C
  /-- Arrow from the left term to the middle term.-/
  α : ∀ i, a i ⟶ b i
  /-- Arrow from the middle term to the right term.-/
  β : ∀ i, b i ⟶ c i
  /-- Connecting arrow to the next left term.-/
  γ : ∀ i, c i ⟶ a (i + 1)
  /-- Consecutive arrows `α` and `β` compose to zero.-/
  zeroAB : ∀ i, α i ≫ β i = 0
  /-- Consecutive arrows `β` and `γ` compose to zero.-/
  zeroBC : ∀ i, β i ≫ γ i = 0
  /-- Consecutive arrows `γ` and the next `α` compose to zero.-/
  zeroCA : ∀ i, γ i ≫ α (i + 1) = 0
  /-- Exactness at every middle term.-/
  exactAB : ∀ i, (ShortComplex.mk (α i) (β i) (zeroAB i)).Exact
  /-- Exactness at every right term.-/
  exactBC : ∀ i, (ShortComplex.mk (β i) (γ i) (zeroBC i)).Exact
  /-- Exactness at every positive-degree left term.-/
  exactCA : ∀ i, (ShortComplex.mk (γ i) (α (i + 1)) (zeroCA i)).Exact
  /-- The degree-zero left arrow has zero kernel.-/
  leftMono : Mono (α 0)
  /-- The final connecting image vanishes at the chosen bound.-/
  rightImageZero : IsZero (Abelian.image (γ n))
  /-- The chosen exact subcategory contains a zero object.-/
  zero_mem : P (0 : C)
  /-- Every left term belongs to the exact subcategory.-/
  a_mem : ∀ i, P (a i)
  /-- Every middle term belongs to the exact subcategory.-/
  b_mem : ∀ i, P (b i)
  /-- Every right term belongs to the exact subcategory.-/
  c_mem : ∀ i, P (c i)
  /-- Every image of `α` belongs to the exact subcategory.-/
  imageα_mem : ∀ i, P (Abelian.image (α i))
  /-- Every image of `β` belongs to the exact subcategory.-/
  imageβ_mem : ∀ i, P (Abelian.image (β i))
  /-- Every image of `γ` belongs to the exact subcategory.-/
  imageγ_mem : ∀ i, P (Abelian.image (γ i))

namespace BoundedLongExactData

variable {P} {n : ℕ}

/-- The exact Grothendieck group in which the long-exact-sequence classes live.-/
abbrev TargetGroup (_d : BoundedLongExactData P n) :=
  ExactGrothendieck.SubcategoryGroup C P

/-- Grothendieck class of the left term.-/
noncomputable def aClass (d : BoundedLongExactData P n) (i : ℕ) : d.TargetGroup :=
  ExactGrothendieck.subcategoryClassOf C P (d.a i) (d.a_mem i)

/-- Grothendieck class of the middle term.-/
noncomputable def bClass (d : BoundedLongExactData P n) (i : ℕ) : d.TargetGroup :=
  ExactGrothendieck.subcategoryClassOf C P (d.b i) (d.b_mem i)

/-- Grothendieck class of the right term.-/
noncomputable def cClass (d : BoundedLongExactData P n) (i : ℕ) : d.TargetGroup :=
  ExactGrothendieck.subcategoryClassOf C P (d.c i) (d.c_mem i)

/-- Grothendieck class of the image of `α`.-/
noncomputable def imageαClass (d : BoundedLongExactData P n) (i : ℕ) : d.TargetGroup :=
  ExactGrothendieck.subcategoryClassOf C P (Abelian.image (d.α i)) (d.imageα_mem i)

/-- Grothendieck class of the image of `β`.-/
noncomputable def imageβClass (d : BoundedLongExactData P n) (i : ℕ) : d.TargetGroup :=
  ExactGrothendieck.subcategoryClassOf C P (Abelian.image (d.β i)) (d.imageβ_mem i)

/-- Incoming connecting-image class, with the degree-zero boundary set to zero.-/
noncomputable def boundaryClass (d : BoundedLongExactData P n) : ℕ → d.TargetGroup
  | 0 => 0
  | i + 1 =>
      ExactGrothendieck.subcategoryClassOf C P (Abelian.image (d.γ i)) (d.imageγ_mem i)

/-- A genuine bounded long exact sequence canonically supplies the image-class witness used by
`derivedPushforward`.-/
noncomputable def toLongExactWitness (d : BoundedLongExactData P n) :
    LongExactWitness n d.aClass d.bClass d.cClass where
  u := d.imageαClass
  v := d.imageβClass
  w := d.boundaryClass
  leftBoundary := rfl
  rightBoundary := by
    change ExactGrothendieck.subcategoryClassOf C P
      (Abelian.image (d.γ n)) (d.imageγ_mem n) = 0
    exact ExactGrothendieck.subcategoryClassOf_isZero C P
      (d.imageγ_mem n) d.rightImageZero
  leftDecomposition i := by
    cases i with
    | zero =>
        letI : Mono (d.α 0) := d.leftMono
        change ExactGrothendieck.subcategoryClassOf C P (d.a 0) (d.a_mem 0) =
          0 + ExactGrothendieck.subcategoryClassOf C P
            (Abelian.image (d.α 0)) (d.imageα_mem 0)
        rw [zero_add]
        exact ExactGrothendieck.subcategoryClassOf_iso C P
          (d.a_mem 0) (d.imageα_mem 0) d.zero_mem (Limits.isZero_zero C)
          (asIso (Abelian.factorThruImage (d.α 0)))
    | succ i =>
        exact subcategoryClassOf_eq_image_add_image P
          (d.γ i) (d.α (i + 1)) (d.zeroCA i) (d.exactCA i)
          (d.imageγ_mem i) (d.a_mem (i + 1)) (d.imageα_mem (i + 1))
  middleDecomposition i :=
    subcategoryClassOf_eq_image_add_image P
      (d.α i) (d.β i) (d.zeroAB i) (d.exactAB i)
      (d.imageα_mem i) (d.b_mem i) (d.imageβ_mem i)
  rightDecomposition i :=
    subcategoryClassOf_eq_image_add_image P
      (d.β i) (d.γ i) (d.zeroBC i) (d.exactBC i)
      (d.imageβ_mem i) (d.c_mem i) (d.imageγ_mem i)

end BoundedLongExactData

/-- A higher-image system in an abelian category, equipped for every exact source triple with a
bounded genuine long exact sequence whose three columns are the chosen higher-image objects.-/
structure BoundedLongExactSystem
    (Object : Type w) (Exact : Object → Object → Object → Prop) (n : ℕ) where
  /-- Higher-image object in each degree.-/
  higher : Object → ℕ → C
  /-- Every higher-image object belongs to the selected exact subcategory.-/
  higher_mem : ∀ X i, P (higher X i)
  /-- Genuine bounded long-exact data attached to every exact source triple.-/
  sequence : ∀ X Y Z, Exact X Y Z → BoundedLongExactData P n
  /-- The left column is the higher-image family of the left source object.-/
  sequence_a : ∀ X Y Z (h : Exact X Y Z) i, (sequence X Y Z h).a i = higher X i
  /-- The middle column is the higher-image family of the middle source object.-/
  sequence_b : ∀ X Y Z (h : Exact X Y Z) i, (sequence X Y Z h).b i = higher Y i
  /-- The right column is the higher-image family of the right source object.-/
  sequence_c : ∀ X Y Z (h : Exact X Y Z) i, (sequence X Y Z h).c i = higher Z i

namespace BoundedLongExactSystem

variable {P} {Object : Type w} {Exact : Object → Object → Object → Prop} {n : ℕ}

/-- Grothendieck class of a higher-image object.-/
noncomputable def higherClass (s : BoundedLongExactSystem P Object Exact n)
    (X : Object) (i : ℕ) : ExactGrothendieck.SubcategoryGroup C P :=
  ExactGrothendieck.subcategoryClassOf C P (s.higher X i) (s.higher_mem X i)

/-- The genuine long exact sequence attached to an exact triple yields the class-level witness
for the selected higher-image system.-/
noncomputable def longExactWitness (s : BoundedLongExactSystem P Object Exact n)
    (X Y Z : Object) (h : Exact X Y Z) :
    LongExactWitness n (s.higherClass X) (s.higherClass Y) (s.higherClass Z) := by
  let d := s.sequence X Y Z h
  have W := d.toLongExactWitness
  have ha : d.aClass = s.higherClass X := by
    funext i
    unfold BoundedLongExactData.aClass higherClass
    have hi : d.a i = s.higher X i := s.sequence_a X Y Z h i
    exact congrArg (fun E : {E : C // P E} ↦
      ExactGrothendieck.classOf {E : C // P E}
        (ExactGrothendieck.shortExactIn C P) E) (Subtype.ext hi)
  have hb : d.bClass = s.higherClass Y := by
    funext i
    unfold BoundedLongExactData.bClass higherClass
    have hi : d.b i = s.higher Y i := s.sequence_b X Y Z h i
    exact congrArg (fun E : {E : C // P E} ↦
      ExactGrothendieck.classOf {E : C // P E}
        (ExactGrothendieck.shortExactIn C P) E) (Subtype.ext hi)
  have hc : d.cClass = s.higherClass Z := by
    funext i
    unfold BoundedLongExactData.cClass higherClass
    have hi : d.c i = s.higher Z i := s.sequence_c X Y Z h i
    exact congrArg (fun E : {E : C // P E} ↦
      ExactGrothendieck.classOf {E : C // P E}
        (ExactGrothendieck.shortExactIn C P) E) (Subtype.ext hi)
  rw [ha, hb, hc] at W
  exact W

/-- Derived pushforward canonically constructed from a system of genuine bounded long exact
sequences.-/
noncomputable def toDerivedPushforward (s : BoundedLongExactSystem P Object Exact n) :
    ExactGrothendieck.Group Object Exact →+
      ExactGrothendieck.SubcategoryGroup C P :=
  derivedPushforward n s.higherClass s.longExactWitness

/--
@isnad1 id=eq.0h7v.s8.1e2444ab92fe from=translated src=- shape=8e3836d0 vocab=d2dde4d7
-/
@[simp]
theorem toDerivedPushforward_classOf (s : BoundedLongExactSystem P Object Exact n)
    (X : Object) :
    s.toDerivedPushforward (ExactGrothendieck.classOf Object Exact X) =
      alternatingSum n (s.higherClass X) :=
  derivedPushforward_classOf n s.higherClass s.longExactWitness X

end BoundedLongExactSystem

end GrothendieckRiemannRoch
