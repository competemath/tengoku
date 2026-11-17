import Tengoku.StringDiagramsLean.StringDiagrams.Biadjunction.Trace
import Tengoku.Seed.CategoryTheory.Opposites

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Pivotal structures on bicategories: rotation of 2-morphisms

A pivotal structure `Pivotal B` chooses for every 1-morphism `f : a ⟶ b` a biadjoint
`dual f : b ⟶ a` and a biadjunction `biadj f : f ⊣⊢ dual f` such that *every* 2-morphism
`α : f ⟶ f'` is cyclic for the chosen biadjunctions: its right and left mates agree. The
common mate is the rotation `rotate α : dual f' ⟶ dual f` of `α` (by a half turn, in either
direction). This is the formal content of the rotation invariance of string diagrams:

* `rotate` is a contravariant functor on each hom category (`rotate_id`, `rotate_comp`,
  `rotateFunctor`), and a bijection (`rotateEquiv`);
* rotating back, using the exchanged biadjunctions `(biadj f).symm`, recovers `α`
  (`rightMate_symm_rotate`, `leftMate_symm_rotate`), whichever direction is used;
* rotating twice with the chosen biadjunctions is conjugation by the canonical comparison
  `pivotalIso f : f ≅ dual (dual f)` (`rotate_rotate`), which is therefore natural
  (`pivotalIso_hom_naturality`);
* rotation is compatible with whiskering, up to the canonical comparisons
  `dualCompIso f h : dual (f ≫ h) ≅ dual h ≫ dual f` (`rotate_whiskerRight`,
  `rotate_whiskerLeft`);
* traces are cyclic: `rightTrace (α ≫ β) = rightTrace (β ≫ α)` for all `α : f ⟶ f'`,
  `β : f' ⟶ f` (`Pivotal.rightTrace_comp_comm`, `Pivotal.leftTrace_comp_comm`).

The comparisons `pivotalIso` and `dualCompIso` are defined using the adjunctions in which
`dual f` is a left adjoint (resp. `f ≫ h` is a left adjoint); no condition is imposed on how
the chosen biadjunctions of composites relate to composite biadjunctions, so the natural
isomorphism `pivotalIso` is not asserted to be compatible with composition.
-/

namespace StringDiagrams

open CategoryTheory Bicategory

universe w v u

/-- A pivotal structure on a bicategory: a chosen biadjoint `dual f` of every 1-morphism `f`,
with a biadjunction `biadj f : f ⊣⊢ dual f`, such that every 2-morphism is cyclic for the
chosen biadjunctions.-/
class Pivotal (B : Type u) [Bicategory.{w, v} B] where
  /-- The chosen biadjoint.-/
  dual : ∀ {a b : B}, (a ⟶ b) → (b ⟶ a)
  /-- The chosen biadjunction.-/
  biadj : ∀ {a b : B} (f : a ⟶ b), f ⊣⊢ dual f
  /-- Every 2-morphism is cyclic for the chosen biadjunctions.-/
  isCyclic : ∀ {a b : B} {f f' : a ⟶ b} (α : f ⟶ f'), (biadj f).IsCyclic (biadj f') α

namespace Pivotal

open Biadjunction

variable {B : Type u} [Bicategory.{w, v} B] [Pivotal B] {a b c : B}

section Rotate

variable {f f' f'' : a ⟶ b}

/-- The rotation of a 2-morphism `α : f ⟶ f'`: its (right, equivalently left) mate for the
chosen biadjunctions.-/
def rotate (α : f ⟶ f') : dual f' ⟶ dual f :=
  rightMate (biadj f) (biadj f') α

/--
@isnad1 id=eq.0h6v.s9.81f038884718 from=translated src=- shape=b5a024fc vocab=cebe5f89
-/
theorem rotate_eq_rightMate (α : f ⟶ f') : rotate α = rightMate (biadj f) (biadj f') α := rfl

/--
@isnad1 id=eq.0h6v.s9.b58147e83567 from=translated src=- shape=b5a024fc vocab=47daa10e
-/
theorem rotate_eq_leftMate (α : f ⟶ f') : rotate α = leftMate (biadj f) (biadj f') α :=
  isCyclic α

/--
@isnad1 id=eq.0h4v.s7.ba4a5667b41d from=translated src=- shape=58a7e1dc vocab=2912ba1f
-/
@[simp]
theorem rotate_id (f : a ⟶ b) : rotate (𝟙 f) = 𝟙 (dual f) :=
  rightMate_id _

/--
@isnad1 id=eq.0h8v.s8.bfa8ece706d9 from=translated src=- shape=e3f7a14f vocab=290add7e
-/
@[simp]
theorem rotate_comp (α : f ⟶ f') (β : f' ⟶ f'') : rotate (α ≫ β) = rotate β ≫ rotate α :=
  rightMate_comp _ _ _ α β

/-- Rotation as a bijection.-/
def rotateEquiv (f f' : a ⟶ b) : (f ⟶ f') ≃ (dual f' ⟶ dual f) :=
  rightMate (biadj f) (biadj f')

/--
@isnad1 id=eq.0h6v.s9.ac5e31f8a63e from=translated src=- shape=dc12a5c6 vocab=aaa80d64
-/
@[simp]
theorem rotateEquiv_apply (α : f ⟶ f') : rotateEquiv f f' α = rotate α := rfl

/--
@isnad1 id=injectiv.0h5v.s7.e766e15b1e75 from=translated src=- shape=4857785f vocab=e53f0076
-/
theorem rotate_injective : Function.Injective (rotate : (f ⟶ f') → (dual f' ⟶ dual f)) :=
  (rotateEquiv f f').injective

/-- Rotation as a contravariant functor between hom categories.-/
@[simps]
def rotateFunctor (a b : B) : (a ⟶ b)ᵒᵖ ⥤ (b ⟶ a) where
  obj f := dual f.unop
  map α := rotate α.unop
  map_id _ := rotate_id _
  map_comp _ _ := rotate_comp _ _

/-- Rotating back with the exchanged biadjunctions (in the direction of the right mate)
recovers the original 2-morphism.
@isnad1 id=eq.0h6v.s9.1ffa20654bed from=translated src=- shape=3f723a67 vocab=886e07b6
-/
@[simp]
theorem rightMate_symm_rotate (α : f ⟶ f') :
    rightMate (biadj f').symm (biadj f).symm (rotate α) = α := by
  rw [rotate_eq_leftMate, rightMate_symm_leftMate]

/-- Rotating back with the exchanged biadjunctions (in the direction of the left mate)
recovers the original 2-morphism.
@isnad1 id=eq.0h6v.s9.1274dfad4623 from=translated src=- shape=3f723a67 vocab=1372c98b
-/
@[simp]
theorem leftMate_symm_rotate (α : f ⟶ f') :
    leftMate (biadj f').symm (biadj f).symm (rotate α) = α :=
  leftMate_symm_rightMate _ _ α

/-- The rotation of `α` is cyclic for the exchanged biadjunctions.
@isnad1 id=iscyclic.0h6v.s7.439daded1adf from=translated src=- shape=e6445922 vocab=5cd06d6d
-/
theorem isCyclic_rotate (α : f ⟶ f') : IsCyclic (biadj f').symm (biadj f).symm (rotate α) :=
  (isCyclic α).rightMate

end Rotate

/-! ## Double rotation -/

section Double

/-- The canonical comparison `f ≅ dual (dual f)`: `f` and `dual (dual f)` are both right
adjoints of `dual f`.-/
def pivotalIso (f : a ⟶ b) : f ≅ dual (dual f) :=
  conjugateIsoEquiv (biadj f).right (biadj (dual f)).left (Iso.refl _)

/--
@isnad1 id=eq.0h4v.s9.0a6b1ba631d5 from=translated src=- shape=f6d68649 vocab=cf94dd11
-/
theorem pivotalIso_hom (f : a ⟶ b) :
    (pivotalIso f).hom = rightMate (biadj (dual f)) (biadj f).symm (𝟙 (dual f)) := rfl

/-- Rotating twice is conjugation by the canonical comparisons `f ≅ dual (dual f)`.
@isnad1 id=eq.0h6v.s8.9ff2959d5497 from=translated src=- shape=d2e09971 vocab=81045f70
-/
theorem rotate_rotate {f f' : a ⟶ b} (α : f ⟶ f') :
    rotate (rotate α) = (pivotalIso f).inv ≫ α ≫ (pivotalIso f').hom := by
  rw [rotate, rightMate_eq_comp' _ (biadj f').symm _ (biadj f).symm, rightMate_symm_rotate]
  rfl

/-- The canonical comparison `f ≅ dual (dual f)` is natural.
@isnad1 id=eq.0h6v.s8.b56ea4cde7b3 from=translated src=- shape=38e55a8a vocab=fa2685d3
-/
theorem pivotalIso_hom_naturality {f f' : a ⟶ b} (α : f ⟶ f') :
    α ≫ (pivotalIso f').hom = (pivotalIso f).hom ≫ rotate (rotate α) := by
  rw [rotate_rotate, Iso.hom_inv_id_assoc]

end Double

/-! ## Whiskering -/

section Whisker

/-- The canonical comparison `dual (f ≫ h) ≅ dual h ≫ dual f`: both are right adjoints of
`f ≫ h`.-/
def dualCompIso (f : a ⟶ b) (h : b ⟶ c) : dual (f ≫ h) ≅ dual h ≫ dual f :=
  conjugateIsoEquiv (biadj (f ≫ h)).left ((biadj f).comp (biadj h)).left (Iso.refl _)

/-- Rotation commutes with right whiskering, up to the canonical comparisons.
@isnad1 id=eq.0h8v.s8.e4fa95090816 from=translated src=- shape=2fcb5f34 vocab=5e398e30
-/
theorem rotate_whiskerRight {f f' : a ⟶ b} (α : f ⟶ f') (h : b ⟶ c) :
    rotate (α ▷ h) = (dualCompIso f' h).hom ≫ dual h ◁ rotate α ≫ (dualCompIso f h).inv := by
  rw [rotate, rightMate_eq_comp' _ ((biadj f).comp (biadj h)) _ ((biadj f').comp (biadj h)),
    rightMate_whiskerRight]
  rfl

/-- Rotation commutes with left whiskering, up to the canonical comparisons.
@isnad1 id=eq.0h8v.s8.b85530e06270 from=translated src=- shape=b4fbcb82 vocab=5e398e30
-/
theorem rotate_whiskerLeft (h : c ⟶ a) {f f' : a ⟶ b} (α : f ⟶ f') :
    rotate (h ◁ α) = (dualCompIso h f').hom ≫ rotate α ▷ dual h ≫ (dualCompIso h f).inv := by
  rw [rotate, rightMate_eq_comp' _ ((biadj h).comp (biadj f)) _ ((biadj h).comp (biadj f')),
    rightMate_whiskerLeft]
  rfl

end Whisker

/-! ## Traces -/

section Trace

variable {f f' : a ⟶ b}

/-- The right trace for the chosen biadjunction.-/
abbrev rightTrace (α : f ⟶ f) : 𝟙 a ⟶ 𝟙 a := (biadj f).rightTrace α

/-- The left trace for the chosen biadjunction.-/
abbrev leftTrace (α : f ⟶ f) : 𝟙 b ⟶ 𝟙 b := (biadj f).leftTrace α

/--
@isnad1 id=eq.0h7v.s7.3625f6ec5be9 from=translated src=- shape=677a6854 vocab=6cbaf008
-/
theorem rightTrace_comp_comm (α : f ⟶ f') (β : f' ⟶ f) :
    rightTrace (α ≫ β) = rightTrace (β ≫ α) :=
  rightTrace_comp_comm_of_isCyclic_left (isCyclic α) β

/--
@isnad1 id=eq.0h7v.s7.85421914fc63 from=translated src=- shape=ff03e9cf vocab=1b1a68a0
-/
theorem leftTrace_comp_comm (α : f ⟶ f') (β : f' ⟶ f) :
    leftTrace (α ≫ β) = leftTrace (β ≫ α) :=
  leftTrace_comp_comm_of_isCyclic_left (isCyclic α) β

/-- The right trace of `α` is the left trace of its rotation, for the exchanged
biadjunction.
@isnad1 id=eq.0h5v.s7.25ac4a18c8e9 from=translated src=- shape=12a2fe7a vocab=7a70dd92
-/
theorem rightTrace_eq_leftTrace_rotate (α : f ⟶ f) :
    rightTrace α = (biadj f).symm.leftTrace (rotate α) :=
  rightTrace_eq_leftTrace_rightMate _ α

/-- The left trace of `α` is the right trace of its rotation, for the exchanged
biadjunction.
@isnad1 id=eq.0h5v.s7.ce068a9d5501 from=translated src=- shape=3822393c vocab=9cf49881
-/
theorem leftTrace_eq_rightTrace_rotate (α : f ⟶ f) :
    leftTrace α = (biadj f).symm.rightTrace (rotate α) :=
  leftTrace_eq_rightTrace_rightMate _ α

end Trace

end Pivotal

end StringDiagrams
