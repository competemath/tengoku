import Tengoku.Brauerinduction.BrauerInduction.Background.FDRep.Character.Basic
import Tengoku.Brauerinduction.BrauerInduction.Background.ClassFun.Maps

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Basic character identities for finite-dimensional representations

This file defines the character of a finite-dimensional representation as a
class function and proves its basic identities: evaluation, invariance under
isomorphism, and compatibility with standard constructions such as sums, tensor
products, duals, internal Homs, biproducts, and restriction.
-/
namespace Tengoku.Brauerinduction end Tengoku.Brauerinduction open Tengoku.Brauerinduction
universe u v

namespace Tengoku.Brauerinduction.ClassFun

open CategoryTheory

section character_def

variable {k : Type u} {G : Type v}
variable [Field k] [Group G]

/--
The character of a finite-dimensional representation, bundled as a class function.-/
noncomputable def character (V : FDRep k G) : ClassFun k G where
  toFun := V.character
  map_conj := by
    intro x y h
    exact FDRep.char_eq_of_isConj V h

/--
@isnad1 id=eq.0h4v.s5.480f4fe6fc0a from=translated src=- shape=4e0ce5d2 vocab=7669bc7b
-/
@[simp]
theorem char_apply (V : FDRep k G) (g : G) :
    ClassFun.character V g = V.character g :=
  rfl

end character_def

variable {k : Type u} {G : Type v} [Field k] [Group G]

/--
Character value on a product is unchanged when the two factors are swapped:
`χ(hg) = χ(gh)`.
@isnad1 id=eq.0h5v.s6.d7c734f1b922 from=translated src=- shape=3aed368e vocab=fd76b82b
-/
theorem char_mul_comm (V : FDRep k G) (g : G) (h : G) :
    ClassFun.character V (h * g) = ClassFun.character V (g * h) :=
      Representation.char_mul_comm V.ρ g h

/--
@isnad1 id=eq.0h3v.s8.01e1c762e2ee from=translated src=- shape=bbc781bd vocab=90020555
-/
@[simp]
lemma char_one (V : FDRep k G) :
    ClassFun.character V 1 = Module.finrank k V := by
  simp only [character, coe_mk, FDRep.char_one]

/--
Isomorphic representations have equal characters.
@isnad1 id=eq.0h5v.s6.586d4452c2ba from=translated src=- shape=29ea2d90 vocab=a51b0063
-/
lemma char_eq_of_iso
    {V W : FDRep k G} (e : V ≅ W) :
    ClassFun.character V = ClassFun.character W := by
  ext g
  exact congrFun (FDRep.char_eq_of_iso e) g

/--
The trivial representation has constant character `1`.
@isnad1 id=eq.0h2v.s5.f56ca102b239 from=translated src=- shape=7f4dcf24 vocab=9bc66872
-/
@[simp]
lemma char_trivial
    (k : Type u) (G : Type v)
    [Field k] [Group G] :
    ClassFun.character (FDRep.trivial k G) = (1 : ClassFun k G) := by
  ext g
  simp only [character, FDRep.char_trivial, coe_mk, Pi.one_apply, one_apply]

/--
The character of a binary product is the sum of the characters.
@isnad1 id=eq.0h4v.s6.fe2402049b9c from=translated src=- shape=7c813a74 vocab=4fcaa758
-/
@[simp]
lemma char_prod (V W : FDRep k G) :
    ClassFun.character (V.prod W) = ClassFun.character V + ClassFun.character W := by
  simp only [character, FDRep.char_prod]
  rfl
/--
The character of a tensor product is the product of the characters.
@isnad1 id=eq.0h4v.s6.9d256d6b321d from=translated src=- shape=7c813a74 vocab=7c79432a
-/
@[simp]
theorem char_tensor
    (V W : FDRep k G) :
    ClassFun.character (FDRep.tensor V W)
      =
    ClassFun.character V * ClassFun.character W := by
  ext g
  exact congrFun (FDRep.char_tensor V W) g

/--
The character of the dual representation is the involution of the character.
@isnad1 id=eq.0h3v.s5.4a0723fd885f from=translated src=- shape=1b7ac577 vocab=42b89ffd
-/
@[simp]
lemma char_dual (V : FDRep k G) :
    ClassFun.character (V.dual) = ClassFun.involution (ClassFun.character V) := by
  ext g
  change V.dual.character g = V.character g⁻¹
  exact FDRep.char_dual V g

/--
The character of the internal Hom representation is `χ_V(g⁻¹) * χ_W(g)`.
@isnad1 id=eq.0h5v.s6.45705bfb3386 from=translated src=- shape=568f59f6 vocab=7d853726
-/
@[simp]
lemma char_linHom (V W : FDRep k G) (g : G) :
    ClassFun.character (FDRep.linHom V W) g =
      V.character g⁻¹ * W.character g  := by
  simp only [character, coe_mk, FDRep.char_linHom_apply]

/--
The character of a finite biproduct is the sum of the characters.
@isnad1 id=eq.0h4v.s7.5a88327f4b4a from=translated src=- shape=3f22cc0e vocab=33ed9f23
-/
@[simp]
lemma char_biproduct
    {ι : Type} [Fintype ι]
    (V : ι → FDRep k G) :
    ClassFun.character (Limits.biproduct V)
      =
    ∑ i, ClassFun.character (V i) := by
  ext g
  change (Limits.biproduct V).character g =
    (∑ i, ClassFun.character (V i)) g
  rw [FDRep.char_biproduct]
  calc
    (∑ i, (V i).character) g
        = ∑ i, (V i).character g := by
            simp
    _   = ∑ i, ClassFun.character (V i) g := by
            rfl
    _   = (∑ i, ClassFun.character (V i)) g := by
            exact Eq.symm (sum_apply (fun i ↦ character (V i)) g)

section res

variable {k : Type u} [Field k]
variable {G : Type v} [Group G]

/--
Restricting the character of a representation agrees with the character of
the restricted representation.
@isnad1 id=eq.0h4v.s6.a318e4ec6181 from=translated src=- shape=19e50ec9 vocab=f0e181f4
-/
@[simp] theorem res_ofChar
    {H : Subgroup G} (V : FDRep k G) :
    ClassFun.res (G := G) (k := k) H (ClassFun.character V)
      =
    ClassFun.character (FDRep.res (k := k) (G := G) V H) := by
  ext h
  rfl

end res

end Tengoku.Brauerinduction.ClassFun
-- Tengoku: root names of this library moved to Tengoku.Brauerinduction so they do not collide with other libraries (generated)
