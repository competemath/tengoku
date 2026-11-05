/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.AclGeom.AclGeom.Correspondence.Composition
import Tengoku.Seed.Algebra.Group.MinimalAxioms

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Abstract group laws for the group-chunk route

This module assumes everywhere-defined multiplication and inverse operations
and constructs an abstract group from their total identities.  It does not
construct these operations from generic finite correspondences, extend
partial rational operations, or algebraize them to a group scheme.  Those
steps of blueprint Theorem `rational-group-chunk` remain open (issue #12):

* `RationalGroupChunk` records associativity and the two generic inverse
  identities in their everywhere-defined algebraic form;
* `RationalGroupChunk.toGroup` constructs the canonical group structure,
  proving rather than assuming the identity laws;
* `TranslationGroupChunk` records the faithful chart of left translations
  in the automorphism group of the normalized function field;
* `TranslationGroupChunk.translationHom` is that chart as an injective group
  homomorphism.

The historical M4a route is frozen pending the audit re-plan (#19).  These
abstract identities remain available as bookkeeping; no rational group-chunk
theorem follows from them without the missing geometric construction.

**Status:** abstract group-law bookkeeping; blueprint Theorem 8.2 is open (#12).

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

noncomputable section

/-- Total multiplication and inverse operations with associativity and
cancellation identities.  The legacy name records their intended use in the
rational group-chunk route; construction of this total data from the generic
hypotheses of blueprint Theorem 8.2 remains open (#12).-/
structure RationalGroupChunk (V : Type*) where
  /-- Multiplication defined on every pair of parameters.-/
  mul : V → V → V
  /-- Inverse defined on every parameter.-/
  inv : V → V
  /-- Associativity on every parameter triple.-/
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  /-- Left cancellation by the selected inverse.-/
  inv_mul_mul : ∀ a b, mul (inv a) (mul a b) = b
  /-- Right cancellation by the selected inverse.-/
  mul_mul_inv : ∀ a b, mul (mul b a) (inv a) = b

namespace RationalGroupChunk

variable {V : Type*} (C : RationalGroupChunk V)

/-- Transport a rational group chunk along an equivalence of its parameter
type.-/
def reindex {W : Type*} (D : RationalGroupChunk W) (e : V ≃ W) :
    RationalGroupChunk V where
  mul a b := e.symm (D.mul (e a) (e b))
  inv a := e.symm (D.inv (e a))
  mul_assoc a b c := by
    apply e.injective
    simp [D.mul_assoc]
  inv_mul_mul a b := by
    apply e.injective
    simp [D.inv_mul_mul]
  mul_mul_inv a b := by
    apply e.injective
    simp [D.mul_mul_inv]

@[simp] theorem reindex_mul {W : Type*} (D : RationalGroupChunk W)
    (e : V ≃ W) (a b : V) :
    (D.reindex e).mul a b = e.symm (D.mul (e a) (e b)) := rfl

@[simp] theorem reindex_inv {W : Type*} (D : RationalGroupChunk W)
    (e : V ≃ W) (a : V) :
    (D.reindex e).inv a = e.symm (D.inv (e a)) := rfl

/-- The left unit produced from a parameter `a`.-/
def leftUnit (a : V) : V := C.mul (C.inv a) a

/-- The right unit produced from a parameter `a`.-/
def rightUnit (a : V) : V := C.mul a (C.inv a)

/-- Every `leftUnit a` acts as a left identity.-/
theorem leftUnit_mul (a b : V) : C.mul (C.leftUnit a) b = b := by
  rw [leftUnit, C.mul_assoc]
  exact C.inv_mul_mul a b

/-- Every `rightUnit a` acts as a right identity.-/
theorem mul_rightUnit (a b : V) : C.mul b (C.rightUnit a) = b := by
  rw [rightUnit, ← C.mul_assoc]
  exact C.mul_mul_inv a b

/-- A left unit and a right unit necessarily coincide.-/
theorem leftUnit_eq_rightUnit (a b : V) : C.leftUnit a = C.rightUnit b := by
  calc
    C.leftUnit a = C.mul (C.leftUnit a) (C.rightUnit b) :=
      (C.mul_rightUnit b (C.leftUnit a)).symm
    _ = C.rightUnit b := C.leftUnit_mul a (C.rightUnit b)

/-- All parameter-dependent left units coincide.-/
theorem leftUnit_eq_leftUnit (a b : V) : C.leftUnit a = C.leftUnit b :=
  (C.leftUnit_eq_rightUnit a b).trans (C.leftUnit_eq_rightUnit b b).symm

/-- All parameter-dependent right units coincide.-/
theorem rightUnit_eq_rightUnit (a b : V) : C.rightUnit a = C.rightUnit b :=
  (C.leftUnit_eq_rightUnit a a).symm.trans (C.leftUnit_eq_rightUnit a b)

/-- The canonical group carried by a nonempty rational group chunk.

The identity is `i(a₀) * a₀` for an arbitrary parameter `a₀`;
`leftUnit_eq_leftUnit` proves independence of this choice.  The resulting
group multiplication and inverse are definitionally the chunk operations.-/
@[reducible] def toGroup [Nonempty V] : Group V := by
  let a₀ : V := Classical.choice inferInstance
  letI : Mul V := ⟨C.mul⟩
  letI : Inv V := ⟨C.inv⟩
  letI : One V := ⟨C.leftUnit a₀⟩
  exact Group.ofLeftAxioms
    (fun a b c ↦ C.mul_assoc a b c)
    (fun a ↦ C.leftUnit_mul a₀ a)
    (fun a ↦ C.leftUnit_eq_leftUnit a a₀)

end RationalGroupChunk

section TranslationChart

variable (k F V : Type*) [Field k] [Field F] [Algebra k F]

/-- A rational group chunk together with its faithful chart of left
translations on the normalized function field.  These are the germs `L_a`
in blueprint (8.2).-/
structure TranslationGroupChunk extends RationalGroupChunk V where
  /-- The birational left translation attached to a chart parameter.-/
  translation : V → (F ≃ₐ[k] F)
  /-- Composition of translations is chart multiplication.-/
  translation_mul : ∀ a b,
    translation (mul a b) = translation a * translation b
  /-- The selected inverse gives the inverse birational transformation.-/
  translation_inv : ∀ a, translation (inv a) = (translation a)⁻¹
  /-- The translation chart is generically faithful.-/
  translation_injective : Function.Injective translation

namespace TranslationGroupChunk

variable {k F V W : Type*} [Field k] [Field F] [Algebra k F]

/-- Transport a faithful translation chunk along an equivalence of its
parameter type, keeping the normalized function field fixed.-/
def reindex (C : TranslationGroupChunk k F W) (e : V ≃ W) :
    TranslationGroupChunk k F V where
  toRationalGroupChunk := C.toRationalGroupChunk.reindex e
  translation a := C.translation (e a)
  translation_mul a b := by
    change C.translation
      (e (e.symm (C.mul (e a) (e b)))) =
        C.translation (e a) * C.translation (e b)
    rw [e.apply_symm_apply]
    exact C.translation_mul _ _
  translation_inv a := by
    change C.translation (e (e.symm (C.inv (e a)))) =
      (C.translation (e a))⁻¹
    rw [e.apply_symm_apply]
    exact C.translation_inv _
  translation_injective := by
    intro a b h
    exact e.injective (C.translation_injective h)

@[simp] theorem reindex_translation
    (C : TranslationGroupChunk k F W) (e : V ≃ W) (a : V) :
    (C.reindex e).translation a = C.translation (e a) := rfl

variable (C : TranslationGroupChunk k F V) [Nonempty V]

/-- The multiplication and identity underlying the canonical chunk group,
exposed as the instance parameter needed by bundled homomorphisms.-/
@[reducible] def chunkMulOne : MulOne V where
  one := C.toRationalGroupChunk.leftUnit (Classical.choice inferInstance)
  mul := C.mul

/-- The faithful translation chart as a group homomorphism into the
`k`-automorphism group of the normalized function field.-/
def translationHom : @MonoidHom V (F ≃ₐ[k] F) C.chunkMulOne inferInstance := by
  letI : MulOne V := C.chunkMulOne
  let a₀ : V := Classical.choice inferInstance
  refine
    { toFun := C.translation
      map_one' := ?_
      map_mul' := C.translation_mul }
  change C.translation (C.toRationalGroupChunk.leftUnit a₀) = 1
  calc
    C.translation (C.toRationalGroupChunk.leftUnit a₀) =
        C.translation (C.inv a₀) * C.translation a₀ := C.translation_mul _ _
    _ = (C.translation a₀)⁻¹ * C.translation a₀ := by rw [C.translation_inv]
    _ = 1 := inv_mul_cancel _

end TranslationGroupChunk

end TranslationChart

end

end AclGeom
