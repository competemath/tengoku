/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Homology.HomotopyCategory.KInjective
public import Tengoku.Seed.Algebra.Homology.CochainComplexOpposite

/-!
# K-projective cochain complexes

We define the notion of K-projective cochain complex in an abelian category,
and show that bounded above complexes of projective objects are K-projective.

## TODO (@joelriou)
* Provide an API for computing `Ext`-groups using a projective resolution

## References
* [N. Spaltenstein, *Resolutions of unbounded complexes*][spaltenstein1998]

-/

@[expose] public section

open CategoryTheory Limits Preadditive Opposite

namespace CochainComplex

open HomComplex

variable {C : Type*} [Category* C] [Abelian C]

-- TODO (@joelriou): show that this definition is equivalent to the
-- original definition by Spaltenstein saying that whenever `L`
-- is acyclic, then `HomComplex K L` is acyclic. (The condition below
-- is equivalent to the acyclicity of `HomComplex K L` in degree
-- `0`, and the general case follows by shifting `L`.)
/-- A cochain complex `K` is K-projective if any morphism `K ⟶ L`
with `L` acyclic is homotopic to zero. -/
class IsKProjective (K : CochainComplex C ℤ) : Prop where
  nonempty_homotopy_zero {L : CochainComplex C ℤ} (f : K ⟶ L) :
    L.Acyclic → Nonempty (Homotopy f 0)

/-- A choice of homotopy to zero for a morphism from a
K-projective cochain complex to an acyclic cochain complex. -/
noncomputable irreducible_def IsKProjective.homotopyZero
    {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (hL : L.Acyclic) [K.IsKProjective] :
    Homotopy f 0 :=
  (IsKProjective.nonempty_homotopy_zero f hL).some

lemma _root_.HomotopyEquiv.isKProjective {K₁ K₂ : CochainComplex C ℤ}
    (e : HomotopyEquiv K₁ K₂)
    [K₁.IsKProjective] : K₂.IsKProjective where
  nonempty_homotopy_zero {L} f hL :=
    ⟨Homotopy.trans (Homotopy.trans (.ofEq (by simp))
      ((e.homotopyInvHomId.symm.compRight f).trans (.ofEq (by simp))))
        (((IsKProjective.homotopyZero (e.hom ≫ f) hL).compLeft e.inv).trans (.ofEq (by simp)))⟩

/--
@isnad1 id=iskproje.0h4v.s7.b616d0c8ea61 from=seed src=0 shape=e030ae96 vocab=13e664fd
-/
lemma isKProjective_of_iso {K₁ K₂ : CochainComplex C ℤ} (e : K₁ ≅ K₂)
    [K₁.IsKProjective] :
    K₂.IsKProjective :=
  (HomotopyEquiv.ofIso e).isKProjective

/--
@isnad1 id=iff.0h4v.s7.9e0fdb6f6fea from=seed src=0 shape=c4e3914e vocab=13e664fd
-/
lemma isKProjective_iff_of_iso {K₁ K₂ : CochainComplex C ℤ} (e : K₁ ≅ K₂) :
    K₁.IsKProjective ↔ K₂.IsKProjective :=
  ⟨fun _ ↦ isKProjective_of_iso e, fun _ ↦ isKProjective_of_iso e.symm⟩

/--
@isnad1 id=iff.0h2v.s7.ac94de926788 from=seed src=0 shape=fc552400 vocab=efdf3912
-/
lemma isKProjective_iff_leftOrthogonal (K : CochainComplex C ℤ) :
    K.IsKProjective ↔
      (HomotopyCategory.subcategoryAcyclic C).leftOrthogonal
        ((HomotopyCategory.quotient _ _).obj K) := by
  refine ⟨fun _ L f hL ↦ ?_,
      fun hK ↦ ⟨fun {L} f hL ↦ ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩⟩
  · obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective L
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective f
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hL
    rw [HomotopyCategory.eq_of_homotopy f 0 (IsKProjective.homotopyZero f hL), Functor.map_zero]
  · rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hL
    rw [hK ((HomotopyCategory.quotient _ _).map f) hL, Functor.map_zero]

/--
@isnad1 id=leftorth.0h2v.s7.3aacffce2a12 from=seed src=0 shape=e3cffc10 vocab=efdf3912
-/
lemma IsKProjective.leftOrthogonal (K : CochainComplex C ℤ) [K.IsKProjective] :
    (HomotopyCategory.subcategoryAcyclic C).leftOrthogonal
        ((HomotopyCategory.quotient _ _).obj K) := by
  rwa [← isKProjective_iff_leftOrthogonal]

instance (K : CochainComplex C ℤ) [hK : K.IsKProjective] (n : ℤ) :
    (K⟦n⟧).IsKProjective := by
  rw [isKProjective_iff_leftOrthogonal] at hK ⊢
  exact ObjectProperty.prop_of_iso _
    (((HomotopyCategory.quotient C (.up ℤ)).commShiftIso n).symm.app K)
    ((HomotopyCategory.subcategoryAcyclic C).leftOrthogonal.le_shift n _ hK)

/--
@isnad1 id=iff.0h3v.s7.0725b10512dd from=seed src=0 shape=42586b63 vocab=9347c108
-/
lemma isKProjective_shift_iff (K : CochainComplex C ℤ) (n : ℤ) :
    (K⟦n⟧).IsKProjective ↔ K.IsKProjective :=
  ⟨fun _ ↦ isKProjective_of_iso (show K⟦n⟧⟦-n⟧ ≅ K from (shiftEquiv _ n).unitIso.symm.app K),
    fun _ ↦ inferInstance⟩

/--
@isnad1 id=iskproje.1h2v.s8.9098e5b46e6a from=seed src=0 shape=3b39e62d vocab=39a032ad
-/
lemma isKProjective_of_op {K : CochainComplex C ℤ}
    (hK : IsKInjective ((opEquivalence C).functor.obj (op K))) :
    K.IsKProjective where
  nonempty_homotopy_zero {L} f hL :=
    ⟨homotopyUnop ((IsKInjective.homotopyZero
      ((opEquivalence C).functor.map f.op) (acyclic_op hL)).trans
        (.ofEq (by simp)))⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
attribute [local simp] opEquivalence ChainComplex.cochainComplexEquivalence in
open Cochain.InductionUp in
/--
@isnad1 id=iskproje.0h3v.s6.b6a22f4c7594 from=seed src=0 shape=9785c443 vocab=0b8ac723
-/
lemma isKProjective_of_projective (K : CochainComplex C ℤ) (d : ℤ)
    [K.IsStrictlyLE d] [∀ (n : ℤ), Projective (K.X n)] :
    K.IsKProjective := by
  let L := ((opEquivalence C).functor.obj (op K))
  have (n : ℤ) : Injective (L.X n) := by
    dsimp [L]
    infer_instance
  have : L.IsStrictlyGE (-d) := by
    rw [isStrictlyGE_iff]
    intro i hi
    exact (K.isZero_of_isStrictlyLE d _ (by dsimp; lia)).op
  exact isKProjective_of_op (isKInjective_of_injective L (-d))

instance (K : ChainComplex C ℕ) [∀ n, Projective (K.X n)] :
    CochainComplex.IsKProjective (K.extend ComplexShape.embeddingDownNat) :=
  CochainComplex.isKProjective_of_projective _ 0

end CochainComplex
