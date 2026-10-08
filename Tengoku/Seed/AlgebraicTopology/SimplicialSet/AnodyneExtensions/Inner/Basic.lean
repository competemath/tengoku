/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen, Joël Riou
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.AlgebraicTopology.Quasicategory.InnerFibration
public import Tengoku.Seed.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic
public import Tengoku.Seed.AlgebraicTopology.SimplicialSet.Presentable
public import Tengoku.Seed.CategoryTheory.SmallObject.Basic

/-!
# Inner anodyne extensions

Much of this file is mirrored from
`Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic`.

*Inner* anodyne extensions form a property of morphisms in the category of simplicial
sets. It contains *inner* horn inclusions and it is closed under coproducts, pushouts,
transfinite compositions and retracts. Equivalently, using the small
object argument, inner anodyne extensions can be defined (and are defined here)
as the class of morphisms that satisfy the left lifting property with respect
to the class of inner fibrations.

-/

public section

universe u

open CategoryTheory HomotopicalAlgebra Simplicial

namespace SSet

open MorphismProperty

/-- In the category of simplicial sets, an *inner* anodyne extension is a morphism
that has the left lifting property with respect to *inner* fibrations, where
an inner fibration is a morphism that has the right lifting property with respect
to inner horn inclusions. -/
@[expose, kerodon 01BR]
def innerAnodyneExtensions : MorphismProperty SSet.{u} := innerFibrations.llp
deriving IsMultiplicative, RespectsIso, IsStableUnderCobaseChange,
  IsStableUnderRetracts, IsStableUnderTransfiniteComposition,
  IsStableUnderCoproducts

/--
@isnad1 id=innerano.0h3v.s5.b3f9d17312f4 from=seed src=0 shape=31ca8f87 vocab=86e1740c
-/
lemma innerAnodyneExtensions.of_isIso {X Y : SSet.{u}} (f : X ⟶ Y) [IsIso f] :
    innerAnodyneExtensions f :=
  MorphismProperty.of_isIso innerAnodyneExtensions f

/--
@isnad1 id=eq.0h0v.s5.2477fc4ccf48 from=seed src=0 shape=e82b111c vocab=a36e4dfe
-/
lemma innerAnodyneExtensions_eq_llp_rlp :
    innerAnodyneExtensions.{u} = innerHornInclusions.rlp.llp :=
  rfl

/--
@isnad1 id=innerano.2h2v.s7.56ee40b6ae77 from=seed src=0 shape=d444b14a vocab=77dcc688
-/
lemma innerAnodyneExtensions.horn_ι {n : ℕ} {i : Fin (n + 1)}
    (h0 : 0 < i) (hn : i < Fin.last n) :
    innerAnodyneExtensions.{u} Λ[n, i].ι := by
  rw [innerAnodyneExtensions_eq_llp_rlp]
  exact le_llp_rlp _ _ (horn_ι_mem_innerHornInclusions h0 hn)

/--
@isnad1 id=le.0h0v.s6.9a5e4735102c from=seed src=0 shape=836e6cbb vocab=97879f9b
-/
lemma innerAnodyneExtensions_le : innerAnodyneExtensions ≤ anodyneExtensions.{u} := by
  rw [anodyneExtensions_eq_llp_rlp, innerAnodyneExtensions_eq_llp_rlp, le_llp_iff_le_rlp,
    rlp_llp_rlp]
  exact antitone_rlp innerHornInclusions_le_J

attribute [local instance] Cardinal.fact_isRegular_aleph0
  Cardinal.orderBotAleph0OrdToType

instance : MorphismProperty.IsSmall.{u} innerHornInclusions.{u} := by
  rw [innerHornInclusions_eq_iSup]
  have (n : ℕ) : MorphismProperty.IsSmall.{u}
    (MorphismProperty.ofHoms.{u}
      fun p : {p : Fin (n + 3) // 0 < p ∧ p < Fin.last (n + 2)} ↦ Λ[n + 2, p].ι) :=
    isSmall_ofHoms ..
  exact isSmall_iSup _

instance : IsCardinalForSmallObjectArgument innerHornInclusions.{u} Cardinal.aleph0.{u} where
  preservesColimit {A B X Y} i hi f hf := by
    have : IsFinitelyPresentable.{u} A := by
      simp only [innerHornInclusions_eq_iSup, iSup_iff] at hi
      obtain ⟨n, ⟨i⟩⟩ := hi
      infer_instance
    infer_instance

instance : HasSmallObjectArgument.{u} innerHornInclusions.{u} where
  exists_cardinal := ⟨.aleph0, inferInstance, inferInstance, inferInstance⟩

/--
@isnad1 id=eq.0h0v.s5.431eed84d951 from=seed src=0 shape=a3ba6194 vocab=571baf6e
-/
lemma innerAnodyneExtensions_eq_retracts_transfiniteCompositions :
    innerAnodyneExtensions = (transfiniteCompositions.{u}
      (coproducts.{u} innerHornInclusions.{u}).pushouts).retracts := by
  rw [innerAnodyneExtensions_eq_llp_rlp, llp_rlp_of_hasSmallObjectArgument]

/--
@isnad1 id=eq.0h0v.s5.221184e35357 from=seed src=0 shape=46760855 vocab=fb7a3f5d
-/
lemma innerAnodyneExtensions_eq_retracts_transfiniteCompositionsOfShape :
    innerAnodyneExtensions = (transfiniteCompositionsOfShape
      (coproducts.{u} innerHornInclusions.{u}).pushouts ℕ).retracts := by
  rw [innerAnodyneExtensions_eq_llp_rlp,
    SmallObject.llp_rlp_of_isCardinalForSmallObjectArgument_aleph0]

/-- In the category of simplicial sets, a strong *inner* anodyne extension is a morphism
which belongs to the closure of *inner* horn inclusions by pushouts, coproducts,
transfinite compositions (but not by retracts). We define this class here
by saying that `f : X ⟶ Y` is a strong inner anodyne extension if `f` is a monomorphism
and there exists a regular, *inner* pairing (in the sense of Moss) for the subcomplex
`Subcomplex.range f` of `Y`. -/
def strongInnerAnodyneExtensions : MorphismProperty SSet.{u} :=
  fun _ _ f ↦ Mono f ∧ ∃ (P : (Subcomplex.range f).Pairing) (_ : P.IsRegular), P.IsInner

/--
@isnad1 id=mono.0h4v.s5.ed39b9f5e896 from=seed src=0 shape=d03ea59f vocab=3f51247b
-/
lemma strongInnerAnodyneExtensions.mono {X Y : SSet.{u}} {f : X ⟶ Y}
    (hf : strongInnerAnodyneExtensions f) : Mono f := hf.1

/--
@isnad1 id=le.0h0v.s6.50c7ebf5b482 from=seed src=0 shape=836e6cbb vocab=cb0fe880
-/
lemma strongInnerAnodyneExtensions_le_strongAnodyneExtensions :
    strongInnerAnodyneExtensions.{u} ≤ strongAnodyneExtensions :=
  fun _ _ _ ⟨_, P, _, _⟩ ↦ ⟨inferInstance, P, inferInstance⟩

/--
@isnad1 id=strongin.0h3v.s4.4a12345254f1 from=seed src=0 shape=b84e066c vocab=1e418a4f
-/
lemma Subcomplex.Pairing.strongInnerAnodyneExtensions {X : SSet.{u}} {A : X.Subcomplex}
    (P : A.Pairing) [h₁ : P.IsRegular] [h₂ : P.IsInner] :
    strongInnerAnodyneExtensions A.ι :=
  ⟨inferInstance, Pairing.ofIso P (Iso.refl _)
    (by simp only [Iso.refl_hom, preimage_id, Subfunctor.range_ι]), inferInstance, inferInstance⟩

/--
@isnad1 id=iff.0h2v.s5.fe2a0041f761 from=seed src=0 shape=8ffee485 vocab=1e418a4f
-/
lemma strongInnerAnodyneExtensions_ι_iff {X : SSet.{u}} (A : X.Subcomplex) :
    strongInnerAnodyneExtensions A.ι ↔ ∃ (P : A.Pairing) (_ : P.IsRegular), P.IsInner :=
  ⟨fun hA ↦ by
    obtain ⟨_, P, _, ⟨_, rfl⟩⟩ :
        ∃ (B : X.Subcomplex) (P : B.Pairing) (h : P.IsRegular), P.IsInner ∧ B = A := by
      obtain ⟨_, P₁, _, P₂⟩ := hA
      exact ⟨_, P₁, inferInstance, ⟨P₂, by simp⟩⟩
    exact ⟨P, ⟨inferInstance, inferInstance⟩⟩,
  fun ⟨P, ⟨_, _⟩⟩ ↦ P.strongInnerAnodyneExtensions⟩

/--
@isnad1 id=innerano.0h3v.s4.3dca0b0cc055 from=seed src=0 shape=b84e066c vocab=8098581f
-/
lemma Subcomplex.Pairing.innerAnodyneExtensions {X : SSet.{u}} {A : X.Subcomplex}
    (P : A.Pairing) [P.IsRegular] [P.IsInner] :
    innerAnodyneExtensions A.ι :=
  transfiniteCompositionsOfShape_le _ _ _
    ⟨P.rankFunction.relativeCellComplex.toTransfiniteCompositionOfShape, fun j hj ↦ by
      refine (?_ : (_ : MorphismProperty _) ≤ _ ) _
        (P.rankFunction.relativeCellComplex.attachCells j hj).pushouts_coproducts
      simp only [pushouts_le_iff, coproducts_le_iff]
      rintro _ _ _ ⟨c⟩
      have h0 := Fin.pos_iff_ne_zero.mpr (IsInner.ne_zero c.s rfl)
      have hn := Fin.lt_last_iff_ne_last.mpr (IsInner.ne_last c.s rfl)
      have : NeZero c.dim := ⟨by grind⟩
      exact .horn_ι h0 hn⟩

instance : strongInnerAnodyneExtensions.{u}.RespectsIso where
  precomp e _ f hf := by
    obtain ⟨_, P, hP, hP'⟩ := hf
    refine ⟨inferInstance, P.ofIso (Iso.refl _) ?_, inferInstance, inferInstance⟩
    simp [Subcomplex.range_comp, Subcomplex.range_eq_top e, Subcomplex.image_top]
  postcomp e _ f hf := by
    obtain ⟨_, P, hP, hP'⟩ := hf
    refine ⟨inferInstance, P.ofIso (asIso e).symm ?_, inferInstance, inferInstance⟩
    simp [Subcomplex.preimage_inv, Subcomplex.range_comp]

/--
@isnad1 id=le.0h0v.s6.303bbad29e8b from=seed src=0 shape=836e6cbb vocab=a95f8e19
-/
lemma strongInnerAnodyneExtensions_le_innerAnodyneExtensions :
    strongInnerAnodyneExtensions.{u} ≤ innerAnodyneExtensions := by
  rintro X Y f ⟨_, P, _, _⟩
  rw [← Subfunctor.toRange_ι f]
  exact comp_mem _ _ _ (.of_isIso _) P.innerAnodyneExtensions

end SSet
