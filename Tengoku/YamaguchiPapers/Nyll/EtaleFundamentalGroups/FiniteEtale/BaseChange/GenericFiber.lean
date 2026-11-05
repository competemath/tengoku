/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Compositum
import Tengoku.Seed.RingTheory.TensorProduct.Finite
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.FiniteEtale.GenericFiber.Component

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Selected generic components after finite-etale base change

This file packages the generic-fibre bookkeeping needed after a finite-etale
base change.  The generic fibre of `B ⊗[A] T` over a fraction field `K` of
`B` is canonically `K ⊗[A] T`.  A surjective map from that tensor product to
a field selects a maximal component by its kernel.  The normalization of the
selected field is finite etale over `B`.

The final theorem specializes the target field to an actual compositum in a
fixed ambient field, using the product-map API from ClassFieldTheory.
-/

noncomputable section

namespace EtaleFundamentalGroups

open scoped TensorProduct

universe uA uB uT uK uF uE uΩ

/-- Reassociate the generic fibre of a base-changed algebra:
`(B ⊗[A] T) ⊗[B] K ≃ K ⊗[A] T`.

The source uses the right `K`-algebra structure.-/
def baseChangeGenericFiberEquiv
    (A : Type uA) (B : Type uB) (T : Type uT) (K : Type uK)
    [CommRing A] [CommRing B] [CommRing T] [CommRing K]
    [Algebra A B] [Algebra A T] [Algebra B K]
    [Algebra A K] [IsScalarTower A B K] :
    letI : Algebra K ((B ⊗[A] T) ⊗[B] K) :=
      Algebra.TensorProduct.rightAlgebra
    ((B ⊗[A] T) ⊗[B] K) ≃ₐ[K] (K ⊗[A] T) := by
  letI : Algebra K ((B ⊗[A] T) ⊗[B] K) :=
    Algebra.TensorProduct.rightAlgebra
  exact
    (Algebra.TensorProduct.commRight B K (B ⊗[A] T)).symm.trans
      (Algebra.TensorProduct.cancelBaseChange A B K K T)

/-- If the generic fibre of `T / A` is identified with `E / F`, extending
the fraction field from `F` to `K` identifies `K ⊗[A] T` with
`K ⊗[F] E`.-/
def iteratedGenericFiberEquiv
    (A : Type uA) (F : Type uF) (K : Type uK)
    (T : Type uT) (E : Type uE)
    [CommRing A] [CommRing F] [CommRing K] [CommRing T] [CommRing E]
    [Algebra A F] [Algebra A K] [Algebra F K] [IsScalarTower A F K]
    [Algebra A T] [Algebra F E]
    (e : (F ⊗[A] T) ≃ₐ[F] E) :
    (K ⊗[A] T) ≃ₐ[K] (K ⊗[F] E) :=
  (Algebra.TensorProduct.cancelBaseChange A F K K T).symm.trans
    (Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K) e)

/-- The kernel of a map from a generic fibre to a specified field.-/
abbrev selectedGenericFiberIdeal
    {R : Type uA} {T : Type uT} {K : Type uK} {Ω : Type uΩ}
    [CommRing R] [CommRing T] [Algebra R T]
    [CommRing K] [Algebra R K]
    [CommRing Ω] [Algebra R Ω]
    (f : (T ⊗[R] K) →ₐ[R] Ω) : Ideal (T ⊗[R] K) :=
  RingHom.ker f

/-- A surjective generic-fibre map to a field selects a maximal ideal.-/
theorem selectedGenericFiberIdeal_isMaximal
    {R : Type uA} {T : Type uT} {K : Type uK} {Ω : Type uΩ}
    [CommRing R] [CommRing T] [Algebra R T]
    [CommRing K] [Algebra R K]
    [Field Ω] [Algebra R Ω]
    (f : (T ⊗[R] K) →ₐ[R] Ω) (hf : Function.Surjective f) :
    (selectedGenericFiberIdeal f).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective f hf

/-- The component selected by a surjective generic-fibre map is the target
field itself.-/
def selectedGenericFiberComponentEquiv
    {R : Type uA} {T : Type uT} {K : Type uK} {Ω : Type uΩ}
    [CommRing R] [CommRing T] [Algebra R T]
    [CommRing K] [Algebra R K]
    [Field Ω] [Algebra R Ω]
    (f : (T ⊗[R] K) →ₐ[R] Ω) (hf : Function.Surjective f) :
    ((T ⊗[R] K) ⧸ selectedGenericFiberIdeal f) ≃ₐ[R] Ω := by
  simpa only [selectedGenericFiberIdeal] using
    (Ideal.quotientKerAlgEquivOfSurjective (f := f) hf)

open DiscreteValuationField.FieldCompositum

end EtaleFundamentalGroups

end
