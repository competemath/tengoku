/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.ClassfieldtheoryYamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Adele.Coordinates

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Joint local components of relative adeles and ideles

The archimedean and finite tensor components jointly determine an element
of `𝔸_K ⊗[K] L`.  This file records the corresponding injective
homomorphism on relative ideles.  Surjectivity onto the restricted local
product is handled separately, once integral compatibility with the local
tensor decomposition has been established.
-/

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section

universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

omit [NumberField L] in
/-- A local tensor component has the expected chosen-basis
coordinates at a finite place.
@isnad1 id=eq.0h5v.s13.939899b0ee5c from=translated src=- shape=d8552688 vocab=d502deb2
-/
@[simp]
theorem relativeAdeleFiniteComponent_basis_repr
    (z : RelativeAdeleRing K L)
    (w : HeightOneSpectrum (𝓞 K))
    (i : RelativeAdeleBasisIndex (K := K) (L := L)) :
    (Algebra.TensorProduct.basis
        (w.adicCompletion K)
        (relativeExtensionBasis
          (K := K) (L := L))).repr
        (relativeAdeleFiniteComponent
          (K := K) (L := L) w z) i =
      (relativeAdeleCoefficient
        (K := K) (L := L) z i).2 w := by
  classical
  rw [relativeAdeleFiniteComponent_eq_sum_tmul_coefficients]
  simp [relativeExtensionBasis, Finsupp.single_apply]

omit [NumberField L] in
/-- A local tensor component has the expected chosen-basis
coordinates at an infinite place.
@isnad1 id=eq.0h5v.s12.100377e38677 from=translated src=- shape=fa5a4ce2 vocab=2976dae5
-/
@[simp]
theorem relativeAdeleInfiniteComponent_basis_repr
    (z : RelativeAdeleRing K L)
    (w : InfinitePlace K)
    (i : RelativeAdeleBasisIndex (K := K) (L := L)) :
    (Algebra.TensorProduct.basis
        w.Completion
        (relativeExtensionBasis
          (K := K) (L := L))).repr
        (relativeAdeleInfiniteComponent
          (K := K) (L := L) w z) i =
      (relativeAdeleCoefficient
        (K := K) (L := L) z i).1 w := by
  classical
  rw [relativeAdeleInfiniteComponent_eq_sum_tmul_coefficients]
  simp [relativeExtensionBasis, Finsupp.single_apply]
  change
    (relativeAdeleCoefficient
        (K := K) (L := L) z i).1 w *
        algebraMap K w.Completion (1 : K) =
      (relativeAdeleCoefficient
        (K := K) (L := L) z i).1 w
  rw [map_one, mul_one]

omit [NumberField L] in
/-- Equality of every archimedean and finite tensor component implies
equality of relative adeles.
@isnad1 id=eq.2h4v.s12.09b789b63063 from=translated src=- shape=a31ffc79 vocab=1cb9e748
-/
theorem relativeAdele_ext_of_components
    {x y : RelativeAdeleRing K L}
    (hinfinite :
      ∀ w : InfinitePlace K,
        relativeAdeleInfiniteComponent
            (K := K) (L := L) w x =
          relativeAdeleInfiniteComponent
            (K := K) (L := L) w y)
    (hfinite :
      ∀ w : HeightOneSpectrum (𝓞 K),
        relativeAdeleFiniteComponent
            (K := K) (L := L) w x =
          relativeAdeleFiniteComponent
            (K := K) (L := L) w y) :
    x = y := by
  apply
    (relativeAdeleCoefficientLinearEquiv
      (K := K) (L := L)).injective
  funext i
  apply Prod.ext
  · funext w
    have h :=
      congrArg
        (fun z =>
          (Algebra.TensorProduct.basis
            w.Completion
            (relativeExtensionBasis
              (K := K) (L := L))).repr z i)
        (hinfinite w)
    change (relativeAdeleCoefficient (K := K) (L := L) x i).1 w =
      (relativeAdeleCoefficient (K := K) (L := L) y i).1 w
    simpa using h
  · apply DFunLike.coe_injective
    funext w
    have h :=
      congrArg
        (fun z =>
          (Algebra.TensorProduct.basis
            (w.adicCompletion K)
            (relativeExtensionBasis
              (K := K) (L := L))).repr z i)
        (hfinite w)
    change (relativeAdeleCoefficient (K := K) (L := L) x i).2 w =
      (relativeAdeleCoefficient (K := K) (L := L) y i).2 w
    simpa using h

/-- The unrestricted family of every archimedean and finite local
tensor unit group.-/
abbrev RelativeLocalTensorFamily :=
  (∀ w : InfinitePlace K,
      (w.Completion ⊗[K] L)ˣ) ×
    (∀ w : HeightOneSpectrum (𝓞 K),
      (w.adicCompletion K ⊗[K] L)ˣ)

/-- All local tensor components of a relative idele.-/
def relativeIdeleLocalComponents :
    RelativeIdeleGroup K L →*
      RelativeLocalTensorFamily (K := K) (L := L) where
  toFun z :=
    ⟨fun w =>
        RelativeIdeleGroup.infiniteComponent
          (K := K) (L := L) w z,
      fun w =>
        RelativeIdeleGroup.finiteComponent
          (K := K) (L := L) w z⟩
  map_one' := by
    apply Prod.ext
    · funext w
      exact map_one
        (RelativeIdeleGroup.infiniteComponent
          (K := K) (L := L) w)
    · funext w
      exact map_one
        (RelativeIdeleGroup.finiteComponent
          (K := K) (L := L) w)
  map_mul' x y := by
    apply Prod.ext
    · funext w
      exact map_mul
        (RelativeIdeleGroup.infiniteComponent
          (K := K) (L := L) w) x y
    · funext w
      exact map_mul
        (RelativeIdeleGroup.finiteComponent
          (K := K) (L := L) w) x y

omit [NumberField L] [FiniteDimensional K L] in
/--
@isnad1 id=eq.0h4v.s13.afd591b932cd from=translated src=- shape=065d711f vocab=74fcd895
-/
@[simp]
theorem relativeIdeleLocalComponents_infinite
    (z : RelativeIdeleGroup K L)
    (w : InfinitePlace K) :
    (relativeIdeleLocalComponents
      (K := K) (L := L) z).1 w =
      RelativeIdeleGroup.infiniteComponent
        (K := K) (L := L) w z :=
  rfl

omit [NumberField L] [FiniteDimensional K L] in
/--
@isnad1 id=eq.0h4v.s13.d1a0b42b7152 from=translated src=- shape=fabfd258 vocab=9b08e4f1
-/
@[simp]
theorem relativeIdeleLocalComponents_finite
    (z : RelativeIdeleGroup K L)
    (w : HeightOneSpectrum (𝓞 K)) :
    (relativeIdeleLocalComponents
      (K := K) (L := L) z).2 w =
      RelativeIdeleGroup.finiteComponent
        (K := K) (L := L) w z :=
  rfl

omit [NumberField L] in
/-- The complete local-component map is injective.
@isnad1 id=injectiv.0h2v.s12.06e43cdfd921 from=translated src=- shape=7030abac vocab=d8f8d2a9
-/
theorem relativeIdeleLocalComponents_injective :
    Function.Injective
      (relativeIdeleLocalComponents
        (K := K) (L := L)) := by
  intro x y hxy
  apply Units.ext
  apply relativeAdele_ext_of_components
  · intro w
    have h := congrArg (fun z => z.1 w) hxy
    exact congrArg Units.val h
  · intro w
    have h := congrArg (fun z => z.2 w) hxy
    exact congrArg Units.val h
