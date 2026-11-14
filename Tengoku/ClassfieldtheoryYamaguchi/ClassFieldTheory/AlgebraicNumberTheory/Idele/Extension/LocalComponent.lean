/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.ClassfieldtheoryYamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.GaloisNorm

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.ClassfieldtheoryYamaguchi end Tengoku.ClassfieldtheoryYamaguchi open Tengoku.ClassfieldtheoryYamaguchi
set_option autoImplicit false

/-!
# Local components of relative adeles and ideles

For a finite place `v` of `K`, evaluation on the finite-adele coordinate is
a `K`-algebra homomorphism `𝔸_K → K_v`.  Scalar extension along `L/K`
therefore gives the actual local component map

`𝔸_K ⊗[K] L → K_v ⊗[K] L`.

This is the map needed to apply the local tensor decomposition and the local
norm calculation to a genuine relative idele.
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

/-- Evaluation of an adele at an infinite place, as a `K`-algebra
homomorphism.-/
def _root_.Tengoku.ClassfieldtheoryYamaguchi.infiniteAdeleComponentAlgHom
    (v : InfinitePlace K) :
    NumberField.AdeleRing (𝓞 K) K →ₐ[K]
      v.Completion :=
  (Pi.evalAlgHom K
      (fun w : InfinitePlace K => w.Completion) v).comp
    (AlgHom.fst K
      (NumberField.InfiniteAdeleRing K)
      (FiniteAdeleRing (𝓞 K) K))

/--
@isnad1 id=eq.0h3v.s9.45607574d15c from=translated src=- shape=07cf9b88 vocab=bbbba3d6
-/
@[simp]
theorem _root_.Tengoku.ClassfieldtheoryYamaguchi.infiniteAdeleComponentAlgHom_apply
    (v : InfinitePlace K)
    (a : NumberField.AdeleRing (𝓞 K) K) :
    infiniteAdeleComponentAlgHom v a = a.1 v :=
  rfl

/--
@isnad1 id=eq.0h3v.s9.df136c57a761 from=translated src=- shape=a72abcd8 vocab=37a0e62b
-/
@[simp]
theorem _root_.Tengoku.ClassfieldtheoryYamaguchi.infiniteAdeleComponentAlgHom_algebraMap
    (v : InfinitePlace K) (x : K) :
    infiniteAdeleComponentAlgHom v
        (algebraMap K
          (NumberField.AdeleRing (𝓞 K) K) x) =
      algebraMap K v.Completion x :=
  rfl

/-- The relative-adele component at an infinite place:
`𝔸_K ⊗[K] L → K_v ⊗[K] L`.-/
def _root_.Tengoku.ClassfieldtheoryYamaguchi.relativeAdeleInfiniteComponent
    (v : InfinitePlace K) :
    RelativeAdeleRing K L →ₐ[K]
      v.Completion ⊗[K] L :=
  Algebra.TensorProduct.map
    (infiniteAdeleComponentAlgHom v)
    (AlgHom.id K L)

omit [NumberField L] [FiniteDimensional K L] in
/--
@isnad1 id=eq.0h5v.s11.5064eeb91ae9 from=translated src=- shape=f20a83ff vocab=7239895f
-/
@[simp]
theorem _root_.Tengoku.ClassfieldtheoryYamaguchi.relativeAdeleInfiniteComponent_tmul
    (v : InfinitePlace K)
    (a : NumberField.AdeleRing (𝓞 K) K) (x : L) :
    relativeAdeleInfiniteComponent
        (K := K) (L := L) v (a ⊗ₜ[K] x) =
      a.1 v ⊗ₜ[K] x := by
  simp [relativeAdeleInfiniteComponent]

/-- Evaluation of an adele at a finite place, as a `K`-algebra
homomorphism.-/
def _root_.Tengoku.ClassfieldtheoryYamaguchi.finiteAdeleComponentAlgHom
    (v : HeightOneSpectrum (𝓞 K)) :
    NumberField.AdeleRing (𝓞 K) K →ₐ[K]
      v.adicCompletion K :=
  { __ :=
      (RestrictedProduct.evalRingHom
        (fun w : HeightOneSpectrum (𝓞 K) =>
          w.adicCompletion K) v).comp
        (RingHom.snd
          (NumberField.InfiniteAdeleRing K)
          (FiniteAdeleRing (𝓞 K) K))
    commutes' := by
      intro x
      rfl }

/--
@isnad1 id=eq.0h3v.s9.534f35348812 from=translated src=- shape=2c9cace6 vocab=5de559a0
-/
@[simp]
theorem _root_.Tengoku.ClassfieldtheoryYamaguchi.finiteAdeleComponentAlgHom_apply
    (v : HeightOneSpectrum (𝓞 K))
    (a : NumberField.AdeleRing (𝓞 K) K) :
    finiteAdeleComponentAlgHom v a = a.2 v :=
  rfl

/--
@isnad1 id=eq.0h3v.s10.606bf1ec9cdb from=translated src=- shape=baa3a180 vocab=ac10e221
-/
@[simp]
theorem _root_.Tengoku.ClassfieldtheoryYamaguchi.finiteAdeleComponentAlgHom_algebraMap
    (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    finiteAdeleComponentAlgHom v
        (algebraMap K
          (NumberField.AdeleRing (𝓞 K) K) x) =
      algebraMap K (v.adicCompletion K) x :=
  rfl

omit [NumberField L] [FiniteDimensional K L] in
/-- The relative-adele component at a finite place:
`𝔸_K ⊗[K] L → K_v ⊗[K] L`.-/
def _root_.Tengoku.ClassfieldtheoryYamaguchi.relativeAdeleFiniteComponent
    (v : HeightOneSpectrum (𝓞 K)) :
    RelativeAdeleRing K L →ₐ[K]
      v.adicCompletion K ⊗[K] L :=
  Algebra.TensorProduct.map
    (finiteAdeleComponentAlgHom v)
    (AlgHom.id K L)

omit [NumberField L] [FiniteDimensional K L] in
/--
@isnad1 id=eq.0h5v.s11.907b86b10875 from=translated src=- shape=98aac0ef vocab=5be24ef8
-/
@[simp]
theorem _root_.Tengoku.ClassfieldtheoryYamaguchi.relativeAdeleFiniteComponent_tmul
    (v : HeightOneSpectrum (𝓞 K))
    (a : NumberField.AdeleRing (𝓞 K) K) (x : L) :
    relativeAdeleFiniteComponent (K := K) (L := L) v
        (a ⊗ₜ[K] x) =
      a.2 v ⊗ₜ[K] x := by
  simp [relativeAdeleFiniteComponent]

/-- The unit-valued infinite component of a relative idele.-/
def Tengoku.ClassfieldtheoryYamaguchi.RelativeIdeleGroup.infiniteComponent
    (v : InfinitePlace K) :
    RelativeIdeleGroup K L →*
      (v.Completion ⊗[K] L)ˣ :=
  Units.map
    (relativeAdeleInfiniteComponent
      (K := K) (L := L) v).toRingHom

omit [NumberField L] [FiniteDimensional K L] in
/--
@isnad1 id=eq.0h4v.s12.0e2cc9621359 from=translated src=- shape=89a2dbfa vocab=d5b31639
-/
@[simp]
theorem Tengoku.ClassfieldtheoryYamaguchi.RelativeIdeleGroup.infiniteComponent_coe
    (v : InfinitePlace K)
    (a : RelativeIdeleGroup K L) :
    ((RelativeIdeleGroup.infiniteComponent
        (K := K) (L := L) v a :
        (v.Completion ⊗[K] L)ˣ) :
        v.Completion ⊗[K] L) =
      relativeAdeleInfiniteComponent
        (K := K) (L := L) v
        (a : RelativeAdeleRing K L) :=
  rfl

/-- The unit-valued local component of a relative idele.-/
def Tengoku.ClassfieldtheoryYamaguchi.RelativeIdeleGroup.finiteComponent
    (v : HeightOneSpectrum (𝓞 K)) :
    RelativeIdeleGroup K L →*
      (v.adicCompletion K ⊗[K] L)ˣ :=
  Units.map
    (relativeAdeleFiniteComponent
      (K := K) (L := L) v).toRingHom

omit [NumberField L] [FiniteDimensional K L] in
/--
@isnad1 id=eq.0h4v.s12.43f9b981a08b from=translated src=- shape=e08da81b vocab=f61ae44b
-/
@[simp]
theorem Tengoku.ClassfieldtheoryYamaguchi.RelativeIdeleGroup.finiteComponent_coe
    (v : HeightOneSpectrum (𝓞 K))
    (a : RelativeIdeleGroup K L) :
    ((RelativeIdeleGroup.finiteComponent
        (K := K) (L := L) v a :
        (v.adicCompletion K ⊗[K] L)ˣ) :
        v.adicCompletion K ⊗[K] L) =
      relativeAdeleFiniteComponent
        (K := K) (L := L) v
        (a : RelativeAdeleRing K L) :=
  rfl

/-- The determinant norm on the local tensor algebra.-/
def _root_.Tengoku.ClassfieldtheoryYamaguchi.localTensorNorm
    (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K ⊗[K] L)ˣ →*
      (v.adicCompletion K)ˣ :=
  Units.map (Algebra.norm (v.adicCompletion K))

/-- Scalar extension of an archimedean base-field unit into its local
tensor algebra.-/
def _root_.Tengoku.ClassfieldtheoryYamaguchi.infiniteLocalIdeleInclusion
    (v : InfinitePlace K) :
    v.Completionˣ →*
      (v.Completion ⊗[K] L)ˣ :=
  Units.map
    (Algebra.TensorProduct.includeLeft
      (R := K) (S := K)
      (A := v.Completion) (B := L)).toRingHom

/-- Scalar extension of an extension-field unit into an archimedean
local tensor algebra.-/
def _root_.Tengoku.ClassfieldtheoryYamaguchi.infiniteLocalFieldIdeleInclusion
    (v : InfinitePlace K) :
    Lˣ →* (v.Completion ⊗[K] L)ˣ :=
  Units.map
    (Algebra.TensorProduct.includeRight
      (R := K) (A := v.Completion)
      (B := L)).toRingHom

omit [NumberField L] [FiniteDimensional K L] in
/-- The infinite component of a globally included idele is scalar
extension of its ordinary infinite component.
@isnad1 id=eq.0h4v.s13.66409f59f33a from=translated src=- shape=bd06ef47 vocab=69f2b40e
-/
@[simp]
theorem Tengoku.ClassfieldtheoryYamaguchi.RelativeIdeleGroup.infiniteComponent_inclusion
    (v : InfinitePlace K)
    (a : IdeleGroup K) :
    RelativeIdeleGroup.infiniteComponent
        (K := K) (L := L) v
        (RelativeIdeleGroup.inclusion K L a) =
      infiniteLocalIdeleInclusion
        (K := K) (L := L) v
        (IdeleGroup.infiniteComponent v a) := by
  apply Units.ext
  rfl

omit [NumberField L] [FiniteDimensional K L] in
/-- The infinite component of a principal relative idele is the
diagonal extension-field unit in the local tensor algebra.
@isnad1 id=eq.0h4v.s13.43192c8fc003 from=translated src=- shape=f423c350 vocab=757d3fdc
-/
@[simp]
theorem Tengoku.ClassfieldtheoryYamaguchi.RelativeIdeleGroup.infiniteComponent_principalIdele
    (v : InfinitePlace K) (x : Lˣ) :
    RelativeIdeleGroup.infiniteComponent
        (K := K) (L := L) v
        (RelativeIdeleGroup.principalIdele K L x) =
      infiniteLocalFieldIdeleInclusion
        (K := K) (L := L) v x := by
  apply Units.ext
  rfl

/-- Scalar extension of a local base-field unit into the local tensor
algebra.-/
def _root_.Tengoku.ClassfieldtheoryYamaguchi.localIdeleInclusion
    (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K)ˣ →*
      (v.adicCompletion K ⊗[K] L)ˣ :=
  Units.map
    (Algebra.TensorProduct.includeLeft
      (R := K) (S := K)
      (A := v.adicCompletion K) (B := L)).toRingHom

omit [NumberField L] [FiniteDimensional K L] in
/-- The local component of the globally included idele is the scalar
extension of its ordinary local component.
@isnad1 id=eq.0h4v.s13.afb70897792b from=translated src=- shape=a1a43062 vocab=dc16d6ef
-/
@[simp]
theorem Tengoku.ClassfieldtheoryYamaguchi.RelativeIdeleGroup.finiteComponent_inclusion
    (v : HeightOneSpectrum (𝓞 K))
    (a : IdeleGroup K) :
    RelativeIdeleGroup.finiteComponent
        (K := K) (L := L) v
        (RelativeIdeleGroup.inclusion K L a) =
      localIdeleInclusion (K := K) (L := L) v
        (IdeleGroup.finiteComponent v a) := by
  apply Units.ext
  rfl

/-- Scalar extension of an extension-field unit into the local tensor
algebra.-/
def _root_.Tengoku.ClassfieldtheoryYamaguchi.localFieldIdeleInclusion
    (v : HeightOneSpectrum (𝓞 K)) :
    Lˣ →* (v.adicCompletion K ⊗[K] L)ˣ :=
  Units.map
    (Algebra.TensorProduct.includeRight
      (R := K) (A := v.adicCompletion K)
      (B := L)).toRingHom

omit [NumberField L] [FiniteDimensional K L] in
/-- The local component of a principal relative idele is the diagonal
extension-field unit in the local tensor algebra.
@isnad1 id=eq.0h4v.s13.e30667c3402e from=translated src=- shape=f64b1e9d vocab=410a04e7
-/
@[simp]
theorem Tengoku.ClassfieldtheoryYamaguchi.RelativeIdeleGroup.finiteComponent_principalIdele
    (v : HeightOneSpectrum (𝓞 K)) (x : Lˣ) :
    RelativeIdeleGroup.finiteComponent
        (K := K) (L := L) v
        (RelativeIdeleGroup.principalIdele K L x) =
      localFieldIdeleInclusion (K := K) (L := L) v x := by
  apply Units.ext
  rfl
-- Tengoku: root names of this library moved to Tengoku.ClassfieldtheoryYamaguchi so they do not collide with other libraries (generated)
