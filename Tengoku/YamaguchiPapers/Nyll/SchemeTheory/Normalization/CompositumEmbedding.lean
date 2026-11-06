/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.RingTheory.Ideal.GoingUp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Embedding a normalization into a compositum normalization

Suppose `L → Ω` is compatible with a base change `A → B`.  Every
element of the normalization of `A` in `L` maps to an element integral over
`B`, hence into the normalization of `B` in `Ω`.  This file constructs the
actual normalization embedding and uses integrality to lift a chosen prime.

No compositum field or prime is chosen here; those remain inputs produced by
the generic tensor-component construction.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe uA uB uL uO

/-- Enlarging the base ring enlarges the integral closure inside a fixed top
ring.-/
noncomputable def integralClosureBaseChangeAlgHom
    {A : Type uA} {B : Type uB} {Ω : Type uO}
    [CommRing A] [CommRing B] [CommRing Ω]
    [Algebra A B] [Algebra A Ω]
    [Algebra B Ω] [IsScalarTower A B Ω] :
    integralClosure A Ω →ₐ[A] integralClosure B Ω where
  toFun x := ⟨x.1, x.2.tower_top⟩
  map_one' := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

/-- The canonical map from the old normalization to the normalization after
embedding its generic field into a field over a larger base.-/
noncomputable def integralClosureToCompositumAlgHom
    {A : Type uA} {B : Type uB} {L : Type uL} {Ω : Type uO}
    [CommRing A] [CommRing B] [CommRing L] [CommRing Ω]
    [Algebra A B] [Algebra A L] [Algebra A Ω]
    [Algebra B Ω] [IsScalarTower A B Ω]
    (f : L →ₐ[A] Ω) :
    integralClosure A L →ₐ[A] integralClosure B Ω :=
  integralClosureBaseChangeAlgHom.comp f.mapIntegralClosure

/--
@isnad1 id=eq.0h6v.s9.79e8a7005b2b from=translated src=- shape=f04a7c8b vocab=4b4deb54
-/
@[simp]
theorem integralClosureToCompositumAlgHom_coe
    {A : Type uA} {B : Type uB} {L : Type uL} {Ω : Type uO}
    [CommRing A] [CommRing B] [CommRing L] [CommRing Ω]
    [Algebra A B] [Algebra A L] [Algebra A Ω]
    [Algebra B Ω] [IsScalarTower A B Ω]
    (f : L →ₐ[A] Ω) (x : integralClosure A L) :
    ((integralClosureToCompositumAlgHom f x : integralClosure B Ω) : Ω) =
      f (x : L) :=
  rfl

/-- The normalization map is injective whenever the chosen generic-field
map is injective.
@isnad1 id=injectiv.1h5v.s9.d2d7b5eb7276 from=translated src=- shape=d5112dd3 vocab=fef33e6c
-/
theorem integralClosureToCompositumAlgHom_injective
    {A : Type uA} {B : Type uB} {L : Type uL} {Ω : Type uO}
    [CommRing A] [CommRing B] [CommRing L] [CommRing Ω]
    [Algebra A B] [Algebra A L] [Algebra A Ω]
    [Algebra B Ω] [IsScalarTower A B Ω]
    (f : L →ₐ[A] Ω) (hf : Function.Injective f) :
    Function.Injective
      (integralClosureToCompositumAlgHom
        (A := A) (B := B) (L := L) (Ω := Ω) f) := by
  intro x y hxy
  apply Subtype.ext
  apply hf
  exact congrArg
    (fun z : integralClosure B Ω ↦ (z : Ω)) hxy

/-- The algebra structure on the new normalization induced by the preceding
canonical embedding.  It is kept explicit rather than registered globally.-/
noncomputable abbrev integralClosureToCompositumAlgebra
    {A : Type uA} {B : Type uB} {L : Type uL} {Ω : Type uO}
    [CommRing A] [CommRing B] [CommRing L] [CommRing Ω]
    [Algebra A B] [Algebra A L] [Algebra A Ω]
    [Algebra B Ω] [IsScalarTower A B Ω]
    (f : L →ₐ[A] Ω) :
    Algebra (integralClosure A L) (integralClosure B Ω) :=
  (integralClosureToCompositumAlgHom f).toAlgebra

/-- If the base change `B / A` is integral, then the compositum
normalization is integral over the old normalization.
@isnad1 id=isintegr.0h5v.s8.fa762f270b6a from=translated src=- shape=0ba7740c vocab=3e672d4b
-/
theorem integralClosureToCompositum_isIntegral
    {A : Type uA} {B : Type uB} {L : Type uL} {Ω : Type uO}
    [CommRing A] [CommRing B] [CommRing L] [CommRing Ω]
    [Algebra A B] [Algebra.IsIntegral A B]
    [Algebra A L] [Algebra A Ω]
    [Algebra B Ω] [IsScalarTower A B Ω]
    (f : L →ₐ[A] Ω) :
    letI := integralClosureToCompositumAlgebra
      (A := A) (B := B) (L := L) (Ω := Ω) f
    Algebra.IsIntegral (integralClosure A L) (integralClosure B Ω) := by
  let : Algebra (integralClosure A L) (integralClosure B Ω) :=
    integralClosureToCompositumAlgebra
      (A := A) (B := B) (L := L) (Ω := Ω) f
  let : IsScalarTower A (integralClosure A L) (integralClosure B Ω) :=
    IsScalarTower.of_algebraMap_eq fun x ↦
      (integralClosureToCompositumAlgHom
        (A := A) (B := B) (L := L) (Ω := Ω) f).commutes x |>.symm
  let : Algebra.IsIntegral B (integralClosure B Ω) :=
    IsIntegralClosure.isIntegral_algebra B Ω
  let : Algebra.IsIntegral A (integralClosure B Ω) :=
    Algebra.IsIntegral.trans B
  exact Algebra.IsIntegral.tower_top A

/-- A chosen prime of the old normalization has a prime above it in the
compositum normalization.  Both the integral extension and injectivity are
derived from the source field embedding and the integral base change.
@isnad1 id=ex.1h6v.s9.ca798f13ed5d from=translated src=- shape=34713206 vocab=326a66c2
-/
theorem exists_integralClosureCompositum_prime_liesOver
    {A : Type uA} {B : Type uB} {L : Type uL} {Ω : Type uO}
    [CommRing A] [CommRing B] [CommRing L] [CommRing Ω]
    [Algebra A B] [Algebra.IsIntegral A B]
    [Algebra A L] [Algebra A Ω]
    [Algebra B Ω] [IsScalarTower A B Ω]
    (f : L →ₐ[A] Ω) (hf : Function.Injective f)
    (Q : Ideal (integralClosure A L)) [Q.IsPrime] :
    letI := integralClosureToCompositumAlgebra
      (A := A) (B := B) (L := L) (Ω := Ω) f
    ∃ q : Ideal (integralClosure B Ω), q.IsPrime ∧ q.LiesOver Q := by
  let : Algebra (integralClosure A L) (integralClosure B Ω) :=
    integralClosureToCompositumAlgebra
      (A := A) (B := B) (L := L) (Ω := Ω) f
  let : Algebra.IsIntegral (integralClosure A L) (integralClosure B Ω) :=
    integralClosureToCompositum_isIntegral
      (A := A) (B := B) (L := L) (Ω := Ω) f
  have hinjective : Function.Injective
      (algebraMap (integralClosure A L) (integralClosure B Ω)) :=
    integralClosureToCompositumAlgHom_injective
      (A := A) (B := B) (L := L) (Ω := Ω) f hf
  obtain ⟨q, -, hqPrime, hqComap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral Q
      (⊥ : Ideal (integralClosure B Ω)) (by
        change RingHom.ker
          (algebraMap (integralClosure A L) (integralClosure B Ω)) ≤ Q
        rw [(RingHom.injective_iff_ker_eq_bot _).mp hinjective]
        exact bot_le)
  exact ⟨q, hqPrime, (Ideal.liesOver_iff q Q).mpr hqComap.symm⟩

end EtaleFundamentalGroups

end
