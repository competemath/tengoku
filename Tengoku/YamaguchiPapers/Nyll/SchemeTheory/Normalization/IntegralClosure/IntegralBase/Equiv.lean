/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Tengoku.Seed.RingTheory.RingHom.Etale

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Integral closure after an integral enlargement of the base

If `A → B` is integral and both rings act compatibly on the same ambient
ring `L`, an element of `L` is integral over `A` exactly when it is integral
over `B`.  Thus the two literal integral-closure types are canonically
equivalent.  This is the comparison used when a radical root ring has already
been embedded in a chosen normalization factor.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe uA uB uL

variable {A : Type uA} {B : Type uB} {L : Type uL}
variable [CommRing A] [CommRing B] [CommRing L]
variable [Algebra A B] [Algebra A L] [Algebra B L]
variable [IsScalarTower A B L] [Algebra.IsIntegral A B]

/-- The canonical `B`-algebra structure on the `A`-integral closure inside
`L`.  Integrality of `B / A` makes the lift land in the integral closure.-/
@[reducible]
noncomputable def integralClosureIntegralBaseAlgebra :
    Algebra B (integralClosure A L) :=
  (IsIntegralClosure.lift A (integralClosure A L) L).toRingHom.toAlgebra

/-- The canonical lift of `B` into the `A`-integral closure is compatible
with the original map `A → B`.
@isnad1 id=isscalar.0h3v.s8.3306439953ab from=translated src=- shape=f1e5b386 vocab=c377fa58
-/
theorem integralClosureIntegralBase_isScalarTower :
    letI : Algebra B (integralClosure A L) :=
      integralClosureIntegralBaseAlgebra
    IsScalarTower A B (integralClosure A L) := by
  let : Algebra B (integralClosure A L) :=
    integralClosureIntegralBaseAlgebra
  exact IsScalarTower.of_algebraMap_eq fun a ↦
    (IsIntegralClosure.lift A (integralClosure A L) L).commutes a |>.symm

/-- The canonical lift into the integral closure has the expected composite
map to the ambient ring.
@isnad1 id=isscalar.0h3v.s8.bf2fc9dfee88 from=translated src=- shape=0be222e9 vocab=c377fa58
-/
theorem integralClosureIntegralBase_toAmbient_isScalarTower :
    letI : Algebra B (integralClosure A L) :=
      integralClosureIntegralBaseAlgebra
    IsScalarTower B (integralClosure A L) L := by
  let : Algebra B (integralClosure A L) :=
    integralClosureIntegralBaseAlgebra
  exact IsScalarTower.of_algebraMap_eq fun b ↦
    (IsIntegralClosure.algebraMap_lift A (integralClosure A L) L b).symm

/-- Enlarging a base integrally does not change its integral closure inside
one fixed ambient ring.-/
noncomputable def integralClosureIntegralBaseAlgEquiv :
    letI : Algebra B (integralClosure A L) :=
      integralClosureIntegralBaseAlgebra
    integralClosure B L ≃ₐ[B] integralClosure A L := by
  letI : Algebra B (integralClosure A L) :=
    integralClosureIntegralBaseAlgebra
  letI : IsScalarTower A B (integralClosure A L) :=
    integralClosureIntegralBase_isScalarTower
  letI : IsScalarTower B (integralClosure A L) L :=
    integralClosureIntegralBase_toAmbient_isScalarTower
  letI : IsIntegralClosure (integralClosure A L) B L :=
    IsIntegralClosure.tower_top (R := A) (A := B) (B := L)
      (C := integralClosure A L)
  exact IsIntegralClosure.equiv B (integralClosure B L) L
    (integralClosure A L)

/-- Module finiteness over the enlarged base is unchanged by writing the
same normalization as the integral closure over the original base.
@isnad1 id=finite.0h3v.s8.88b690efa1d5 from=translated src=- shape=3948c88d vocab=38ae0326
-/
theorem moduleFinite_integralClosure_of_integralBase
    [Module.Finite B (integralClosure B L)] :
    letI : Algebra B (integralClosure A L) :=
      integralClosureIntegralBaseAlgebra
    Module.Finite B (integralClosure A L) := by
  let : Algebra B (integralClosure A L) :=
    integralClosureIntegralBaseAlgebra
  exact Module.Finite.equiv
    integralClosureIntegralBaseAlgEquiv.toLinearEquiv

/-- Etaleness over the enlarged integral base transports to the same
normalization written as the integral closure over the original base.
@isnad1 id=etale.1h3v.s8.ea26f41f0cbe from=translated src=- shape=3948c88d vocab=9cdb64fd
-/
theorem integralClosure_etale_of_integralBase
    (hEtale : Algebra.Etale B (integralClosure B L)) :
    letI : Algebra B (integralClosure A L) :=
      integralClosureIntegralBaseAlgebra
    Algebra.Etale B (integralClosure A L) := by
  let : Algebra B (integralClosure A L) :=
    integralClosureIntegralBaseAlgebra
  let : Algebra.Etale B (integralClosure B L) := hEtale
  exact Algebra.Etale.of_equiv integralClosureIntegralBaseAlgEquiv

/-- The preceding equivalence is the identity after coercion to the common
ambient ring.
@isnad1 id=eq.0h4v.s10.a7917e1282b2 from=translated src=- shape=e4dbe476 vocab=6414cbbe
-/
@[simp]
theorem algebraMap_integralClosureIntegralBaseAlgEquiv
    (x : integralClosure B L) :
    letI : Algebra B (integralClosure A L) :=
      integralClosureIntegralBaseAlgebra
    algebraMap (integralClosure A L) L
        (integralClosureIntegralBaseAlgEquiv x) =
      algebraMap (integralClosure B L) L x := by
  let : Algebra B (integralClosure A L) :=
    integralClosureIntegralBaseAlgebra
  let : IsScalarTower A B (integralClosure A L) :=
    integralClosureIntegralBase_isScalarTower
  let : IsScalarTower B (integralClosure A L) L :=
    integralClosureIntegralBase_toAmbient_isScalarTower
  let : IsIntegralClosure (integralClosure A L) B L :=
    IsIntegralClosure.tower_top (R := A) (A := B) (B := L)
      (C := integralClosure A L)
  exact IsIntegralClosure.algebraMap_equiv B (integralClosure B L) L
    (integralClosure A L) x

end EtaleFundamentalGroups

end
