/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.Algebra.Algebra.Pi
import Tengoku.Seed.RingTheory.Idempotents

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Product decomposition from complete orthogonal idempotents

A finite complete orthogonal family `e : I → D` decomposes a commutative ring into
the product of the quotients `D / (1 - e i)`.  This file packages the bijectivity
statement in `CompleteOrthogonalIdempotents.bijective_pi` as ring and algebra
equivalences whose forward maps are definitionally the quotient maps.
-/

namespace CompleteOrthogonalIdempotents

variable {I : Type*} [Fintype I]

/-- The product decomposition induced by a finite complete orthogonal family.-/
noncomputable def quotientPiRingEquiv {D : Type*} [CommRing D] {e : I → D}
    (he : CompleteOrthogonalIdempotents e) :
    D ≃+* ∀ i, D ⧸ Ideal.span {1 - e i} :=
  RingEquiv.ofBijective
    (RingHom.pi fun i ↦ Ideal.Quotient.mk (Ideal.span {1 - e i}))
    he.bijective_pi

/--
@isnad1 id=eq.1h3v.s9.8cd197fb70ce from=translated src=- shape=2cb1f2a1 vocab=58a9791e
-/
@[simp]
theorem quotientPiRingEquiv_toRingHom {D : Type*} [CommRing D] {e : I → D}
    (he : CompleteOrthogonalIdempotents e) :
    he.quotientPiRingEquiv.toRingHom =
      RingHom.pi fun i ↦ Ideal.Quotient.mk (Ideal.span {1 - e i}) :=
  rfl

/--
@isnad1 id=eq.1h5v.s11.bef9bb5f5c37 from=translated src=- shape=f3f9fdb3 vocab=bf49ffa2
-/
@[simp]
theorem quotientPiRingEquiv_apply {D : Type*} [CommRing D] {e : I → D}
    (he : CompleteOrthogonalIdempotents e) (x : D) (i : I) :
    he.quotientPiRingEquiv x i =
      Ideal.Quotient.mk (Ideal.span {1 - e i}) x :=
  rfl

/-- The product decomposition as an equivalence over any base ring acting on `D`.-/
noncomputable def quotientPiAlgEquiv {B D : Type*} [CommRing B] [CommRing D]
    [Algebra B D] {e : I → D} (he : CompleteOrthogonalIdempotents e) :
    D ≃ₐ[B] ∀ i, D ⧸ Ideal.span {1 - e i} :=
  AlgEquiv.ofBijective
    (AlgHom.pi fun i ↦ Ideal.Quotient.mkₐ B (Ideal.span {1 - e i}))
    he.bijective_pi

/--
@isnad1 id=eq.1h4v.s10.e4db3880985f from=translated src=- shape=43e1c8ea vocab=dd7f845d
-/
@[simp]
theorem quotientPiAlgEquiv_toAlgHom {B D : Type*} [CommRing B] [CommRing D]
    [Algebra B D] {e : I → D} (he : CompleteOrthogonalIdempotents e) :
    (he.quotientPiAlgEquiv (B := B)).toAlgHom =
      AlgHom.pi fun i ↦ Ideal.Quotient.mkₐ B (Ideal.span {1 - e i}) :=
  rfl

/--
@isnad1 id=eq.1h6v.s10.583d3732ed9c from=translated src=- shape=ce11c036 vocab=05b42d0e
-/
@[simp]
theorem quotientPiAlgEquiv_apply {B D : Type*} [CommRing B] [CommRing D]
    [Algebra B D] {e : I → D} (he : CompleteOrthogonalIdempotents e)
    (x : D) (i : I) :
    (he.quotientPiAlgEquiv (B := B)) x i =
      Ideal.Quotient.mk (Ideal.span {1 - e i}) x :=
  rfl

end CompleteOrthogonalIdempotents
