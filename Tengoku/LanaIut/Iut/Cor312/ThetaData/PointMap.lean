/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Tengoku.Seed.AlgebraicGeometry.EllipticCurve.Affine.Point

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Points of Weierstrass curves along ring homomorphisms

`Iut.Anabelian.pointMap E f : E(k) →+ (E.map f)(K)` for a ring homomorphism of fields
`f : k →+* K` (Mathlib's `WeierstrassCurve.Affine.Point.map` for the base change `E.map f`),
with its basic properties.
-/

namespace Iut.Anabelian

open WeierstrassCurve
open scoped Classical

/-! ## Points of Weierstrass curves along ring homomorphisms -/

section PointMap

variable {k K L : Type*} [Field k] [Field K] [Field L]

/-- The group homomorphism on points induced by a ring homomorphism of fields
(`WeierstrassCurve.Affine.Point.map` for the base change `E.map f`). -/
noncomputable def pointMap (E : WeierstrassCurve k) (f : k →+* K) :
    E.toAffine.Point →+ (E.map f).toAffine.Point :=
  letI := f.toAlgebra
  Affine.Point.map (W' := E) (S := k) (F := k) (K := K) (Algebra.ofId k K)

variable (E : WeierstrassCurve k) (f : k →+* K)

/--
@isnad1 id=eq.0h4v.s8.6eb8f9674145 from=translated src=- shape=092129a8 vocab=c6295a95
-/
@[simp] lemma pointMap_zero : pointMap E f 0 = 0 := rfl

/--
@isnad1 id=eq.1h6v.s8.40e257d254e1 from=translated src=- shape=527d2c9f vocab=aa128074
-/
lemma pointMap_some {x y : k} (h : E.toAffine.Nonsingular x y) :
    pointMap E f (Affine.Point.some x y h) =
      Affine.Point.some (f x) (f y) ((E.toAffine.map_nonsingular f.injective x y).mpr h) := rfl

/--
@isnad1 id=injectiv.0h4v.s8.681274a1b571 from=translated src=- shape=b2a858f4 vocab=0ab91478
-/
lemma pointMap_injective : Function.Injective (pointMap E f) := by
  letI := f.toAlgebra
  exact Affine.Point.map_injective (W' := E) (S := k) (F := k) (K := K) (Algebra.ofId k K)

/--
@isnad1 id=eq.0h7v.s10.e84a38fb6da1 from=translated src=- shape=ce790dce vocab=5cf46a06
-/
lemma pointMap_map (g : K →+* L) (P : E.toAffine.Point) :
    pointMap (E.map f) g (pointMap E f P) = pointMap E (g.comp f) P := by
  cases P <;> rfl

/--
@isnad1 id=eq.0h3v.s8.b2d34c887835 from=translated src=- shape=cf088f4b vocab=2377d19b
-/
lemma pointMap_id (P : E.toAffine.Point) : pointMap E (RingHom.id k) P = P := by
  cases P <;> rfl

end PointMap

end Iut.Anabelian
