/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.Algebra.Category.Ring.Under.Basic
import Tengoku.Seed.CategoryTheory.Limits.Cones
import Tengoku.Seed.RingTheory.TensorProduct.Maps

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Literal tensor-product legs of algebra cocones

The categorical base-change functor stores its objects with the algebra
structure induced by an object of `Under`.  Downstream algebra calculations
use the canonical tensor-product algebra structure instead.  This file is the
single boundary between those two presentations: it exposes literal canonical
algebra homomorphisms, proves that their `Under` morphisms are the mapped
cocone legs, and records naturality and the tensor-symmetry square.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace EtaleFundamentalGroups

universe u

/-- The algebra structure carried by an object under `CommRingCat.of R`,
spelled with the underlying type `R`.-/
local instance underCommRingCatAlgebra
    {R : Type u} [CommRing R] (A : Under (CommRingCat.of R)) : Algebra R A :=
  RingHom.toAlgebra A.hom.hom

/-- The literal tensor-product map induced by a leg of a cocone of
`R`-algebras, with the stage algebra in the left tensor coordinate.-/
def filteredTensorToColimitAlgHom
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {J : Type u} [SmallCategory J]
    {F : J ⥤ Under (CommRingCat.of R)} (c : Cocone F) (i : J) :
    (F.obj i ⊗[R] A) →ₐ[R] (c.pt ⊗[R] A) :=
  Algebra.TensorProduct.map
    (CommRingCat.toAlgHom (c.ι.app i)) (AlgHom.id R A)

/--
@isnad1 id=eq.0h8v.s12.1629cb8f6c38 from=translated src=- shape=209e3385 vocab=4c04fef7
-/
@[simp]
theorem filteredTensorToColimitAlgHom_tmul
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {J : Type u} [SmallCategory J]
    {F : J ⥤ Under (CommRingCat.of R)} (c : Cocone F) (i : J)
    (x : F.obj i) (a : A) :
    filteredTensorToColimitAlgHom c i (x ⊗ₜ[R] a) =
      CommRingCat.toAlgHom (c.ι.app i) x ⊗ₜ[R] a := by
  rfl

/-- The same cocone leg in the orientation used by categorical base change:
the fixed algebra is the left tensor coordinate and hence the scalar ring.-/
def filteredBaseChangeCoconeLegAlgHom
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {J : Type u} [SmallCategory J]
    {F : J ⥤ Under (CommRingCat.of R)} (c : Cocone F) (i : J) :
    (A ⊗[R] F.obj i) →ₐ[A] (A ⊗[R] c.pt) :=
  Algebra.TensorProduct.map
    (AlgHom.id A A) (CommRingCat.toAlgHom (c.ι.app i))

/--
@isnad1 id=eq.0h8v.s12.627f5ee3f322 from=translated src=- shape=7c2f36b7 vocab=92fecbce
-/
@[simp]
theorem filteredBaseChangeCoconeLegAlgHom_tmul
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {J : Type u} [SmallCategory J]
    {F : J ⥤ Under (CommRingCat.of R)} (c : Cocone F) (i : J)
    (a : A) (x : F.obj i) :
    filteredBaseChangeCoconeLegAlgHom c i (a ⊗ₜ[R] x) =
      a ⊗ₜ[R] CommRingCat.toAlgHom (c.ι.app i) x := by
  rfl

/-- The literal base-change leg is exactly the leg of the categorically
mapped cocone after forgetting back to `Under`.
@isnad1 id=eq.0h6v.s11.4f34a04d1d13 from=translated src=- shape=383716d4 vocab=fd9ca09a
-/
theorem filteredBaseChangeCoconeLegAlgHom_toUnder
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {J : Type u} [SmallCategory J]
    {F : J ⥤ Under (CommRingCat.of R)} (c : Cocone F) (i : J) :
    (filteredBaseChangeCoconeLegAlgHom c i).toUnder =
      ((CommRingCat.tensorProd (CommRingCat.of R) (CommRingCat.of A)).mapCocone c).ι.app i :=
  rfl

/-- Naturality of the literal base-change cocone legs.
@isnad1 id=eq.0h8v.s11.02a753f8a1ff from=translated src=- shape=a5735db7 vocab=377ea2de
-/
theorem filteredBaseChangeCoconeLegAlgHom_naturality
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {J : Type u} [SmallCategory J]
    {F : J ⥤ Under (CommRingCat.of R)} (c : Cocone F)
    {i j : J} (f : i ⟶ j) :
    (filteredBaseChangeCoconeLegAlgHom c j).comp
        (Algebra.TensorProduct.map (AlgHom.id A A)
          (CommRingCat.toAlgHom (F.map f))) =
      filteredBaseChangeCoconeLegAlgHom c i := by
  apply Algebra.TensorProduct.ext_ring
  ext x
  have h := congrArg (fun q ↦ q.right x) (c.w f)
  change CommRingCat.toAlgHom (c.ι.app j)
      (CommRingCat.toAlgHom (F.map f) x) =
    CommRingCat.toAlgHom (c.ι.app i) x at h
  exact congrArg (fun y ↦ (1 : A) ⊗ₜ[R] y) h

/-- Swapping tensor factors intertwines the two literal versions of a cocone
leg.
@isnad1 id=eq.0h7v.s13.0edcdebf7fb5 from=translated src=- shape=d7357b68 vocab=2f8bdf71
-/
theorem filteredBaseChangeCoconeLegAlgHom_comm
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {J : Type u} [SmallCategory J]
    {F : J ⥤ Under (CommRingCat.of R)} (c : Cocone F) (i : J)
    (z : F.obj i ⊗[R] A) :
    filteredBaseChangeCoconeLegAlgHom c i
        ((Algebra.TensorProduct.comm R (F.obj i) A) z) =
      (Algebra.TensorProduct.comm R c.pt A)
        (filteredTensorToColimitAlgHom c i z) := by
  exact (Algebra.TensorProduct.comm_comp_map_apply
    (CommRingCat.toAlgHom (c.ι.app i)) (AlgHom.id R A) z).symm

end EtaleFundamentalGroups

end
